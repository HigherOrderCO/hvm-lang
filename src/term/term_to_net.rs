use crate::{
  net::{
    INet,
    NodeKind::{self, *},
    Port, ROOT,
  },
  term::{Book, Name, NumCtr, Op, Tag, Term},
};
use std::collections::{hash_map::Entry, HashMap};

pub fn book_to_nets(book: &Book) -> (HashMap<String, INet>, Labels) {
  let mut nets = HashMap::new();
  let mut labels = Labels::default();

  let main = book.entrypoint.as_ref().unwrap();

  for def in book.defs.values() {
    for rule in def.rules.iter() {
      let net = term_to_compat_net(&rule.body, &mut labels);

      let name = if def.name == *main { book.hvmc_entrypoint().to_string() } else { def.name.0.to_string() };

      nets.insert(name, net);
    }
  }

  labels.con.finish();
  labels.dup.finish();

  (nets, labels)
}

/// Converts an IC term into an IC net.
pub fn term_to_compat_net(term: &Term, labels: &mut Labels) -> INet {
  let mut state = EncodeTermState {
    inet: Default::default(),
    scope: Default::default(),
    vars: Default::default(),
    global_vars: Default::default(),
    labels,
  };

  let main = state.encode_term(term, ROOT);

  for (decl_port, use_port) in std::mem::take(&mut state.global_vars).into_values() {
    state.inet.link(decl_port, use_port);
  }
  if Some(ROOT) != main {
    state.link_local(ROOT, main);
  }

  state.inet
}

#[derive(Debug)]
struct EncodeTermState<'a> {
  inet: INet,
  scope: HashMap<Name, Vec<usize>>,
  vars: Vec<(Port, Option<Port>)>,
  global_vars: HashMap<Name, (Port, Port)>,
  labels: &'a mut Labels,
}

impl EncodeTermState<'_> {
  /// Adds a subterm connected to `up` to the `inet`.
  /// `scope` has the current variable scope.
  /// `vars` has the information of which ports the variables are declared and used in.
  /// `global_vars` has the same information for global lambdas. Must be linked outside this function.
  /// Expects variables to be affine, refs to be stored as Refs and all names to be bound.
  fn encode_term(&mut self, term: &Term, up: Port) -> Option<Port> {
    Term::recursive_call(move || {
      match term {
        // A lambda becomes to a con node. Ports:
        // - 0: points to where the lambda occurs.
        // - 1: points to the lambda variable.
        // - 2: points to the lambda body.
        // core: (var_use bod)
        Term::Lam { tag, nam, bod } => {
          let fun = self.inet.new_node(Con { lab: self.labels.con.generate(tag) });

          self.push_scope(nam, Port(fun, 1));
          let bod = self.encode_term(bod, Port(fun, 2));
          self.pop_scope(nam, Port(fun, 1));
          self.link_local(Port(fun, 2), bod);

          Some(Port(fun, 0))
        }
        // core: (var_use bod)
        Term::Chn { tag, nam, bod } => {
          let fun = self.inet.new_node(Con { lab: self.labels.con.generate(tag) });
          if let Some(nam) = nam {
            self.global_vars.entry(nam.clone()).or_default().0 = Port(fun, 1);
          }
          let bod = self.encode_term(bod, Port(fun, 2));
          self.link_local(Port(fun, 2), bod);
          Some(Port(fun, 0))
        }
        // An application becomes to a con node too. Ports:
        // - 0: points to the function being applied.
        // - 1: points to the function's argument.
        // - 2: points to where the application occurs.
        // core: & fun ~ (arg ret) (fun not necessarily main port)
        Term::App { tag, fun, arg } => {
          let app = self.inet.new_node(Con { lab: self.labels.con.generate(tag) });

          let fun = self.encode_term(fun, Port(app, 0));
          self.link_local(Port(app, 0), fun);

          let arg = self.encode_term(arg, Port(app, 1));
          self.link_local(Port(app, 1), arg);

          Some(Port(app, 2))
        }
        Term::Mat { .. } => unreachable!("Should've been desugared already"),
        // core: & arg ~ ?<(zero succ) ret>
        Term::Swt { arg, rules } => {
          // At this point should be only num matches of 0 and succ.
          debug_assert!(rules.len() == 2);
          debug_assert!(matches!(rules[0].0, NumCtr::Num(0)));
          debug_assert!(matches!(rules[1].0, NumCtr::Succ(None)));

          let mat = self.inet.new_node(Mat);

          let arg = self.encode_term(arg, Port(mat, 0));
          self.link_local(Port(mat, 0), arg);

          let zero = &rules[0].1;
          let succ = &rules[1].1;

          let sel = self.inet.new_node(Con { lab: None });
          self.inet.link(Port(sel, 0), Port(mat, 1));
          let zero = self.encode_term(zero, Port(sel, 1));
          self.link_local(Port(sel, 1), zero);

          let succ = self.encode_term(succ, Port(sel, 2));
          self.link_local(Port(sel, 2), succ);

          Some(Port(mat, 2))
        }
        // A dup becomes a dup node too. Ports for dups of size 2:
        // - 0: points to the value projected.
        // - 1: points to the occurrence of the first variable.
        // - 2: points to the occurrence of the second variable.
        // core: & val ~ {lab fst snd} (val not necessarily main port)
        // Dups with more than 2 variables become a list-like node tree of n-1 nodes.
        // All the nodes of a dup tree have the same label.
        // `@x dup #i {x0 x1 x2 x3}; A` => `({i x0 {i x1 {i x2 x3}}} A)`
        Term::Dup { tag, bnd, val, nxt } => {
          let lab = self.labels.dup.generate(tag).unwrap();
          let (main, aux) = self.make_node_list(Dup { lab }, bnd.len());

          let val = self.encode_term(val, main);
          self.link_local(main, val);

          for (bnd, aux) in bnd.iter().zip(aux.iter()) {
            self.push_scope(bnd, *aux);
          }

          let nxt = self.encode_term(nxt, up);

          for (bnd, aux) in bnd.iter().rev().zip(aux.iter().rev()) {
            self.pop_scope(bnd, *aux);
          }

          nxt
        }
        Term::Var { nam } => {
          // We assume this variable to be valid, bound and correctly scoped.
          // This pass must be done before.
          debug_assert!(
            self.scope.contains_key(nam),
            "Unbound variable {nam}. Expected this check to be already done"
          );
          let var_stack = &self.scope[nam];
          let cur_var = *var_stack.last().unwrap();
          let (declare_port, use_port) = self.vars.get_mut(cur_var).unwrap();
          debug_assert!(use_port.is_none(), "Variable {nam} used more than once");
          self.inet.link(up, *declare_port);
          *use_port = Some(up);
          Some(*declare_port)
        }
        Term::Lnk { nam } => {
          self.global_vars.entry(nam.clone()).or_default().1 = up;
          None
        }
        // core: @def_id
        Term::Ref { nam: def_name } => {
          let node = self.inet.new_node(Ref { def_name: def_name.clone() });
          self.inet.link(Port(node, 1), Port(node, 2));
          self.inet.link(up, Port(node, 0));
          Some(Port(node, 0))
        }
        Term::Ltp { bnd, val, nxt } => {
          let (main, aux) = self.make_node_list(Tup, bnd.len());

          let val = self.encode_term(val, main);
          self.link_local(main, val);

          for (nam, aux) in bnd.iter().zip(aux.iter()) {
            self.push_scope(nam, *aux);
          }
          let nxt = self.encode_term(nxt, up);
          for (nam, aux) in bnd.iter().rev().zip(aux.iter().rev()) {
            self.pop_scope(nam, *aux);
          }

          nxt
        }
        Term::Let { nam: None, val, nxt } => {
          let nod = self.inet.new_node(Era);
          let val = self.encode_term(val, Port(nod, 0));

          self.link_local(Port(nod, 0), val);

          self.encode_term(nxt, up)
        }
        Term::Let { .. } => unreachable!(), // Removed in earlier pass
        Term::Use { .. } => unreachable!(), // Removed in earlier pass
        Term::Sup { tag, els } => {
          let lab = self.labels.dup.generate(tag).unwrap();
          let (main, aux) = self.make_node_list(Dup { lab }, els.len());

          for (el, aux) in els.iter().zip(aux) {
            let el = self.encode_term(el, aux);
            self.link_local(aux, el);
          }

          Some(main)
        }
        Term::Era => {
          let era = self.inet.new_node(Era);
          self.inet.link(Port(era, 1), Port(era, 2));
          Some(Port(era, 0))
        }
        // core: #val
        Term::Num { val } => {
          let node = self.inet.new_node(Num { val: *val });
          // This representation only has nodes of arity 2, so we connect the two aux ports that are not used.
          self.inet.link(Port(node, 1), Port(node, 2));
          Some(Port(node, 0))
        }
        Term::Nat { .. } => unreachable!(), // Removed in encode_nat
        Term::Str { .. } => unreachable!(), // Removed in encode_str
        Term::Lst { .. } => unreachable!(), // Removed in encode_list
        // core: & fst ~ <op snd ret>
        Term::Opx { op, fst, snd } => {
          let opx = self.inet.new_node(Op2 { opr: op.to_hvmc_label() });

          let fst_port = self.encode_term(fst, Port(opx, 0));
          self.link_local(Port(opx, 0), fst_port);

          let snd_port = self.encode_term(snd, Port(opx, 1));
          self.link_local(Port(opx, 1), snd_port);

          Some(Port(opx, 2))
        }
        Term::Tup { els } => {
          let (main, aux) = self.make_node_list(Tup, els.len());
          for (el, aux) in els.iter().zip(aux.iter()) {
            let el = self.encode_term(el, *aux);
            self.link_local(*aux, el);
          }

          Some(main)
        }
        Term::Err => unreachable!(),
      }
    })
  }

  fn push_scope(&mut self, name: &Option<Name>, decl_port: Port) {
    if let Some(name) = name {
      self.scope.entry(name.clone()).or_default().push(self.vars.len());
      self.vars.push((decl_port, None));
    }
  }

  fn pop_scope(&mut self, name: &Option<Name>, decl_port: Port) {
    if let Some(name) = name {
      self.scope.get_mut(name).unwrap().pop().unwrap();
    } else {
      let era = self.inet.new_node(Era);
      self.inet.link(decl_port, Port(era, 0));
      self.inet.link(Port(era, 1), Port(era, 2));
    }
  }

  fn link_local(&mut self, ptr_a: Port, ptr_b: Option<Port>) {
    if let Some(ptr_b) = ptr_b {
      self.inet.link(ptr_a, ptr_b);
    }
  }

  /// Adds a list-like tree of nodes of the same kind to the inet.
  /// Doesn't attach this tree to anything
  fn make_node_list(&mut self, kind: NodeKind, num_ports: usize) -> (Port, Vec<Port>) {
    debug_assert!(num_ports >= 2);
    let nodes: Vec<_> = (0 .. num_ports - 1).map(|_| self.inet.new_node(kind.clone())).collect();

    let mut up = Some(Port(nodes[0], 2));
    for &node in nodes.iter().skip(1) {
      self.link_local(Port(node, 0), up);
      up = Some(Port(node, 2));
    }

    let main_port = Port(nodes[0], 0);
    let mut aux_ports = nodes.iter().map(|n| Port(*n, 1)).collect::<Vec<_>>();
    aux_ports.push(Port(*nodes.last().unwrap(), 2));
    (main_port, aux_ports)
  }
}

impl Op {
  pub fn to_hvmc_label(self) -> hvmc::ops::Op {
    use hvmc::ops::Op as RtOp;
    match self {
      Op::Add => RtOp::Add,
      Op::Sub => RtOp::Sub,
      Op::Mul => RtOp::Mul,
      Op::Div => RtOp::Div,
      Op::Mod => RtOp::Mod,
      Op::Eq => RtOp::Eq,
      Op::Ne => RtOp::Ne,
      Op::Lt => RtOp::Lt,
      Op::Gt => RtOp::Gt,
      Op::Lte => RtOp::Lte,
      Op::Gte => RtOp::Gte,
      Op::And => RtOp::And,
      Op::Or => RtOp::Or,
      Op::Xor => RtOp::Xor,
      Op::Shl => RtOp::Shl,
      Op::Shr => RtOp::Shr,
    }
  }
}

#[derive(Debug, Default, Clone)]
pub struct Labels {
  pub con: LabelGenerator,
  pub dup: LabelGenerator,
}

#[derive(Debug, Default, Clone)]
pub struct LabelGenerator {
  pub next: u32,
  pub name_to_label: HashMap<Name, u32>,
  pub label_to_name: HashMap<u32, Name>,
}

impl LabelGenerator {
  // If some tag and new generate a new label, otherwise return the generated label.
  // If none use the implicit label counter.
  fn generate(&mut self, tag: &Tag) -> Option<u32> {
    let mut unique = || {
      let lab = self.next;
      self.next += 1;
      lab
    };
    match tag {
      Tag::Named(name) => match self.name_to_label.entry(name.clone()) {
        Entry::Occupied(e) => Some(*e.get()),
        Entry::Vacant(e) => {
          let lab = unique();
          self.label_to_name.insert(lab, name.clone());
          Some(*e.insert(lab))
        }
      },
      Tag::Numeric(lab) => Some(*lab),
      Tag::Auto => Some(unique()),
      Tag::Static => None,
    }
  }

  pub fn to_tag(&self, label: Option<u32>) -> Tag {
    match label {
      Some(label) => match self.label_to_name.get(&label) {
        Some(name) => Tag::Named(name.clone()),
        None => Tag::Numeric(label),
      },
      None => Tag::Static,
    }
  }

  fn finish(&mut self) {
    self.next = u32::MAX;
    self.name_to_label.clear();
  }
}
