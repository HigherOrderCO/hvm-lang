use crate::{
  diagnostics::{DiagnosticOrigin, Diagnostics, Severity},
  net::{INet, NodeId, NodeKind::*, Port, SlotId, ROOT},
  term::{num_to_name, term_to_net::Labels, Book, Name, Op, Tag, Term},
};
use std::collections::{BTreeSet, HashMap, HashSet};

// TODO: Display scopeless lambdas as such
/// Converts an Interaction-INet to a Lambda Calculus term
pub fn net_to_term(
  net: &INet,
  book: &Book,
  labels: &Labels,
  linear: bool,
  diagnostics: &mut Diagnostics,
) -> Term {
  let mut reader = Reader {
    net,
    labels,
    book,
    dup_paths: if linear { None } else { Some(Default::default()) },
    scope: Default::default(),
    seen_fans: Default::default(),
    namegen: Default::default(),
    seen: Default::default(),
    errors: Default::default(),
  };

  let mut term = reader.read_term(net.enter_port(ROOT));

  while let Some(node) = reader.scope.pop_first() {
    let val = reader.read_term(reader.net.enter_port(Port(node, 0)));
    let fst = reader.namegen.decl_name(net, Port(node, 1));
    let snd = reader.namegen.decl_name(net, Port(node, 2));

    let tag = match reader.net.node(node).kind {
      Tup => None,
      Dup { lab } => Some(reader.labels.dup.to_tag(Some(lab))),
      _ => unreachable!(),
    };

    let split = &mut Split { tag, fst, snd, val };

    let uses = term.insert_split(split, usize::MAX).unwrap();
    let result = term.insert_split(split, uses);
    debug_assert_eq!(result, None);
  }

  reader.report_errors(diagnostics);
  term
}

// BTreeSet for consistent readback of dups
type Scope = BTreeSet<NodeId>;

pub struct Reader<'a> {
  pub book: &'a Book,
  pub namegen: NameGen,
  net: &'a INet,
  labels: &'a Labels,
  dup_paths: Option<HashMap<u32, Vec<SlotId>>>,
  /// Store for floating/unscoped terms, like dups and let tups.
  scope: Scope,
  seen_fans: Scope,
  seen: HashSet<Port>,
  errors: Vec<ReadbackError>,
}

impl Reader<'_> {
  fn read_term(&mut self, next: Port) -> Term {
    Term::recursive_call(move || {
      if self.dup_paths.is_none() && !self.seen.insert(next) {
        self.error(ReadbackError::Cyclic);
        return Term::Var { nam: Name::from("...") };
      }

      let node = next.node();

      let term = match &self.net.node(node).kind {
        Era => {
          // Only the main port actually exists in an ERA, the aux ports are just an artifact of this representation.
          debug_assert!(next.slot() == 0);
          Term::Era
        }
        // If we're visiting a con node...
        Con { lab } => match next.slot() {
          // If we're visiting a port 0, then it is a lambda.
          0 => {
            let nam = self.namegen.decl_name(self.net, Port(node, 1));
            let bod = self.read_term(self.net.enter_port(Port(node, 2)));
            Term::Lam { tag: self.labels.con.to_tag(*lab), nam, bod: Box::new(bod) }
          }
          // If we're visiting a port 1, then it is a variable.
          1 => Term::Var { nam: self.namegen.var_name(next) },
          // If we're visiting a port 2, then it is an application.
          2 => {
            let fun = self.read_term(self.net.enter_port(Port(node, 0)));
            let arg = self.read_term(self.net.enter_port(Port(node, 1)));
            Term::App { tag: self.labels.con.to_tag(*lab), fun: Box::new(fun), arg: Box::new(arg) }
          }
          _ => unreachable!(),
        },
        Mat => match next.slot() {
          2 => {
            // Read the matched expression
            let mut arg = self.read_term(self.net.enter_port(Port(node, 0)));

            // Read the pattern matching node
            let sel_node = self.net.enter_port(Port(node, 1)).node();

            // We expect the pattern matching node to be a CON
            let sel_kind = &self.net.node(sel_node).kind;
            if *sel_kind != (Con { lab: None }) {
              // TODO: Is there any case where we expect a different node type here on readback?
              self.error(ReadbackError::InvalidNumericMatch);
              Term::switch(arg, Term::Era, Term::Era, None)
            } else {
              let zero_term = self.read_term(self.net.enter_port(Port(sel_node, 1)));
              let mut succ_term = self.read_term(self.net.enter_port(Port(sel_node, 2)));

              match &mut succ_term {
                Term::Lam { nam, bod, .. } => {
                  // Extract non-var args so we can refer to the pred.
                  let (arg, bind) = if let Term::Var { nam } = &mut arg {
                    (std::mem::replace(nam, Name::from("")), None)
                  } else {
                    (self.namegen.unique(), Some(arg))
                  };

                  let nam = std::mem::take(nam);
                  let mut bod = std::mem::take(bod);

                  // Rename the pred variable to indicate it's arg-1.
                  if let Some(nam) = &nam {
                    bod.subst(nam, &Term::Var { nam: Name::new(format!("{arg}-1")) });
                  }

                  let swt = Term::switch(Term::Var { nam: arg.clone() }, zero_term, *bod, nam);
                  if let Some(bind) = bind {
                    Term::Let { nam: Some(arg), val: Box::new(bind), nxt: Box::new(swt) }
                  } else {
                    swt
                  }
                }
                _ => {
                  self.error(ReadbackError::InvalidNumericMatch);
                  Term::switch(arg, zero_term, succ_term, None)
                }
              }
            }
          }
          _ => {
            self.error(ReadbackError::InvalidNumericMatch);
            Term::Err
          }
        },
        Ref { def_name } => {
          if def_name.is_generated() {
            // Dereference generated names since the user is not aware of them
            let def = &self.book.defs[def_name];
            let mut term = def.rule().body.clone();
            term.fix_names(&mut self.namegen.id_counter, self.book);

            term
          } else {
            Term::Ref { nam: def_name.clone() }
          }
        }
        // If we're visiting a fan node...
        Dup { lab } => match next.slot() {
          // If we're visiting a port 0, then it is a pair.
          0 => {
            if let Some(dup_paths) = &mut self.dup_paths {
              let stack = dup_paths.entry(*lab).or_default();
              if let Some(slot) = stack.pop() {
                // Since we had a paired Dup in the path to this Sup,
                // we "decay" the superposition according to the original direction we came from the Dup.
                let term = self.read_term(self.net.enter_port(Port(node, slot)));
                self.dup_paths.as_mut().unwrap().get_mut(lab).unwrap().push(slot);
                Some(term)
              } else {
                None
              }
            } else {
              None
            }
            .unwrap_or_else(|| {
              // If no Dup with same label in the path, we can't resolve the Sup, so keep it as a term.
              self.decay_or_get_ports(node).map_or_else(
                |(fst, snd)| Term::Sup { tag: self.labels.dup.to_tag(Some(*lab)), els: vec![fst, snd] },
                |term| term,
              )
            })
          }
          // If we're visiting a port 1 or 2, then it is a variable.
          // Also, that means we found a dup, so we store it to read later.
          1 | 2 => {
            if let Some(dup_paths) = &mut self.dup_paths {
              dup_paths.entry(*lab).or_default().push(next.slot());
              let term = self.read_term(self.net.enter_port(Port(node, 0)));
              self.dup_paths.as_mut().unwrap().entry(*lab).or_default().pop().unwrap();
              term
            } else {
              if self.seen_fans.insert(node) {
                self.scope.insert(node);
              }
              Term::Var { nam: self.namegen.var_name(next) }
            }
          }
          _ => unreachable!(),
        },
        Num { val } => Term::Num { val: *val },
        Op2 { opr } => match next.slot() {
          2 => {
            let fst = self.read_term(self.net.enter_port(Port(node, 0)));
            let snd = self.read_term(self.net.enter_port(Port(node, 1)));
            let (opr, fst, snd) = if is_op_swapped(*opr) { (opr.swap(), snd, fst) } else { (*opr, fst, snd) };
            Term::Opx { op: Op::from_hvmc_label(opr), fst: Box::new(fst), snd: Box::new(snd) }
          }
          _ => {
            self.error(ReadbackError::InvalidNumericOp);
            Term::Err
          }
        },
        Rot => {
          self.error(ReadbackError::ReachedRoot);
          Term::Err
        }
        Tup => match next.slot() {
          // If we're visiting a port 0, then it is a Tup.
          0 => self
            .decay_or_get_ports(node)
            .map_or_else(|(fst, snd)| Term::Tup { els: vec![fst, snd] }, |term| term),
          // If we're visiting a port 1 or 2, then it is a variable.
          1 | 2 => {
            if self.seen_fans.insert(node) {
              self.scope.insert(node);
            }
            Term::Var { nam: self.namegen.var_name(next) }
          }
          _ => unreachable!(),
        },
      };

      term
    })
  }

  /// Enters both ports 1 and 2 of a node,
  /// Returning a Term if is possible to simplify the net, or the Terms on the two ports of the node.
  /// The two possible outcomes are always equivalent.
  ///
  /// If:
  ///  - The node Kind is CON/TUP/DUP
  ///  - Both ports 1 and 2 are connected to the same node on slots 1 and 2 respectively
  ///  - That node Kind is the same as the given node Kind
  ///
  /// Then:
  ///   Reads the port 0 of the connected node, and returns that term.
  ///
  /// Otherwise:
  ///   Returns the terms on ports 1 and 2 of the given node.
  ///
  /// # Example
  ///
  /// ```hvm
  /// // λa let (a, b) = a; (a, b)
  /// ([a b] [a b])
  ///
  /// // The node `(a, b)` is just a reconstruction of the destructuring of `a`,
  /// // So we can skip both steps and just return the "value" unchanged:
  ///
  /// // λa a
  /// (a a)
  /// ```
  ///
  fn decay_or_get_ports(&mut self, node: NodeId) -> Result<Term, (Term, Term)> {
    let fst_port = self.net.enter_port(Port(node, 1));
    let snd_port = self.net.enter_port(Port(node, 2));

    let node_kind = &self.net.node(node).kind;

    // Eta-reduce the readback inet.
    // This is not valid for all kinds of nodes, only CON/TUP/DUP, due to their interaction rules.
    if matches!(node_kind, Con { .. } | Tup | Dup { .. }) {
      match (fst_port, snd_port) {
        (Port(fst_node, 1), Port(snd_node, 2)) if fst_node == snd_node => {
          if self.net.node(fst_node).kind == *node_kind {
            self.scope.remove(&fst_node);

            let port_zero = self.net.enter_port(Port(fst_node, 0));
            let term = self.read_term(port_zero);
            return Ok(term);
          }
        }
        _ => {}
      }
    }

    let fst = self.read_term(fst_port);
    let snd = self.read_term(snd_port);
    Err((fst, snd))
  }

  pub fn error(&mut self, error: ReadbackError) {
    self.errors.push(error);
  }

  pub fn report_errors(&mut self, diagnostics: &mut Diagnostics) {
    let mut err_counts = std::collections::HashMap::new();
    for err in &self.errors {
      *err_counts.entry(*err).or_insert(0) += 1;
    }

    for (err, count) in err_counts {
      let count_msg = if count > 1 { format!(" ({count} occurrences)") } else { "".to_string() };
      let msg = format!("{}{}", err, count_msg);
      diagnostics.add_diagnostic(msg.as_str(), Severity::Warning, DiagnosticOrigin::Readback);
    }
  }
}

/// Represents `let (fst, snd) = val` if `tag` is `None`, and `dup#tag fst snd = val` otherwise.
#[derive(Default)]
struct Split {
  tag: Option<Tag>,
  fst: Option<Name>,
  snd: Option<Name>,
  val: Term,
}

impl Term {
  /// Calculates the number of times `fst` and `snd` appear in this term. If
  /// that is `>= threshold`, it inserts the split at this term, and returns
  /// `None`. Otherwise, returns `Some(uses)`.
  ///
  /// This is only really useful when called in two passes – first, with
  /// `threshold = usize::MAX`, to count the number of uses, and then with
  /// `threshold = uses`.
  ///
  /// This has the effect of inserting the split at the lowest common ancestor
  /// of all of the uses of `fst` and `snd`.
  fn insert_split(&mut self, split: &mut Split, threshold: usize) -> Option<usize> {
    Term::recursive_call(move || {
      let mut n = match self {
        Term::Var { nam } => usize::from(split.fst.as_ref() == Some(nam) || split.snd.as_ref() == Some(nam)),
        _ => 0,
      };
      for child in self.children_mut() {
        n += child.insert_split(split, threshold)?;
      }

      if n >= threshold {
        let Split { tag, fst, snd, val } = std::mem::take(split);
        let nxt = Box::new(std::mem::take(self));
        *self = match tag {
          None => Term::Ltp { bnd: vec![fst, snd], val: Box::new(val), nxt },
          Some(tag) => Term::Dup { tag, bnd: vec![fst, snd], val: Box::new(val), nxt },
        };
        None
      } else {
        Some(n)
      }
    })
  }

  pub fn fix_names(&mut self, id_counter: &mut u64, book: &Book) {
    fn fix_name(nam: &mut Option<Name>, id_counter: &mut u64, bod: &mut Term) {
      if let Some(nam) = nam {
        let name = Name::new(num_to_name(*id_counter));
        *id_counter += 1;
        bod.subst(nam, &Term::Var { nam: name.clone() });
        *nam = name;
      }
    }

    Term::recursive_call(move || match self {
      Term::Ref { nam: def_name } => {
        if def_name.is_generated() {
          let def = book.defs.get(def_name).unwrap();
          let mut term = def.rule().body.clone();
          term.fix_names(id_counter, book);
          *self = term;
        }
      }
      _ => {
        for (child, bnd) in self.children_mut_with_binds_mut() {
          for bnd in bnd {
            fix_name(bnd, id_counter, child);
            child.fix_names(id_counter, book);
          }
        }
      }
    })
  }
}

#[derive(Default)]
pub struct NameGen {
  pub var_port_to_id: HashMap<Port, u64>,
  pub id_counter: u64,
}

impl NameGen {
  // Given a port, returns its name, or assigns one if it wasn't named yet.
  fn var_name(&mut self, var_port: Port) -> Name {
    let id = self.var_port_to_id.entry(var_port).or_insert_with(|| {
      let id = self.id_counter;
      self.id_counter += 1;
      id
    });
    Name::from(*id)
  }

  fn decl_name(&mut self, net: &INet, var_port: Port) -> Option<Name> {
    // If port is linked to an erase node, return an unused variable
    let var_use = net.enter_port(var_port);
    let var_kind = &net.node(var_use.node()).kind;
    (*var_kind != Era).then(|| self.var_name(var_port))
  }

  pub fn unique(&mut self) -> Name {
    let id = self.id_counter;
    self.id_counter += 1;
    Name::from(id)
  }
}

impl Op {
  pub fn from_hvmc_label(value: hvmc::ops::Op) -> Op {
    use hvmc::ops::Op as RtOp;
    match value {
      RtOp::Add => Op::Add,
      RtOp::Sub => Op::Sub,
      RtOp::Mul => Op::Mul,
      RtOp::Div => Op::Div,
      RtOp::Mod => Op::Mod,
      RtOp::Eq => Op::Eq,
      RtOp::Ne => Op::Ne,
      RtOp::Lt => Op::Lt,
      RtOp::Gt => Op::Gt,
      RtOp::Lte => Op::Lte,
      RtOp::Gte => Op::Gte,
      RtOp::And => Op::And,
      RtOp::Or => Op::Or,
      RtOp::Xor => Op::Xor,
      RtOp::Shl => Op::Shl,
      RtOp::Shr => Op::Shr,
      RtOp::SubS => unreachable!(),
      RtOp::DivS => unreachable!(),
      RtOp::ModS => unreachable!(),
      RtOp::ShlS => unreachable!(),
      RtOp::ShrS => unreachable!(),
    }
  }
}

fn is_op_swapped(op: hvmc::ops::Op) -> bool {
  matches!(
    op,
    hvmc::ops::Op::ShlS
      | hvmc::ops::Op::ShrS
      | hvmc::ops::Op::SubS
      | hvmc::ops::Op::DivS
      | hvmc::ops::Op::ModS
  )
}

#[derive(Debug, Clone, Copy)]
pub enum ReadbackError {
  InvalidNumericMatch,
  InvalidNumericOp,
  ReachedRoot,
  Cyclic,
  InvalidBind,
}

impl PartialEq for ReadbackError {
  fn eq(&self, other: &Self) -> bool {
    core::mem::discriminant(self) == core::mem::discriminant(other)
  }
}

impl Eq for ReadbackError {}

impl std::hash::Hash for ReadbackError {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    core::mem::discriminant(self).hash(state);
  }
}

impl std::fmt::Display for ReadbackError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ReadbackError::InvalidNumericMatch => write!(f, "Invalid Numeric Match."),
      ReadbackError::InvalidNumericOp => write!(f, "Invalid Numeric Operation."),
      ReadbackError::ReachedRoot => write!(f, "Reached Root."),
      ReadbackError::Cyclic => write!(f, "Cyclic Term."),
      ReadbackError::InvalidBind => write!(f, "Invalid Bind."),
    }
  }
}
