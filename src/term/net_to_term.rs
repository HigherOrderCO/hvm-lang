use super::{term_to_net::Labels, var_id_to_name, Book, DefId, MatchNum, Name, Op, Tag, Term, Val};
use crate::{
  net::{INet, NodeId, NodeKind::*, Port, SlotId, ROOT},
  term::Pattern,
};
use hvmc::run::Loc;
use std::collections::{HashMap, HashSet};

// TODO: Display scopeless lambdas as such
/// Converts an Interaction-INet to a Lambda Calculus term
pub fn net_to_term(net: &INet, book: &Book, labels: &Labels, linear: bool) -> (Term, Vec<ReadbackError>) {
  let mut reader = Reader {
    net,
    labels,
    book,
    dup_paths: if linear { None } else { Some(Default::default()) },
    scope: Default::default(),
    namegen: Default::default(),
    seen: Default::default(),
    errors: Default::default(),
  };

  let mut term = reader.read_term(net.enter_port(ROOT));

  while let Some(node) = reader.scope.vec.pop() {
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

  reader.resugar_adts(&mut term);

  (term, reader.errors)
}

#[derive(Debug)]
pub enum ReadbackError {
  InvalidNumericMatch,
  ReachedRoot,
  Cyclic,
  InvalidBind,
  InvalidAdt,
  InvalidAdtMatch,
  InvalidStrLen,
  InvalidStrTerm,
  InvalidChar,
}

struct Reader<'a> {
  net: &'a INet,
  labels: &'a Labels,
  book: &'a Book,
  dup_paths: Option<HashMap<u32, Vec<SlotId>>>,
  scope: Scope,
  namegen: NameGen,
  seen: HashSet<Port>,
  errors: Vec<ReadbackError>,
}

impl<'a> Reader<'a> {
  fn read_term(&mut self, next: Port) -> Term {
    if self.dup_paths.is_none() && !self.seen.insert(next) {
      self.errors.push(ReadbackError::Cyclic);
      return Term::Var { nam: Name::new("...") };
    }

    let node = next.node();

    let term = match self.net.node(node).kind {
      Era => {
        // Only the main port actually exists in an ERA, the auxes are just an artifact of this representation.
        debug_assert!(next.slot() == 0);
        Term::Era
      }
      // If we're visiting a con node...
      Con { lab } => match next.slot() {
        // If we're visiting a port 0, then it is a lambda.
        0 => {
          let nam = self.namegen.decl_name(self.net, Port(node, 1));
          let bod = self.read_term(self.net.enter_port(Port(node, 2)));
          Term::Lam { tag: self.labels.con.to_tag(lab), nam, bod: Box::new(bod) }
        }
        // If we're visiting a port 1, then it is a variable.
        1 => Term::Var { nam: self.namegen.var_name(next) },
        // If we're visiting a port 2, then it is an application.
        2 => {
          let fun = self.read_term(self.net.enter_port(Port(node, 0)));
          let arg = self.read_term(self.net.enter_port(Port(node, 1)));
          Term::App { tag: self.labels.con.to_tag(lab), fun: Box::new(fun), arg: Box::new(arg) }
        }
        _ => unreachable!(),
      },
      Mat => match next.slot() {
        2 => {
          // Read the matched expression
          let scrutinee = self.read_term(self.net.enter_port(Port(node, 0)));

          // Read the pattern matching node
          let sel_node = self.net.enter_port(Port(node, 1)).node();

          // We expect the pattern matching node to be a CON
          let sel_kind = self.net.node(sel_node).kind;
          if sel_kind != (Con { lab: None }) {
            // TODO: Is there any case where we expect a different node type here on readback?
            self.errors.push(ReadbackError::InvalidNumericMatch);
            Term::new_native_match(scrutinee, Term::Era, None, Term::Era)
          } else {
            let zero_term = self.read_term(self.net.enter_port(Port(sel_node, 1)));
            let succ_term = self.read_term(self.net.enter_port(Port(sel_node, 2)));

            let Term::Lam { nam, bod, .. } = succ_term else { unreachable!() };

            Term::new_native_match(scrutinee, zero_term, nam, *bod)
          }
        }
        _ => unreachable!(),
      },
      Ref { def_id } => {
        if self.book.is_generated_def(def_id) {
          let def = self.book.defs.get(&def_id).unwrap();
          def.assert_no_pattern_matching_rules();
          let mut term = def.rules[0].body.clone();
          term.fix_names(&mut self.namegen.id_counter, self.book);

          term
        } else {
          Term::Ref { def_id }
        }
      }
      // If we're visiting a fan node...
      Dup { lab } => match next.slot() {
        // If we're visiting a port 0, then it is a pair.
        0 => {
          if let Some(dup_paths) = &mut self.dup_paths {
            let stack = dup_paths.entry(lab).or_default();
            if let Some(slot) = stack.pop() {
              // Since we had a paired Dup in the path to this Sup,
              // we "decay" the superposition according to the original direction we came from the Dup.
              let term = self.read_term(self.net.enter_port(Port(node, slot)));
              self.dup_paths.as_mut().unwrap().get_mut(&lab).unwrap().push(slot);
              Some(term)
            } else {
              None
            }
          } else {
            None
          }
          .unwrap_or_else(|| {
            // If no Dup with same label in the path, we can't resolve the Sup, so keep it as a term.
            let fst = self.read_term(self.net.enter_port(Port(node, 1)));
            let snd = self.read_term(self.net.enter_port(Port(node, 2)));
            Term::Sup { tag: self.labels.dup.to_tag(Some(lab)), fst: Box::new(fst), snd: Box::new(snd) }
          })
        }
        // If we're visiting a port 1 or 2, then it is a variable.
        // Also, that means we found a dup, so we store it to read later.
        1 | 2 => {
          if let Some(dup_paths) = &mut self.dup_paths {
            dup_paths.entry(lab).or_default().push(next.slot());
            let term = self.read_term(self.net.enter_port(Port(node, 0)));
            self.dup_paths.as_mut().unwrap().entry(lab).or_default().pop().unwrap();
            term
          } else {
            self.scope.insert(node);
            Term::Var { nam: self.namegen.var_name(next) }
          }
        }
        _ => unreachable!(),
      },
      Num { val } => Term::Num { val },
      Op2 { opr } => match next.slot() {
        2 => {
          let fst = self.read_term(self.net.enter_port(Port(node, 0)));
          let snd = self.read_term(self.net.enter_port(Port(node, 1)));

          Term::Opx { op: Op::from_hvmc_label(opr).unwrap(), fst: Box::new(fst), snd: Box::new(snd) }
        }
        _ => unreachable!(),
      },
      Rot => self.error(ReadbackError::ReachedRoot),
      Tup => match next.slot() {
        // If we're visiting a port 0, then it is a Tup.
        0 => {
          let fst = self.read_term(self.net.enter_port(Port(node, 1)));
          let snd = self.read_term(self.net.enter_port(Port(node, 2)));
          match snd {
            Term::Lam { tag, bod, .. } if tag == Tag::str() => self.decode_str(fst, *bod),
            snd => Term::Tup { fst: Box::new(fst), snd: Box::new(snd) },
          }
        }
        // If we're visiting a port 1 or 2, then it is a variable.
        1 | 2 => {
          self.scope.insert(node);
          Term::Var { nam: self.namegen.var_name(next) }
        }
        _ => unreachable!(),
      },
    };

    term
  }
}

impl<'a> Reader<'a> {
  fn decode_str(&mut self, fst: Term, bod: Term) -> Term {
    let Term::Num { val: len } = fst else {
      return self.error(ReadbackError::InvalidStrLen);
    };
    let mut s = String::with_capacity(len as usize);
    let mut next = vec![bod];
    while let Some(t) = next.pop() {
      match t {
        Term::Var { .. } => break, // reached the end of the str
        Term::Tup { fst, snd } => {
          let Term::Num { val } = *fst else {
            return self.error(ReadbackError::InvalidChar);
          };
          if let Some(c) = char::from_u32(val as u32) {
            s.push(c);
            next.push(*snd);
          } else {
            self.errors.push(ReadbackError::InvalidChar);
          }
        }
        _ => self.errors.push(ReadbackError::InvalidStrTerm),
      }
    }
    Term::Str { val: s }
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
    let n = match self {
      Term::Var { nam } => (split.fst.as_ref() == Some(nam) || split.snd.as_ref() == Some(nam)) as usize,
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => bod.insert_split(split, threshold)?,
      Term::Let { val: fst, nxt: snd, .. }
      | Term::App { fun: fst, arg: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { fst, snd, .. } => {
        fst.insert_split(split, threshold)? + snd.insert_split(split, threshold)?
      }
      Term::Match { scrutinee, arms } => {
        let mut n = scrutinee.insert_split(split, threshold)?;
        for arm in arms {
          n += arm.1.insert_split(split, threshold)?;
        }
        n
      }
      Term::Lnk { .. } | Term::Num { .. } | Term::Str { .. } | Term::Ref { .. } | Term::Era => 0,
    };
    if n >= threshold {
      let Split { tag, fst, snd, val } = std::mem::take(split);
      let nxt = Box::new(std::mem::take(self));
      *self = match tag {
        None => Term::Let {
          pat: Pattern::Tup(Box::new(Pattern::Var(fst)), Box::new(Pattern::Var(snd))),
          val: Box::new(val),
          nxt,
        },
        Some(tag) => Term::Dup { tag, fst, snd, val: Box::new(val), nxt },
      };
      None
    } else {
      Some(n)
    }
  }
}

#[derive(Default)]
struct Scope {
  vec: Vec<NodeId>,
  set: HashSet<NodeId>,
}

impl Scope {
  fn insert(&mut self, node: NodeId) {
    if !self.set.contains(&node) {
      self.set.insert(node);
      self.vec.push(node);
    }
  }
}

#[derive(Default)]
struct NameGen {
  var_port_to_id: HashMap<Port, Val>,
  id_counter: Val,
}

impl NameGen {
  // Given a port, returns its name, or assigns one if it wasn't named yet.
  fn var_name(&mut self, var_port: Port) -> Name {
    let id = self.var_port_to_id.entry(var_port).or_insert_with(|| {
      let id = self.id_counter;
      self.id_counter += 1;
      id
    });

    var_id_to_name(*id)
  }

  fn decl_name(&mut self, net: &INet, var_port: Port) -> Option<Name> {
    // If port is linked to an erase node, return an unused variable
    let var_use = net.enter_port(var_port);
    let var_kind = net.node(var_use.node()).kind;
    if let Era = var_kind { None } else { Some(self.var_name(var_port)) }
  }

  fn unique(&mut self) -> Name {
    let id = self.id_counter;
    self.id_counter += 1;
    var_id_to_name(id)
  }
}

impl Op {
  pub fn from_hvmc_label(value: Loc) -> Option<Op> {
    match value {
      0x0 => Some(Op::ADD),
      0x1 => Some(Op::SUB),
      0x2 => Some(Op::MUL),
      0x3 => Some(Op::DIV),
      0x4 => Some(Op::MOD),
      0x5 => Some(Op::EQ),
      0x6 => Some(Op::NE),
      0x7 => Some(Op::LT),
      0x8 => Some(Op::GT),
      0x9 => Some(Op::LTE),
      0xa => Some(Op::GTE),
      0xb => Some(Op::AND),
      0xc => Some(Op::OR),
      0xd => Some(Op::XOR),
      0xe => Some(Op::LSH),
      0xf => Some(Op::RSH),
      0x10 => Some(Op::NOT),
      _ => None,
    }
  }
}

impl Book {
  pub fn is_generated_def(&self, def_id: DefId) -> bool {
    self.def_names.name(&def_id).map_or(false, |Name(name)| name.contains('$'))
  }
}

impl Term {
  fn fix_names(&mut self, id_counter: &mut Val, book: &Book) {
    fn fix_name(nam: &mut Option<Name>, id_counter: &mut Val, bod: &mut Term) {
      if let Some(nam) = nam {
        let name = var_id_to_name(*id_counter);
        *id_counter += 1;
        bod.subst(nam, &Term::Var { nam: name.clone() });
        *nam = name;
      }
    }

    match self {
      Term::Lam { nam, bod, .. } => {
        fix_name(nam, id_counter, bod);
        bod.fix_names(id_counter, book);
      }
      Term::Ref { def_id } => {
        if book.is_generated_def(*def_id) {
          let def = book.defs.get(def_id).unwrap();
          def.assert_no_pattern_matching_rules();
          let mut term = def.rules[0].body.clone();
          term.fix_names(id_counter, book);
          *self = term
        }
      }
      Term::Dup { fst, snd, val, nxt, .. } => {
        val.fix_names(id_counter, book);
        fix_name(fst, id_counter, nxt);
        fix_name(snd, id_counter, nxt);
        nxt.fix_names(id_counter, book);
      }
      Term::Chn { bod, .. } => bod.fix_names(id_counter, book),
      Term::App { fun: fst, arg: snd, .. }
      | Term::Sup { fst, snd, .. }
      | Term::Tup { fst, snd }
      | Term::Opx { op: _, fst, snd } => {
        fst.fix_names(id_counter, book);
        snd.fix_names(id_counter, book);
      }
      Term::Match { scrutinee, arms } => {
        scrutinee.fix_names(id_counter, book);

        for (rule, term) in arms {
          if let Pattern::Num(MatchNum::Succ(Some(nam))) = rule {
            fix_name(nam, id_counter, term);
          }

          term.fix_names(id_counter, book)
        }
      }
      Term::Let { .. } => unreachable!(),
      Term::Var { .. } | Term::Lnk { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => {}
    }
  }
}

impl<'a> Reader<'a> {
  fn deref(&mut self, term: &mut Term) {
    while let Term::Ref { def_id } = term {
      let def = &self.book.defs[def_id];
      def.assert_no_pattern_matching_rules();
      *term = def.rules[0].body.clone();
      term.fix_names(&mut self.namegen.id_counter, self.book);
    }
  }
  fn resugar_adts(&mut self, term: &mut Term) {
    match term {
      Term::Lam { tag: Tag::Named(adt_name), bod, .. } | Term::Chn { tag: Tag::Named(adt_name), bod, .. } => {
        let Some((adt_name, adt)) = self.book.adts.get_key_value(adt_name) else {
          return self.resugar_adts(bod);
        };
        let mut cur = &mut *term;
        let mut current_arm = None;
        for ctr in &adt.ctrs {
          self.deref(cur);
          match cur {
            Term::Lam { tag: Tag::Named(tag), nam, bod } if &*tag == adt_name => {
              if let Some(nam) = nam {
                if current_arm.is_some() {
                  return self.error(ReadbackError::InvalidAdt);
                }
                current_arm = Some((nam.clone(), ctr))
              }
              cur = bod;
            }
            _ => return self.error(ReadbackError::InvalidAdt),
          }
        }
        let Some(current_arm) = current_arm else {
          return self.error(ReadbackError::InvalidAdt);
        };
        let app = cur;
        let mut cur = &mut *app;
        for _ in current_arm.1.1 {
          self.deref(cur);
          match cur {
            Term::App { tag: Tag::Static, fun, .. } => cur = fun,
            Term::App { tag: tag @ Tag::Named(_), fun, .. } => {
              *tag = Tag::Static;
              cur = fun
            }
            _ => return self.error(ReadbackError::InvalidAdt),
          }
        }
        match cur {
          Term::Var { nam } if nam == &current_arm.0 => {}
          _ => return self.error(ReadbackError::InvalidAdt),
        }
        let def_id = self.book.def_names.def_id(current_arm.1.0).unwrap();
        *cur = Term::Ref { def_id };
        let app = std::mem::take(app);
        *term = app;
        self.resugar_adts(term);
      }
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => self.resugar_adts(bod),
      Term::App { tag: Tag::Named(adt_name), fun, arg } => {
        let Some((adt_name, adt)) = self.book.adts.get_key_value(adt_name) else {
          self.resugar_adts(fun);
          self.resugar_adts(arg);
          return;
        };
        let mut cur = &mut *term;
        let mut arms = Vec::new();
        for ctr in adt.ctrs.iter().rev() {
          self.deref(cur);
          match cur {
            Term::App { tag: Tag::Named(tag), fun, arg } if &*tag == adt_name => {
              let mut args = Vec::new();
              let mut arm_term = &mut **arg;
              for _ in ctr.1 {
                self.deref(arm_term);
                if !matches!(arm_term, Term::Lam { tag: Tag::Static, .. } if &*tag == adt_name) {
                  let nam = self.namegen.unique();
                  let body = std::mem::take(arm_term);
                  *arm_term = Term::Lam {
                    tag: Tag::Static,
                    nam: Some(nam.clone()),
                    bod: Box::new(Term::App {
                      tag: Tag::Static,
                      fun: Box::new(body),
                      arg: Box::new(Term::Var { nam }),
                    }),
                  };
                }
                match arm_term {
                  Term::Lam { nam, bod, .. } => {
                    args.push(match nam {
                      Some(x) => Pattern::Var(Some(x.clone())),
                      None => Pattern::Var(None),
                    });
                    arm_term = &mut **bod;
                  }
                  _ => unreachable!(),
                }
              }
              arms.push((Pattern::Ctr(ctr.0.clone(), args), arm_term));
              cur = &mut **fun;
            }
            _ => return self.error(ReadbackError::InvalidAdtMatch),
          }
        }
        let scrutinee = std::mem::take(cur);
        let arms = arms.into_iter().rev().map(|arm| (arm.0, std::mem::take(arm.1))).collect();
        *term = Term::Match { scrutinee: Box::new(scrutinee), arms };
        self.resugar_adts(term);
      }
      Term::App { fun: fst, arg: snd, .. }
      | Term::Let { val: fst, nxt: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { fst, snd, .. } => {
        self.resugar_adts(fst);
        self.resugar_adts(snd);
      }
      Term::Match { scrutinee, arms } => {
        self.resugar_adts(scrutinee);
        for arm in arms {
          self.resugar_adts(&mut arm.1);
        }
      }
      Term::Lnk { .. }
      | Term::Num { .. }
      | Term::Var { .. }
      | Term::Str { .. }
      | Term::Ref { .. }
      | Term::Era => {}
    }
  }
  fn error<T: Default>(&mut self, error: ReadbackError) -> T {
    self.errors.push(error);
    T::default()
  }
}
