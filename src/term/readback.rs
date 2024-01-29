use hvmc::{
  ast::Host,
  run::{Net, Port, Wire},
};
use indexmap::IndexMap;

use crate::term::{DefId, Op, Pattern};

use super::{encoder::Labels, Book, Name, ReadbackError, Tag, Term};

use loaned::LoanedMut;

pub enum SignedTerm<'term> {
  Pos(LoanedMut<'term, Term>),
  Neg(&'term mut Term),
}

pub type WireUid = usize;

pub enum TermHole<'term> {
  Variable(LoanedMut<'term, Term>, &'term mut Pattern),
  Term(LoanedMut<'term, Term>),
}

impl<'term> TermHole<'term> {
  fn place(self, target: &'term mut Term) {
    self.term().place(target)
  }
  fn erase(self) -> bool {
    match self {
      TermHole::Variable(a, _b) => {
        // TODO don't drop
        core::mem::forget(a);
        true
      }
      TermHole::Term(a) => {
        core::mem::forget(a);
        false
      }
    }
  }
  fn term(self) -> LoanedMut<'term, Term> {
    match self {
      TermHole::Variable(t, _) => t,
      TermHole::Term(t) => t,
    }
  }
}
impl<'term> From<LoanedMut<'term, Term>> for TermHole<'term> {
  fn from(value: LoanedMut<'term, Term>) -> Self {
    Self::Term(value)
  }
}
impl<'term> From<(LoanedMut<'term, Term>, &'term mut Pattern)> for TermHole<'term> {
  fn from(value: (LoanedMut<'term, Term>, &'term mut Pattern)) -> Self {
    Self::Variable(value.0, value.1)
  }
}

pub enum ExtPattern {
  Match(Pattern),
  Dup(Name, Name, Tag),
}

struct Reader<'book, 'area, 'term> {
  net: &'book mut Net<'area>,
  vars: IndexMap<WireUid, SignedTerm<'term>>,
  labels: &'book Labels,
  book: &'book Book,
  // Dups float in the top level
  pats: Vec<(ExtPattern, TermHole<'term>)>,
  host: &'book Host,
  name_idx: u64,
  errors: Vec<ReadbackError>,
}

impl Book {
  pub fn is_generated_def(&self, def_id: &DefId) -> bool {
    self.def_names.name(def_id).map_or(false, |Name(name)| name.contains('$'))
  }
}

impl Term {
  pub fn fix_names(&mut self, id_counter: &mut u64, book: &Book) {
    fn fix_name(nam: &mut Name, id_counter: &mut u64, bod: &mut Term) {
      let name = Name::from_num(*id_counter);
      *id_counter += 1;
      bod.subst(nam, &Term::Var { nam: name.clone() });
      *nam = name;
    }

    match self {
      Term::Lam { nam, bod, .. } => {
        if let Some(nam) = nam {
          fix_name(nam, id_counter, bod);
        }
        bod.fix_names(id_counter, book);
      }
      Term::Ref { def_id } => {
        if book.is_generated_def(def_id) {
          let def = book.defs.get(def_id).unwrap();
          def.assert_no_pattern_matching_rules();
          let mut term = def.rules[0].body.clone();
          term.fix_names(id_counter, book);
          *self = term
        }
      }
      Term::Dup { fst, snd, val, nxt, .. } => {
        val.fix_names(id_counter, book);
        if let Some(fst) = fst {
          fix_name(fst, id_counter, nxt);
        };
        if let Some(snd) = snd {
          fix_name(snd, id_counter, nxt);
        };
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
          rule.bound_names_mut().for_each(|nam| fix_name(nam, id_counter, term));

          term.fix_names(id_counter, book)
        }
      }
      Term::Let { .. } => unreachable!(),
      Term::Var { .. } | Term::Lnk { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => {}
    }
  }
}

impl Op {
  pub fn from_hvmc_label(value: hvmc::ops::Op) -> Option<Op> {
    use hvmc::ops::Op as RtOp;
    match value {
      RtOp::Add => Some(Op::ADD),
      RtOp::Sub => Some(Op::SUB),
      RtOp::Mul => Some(Op::MUL),
      RtOp::Div => Some(Op::DIV),
      RtOp::Mod => Some(Op::MOD),
      RtOp::Eq => Some(Op::EQ),
      RtOp::Ne => Some(Op::NE),
      RtOp::Lt => Some(Op::LT),
      RtOp::Gt => Some(Op::GT),
      RtOp::Lte => Some(Op::LTE),
      RtOp::Gte => Some(Op::GTE),
      RtOp::And => Some(Op::AND),
      RtOp::Or => Some(Op::OR),
      RtOp::Xor => Some(Op::XOR),
      RtOp::Lsh => Some(Op::LSH),
      RtOp::Rsh => Some(Op::RSH),
      RtOp::Not => Some(Op::NOT),
    }
  }
}

impl<'book, 'area, 'term> Reader<'book, 'area, 'term> {
  fn generate_name(&mut self) -> Name {
    self.name_idx += 1;
    Name::from_num(self.name_idx - 1)
  }
  fn get_wire_uid(&mut self, wire: Wire) -> WireUid {
    (wire.load_target().wire().0 as usize).min(wire.0 as usize)
  }
  fn read_pos(&mut self, wire: Wire, term: TermHole<'term>) {
    use hvmc::run::Tag as RtTag;
    let port = wire.load_target();

    match port.tag() {
      RtTag::Red => self.read_pos(port.wire(), term),
      RtTag::Var => {
        let id = self.get_wire_uid(wire);
        if let Some(target) = self.vars.remove(&id) {
          match target {
            SignedTerm::Pos(_) => todo!(),
            SignedTerm::Neg(target) => term.place(target),
          }
        } else {
          self.vars.insert(id, SignedTerm::Pos(term.term()));
        }
      }
      RtTag::Ref => {
        if port == Port::ERA {
          term.erase();
        } else {
          todo!()
        };
      }
      RtTag::Num => {
        term.erase();
      }
      RtTag::Op2 => {
        let port = port.traverse_node();

        let op = Op::from_hvmc_label(port.lab.try_into().unwrap()).unwrap();
        let ((fst, snd), out) =
          LoanedMut::loan_with(Term::Opx { op, fst: hole(), snd: hole() }, |term, l| {
            let Term::Opx { fst, snd, .. } = term else { unreachable!() };
            (l.loan_mut(fst), l.loan_mut(snd))
          });
        term.place(fst);
        self.read_neg(port.p1, snd);
        self.read_pos(port.p2, out.into());
      }
      RtTag::Op1 => todo!(),
      RtTag::Mat => {
        let port = port.traverse_node();
        let pred = self.generate_name();
        let pred_var = Term::Var { nam: pred.clone() };
        /*
        let (zero_ref, zero_box) = LoanedMut::loan(Box::new(zero));
        let (succ_ref, succ_box) = LoanedMut::loan(Box::new(succ));
        self.read_neg(port.p1.load_target().traverse_node().p1, zero_ref);
        self.read_neg(port.p1.load_target().traverse_node().p2, succ_ref);
        */
        let mat = Term::Match {
          scrutinee: hole(),
          arms: vec![
            (Pattern::Num { mat: crate::term::MatchNum::Zero }, Term::default()),
            (
              Pattern::Num { mat: crate::term::MatchNum::Succ(Box::new(Pattern::Var { nam: pred })) },
              Term::default(),
            ),
          ],
        };
        let ((scrutinee, zero, succ), mat) = LoanedMut::loan_with(mat, |mat, l| {
          let Term::Match { scrutinee, arms } = mat else { unreachable!() };
          let [(_, Term::Let { nxt: zero, .. }), (_, Term::Let { nxt: succ, .. })] = &mut arms[..] else {
            unreachable!()
          };
          (l.loan_mut(scrutinee), l.loan_mut(zero), l.loan_mut(succ))
        });
        term.place(scrutinee);
        self.read_neg(port.p1.load_target().traverse_node().p1, zero);
        if port.p1.load_target().tag() == RtTag::Ref {
          self.net.call(port.p1.load_target(), Port::new_var(port.p1.loc()));
        }
        if port.p1.load_target().traverse_node().p2.load_target().tag() == RtTag::Ref {
          self.net.call(
            port.p1.load_target().traverse_node().p2.load_target(),
            Port::new_var(port.p1.load_target().traverse_node().p2.loc()),
          );
        }
        assert!(port.p1.load_target().traverse_node().p2.load_target().tag() == RtTag::Ctr);
        self.read_pos(
          port.p1.load_target().traverse_node().p2.load_target().traverse_node().p1,
          LoanedMut::new(pred_var).into(),
        );
        self.read_neg(port.p1.load_target().traverse_node().p2.load_target().traverse_node().p2, succ);
        self.read_pos(port.p2, mat.into());
      }
      RtTag::Ctr => {
        let port = port.traverse_node();
        if port.lab % 2 == 0 {
          // Even labels are CON
          let tag =
            self.labels.con.to_tag(if port.lab == 0 { None } else { Some((port.lab as u32 >> 1) - 1) });
          let ((fun, arg), out) =
            LoanedMut::loan_with(Term::App { tag, fun: hole(), arg: hole() }, |term, l| {
              let Term::App { fun, arg, .. } = term else { unreachable!() };
              (l.loan_mut(fun), l.loan_mut(arg))
            });
          term.place(fun);
          self.read_neg(port.p1, arg);
          self.read_pos(port.p2, out.into());
        } else if port.lab == 1 {
          todo!("Tup-pat")
        } else {
          let tag = self.labels.dup.to_tag(if port.lab == 1 {
            unreachable!()
          } else {
            Some((port.lab as u32 >> 1) - 1)
          });
          let fst_name = self.generate_name();
          let snd_name = self.generate_name();
          let snd_var = Term::Var { nam: snd_name.clone() };
          let snd_box = LoanedMut::new(snd_var);
          let ((val, fst, snd, nxt), dup) = LoanedMut::<'term, Term>::loan_with(
            Term::Let {
              pat: Pattern::Sup {
                tag,
                fst: Box::new(Pattern::Var { nam: fst_name.clone() }),
                snd: Box::new(Pattern::Var { nam: snd_name }),
              },
              val: hole(),
              nxt: hole(),
            },
            |term: &mut Term, l| {
              let Term::Let { pat: Pattern::Sup { tag: _, fst, snd }, val, nxt } = term else { unreachable!() };
              (l.loan_mut(val), l.loan_mut(fst), l.loan_mut(snd), l.loan_mut(nxt))
            },
          );
          let Pattern::Var { nam: _fst } = fst else { unreachable!() };
          let Pattern::Var { nam: _snd } = snd else { unreachable!() };
          term.place(val);
          *nxt = Term::Var { nam: fst_name };
          self.read_pos(port.p1, dup.into());
          self.read_pos(port.p2, snd_box.into());
        }
      }
    }
  }
  fn read_neg(&mut self, wire: Wire, into: &'term mut Term) {
    use hvmc::run::Tag as RtTag;
    let port = wire.load_target();
    match port.tag() {
      RtTag::Red => todo!(),
      RtTag::Var => {
        let id = self.get_wire_uid(wire);
        if let Some(target) = self.vars.remove(&id) {
          match target {
            SignedTerm::Pos(target) => target.place(into),
            SignedTerm::Neg(_) => todo!(),
          }
        } else {
          self.vars.insert(id, SignedTerm::Neg(into));
        }
      }
      RtTag::Ref => {
        if port == Port::ERA {
          *into = Term::Era
        } else {
          if let Some(def_name) = self.host.back.get(&port.loc()) {
            let def_id = DefId(def_name.clone());
            if self.book.is_generated_def(&def_id) {
              let def = self.book.defs.get(&def_id).unwrap();
              def.assert_no_pattern_matching_rules();
              let mut term = def.rules[0].body.clone();
              term.fix_names(&mut self.name_idx, self.book);
              *into = term;
            } else {
              *into = Term::Ref { def_id }
            }
          } else {
            *into = Term::Ref { def_id: DefId("unknown_ref".to_string()) }
          }
        }
      }
      RtTag::Num => {
        *into = Term::Num { val: port.num() };
      }
      RtTag::Op2 | RtTag::Op1 | RtTag::Mat => *into = Term::Era,
      RtTag::Ctr => {
        let port = port.traverse_node();
        if port.lab % 2 == 0 {
          // Even labels are CON
          let nam = self.generate_name();
          let var = Term::Var { nam: nam.clone() };
          let var_box = LoanedMut::new(var);

          let tag =
            self.labels.con.to_tag(if port.lab == 0 { None } else { Some((port.lab as u32 >> 1) - 1) });

          *into = Term::Lam { tag, nam: Some(nam), bod: hole() };
          // Fill it
          let Term::Lam { ref mut bod,  .. } = into else { unreachable!() };
          self.read_pos(port.p1, var_box.into());
          self.read_neg(port.p2, bod);
        } else {
          if port.lab != 1 {
            let _tag = (port.lab as u32 >> 1) - 1;
            let tag = self.labels.dup.to_tag(Some((port.lab as u32 >> 1) - 1));
            *into = Term::Sup { tag, fst: hole(), snd: hole() };
            let Term::Sup { fst, snd, .. } = into else { unreachable!() };
            self.read_neg(port.p1, fst);
            self.read_neg(port.p2, snd);
          } else {
            *into = Term::Tup { fst: hole(), snd: hole() };
            let Term::Tup { ref mut fst, ref mut snd, .. } = into else { unreachable!() };
            self.read_neg(port.p1, fst);
            self.read_neg(port.p2, snd);
          }
        }
      }
    }
  }

  fn decode_str(&mut self, term: &mut Term) -> Term {
    let mut s = String::new();
    fn go(t: &mut Term, s: &mut String, rd: &mut Reader) {
      match t {
        Term::Num { val } => s.push(unsafe { char::from_u32_unchecked(*val as u32) }),
        Term::Lam { bod, .. } => go(bod, s, rd),
        Term::App { tag, arg, .. } if *tag == Tag::string_scons_head() => go(arg, s, rd),
        Term::App { fun, arg, .. } => {
          go(fun, s, rd);
          go(arg, s, rd);
        }
        Term::Var { .. } => {}
        Term::Chn { .. }
        | Term::Lnk { .. }
        | Term::Let { .. }
        | Term::Tup { .. }
        | Term::Dup { .. }
        | Term::Sup { .. }
        | Term::Str { .. }
        | Term::Opx { .. }
        | Term::Match { .. }
        | Term::Ref { .. }
        | Term::Era => rd.error(ReadbackError::InvalidStrTerm),
      }
    }
    go(term, &mut s, self);
    Term::Str { val: s }
  }

  fn deref(&mut self, term: &mut Term) {
    while let Term::Ref { def_id } = term {
      let def = &self.book.defs[def_id];
      def.assert_no_pattern_matching_rules();
      *term = def.rules[0].body.clone();
      term.fix_names(&mut self.name_idx, self.book);
    }
  }
  fn resugar_adts(&mut self, term: &mut Term) {
    match term {
      Term::Lam { tag, bod, .. } if *tag == Tag::string() => *term = self.decode_str(bod),
      Term::Lam { tag: Tag::Named(adt_name), bod, .. } | Term::Chn { tag: Tag::Named(adt_name), bod, .. } => {
        let Some((adt_name, adt)) = self.book.adts.get_key_value(adt_name) else {
          return self.resugar_adts(bod);
        };
        let mut cur = &mut *term;
        let mut current_arm = None;
        for ctr in &adt.ctrs {
          self.deref(cur);
          println!("{:?}", ctr);
          println!("{:?}", adt_name);
          match cur {
            Term::Lam { tag: Tag::Named(tag), nam, bod } if &*tag == adt_name => {
              if let Some(nam) = nam {
                if current_arm.is_some() {
                  println!("{:?}", "Two arm");
                  return self.error(ReadbackError::InvalidAdt);
                }
                current_arm = Some((nam.clone(), ctr))
              }
              cur = bod;
            }
            _ => {
              println!("{:?}", "Two aaarm");
              return self.error(ReadbackError::InvalidAdt);
            }
          }
        }
        println!("{:?}", current_arm);
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
                  let nam = self.generate_name();
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
                      Some(x) => Pattern::Var { nam: x.clone() },
                      None => Pattern::Era,
                    });
                    arm_term = &mut **bod;
                  }
                  _ => unreachable!(),
                }
              }
              arms.push((Pattern::Ctr { nam: ctr.0.clone(), args }, arm_term));
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

pub fn readback(net: &mut Net, labels: &Labels, host: &Host, book: &Book) -> Box<Term> {
  let mut term = Box::new(Term::Era);
  let root = net.root.clone();
  Reader { net, vars: IndexMap::new(), labels, name_idx: 0, pats: vec![], host, book, errors: vec![] }
    .read_neg(root, &mut term);
  term
}

pub fn readback_and_resugar(net: &mut Net, labels: &Labels, host: &Host, book: &Book) -> Box<Term> {
  let mut term = Box::new(Term::Era);
  let root = net.root.clone();
  let vars = {
    let mut reader =
      Reader { net, vars: IndexMap::new(), labels, name_idx: 0, pats: vec![], host, book, errors: vec![] };
    reader.read_neg(root, &mut term);
    core::mem::take(&mut reader.vars)
  };

  // Properly drop vars
  let vars: Vec<_> = vars
    .into_values()
    .filter_map(|x| match x {
      SignedTerm::Pos(x) => Some(x),
      SignedTerm::Neg(_) => None,
    })
    .collect();
  let vars: LoanedMut<Vec<Term>> = vars.into();
  loaned::drop!(vars);

  let mut reader =
    Reader { net, vars: IndexMap::new(), labels, name_idx: 0, pats: vec![], host, book, errors: vec![] };
  assert!(reader.vars.is_empty());
  reader.resugar_adts(&mut term);
  if !reader.errors.is_empty() {
    todo!("{:?}", reader.errors);
  }
  drop(reader);
  term
}

fn hole() -> Box<Term> {
  Box::new(Term::Var { nam: Name("hole".to_string()) })
}
