use std::collections::{BTreeMap, HashMap};

use hvmc::ast::{num_to_str, Net, Tree};

use indexmap::{map::Entry, IndexMap};
use loaned::LoanedMut;

use crate::term::{MatchNum, Pattern};

use super::{Book, DefId, DefNames, Name, Op, Tag, Term};

pub fn book_to_tree(book: &Book, main: DefId) -> (hvmc::ast::Book, Labels) {
  let mut nets = BTreeMap::new();
  let mut labels = Labels::default();

  for def in book.defs.values() {
    for rule in def.rules.iter() {
      let net = term_to_compat_net(&rule.body, &mut labels);

      let name =
        if def.def_id == main { DefNames::ENTRY_POINT.to_string() } else { def_id_to_hvmc_name(&def.def_id) };

      nets.insert(name, net);
    }
  }

  labels.con.finish();
  labels.dup.finish();

  (nets, labels)
}

fn def_id_to_hvmc_name(def_id: &DefId) -> String {
  if def_id.0 == DefNames::HVM1_ENTRY_POINT { String::from(DefNames::ENTRY_POINT) } else { def_id.0.clone() }
}

/// Converts an IC term into an hvm-core net.
pub fn term_to_compat_net(term: &Term, labels: &mut Labels) -> hvmc::ast::Net {
  let mut encoder = Encoder { vars: Default::default(), redexes: Vec::new(), name_idx: 0, labels };

  let (root_ref, root_own) = LoanedMut::loan(Box::new(Tree::Era));

  encoder.encode_term(term, Place::Hole(root_ref));
  encoder.erase_all();
  let loaned_redexes: LoanedMut<Vec<(Tree, Tree)>> = core::mem::take(&mut encoder.redexes).into();
  assert!(encoder.redexes.is_empty());
  encoder.finish();

  let redex = loaned::take!(loaned_redexes);
  let root = loaned::take!(root_own);

  Net { root: *root, rdex: redex.into_iter().collect() }
}

#[derive(Debug)]
enum Place<'t, 'e> {
  Tree(LoanedMut<'t, Tree>),
  Hole(&'t mut Tree),
  Var(&'e Name),
}

#[derive(Debug)]
struct Encoder<'t, 'e> {
  vars: IndexMap<&'e Name, Place<'t, 'e>>,
  redexes: Vec<LoanedMut<'t, (Tree, Tree)>>,
  name_idx: usize,
  labels: &'e mut Labels,
}

#[derive(Debug, Default)]
pub struct Labels {
  pub con: LabelGenerator,
  pub dup: LabelGenerator,
}

#[derive(Debug, Default)]
pub struct LabelGenerator {
  pub next: u32,
  pub name_to_label: HashMap<Name, u32>,
  pub label_to_name: HashMap<u32, Name>,
}

impl LabelGenerator {
  // If some tag and new generate a new label, otherwise return the generated label.
  // If none use the implicit label counter.
  pub fn generate(&mut self, tag: &Tag) -> Option<u32> {
    let mut unique = || {
      let lab = self.next;
      self.next += 1;
      lab
    };
    use std::collections::hash_map::Entry;
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

  pub fn finish(&mut self) {
    self.next = u32::MAX;
    self.name_to_label.clear();
  }
}

impl<'t, 'e> Encoder<'t, 'e> {
  fn generate_string(&mut self) -> String {
    self.name_idx += 1;
    num_to_str(self.name_idx - 1)
  }
  fn make_new_var(&mut self) -> Tree {
    Tree::Var { nam: self.generate_string() }
  }
  fn erase(&mut self, term: Place<'t, 'e>) {
    self.link(term, Place::Tree(LoanedMut::new(Tree::Era)))
  }
  fn link(&mut self, a: Place<'t, 'e>, b: Place<'t, 'e>) {
    match (a, b) {
      (Place::Hole(x), Place::Hole(y)) => {
        let var = self.make_new_var();
        *x = var.clone();
        *y = var;
      }
      (Place::Tree(x), Place::Tree(y)) => {
        let redex = LoanedMut::merge((Tree::Era, Tree::Era), |r, m| {
          m.place(x, &mut r.0);
          m.place(y, &mut r.1);
        });
        self.redexes.push(redex);
      }
      (Place::Tree(t), Place::Hole(h)) | (Place::Hole(h), Place::Tree(t)) => t.place(h),
      (Place::Var(v), p) | (p, Place::Var(v)) => match self.vars.entry(v) {
        Entry::Occupied(e) => {
          let k = e.remove();
          self.link(p, k)
        }
        Entry::Vacant(e) => {
          e.insert(p);
        }
      },
    }
  }
  fn encode_term(&mut self, term: &'e Term, place: Place<'t, 'e>) {
    let other = self._encode_term(term);
    self.link(place, other);
  }
  fn _encode_term(&mut self, term: &'e Term) -> Place<'t, 'e> {
    match term {
      Term::Lnk { nam } => Place::Var(nam),
      Term::Lam { tag, pat, bod } => {
        let lab = (self.labels.con.generate(tag).map(|x| x + 1).unwrap_or(0) << 1) as u16;
        let (tree, lft, rgt) = create_ctr(lab);
        self.encode_pat(pat, Place::Hole(lft));
        self.encode_term(bod.as_ref(), Place::Hole(rgt));
        Place::Tree(tree)
      }
      Term::Var { nam } => Place::Var(nam),
      Term::App { tag, fun, arg } => {
        let lab = (self.labels.con.generate(tag).map(|x| x + 1).unwrap_or(0) << 1) as u16;
        let (tree, lft, rgt) = create_ctr(lab);
        self.encode_term(fun.as_ref(), Place::Tree(tree));
        self.encode_term(arg.as_ref(), Place::Hole(lft));
        Place::Hole(rgt)
      }
      Term::Ref { def_id } => Place::Tree(LoanedMut::new(Tree::Ref { nam: def_id.0.clone() })),
      Term::Sup { tag, fst, snd } => {
        let lab = ((self.labels.dup.generate(tag).map(|x| x + 1).unwrap_or(0) << 1) + 3) as u16;
        let (tree, lft, rgt) = create_ctr(lab);
        self.encode_term(fst, Place::Hole(lft));
        self.encode_term(snd, Place::Hole(rgt));
        Place::Tree(tree)
      }
      Term::Tup { fst, snd } => {
        let lab = 1;
        let (tree, lft, rgt) = create_ctr(lab);
        self.encode_term(fst, Place::Hole(lft));
        self.encode_term(snd, Place::Hole(rgt));
        Place::Tree(tree)
      }
      Term::Era => Place::Tree(LoanedMut::new(Tree::Era)),
      Term::Num { val } => Place::Tree(LoanedMut::new(Tree::Num { val: *val })),
      Term::Opx { op, fst, snd } => {
        let (tree, lft, rgt) = create_op2(op.to_hvmc_label());
        self.encode_term(snd, Place::Hole(lft));
        self.encode_term(fst, Place::Tree(tree));
        Place::Hole(rgt)
      }
      Term::Match { scrutinee, arms } => {
        // It must be a zero-succ match.
        // because other matches get desugared
        println!("{:#?}", arms);
        debug_assert!(
          matches!(arms[0].0, Pattern::Num { mat: MatchNum::Zero }) || matches!(arms[0].0, Pattern::Era)
        );
        let succ_pat = match &arms[1].0 {
          Pattern::Num { mat: MatchNum::Succ(pred) } => pred,
          term @ Pattern::Era => term,
          _ => unimplemented!(),
        };
        let zero = &arms[0].1;
        let succ = &arms[1].1;

        let ((zero_p, succ_pat_p, succ_ret_p, ret), tree_box) = LoanedMut::loan_with(
          Tree::Mat {
            sel: Box::new(Tree::Ctr {
              lab: 0,
              lft: Default::default(),
              rgt: Box::new(Tree::Ctr { lab: 0, lft: Default::default(), rgt: Default::default() }),
            }),
            ret: Default::default(),
          },
          |tree, l| {
            let Tree::Mat {
              sel: box Tree::Ctr { lft: zero_p, rgt: box Tree::Ctr { lft: succ_pat, rgt: succ_ret, .. }, .. },
              ret,
            } = tree
            else {
              unreachable!()
            };
            (l.loan_mut(zero_p), l.loan_mut(succ_pat), l.loan_mut(succ_ret), l.loan_mut(ret))
          },
        );

        self.encode_term(scrutinee, Place::Tree(tree_box));

        self.encode_term(zero, Place::Hole(zero_p));
        self.encode_pat(succ_pat, Place::Hole(succ_pat_p));
        self.encode_term(succ, Place::Hole(succ_ret_p));
        Place::Hole(ret)
      }
      Term::Let { pat, val, nxt } => {
        let place = self._encode_pat(pat);
        self.encode_term(val, place);
        self._encode_term(nxt)
      }
      x => todo!("{:?}", x),
    }
  }
  fn encode_pat(&mut self, pat: &'e Pattern, place: Place<'t, 'e>) {
    let other = self._encode_pat(pat);
    self.link(place, other);
  }
  fn _encode_pat(&mut self, pat: &'e Pattern) -> Place<'t, 'e> {
    match pat {
      Pattern::Lnk { nam } => Place::Var(nam),
      Pattern::Var { nam } => Place::Var(nam),
      Pattern::Sup { tag, fst, snd } => {
        let lab = ((self.labels.dup.generate(tag).map(|x| x + 1).unwrap_or(0) << 1) + 3) as u16;
        let (tree, lft, rgt) = create_ctr(lab);
        self.encode_pat(fst, Place::Hole(lft));
        self.encode_pat(snd, Place::Hole(rgt));
        Place::Tree(tree)
      }
      Pattern::Tup { fst, snd } => {
        let lab = 1;
        let (tree, lft, rgt) = create_ctr(lab);
        self.encode_pat(fst, Place::Hole(lft));
        self.encode_pat(snd, Place::Hole(rgt));
        Place::Tree(tree)
      }
      Pattern::Era => Place::Tree(LoanedMut::new(Tree::Era)),
      _ => unreachable!(),
    }
  }
  fn erase_all(&mut self) {
    for p in std::mem::take(&mut self.vars).into_values() {
      self.erase(p);
    }
  }
  fn finish(mut self) {
    for p in std::mem::take(&mut self.vars).into_values() {
      self.erase(p);
    }
  }
}

fn create_ctr<'t>(lab: u16) -> (LoanedMut<'t, Tree>, &'t mut Tree, &'t mut Tree) {
  let ((lft, rgt), tree) = LoanedMut::loan_with(Tree::Ctr { lab, lft: hole(), rgt: hole() }, |tree, l| {
    let Tree::Ctr { lft, rgt, .. } = tree else { unreachable!() };
    (l.loan_mut(lft), l.loan_mut(rgt))
  });
  (tree, lft, rgt)
}

fn create_op2<'t>(opr: hvmc::ops::Op) -> (LoanedMut<'t, Tree>, &'t mut Tree, &'t mut Tree) {
  let ((lft, rgt), tree) = LoanedMut::loan_with(Tree::Op2 { opr, lft: hole(), rgt: hole() }, |tree, l| {
    let Tree::Op2 { lft, rgt, .. } = tree else { unreachable!() };
    (l.loan_mut(lft), l.loan_mut(rgt))
  });
  (tree, lft, rgt)
}

impl Op {
  pub fn to_hvmc_label(self) -> hvmc::ops::Op {
    use hvmc::ops::Op as RtOp;
    match self {
      Op::ADD => RtOp::Add,
      Op::SUB => RtOp::Sub,
      Op::MUL => RtOp::Mul,
      Op::DIV => RtOp::Div,
      Op::MOD => RtOp::Mod,
      Op::EQ => RtOp::Eq,
      Op::NE => RtOp::Ne,
      Op::LT => RtOp::Lt,
      Op::GT => RtOp::Gt,
      Op::LTE => RtOp::Lte,
      Op::GTE => RtOp::Gte,
      Op::AND => RtOp::And,
      Op::OR => RtOp::Or,
      Op::XOR => RtOp::Xor,
      Op::LSH => RtOp::Lsh,
      Op::RSH => RtOp::Rsh,
      Op::NOT => RtOp::Not,
    }
  }
}

fn hole<T: Default>() -> T {
  T::default()
}
