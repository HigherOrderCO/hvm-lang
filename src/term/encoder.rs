use std::collections::{BTreeMap, HashMap};

use hvmc::ast::{num_to_str, Net, Tree};

use indexmap::{map::Entry, IndexMap};
use loaned::LoanedMut;

use crate::term::{MatchNum, Pattern};

use super::{Book, DefId, DefNames, Name, Op, Tag, Term};

pub fn book_to_tree(book: &Book, main: DefId) -> hvmc::ast::Book {
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

  nets
}

fn def_id_to_hvmc_name(def_id: &DefId) -> String {
  if def_id.0 == DefNames::HVM1_ENTRY_POINT { String::from(DefNames::ENTRY_POINT) } else { def_id.0.clone() }
}

/// Converts an IC term into an hvm-core net.
pub fn term_to_compat_net(term: &Term, labels: &mut Labels) -> hvmc::ast::Net {
  let mut encoder = Encoder {
    global_vars: IndexMap::new(),
    local_vars: IndexMap::new(),
    redexes: Vec::new(),
    name_idx: 0,
    labels,
  };

  let root = Box::new(Box::new(encoder.unfilled_tree()));
  let (root_ref, root_own) = LoanedMut::loan(root);

  encoder.encode_term(term, Place::Hole(root_ref));
  let loaned_redexes: Vec<_> = core::mem::take(&mut encoder.redexes);
  drop(encoder);
  let loaned_redexes: LoanedMut<Vec<(Box<Tree>, Box<Tree>)>> = {
    let mut loaned_redexes = std::mem::ManuallyDrop::new(loaned_redexes);
    unsafe {
      LoanedMut::new(Vec::from_raw_parts(
        loaned_redexes.as_mut_ptr() as *mut _,
        loaned_redexes.len(),
        loaned_redexes.capacity(),
      ))
    }
  };

  let redex = loaned::take!(loaned_redexes);
  let root = loaned::take!(root_own);

  Net { root: **root, rdex: redex.into_iter().map(|(a, b)| (*a, *b)).collect() }
}

#[derive(Debug)]
enum Place<'t> {
  Tree(LoanedMut<'t, Box<Tree>>),
  Hole(&'t mut Box<Tree>),
}

struct Encoder<'t, 'l> {
  local_vars: IndexMap<Name, Vec<Option<Place<'t>>>>,
  global_vars: IndexMap<Name, Place<'t>>,
  redexes: Vec<(LoanedMut<'t, Box<Tree>>, LoanedMut<'t, Box<Tree>>)>,
  name_idx: usize,
  labels: &'l mut Labels,
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

impl<'t, 'l> Encoder<'t, 'l> {
  fn generate_string(&mut self) -> String {
    self.name_idx += 1;
    num_to_str(self.name_idx - 1)
  }
  fn make_new_var(&mut self) -> Tree {
    Tree::Var { nam: self.generate_string() }
  }
  fn erase(&mut self, term: Place<'t>) {
    self.link(term, Place::Tree(LoanedMut::new(Box::new(Tree::Era))))
  }
  fn link(&mut self, a: Place<'t>, b: Place<'t>) {
    match (a, b) {
      (Place::Hole(x), Place::Hole(y)) => {
        let var = self.make_new_var();
        *x = Box::new(var.clone());
        *y = Box::new(var);
      }
      (Place::Tree(x), Place::Tree(y)) => self.redexes.push((x, y)),
      (Place::Tree(t), Place::Hole(h)) | (Place::Hole(h), Place::Tree(t)) => t.place(h),
    }
  }
  fn set_global_var(&mut self, var: Name, place: Place<'t>) {
    match self.global_vars.entry(var) {
      Entry::Occupied(e) => {
        let k = e.remove();
        self.link(place, k)
      }
      Entry::Vacant(e) => {
        e.insert(place);
      }
    }
  }
  fn push_scope(&mut self, var: Name, place: Place<'t>) {
    self.local_vars.entry(var).or_default().push(Some(place));
  }
  fn pop_scope(&mut self, var: Name) -> Option<Option<Place<'t>>> {
    self.local_vars.entry(var).or_default().pop()
  }
  /// Erases var if not used.
  fn pop_scope_erase(&mut self, var: Name) {
    if let Some(e) = self.pop_scope(var.clone()).unwrap_or_else(|| panic!("Pop nonpushed var {:?}", var)) {
      self.erase(e);
    }
  }
  fn use_var(&mut self, var: Name, place: Place<'t>) {
    let other_place = self
      .local_vars
      .entry(var)
      .or_default()
      .last_mut()
      .as_mut()
      .expect("Undefined var")
      .take()
      .expect("Var used twice");
    self.link(other_place, place)
  }
  fn encode_term(&mut self, term: &Term, place: Place<'t>) {
    match term {
      Term::Lnk { nam } => {
        self.set_global_var(nam.clone(), place);
      }
      Term::Chn { tag, nam, bod } => {
        let lab = (self.labels.con.generate(tag).unwrap_or(0) << 1) as u16;
        let (tree_ref, tree_box) =
          LoanedMut::loan(Box::new(Tree::Ctr { lab, lft: Default::default(), rgt: Default::default() }));
        let Tree::Ctr { lft, rgt, .. } = tree_ref else { unreachable!() };
        self.link(place, Place::Tree(tree_box));
        self.set_global_var(nam.clone(), Place::Hole(lft));
        self.encode_term(bod.as_ref(), Place::Hole(rgt));
      }
      Term::Var { nam } => {
        self.use_var(nam.clone(), place);
      }
      Term::Lam { tag, nam, bod } => {
        let lab = (self.labels.con.generate(tag).unwrap_or(0) << 1) as u16;
        let (tree_ref, tree_box) =
          LoanedMut::loan(Box::new(Tree::Ctr { lab, lft: Default::default(), rgt: Default::default() }));
        let Tree::Ctr { lft, rgt, .. } = tree_ref else { unreachable!() };
        self.link(place, Place::Tree(tree_box));
        if let Some(nam) = nam {
          self.push_scope(nam.clone(), Place::Hole(lft));
        }
        self.encode_term(bod.as_ref(), Place::Hole(rgt));
        if let Some(nam) = nam {
          self.pop_scope_erase(nam.clone());
        }
      }
      Term::App { tag, fun, arg } => {
        let lab = (self.labels.con.generate(tag).unwrap_or(0) << 1) as u16;
        let (tree_ref, tree_box) =
          LoanedMut::loan(Box::new(Tree::Ctr { lab, lft: Default::default(), rgt: Default::default() }));
        let Tree::Ctr { lft, rgt, .. } = tree_ref else { unreachable!() };
        self.link(place, Place::Hole(rgt));
        self.encode_term(fun.as_ref(), Place::Tree(tree_box));
        self.encode_term(arg.as_ref(), Place::Hole(lft));
      }
      Term::Dup { tag, fst, snd, val, nxt } => {
        let lab = ((self.labels.dup.generate(tag).unwrap_or(0) << 1) + 3) as u16;
        let (tree_ref, tree_box) =
          LoanedMut::loan(Box::new(Tree::Ctr { lab, lft: Default::default(), rgt: Default::default() }));
        let Tree::Ctr { lft, rgt, .. } = tree_ref else { unreachable!() };
        self.encode_term(val, Place::Tree(tree_box));
        if let Some(fst) = fst {
          self.push_scope(fst.clone(), Place::Hole(lft));
        }
        if let Some(snd) = snd {
          self.push_scope(snd.clone(), Place::Hole(rgt));
        }
        self.encode_term(nxt, place);
        if let Some(fst) = fst {
          self.pop_scope_erase(fst.clone());
        }
        if let Some(snd) = snd {
          self.pop_scope_erase(snd.clone());
        }
      }
      Term::Ref { def_id } => {
        self.link(place, Place::Tree(LoanedMut::new(Box::new(Tree::Ref { nam: def_id.0.clone() }))))
      }
      Term::Sup { tag, fst, snd } => {
        let lab = ((self.labels.dup.generate(tag).unwrap_or(0) << 1) + 3) as u16;
        let (tree_ref, tree_box) =
          LoanedMut::loan(Box::new(Tree::Ctr { lab, lft: Default::default(), rgt: Default::default() }));
        let Tree::Ctr { lft, rgt, .. } = tree_ref else { unreachable!() };
        self.encode_term(fst, Place::Hole(lft));
        self.encode_term(snd, Place::Hole(rgt));
        self.link(Place::Tree(tree_box), place)
      }
      Term::Tup { fst, snd } => {
        let lab = 1;
        let (tree_ref, tree_box) =
          LoanedMut::loan(Box::new(Tree::Ctr { lab, lft: Default::default(), rgt: Default::default() }));
        let Tree::Ctr { lft, rgt, .. } = tree_ref else { unreachable!() };
        self.encode_term(fst, Place::Hole(lft));
        self.encode_term(snd, Place::Hole(rgt));
        self.link(Place::Tree(tree_box), place);
      }
      Term::Era => {
        self.erase(place);
      }
      Term::Num { val } => {
        let tree_own = LoanedMut::new(Box::new(Tree::Num { val: *val }));
        self.link(Place::Tree(tree_own), place);
      }
      Term::Opx { op, fst, snd } => {
        let (tree_ref, tree_box) = LoanedMut::loan(Box::new(Tree::Op2 {
          opr: op.to_hvmc_label(),
          lft: Default::default(),
          rgt: Default::default(),
        }));
        let Tree::Op2 { lft, rgt, .. } = tree_ref else { unreachable!() };
        self.encode_term(snd, Place::Hole(lft));
        self.encode_term(fst, Place::Tree(tree_box));
        self.link(Place::Hole(rgt), place);
      }
      Term::Match { scrutinee, arms } => {
        // It must be a zero-succ match.
        // because other matches get desugared
        //debug_assert!(matches!(arms[0].0, Pattern::Num { MatchNum::Zero }));
        //debug_assert!(matches!(arms[1].0, Pattern::Num { MatchNum::Succ(None))));
        todo!();
        let zero = &arms[0].1;
        let succ = &arms[1].1;

        let (tree_ref, tree_box) = LoanedMut::loan(Box::new(Tree::Mat {
          sel: Box::new(Tree::Ctr { lab: 0, lft: Default::default(), rgt: Default::default() }),
          ret: Default::default(),
        }));

        self.encode_term(scrutinee, Place::Tree(tree_box));
        let Tree::Mat { sel: box Tree::Ctr { lft: zero_p, rgt: succ_p, .. }, ret } = tree_ref else {
          unreachable!()
        };

        self.encode_term(zero, Place::Hole(zero_p));
        self.encode_term(succ, Place::Hole(succ_p));
        self.link(place, Place::Hole(ret));
      }
      x => todo!("{:?}", x),
    }
  }
  fn unfilled_tree(&mut self) -> Tree {
    Tree::default()
  }
  fn erase_vars(&mut self) {
    // Erase all variables
    // SAFETY: Here we make self.vars.drain(..)'s lifetime
    // not overlap with `self`'s when we do `self.erase`
    // This is safe because it's borrow splitting.
    // self.erase does not use `vars` and never will
    // so there's no problem with doing this.
    let vars: indexmap::map::Drain<'_, String, Place<'t>> =
      unsafe { core::mem::transmute(self.global_vars.drain(..)) };
    for (_k, v) in vars {
      self.erase(v);
    }
  }
}

impl<'t, 'l> Drop for Encoder<'t, 'l> {
  fn drop(&mut self) {
    self.erase_vars()
  }
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
