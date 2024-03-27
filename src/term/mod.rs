use self::parser::lexer::STRINGS;
use crate::{
  diagnostics::{Diagnostics, DiagnosticsConfig},
  term::builtins::*,
  ENTRY_POINT,
};
use indexmap::{IndexMap, IndexSet};
use interner::global::GlobalString;
use itertools::Itertools;
use std::{borrow::Cow, collections::HashMap, ops::Deref};

pub mod builtins;
pub mod check;
pub mod display;
pub mod load_book;
pub mod net_to_term;
pub mod parser;
pub mod term_to_net;
pub mod transform;

pub use net_to_term::{net_to_term, ReadbackError};
pub use term_to_net::{book_to_nets, term_to_compat_net};

#[derive(Debug)]
pub struct Ctx<'book> {
  pub book: &'book mut Book,
  pub info: Diagnostics,
}

impl Ctx<'_> {
  pub fn new(book: &mut Book, diagnostics_cfg: DiagnosticsConfig) -> Ctx {
    Ctx { book, info: Diagnostics::new(diagnostics_cfg) }
  }
}

/// The representation of a program.
#[derive(Debug, Clone, Default)]
pub struct Book {
  /// The function definitions.
  pub defs: IndexMap<Name, Definition>,

  /// The algebraic datatypes defined by the program
  pub adts: Adts,

  /// To which type does each constructor belong to.
  pub ctrs: Constructors,

  /// A custom or default "main" entrypoint.
  pub entrypoint: Option<Name>,
}

pub type Adts = IndexMap<Name, Adt>;
pub type Constructors = IndexMap<Name, Name>;

/// A pattern matching function definition.
#[derive(Debug, Clone)]
pub struct Definition {
  pub name: Name,
  pub rules: Vec<Rule>,
  pub builtin: bool,
}

/// A pattern matching rule of a definition.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Rule {
  pub pats: Vec<Pattern>,
  pub body: Term,
}

#[derive(Debug, Default, PartialEq, Eq, Hash)]
pub enum Term {
  Lam {
    tag: Tag,
    nam: Option<Name>,
    bod: Box<Term>,
  },
  Var {
    nam: Name,
  },
  /// Like a scopeless lambda, where the variable can occur outside the body
  Chn {
    tag: Tag,
    nam: Option<Name>,
    bod: Box<Term>,
  },
  /// The use of a Channel variable.
  Lnk {
    nam: Name,
  },
  Let {
    nam: Option<Name>,
    val: Box<Term>,
    nxt: Box<Term>,
  },
  Use {
    nam: Name,
    val: Box<Term>,
    nxt: Box<Term>,
  },
  App {
    tag: Tag,
    fun: Box<Term>,
    arg: Box<Term>,
  },
  /// "let tup" tuple destructor
  Ltp {
    bnd: Vec<Option<Name>>,
    val: Box<Term>,
    nxt: Box<Term>,
  },
  Tup {
    els: Vec<Term>,
  },
  Dup {
    tag: Tag,
    bnd: Vec<Option<Name>>,
    val: Box<Term>,
    nxt: Box<Term>,
  },
  Sup {
    tag: Tag,
    els: Vec<Term>,
  },
  Num {
    val: u64,
  },
  Nat {
    val: u64,
  },
  Str {
    val: GlobalString,
  },
  Lst {
    els: Vec<Term>,
  },
  /// A numeric operation between built-in numbers.
  Opx {
    op: Op,
    fst: Box<Term>,
    snd: Box<Term>,
  },
  /// Pattern matching on an ADT.
  Mat {
    arg: Box<Term>,
    rules: Vec<(Option<Name>, Vec<Option<Name>>, Term)>,
  },
  /// Native pattern matching on numbers
  Swt {
    arg: Box<Term>,
    rules: Vec<(NumCtr, Term)>,
  },
  Ref {
    nam: Name,
  },
  Era,
  #[default]
  Err,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern {
  Var(Option<Name>),
  Ctr(Name, Vec<Pattern>),
  Num(u64),
  Tup(Vec<Pattern>),
  Lst(Vec<Pattern>),
  Str(GlobalString),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NumCtr {
  Num(u64),
  Succ(Option<Name>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Tag {
  Named(Name),
  Numeric(u32),
  Auto,
  Static,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
  Add,
  Sub,
  Mul,
  Div,
  Mod,
  Eq,
  Ne,
  Lt,
  Gt,
  Lte,
  Gte,
  And,
  Or,
  Xor,
  Shl,
  Shr,
}

/// A user defined datatype
#[derive(Debug, Clone, Default)]
pub struct Adt {
  pub ctrs: IndexMap<Name, Vec<Name>>,
  pub builtin: bool,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum AdtEncoding {
  Scott,

  #[default]
  TaggedScott,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(GlobalString);

/* Implementations */

/// A macro for creating iterators that can have statically known
/// different types. Useful for iterating over tree children, where
/// each tree node variant yields a different iterator type.
macro_rules! multi_iterator {
  ($Iter:ident { $($Variant:ident),* $(,)? }) => {
    #[derive(Debug, Clone)]
    enum $Iter<$($Variant),*> {
      $($Variant { iter: $Variant }),*
    }

    impl<$($Variant),*> $Iter<$($Variant),*> {
      $(
        #[allow(non_snake_case)]
        fn $Variant(iter: impl IntoIterator<IntoIter = $Variant>) -> Self {
          $Iter::$Variant { iter: iter.into_iter() }
        }
      )*
    }

    impl<T, $($Variant: Iterator<Item = T>),*> Iterator for $Iter<$($Variant),*> {
      type Item = T;
      fn next(&mut self) -> Option<T> {
        match self { $($Iter::$Variant { iter } => iter.next()),* }
      }

      fn size_hint(&self) -> (usize, Option<usize>) {
        match self { $($Iter::$Variant { iter } => iter.size_hint()),* }
      }
    }

    impl<T, $($Variant: DoubleEndedIterator<Item = T>),*> DoubleEndedIterator for $Iter<$($Variant),*> {
      fn next_back(&mut self) -> Option<T> {
        match self { $($Iter::$Variant { iter } => iter.next_back()),* }
      }
    }
  };
}

impl PartialEq<str> for Name {
  fn eq(&self, other: &str) -> bool {
    &**self == other
  }
}

impl PartialEq<&str> for Name {
  fn eq(&self, other: &&str) -> bool {
    self == other
  }
}

impl PartialEq<Option<Name>> for Name {
  fn eq(&self, other: &Option<Name>) -> bool {
    if let Some(other) = other.as_ref() { self == other } else { false }
  }
}

impl PartialEq<Name> for Option<Name> {
  fn eq(&self, other: &Name) -> bool {
    other.eq(self)
  }
}

pub fn num_to_name(mut num: u64) -> String {
  let mut name = String::new();
  loop {
    let c = (num % 26) as u8 + b'a';
    name.push(c as char);
    num /= 26;
    if num == 0 {
      break;
    }
  }
  name
}

impl Tag {
  pub fn adt_name(name: &Name) -> Self {
    Self::Named(name.clone())
  }
}

impl Clone for Term {
  fn clone(&self) -> Self {
    Self::recursive_call(move || match self {
      Self::Lam { tag, nam, bod } => Self::Lam { tag: tag.clone(), nam: nam.clone(), bod: bod.clone() },
      Self::Var { nam } => Self::Var { nam: nam.clone() },
      Self::Chn { tag, nam, bod } => Self::Chn { tag: tag.clone(), nam: nam.clone(), bod: bod.clone() },
      Self::Lnk { nam } => Self::Lnk { nam: nam.clone() },
      Self::Let { nam, val, nxt } => Self::Let { nam: nam.clone(), val: val.clone(), nxt: nxt.clone() },
      Self::Use { nam, val, nxt } => Self::Use { nam: nam.clone(), val: val.clone(), nxt: nxt.clone() },
      Self::App { tag, fun, arg } => Self::App { tag: tag.clone(), fun: fun.clone(), arg: arg.clone() },
      Self::Ltp { bnd, val, nxt } => Self::Ltp { bnd: bnd.clone(), val: val.clone(), nxt: nxt.clone() },
      Self::Tup { els } => Self::Tup { els: els.clone() },
      Self::Dup { tag, bnd, val, nxt } => {
        Self::Dup { tag: tag.clone(), bnd: bnd.clone(), val: val.clone(), nxt: nxt.clone() }
      }
      Self::Sup { tag, els } => Self::Sup { tag: tag.clone(), els: els.clone() },
      Self::Num { val } => Self::Num { val: *val },
      Self::Nat { val } => Self::Nat { val: *val },
      Self::Str { val } => Self::Str { val: val.clone() },
      Self::Lst { els } => Self::Lst { els: els.clone() },
      Self::Opx { op, fst, snd } => Self::Opx { op: *op, fst: fst.clone(), snd: snd.clone() },
      Self::Mat { arg, rules } => Self::Mat { arg: arg.clone(), rules: rules.clone() },
      Self::Swt { arg, rules } => Self::Swt { arg: arg.clone(), rules: rules.clone() },
      Self::Ref { nam } => Self::Ref { nam: nam.clone() },
      Self::Era => Self::Era,
      Self::Err => Self::Err,
    })
  }
}

impl Drop for Term {
  fn drop(&mut self) {
    impl Term {
      fn take_children(&mut self, stack: &mut Vec<Term>) {
        match self {
          Term::Lam { bod, .. } | Term::Chn { bod, .. } => {
            stack.push(std::mem::take(bod.as_mut()));
          }
          Term::Let { val: fst, nxt: snd, .. }
          | Term::Use { val: fst, nxt: snd, .. }
          | Term::App { fun: fst, arg: snd, .. }
          | Term::Dup { val: fst, nxt: snd, .. }
          | Term::Opx { fst, snd, .. } => {
            stack.push(std::mem::take(fst.as_mut()));
            stack.push(std::mem::take(snd.as_mut()));
          }
          Term::Mat { arg, rules } => {
            stack.push(std::mem::take(arg));
            for (_ctr, _fields, body) in std::mem::take(rules).into_iter() {
              stack.push(body);
            }
          }
          Term::Swt { arg, rules } => {
            stack.push(std::mem::take(arg));
            for (_nam, body) in std::mem::take(rules).into_iter() {
              stack.push(body);
            }
          }
          Term::Lst { els } | Term::Tup { els } | Term::Sup { els, .. } => {
            for el in std::mem::take(els).into_iter() {
              stack.push(el);
            }
          }
          _ => {}
        }
      }
    }

    if matches!(self, Term::Era | Term::Err) {
      return;
    }

    let mut stack = vec![];
    self.take_children(&mut stack);

    while let Some(mut term) = stack.pop() {
      term.take_children(&mut stack)
    }
  }
}

impl Term {
  /* Common construction patterns */
  pub fn lam(nam: Option<Name>, bod: Term) -> Self {
    Term::Lam { tag: Tag::Static, nam, bod: Box::new(bod) }
  }

  pub fn named_lam(nam: Name, bod: Term) -> Self {
    Term::Lam { tag: Tag::Static, nam: Some(nam), bod: Box::new(bod) }
  }

  pub fn erased_lam(bod: Term) -> Self {
    Term::Lam { tag: Tag::Static, nam: None, bod: Box::new(bod) }
  }

  pub fn tagged_lam(tag: Tag, nam: Option<Name>, bod: Term) -> Self {
    Term::Lam { tag, nam, bod: Box::new(bod) }
  }

  pub fn var_or_era(nam: Option<Name>) -> Self {
    if let Some(nam) = nam { Term::Var { nam } } else { Term::Era }
  }

  pub fn app(fun: Term, arg: Term) -> Self {
    Term::App { tag: Tag::Static, fun: Box::new(fun), arg: Box::new(arg) }
  }

  pub fn tagged_app(tag: Tag, fun: Term, arg: Term) -> Self {
    Term::App { tag, fun: Box::new(fun), arg: Box::new(arg) }
  }

  /// Make a call term by folding args around a called function term with applications.
  pub fn call(called: Term, args: impl IntoIterator<Item = Term>) -> Self {
    args.into_iter().fold(called, Term::app)
  }

  pub fn tagged_call(tag: Tag, called: Term, args: impl IntoIterator<Item = Term>) -> Self {
    args.into_iter().fold(called, |acc, arg| Term::tagged_app(tag.clone(), acc, arg))
  }

  /// Apply a variable to a term by the var name.
  pub fn arg_call(fun: Term, arg: Name) -> Self {
    Term::app(fun, Term::Var { nam: arg })
  }

  pub fn r#ref(name: &str) -> Self {
    Term::Ref { nam: name.into() }
  }

  pub fn str(str: &str) -> Self {
    Term::Str { val: STRINGS.get(str) }
  }

  pub fn switch(arg: Term, zero: Term, succ: Term, succ_var: Option<Name>) -> Term {
    let zero = (NumCtr::Num(0), zero);
    let succ = (NumCtr::Succ(succ_var), succ);
    Term::Swt { arg: Box::new(arg), rules: vec![zero, succ] }
  }

  pub fn sub_num(arg: Term, val: u64) -> Term {
    if val == 0 {
      arg
    } else {
      Term::Opx { op: Op::Sub, fst: Box::new(arg), snd: Box::new(Term::Num { val }) }
    }
  }

  pub fn add_num(arg: Term, val: u64) -> Term {
    if val == 0 {
      arg
    } else {
      Term::Opx { op: Op::Add, fst: Box::new(arg), snd: Box::new(Term::Num { val }) }
    }
  }

  /* Iterators */
  pub fn children(&self) -> impl DoubleEndedIterator<Item = &Term> + Clone {
    multi_iterator!(ChildrenIter { Zero, One, Two, Vec, Mat, Swt });
    match self {
      Term::Mat { arg, rules } => {
        ChildrenIter::Mat([arg.as_ref()].into_iter().chain(rules.iter().map(|r| &r.2)))
      }
      Term::Swt { arg, rules } => {
        ChildrenIter::Swt([arg.as_ref()].into_iter().chain(rules.iter().map(|r| &r.1)))
      }
      Term::Tup { els } | Term::Sup { els, .. } | Term::Lst { els } => ChildrenIter::Vec(els),
      Term::Let { val: fst, nxt: snd, .. }
      | Term::Use { val: fst, nxt: snd, .. }
      | Term::App { fun: fst, arg: snd, .. }
      | Term::Ltp { val: fst, nxt: snd, .. }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Opx { fst, snd, .. } => ChildrenIter::Two([fst.as_ref(), snd.as_ref()]),
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => ChildrenIter::One([bod.as_ref()]),
      Term::Var { .. }
      | Term::Lnk { .. }
      | Term::Num { .. }
      | Term::Nat { .. }
      | Term::Str { .. }
      | Term::Ref { .. }
      | Term::Era
      | Term::Err => ChildrenIter::Zero([]),
    }
  }

  pub fn children_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Term> {
    multi_iterator!(ChildrenIter { Zero, One, Two, Vec, Mat, Swt });
    match self {
      Term::Mat { arg, rules } => {
        ChildrenIter::Mat([arg.as_mut()].into_iter().chain(rules.iter_mut().map(|r| &mut r.2)))
      }
      Term::Swt { arg, rules } => {
        ChildrenIter::Swt([arg.as_mut()].into_iter().chain(rules.iter_mut().map(|r| &mut r.1)))
      }
      Term::Tup { els } | Term::Sup { els, .. } | Term::Lst { els } => ChildrenIter::Vec(els),
      Term::Let { val: fst, nxt: snd, .. }
      | Term::Use { val: fst, nxt: snd, .. }
      | Term::App { fun: fst, arg: snd, .. }
      | Term::Ltp { val: fst, nxt: snd, .. }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Opx { fst, snd, .. } => ChildrenIter::Two([fst.as_mut(), snd.as_mut()]),
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => ChildrenIter::One([bod.as_mut()]),
      Term::Var { .. }
      | Term::Lnk { .. }
      | Term::Num { .. }
      | Term::Nat { .. }
      | Term::Str { .. }
      | Term::Ref { .. }
      | Term::Era
      | Term::Err => ChildrenIter::Zero([]),
    }
  }

  /// An iterator over the subterms with an iterator over the binds
  /// introduced by the current term for each subterm.
  ///
  /// Example: A lambda introduces 1 bind for it's only subterm,
  /// while a let expression introduces 0 binds for the value and
  /// many binds for the next term.
  pub fn children_with_binds(
    &self,
  ) -> impl DoubleEndedIterator<Item = (&Term, impl DoubleEndedIterator<Item = &Option<Name>> + Clone)> + Clone
  {
    multi_iterator!(ChildrenIter { Zero, One, Two, Vec, Mat, Swt });
    multi_iterator!(BindsIter { Zero, One, Dup, Mat });
    match self {
      Term::Mat { arg, rules } => ChildrenIter::Mat(
        [(arg.as_ref(), BindsIter::Zero([]))]
          .into_iter()
          .chain(rules.iter().map(|r| (&r.2, BindsIter::Mat(r.1.iter())))),
      ),
      Term::Swt { arg, rules } => {
        ChildrenIter::Swt([(arg.as_ref(), BindsIter::Zero([]))].into_iter().chain(rules.iter().map(|r| {
          match &r.0 {
            NumCtr::Num(_) => (&r.1, BindsIter::Zero([])),
            NumCtr::Succ(nam) => (&r.1, BindsIter::One([nam])),
          }
        })))
      }
      Term::Tup { els } | Term::Sup { els, .. } | Term::Lst { els } => {
        ChildrenIter::Vec(els.iter().map(|el| (el, BindsIter::Zero([]))))
      }
      Term::Let { nam, val, nxt, .. } => {
        ChildrenIter::Two([(val.as_ref(), BindsIter::Zero([])), (nxt.as_ref(), BindsIter::One([nam]))])
      }
      Term::Use { .. } => todo!(),
      Term::Ltp { bnd, val, nxt, .. } | Term::Dup { bnd, val, nxt, .. } => {
        ChildrenIter::Two([(val.as_ref(), BindsIter::Zero([])), (nxt.as_ref(), BindsIter::Dup(bnd))])
      }
      Term::App { fun: fst, arg: snd, .. } | Term::Opx { fst, snd, .. } => {
        ChildrenIter::Two([(fst.as_ref(), BindsIter::Zero([])), (snd.as_ref(), BindsIter::Zero([]))])
      }
      Term::Lam { nam, bod, .. } => ChildrenIter::One([(bod.as_ref(), BindsIter::One([nam]))]),
      Term::Chn { bod, .. } => ChildrenIter::One([(bod.as_ref(), BindsIter::Zero([]))]),
      Term::Var { .. }
      | Term::Lnk { .. }
      | Term::Num { .. }
      | Term::Nat { .. }
      | Term::Str { .. }
      | Term::Ref { .. }
      | Term::Era
      | Term::Err => ChildrenIter::Zero([]),
    }
  }

  pub fn children_mut_with_binds(
    &mut self,
  ) -> impl DoubleEndedIterator<Item = (&mut Term, impl DoubleEndedIterator<Item = &Option<Name>> + Clone)>
  {
    multi_iterator!(ChildrenIter { Zero, One, Two, Vec, Mat, Swt });
    multi_iterator!(BindsIter { Zero, One, Dup, Mat });
    match self {
      Term::Mat { arg, rules } => ChildrenIter::Mat(
        [(arg.as_mut(), BindsIter::Zero([]))]
          .into_iter()
          .chain(rules.iter_mut().map(|r| (&mut r.2, BindsIter::Mat(r.1.iter())))),
      ),
      Term::Swt { arg, rules } => ChildrenIter::Swt([(arg.as_mut(), BindsIter::Zero([]))].into_iter().chain(
        rules.iter_mut().map(|r| match &r.0 {
          NumCtr::Num(_) => (&mut r.1, BindsIter::Zero([])),
          NumCtr::Succ(nam) => (&mut r.1, BindsIter::One([nam])),
        }),
      )),
      Term::Tup { els } | Term::Sup { els, .. } | Term::Lst { els } => {
        ChildrenIter::Vec(els.iter_mut().map(|el| (el, BindsIter::Zero([]))))
      }
      Term::Let { nam, val, nxt, .. } => {
        ChildrenIter::Two([(val.as_mut(), BindsIter::Zero([])), (nxt.as_mut(), BindsIter::One([&*nam]))])
      }
      Term::Use { .. } => todo!(),
      Term::Ltp { bnd, val, nxt, .. } | Term::Dup { bnd, val, nxt, .. } => {
        ChildrenIter::Two([(val.as_mut(), BindsIter::Zero([])), (nxt.as_mut(), BindsIter::Dup(bnd.iter()))])
      }
      Term::App { fun: fst, arg: snd, .. } | Term::Opx { fst, snd, .. } => {
        ChildrenIter::Two([(fst.as_mut(), BindsIter::Zero([])), (snd.as_mut(), BindsIter::Zero([]))])
      }
      Term::Lam { nam, bod, .. } => ChildrenIter::One([(bod.as_mut(), BindsIter::One([&*nam]))]),
      Term::Chn { bod, .. } => ChildrenIter::One([(bod.as_mut(), BindsIter::Zero([]))]),
      Term::Var { .. }
      | Term::Lnk { .. }
      | Term::Num { .. }
      | Term::Nat { .. }
      | Term::Str { .. }
      | Term::Ref { .. }
      | Term::Era
      | Term::Err => ChildrenIter::Zero([]),
    }
  }

  pub fn children_mut_with_binds_mut(
    &mut self,
  ) -> impl DoubleEndedIterator<Item = (&mut Term, impl DoubleEndedIterator<Item = &mut Option<Name>>)> {
    multi_iterator!(ChildrenIter { Zero, One, Two, Vec, Mat, Swt });
    multi_iterator!(BindsIter { Zero, One, Dup, Mat });
    match self {
      Term::Mat { arg, rules } => ChildrenIter::Mat(
        [(arg.as_mut(), BindsIter::Zero([]))]
          .into_iter()
          .chain(rules.iter_mut().map(|r| (&mut r.2, BindsIter::Mat(r.1.iter_mut())))),
      ),
      Term::Swt { arg, rules } => ChildrenIter::Swt([(arg.as_mut(), BindsIter::Zero([]))].into_iter().chain(
        rules.iter_mut().map(|r| match &mut r.0 {
          NumCtr::Num(_) => (&mut r.1, BindsIter::Zero([])),
          NumCtr::Succ(nam) => (&mut r.1, BindsIter::One([nam])),
        }),
      )),
      Term::Tup { els } | Term::Sup { els, .. } | Term::Lst { els } => {
        ChildrenIter::Vec(els.iter_mut().map(|el| (el, BindsIter::Zero([]))))
      }
      Term::Use { .. } => todo!(),
      Term::Let { nam, val, nxt, .. } => {
        ChildrenIter::Two([(val.as_mut(), BindsIter::Zero([])), (nxt.as_mut(), BindsIter::One([nam]))])
      }
      Term::Ltp { bnd, val, nxt, .. } | Term::Dup { bnd, val, nxt, .. } => {
        ChildrenIter::Two([(val.as_mut(), BindsIter::Zero([])), (nxt.as_mut(), BindsIter::Dup(bnd))])
      }
      Term::App { fun: fst, arg: snd, .. } | Term::Opx { fst, snd, .. } => {
        ChildrenIter::Two([(fst.as_mut(), BindsIter::Zero([])), (snd.as_mut(), BindsIter::Zero([]))])
      }
      Term::Lam { nam, bod, .. } => ChildrenIter::One([(bod.as_mut(), BindsIter::One([nam]))]),
      Term::Chn { bod, .. } => ChildrenIter::One([(bod.as_mut(), BindsIter::Zero([]))]),
      Term::Var { .. }
      | Term::Lnk { .. }
      | Term::Num { .. }
      | Term::Nat { .. }
      | Term::Str { .. }
      | Term::Ref { .. }
      | Term::Era
      | Term::Err => ChildrenIter::Zero([]),
    }
  }

  /* Common checks and transformations */
  pub fn recursive_call<R, F>(f: F) -> R
  where
    F: FnOnce() -> R,
  {
    stacker::maybe_grow(1024 * 32, 1024 * 1024, f)
  }

  /// Substitute the occurrences of a variable in a term with the given term.
  ///
  /// Caution: can cause invalid shadowing of variables if used incorrectly.
  /// Ex: Using subst to beta-reduce `(@a @b a b)` converting it into `@b b`.
  ///
  /// Expects var bind information to be properly stored in match expressions,
  /// so it must run AFTER `fix_match_terms`.
  pub fn subst(&mut self, from: &Name, to: &Term) {
    Term::recursive_call(move || match self {
      Term::Var { nam } if nam == from => *self = to.clone(),

      _ => {
        for (child, binds) in self.children_mut_with_binds() {
          if !binds.flat_map(|b| b.as_ref()).contains(from) {
            child.subst(from, to);
          }
        }
      }
    })
  }

  /// Substitute the occurrence of an unscoped variable with the given term.
  pub fn subst_unscoped(&mut self, from: &Name, to: &Term) {
    Term::recursive_call(move || {
      if let Term::Lnk { nam } = self
        && nam == from
      {
        *self = to.clone();
      }

      for child in self.children_mut() {
        child.subst_unscoped(from, to);
      }
    })
  }

  /// Collects all the free variables that a term has
  /// and the number of times each var is used
  pub fn free_vars(&self) -> HashMap<Name, u64> {
    fn go(term: &Term, free_vars: &mut HashMap<Name, u64>) {
      Term::recursive_call(move || {
        if let Term::Var { nam } = term {
          *free_vars.entry(nam.clone()).or_default() += 1;
        }

        for (child, binds) in term.children_with_binds() {
          let mut new_scope = Default::default();
          go(child, &mut new_scope);

          for nam in binds.flatten() {
            new_scope.remove(nam);
          }

          free_vars.extend(new_scope);
        }
      })
    }

    let mut free_vars = Default::default();
    go(self, &mut free_vars);
    free_vars
  }

  /// Returns the set of declared and the set of used unscoped variables
  pub fn unscoped_vars(&self) -> (IndexSet<Name>, IndexSet<Name>) {
    fn go(term: &Term, decls: &mut IndexSet<Name>, uses: &mut IndexSet<Name>) {
      Term::recursive_call(move || {
        match term {
          Term::Chn { nam: Some(nam), .. } => {
            decls.insert(nam.clone());
          }
          Term::Lnk { nam } => {
            uses.insert(nam.clone());
          }
          _ => {}
        }

        for child in term.children() {
          go(child, decls, uses);
        }
      })
    }
    let mut decls = Default::default();
    let mut uses = Default::default();
    go(self, &mut decls, &mut uses);
    (decls, uses)
  }
}

impl Pattern {
  pub fn binds(&self) -> impl DoubleEndedIterator<Item = &Option<Name>> + Clone {
    self.iter().filter_map(|pat| match pat {
      Pattern::Var(nam) => Some(nam),
      _ => None,
    })
  }

  pub fn binds_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Option<Name>> {
    // Can't have a Pattern::iter_mut() since it has a tree-like structure.
    let mut binds = vec![];
    let mut to_visit = vec![self];
    while let Some(pat) = to_visit.pop() {
      match pat {
        Pattern::Var(nam) => binds.push(nam),
        _ => to_visit.extend(pat.children_mut().rev()),
      }
    }
    binds.into_iter()
  }

  /// Returns an iterator over each immediate child sub-pattern of `self`.
  /// Considers Lists as its own pattern and not a sequence of Cons.
  pub fn children(&self) -> impl DoubleEndedIterator<Item = &Pattern> + Clone {
    multi_iterator!(ChildrenIter { Zero, Vec });
    match self {
      Pattern::Ctr(_, els) | Pattern::Tup(els) | Pattern::Lst(els) => ChildrenIter::Vec(els.iter()),
      Pattern::Var(_) | Pattern::Num(_) | Pattern::Str(_) => ChildrenIter::Zero([]),
    }
  }

  pub fn children_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Pattern> {
    multi_iterator!(ChildrenIter { Zero, Vec });
    match self {
      Pattern::Ctr(_, els) | Pattern::Tup(els) | Pattern::Lst(els) => ChildrenIter::Vec(els.iter_mut()),
      Pattern::Var(_) | Pattern::Num(_) | Pattern::Str(_) => ChildrenIter::Zero([]),
    }
  }

  /// Returns an iterator over each subpattern in depth-first, left to right order.
  // TODO: Not lazy.
  pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Pattern> + Clone {
    let mut to_visit = vec![self];
    let mut els = vec![];
    while let Some(pat) = to_visit.pop() {
      els.push(pat);
      to_visit.extend(pat.children().rev());
    }
    els.into_iter()
  }

  pub fn is_wildcard(&self) -> bool {
    matches!(self, Pattern::Var(_))
  }

  pub fn to_term(&self) -> Term {
    match self {
      Pattern::Var(nam) => Term::var_or_era(nam.clone()),
      Pattern::Ctr(ctr, args) => {
        Term::call(Term::Ref { nam: ctr.clone() }, args.iter().map(|arg| arg.to_term()))
      }
      Pattern::Num(val) => Term::Num { val: *val },
      Pattern::Tup(args) => Term::Tup { els: args.iter().map(|p| p.to_term()).collect() },
      Pattern::Lst(_) | Pattern::Str(_) => todo!(),
    }
  }
}

impl Rule {
  pub fn arity(&self) -> usize {
    self.pats.len()
  }
}

impl Definition {
  pub fn arity(&self) -> usize {
    self.rules[0].arity()
  }

  #[track_caller]
  pub fn assert_no_pattern_matching_rules(&self) {
    assert!(self.rules.len() == 1, "Definition rules should have been removed in earlier pass");
    assert!(self.rules[0].pats.is_empty(), "Definition args should have been removed in an earlier pass");
  }

  #[track_caller]
  pub fn rule(&self) -> &Rule {
    self.assert_no_pattern_matching_rules();
    &self.rules[0]
  }

  #[track_caller]
  pub fn rule_mut(&mut self) -> &mut Rule {
    self.assert_no_pattern_matching_rules();
    &mut self.rules[0]
  }
}

impl Name {
  pub fn new<'a, V: Into<Cow<'a, str>>>(value: V) -> Name {
    Name(STRINGS.get(value))
  }

  pub fn is_generated(&self) -> bool {
    // Generated def names use $ while var names use %
    self.contains('$') || self.contains('%')
  }
}

impl From<&str> for Name {
  fn from(value: &str) -> Self {
    Name(STRINGS.get(value))
  }
}

impl From<u64> for Name {
  fn from(value: u64) -> Self {
    num_to_name(value).as_str().into()
  }
}

impl From<u32> for Name {
  fn from(value: u32) -> Self {
    num_to_name(value as u64).as_str().into()
  }
}

impl Deref for Name {
  type Target = str;

  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

impl AsRef<str> for Name {
  fn as_ref(&self) -> &str {
    &self.0
  }
}

impl Book {
  pub fn hvmc_entrypoint(&self) -> &str {
    match self.entrypoint.as_ref().map(|e| e.as_ref()) {
      Some("main" | "Main") | None => ENTRY_POINT,
      Some(nam) => nam,
    }
  }
}
