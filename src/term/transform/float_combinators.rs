use indexmap::IndexSet;

use crate::{
  multi_iterator,
  term::{Book, Definition, Name, Rule, Term},
};
use std::collections::BTreeMap;

type Combinators = BTreeMap<Name, Definition>;

impl Book {
  /// Extracts unsafe terms into new definitions.
  ///
  /// Precondition: Variables must have been sanitized.
  ///
  /// The floating algorithm follows these rules:
  /// - Recursively float every child term.
  /// - Extract if it is a combinator and not is a safe term.
  pub fn float_combinators(&mut self) {
    let mut combinators = Combinators::new();

    let slf = self.clone();
    for (def_name, def) in self.defs.iter_mut() {
      let mut name_gen = 0;

      if self.entrypoint.as_ref().is_some_and(|m| m == def_name) {
        continue;
      }

      let builtin = def.builtin;
      let rule = def.rule_mut();
      let mut seen = IndexSet::new();
      rule.body.float_combinators(&mut combinators, &mut name_gen, &slf, def_name, builtin, &mut seen);
    }

    self.defs.extend(combinators);
  }
}

impl Term {
  fn float_combinators(
    &mut self,
    combinators: &mut Combinators,
    name_gen: &mut usize,
    book: &Book,
    def_name: &Name,
    builtin: bool,
    seen: &mut IndexSet<Name>,
  ) {
    for term in self.float_children_mut() {
      // Recursively float the children terms.
      term.float_combinators(combinators, name_gen, book, def_name, builtin, seen);

      if term.is_combinator() && !term.is_safe(book, seen) {
        float_combinator(def_name, name_gen, term, builtin, combinators);
      }
    }
  }
}

/// Inserts a new definition for the given term in the combinators map.
fn float_combinator(
  def_name: &Name,
  name_gen: &mut usize,
  term: &mut Term,
  builtin: bool,
  combinators: &mut BTreeMap<Name, Definition>,
) {
  let comb_name = Name::new(format!("{}$C{}", def_name, *name_gen));
  *name_gen += 1;

  let comb_ref = Term::Ref { nam: comb_name.clone() };
  let extracted_term = std::mem::replace(term, comb_ref);

  let rules = vec![Rule { body: extracted_term, pats: Vec::new() }];
  let rule = Definition { name: comb_name.clone(), rules, builtin };
  combinators.insert(comb_name, rule);
}

impl Term {
  /// A term can be considered safe if it is:
  /// - A Number or an Eraser.
  /// - A Tuple or Superposition where all elements are safe.
  /// - A safe Lambda, e.g. a nullary constructor or a lambda with safe body.
  /// - A Reference with safe body.
  pub fn is_safe(&self, book: &Book, seen: &mut IndexSet<Name>) -> bool {
    Term::recursive_call(move || match self {
      Term::Num { .. } | Term::Era => true,

      Term::Tup { els } | Term::Sup { els, .. } => els.iter().all(|e| Term::is_safe(e, book, seen)),

      Term::Lam { .. } => self.is_safe_lambda(book, seen),

      Term::Ref { nam } => {
        if seen.contains(nam) {
          return false;
        }

        seen.insert(nam.clone());
        if let Some(definition) = book.defs.get(nam) {
          definition.rule().body.is_safe(book, seen)
        } else {
          false
        }
      }

      _ => false,
    })
  }

  /// Checks if the term is a lambda sequence with the body being a variable in the scope or a reference.
  fn is_safe_lambda(&self, book: &Book, seen: &mut IndexSet<Name>) -> bool {
    let mut current = self;
    let mut scope = Vec::new();

    while let Term::Lam { nam, bod, .. } = current {
      if let Some(nam) = nam {
        scope.push(nam);
      }
      current = bod;
    }

    match current {
      Term::Var { nam } if scope.contains(&nam) => true,
      Term::Ref { .. } => true,
      term => term.is_safe(book, seen),
    }
  }

  pub fn has_unscoped_diff(&self) -> bool {
    let (declared, used) = self.unscoped_vars();

    declared.difference(&used).count() != 0 || used.difference(&declared).count() != 0
  }

  fn is_combinator(&self) -> bool {
    self.free_vars().is_empty() && !self.has_unscoped_diff() && !matches!(self, Term::Ref { .. })
  }
}

impl Term {
  pub fn float_children_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Term> {
    multi_iterator!(FloatIter { Zero, Two, Vec, Mat, App });
    match self {
      Term::App { fun, arg, .. } => {
        let mut args = vec![arg.as_mut()];
        let mut app = fun.as_mut();
        while let Term::App { fun, arg, .. } = app {
          args.push(arg);
          app = fun;
        }
        args.push(app);
        FloatIter::App(args)
      }
      Term::Mat { args, rules } => {
        FloatIter::Mat(args.iter_mut().chain(rules.iter_mut().map(|r| &mut r.body)))
      }
      Term::Tup { els } | Term::Sup { els, .. } | Term::Lst { els } => FloatIter::Vec(els),
      Term::Let { val: fst, nxt: snd, .. }
      | Term::Use { val: fst, nxt: snd, .. }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Opx { fst, snd, .. } => FloatIter::Two([fst.as_mut(), snd.as_mut()]),
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => bod.float_children_mut(),
      Term::Var { .. }
      | Term::Lnk { .. }
      | Term::Num { .. }
      | Term::Nat { .. }
      | Term::Str { .. }
      | Term::Ref { .. }
      | Term::Era
      | Term::Err => FloatIter::Zero([]),
    }
  }
}
