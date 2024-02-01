use std::collections::{BTreeMap, HashSet};

use chumsky::container::Container;

use crate::term::{Book, DefId, DefNames, Definition, Name, Pattern, Rule, Term};

/// Replaces closed Terms (i.e. without free variables) with a Ref to the extracted term
/// Precondition: Vars must have been sanitized
impl Book {
  pub fn detach_supercombinators(&mut self) {
    let mut combinators = Combinators::new();

    for def in self.defs.values_mut() {
      for rule in def.rules.iter_mut() {
        let mut detacher = Detacher {
          name: def.def_id.clone(),
          combinators: &mut combinators,
          scope: Default::default(),
          depths: Default::default(),
          counter: 0,
        };
        detacher.is_detachable_level(&mut rule.body);
      }
    }


    for i in combinators.keys() {
      self.def_names.insert(Name(i.0.clone()));
    }

    // Definitions are not inserted to the book as they are defined to appease the borrow checker.
    // Since we are mut borrowing the rules we can't borrow the book to insert at the same time.
    self.defs.append(&mut combinators)
  }
}

type Combinators = BTreeMap<DefId, Definition>;

pub struct Detacher<'c> {
  combinators: &'c mut Combinators,
  scope: Vec<Name>,
  depths: Vec<usize>,
  counter: usize,
  name: DefId,
}

impl<'c> Detacher<'c> {
  pub fn push_scope(&mut self) {
    self.depths.push(self.scope.len())
  }
  pub fn pop_scope(&mut self) {
    self.scope.shrink_to(self.depths.pop().unwrap())
  }
  pub fn walk_pattern(&mut self, pattern: &mut Pattern) {
    match pattern {
        Pattern::Lnk { nam } => {
          self.scope.push(nam.clone());
        },
        _ => {

        }
    }
  }
  pub fn new_def_id(&mut self) -> DefId {
    self.counter += 1;
    DefId(format!("{}$S{}", self.name.0, self.counter - 1))
  }
  pub fn depth_of(&self, var: &Name) -> usize {
    let scope_idx = self.scope.iter().enumerate().find(|(idx, i)| var == *i).map(|x| x.0).unwrap_or(0);
    self.depths.binary_search(&scope_idx).unwrap_or_else(|x| x)
  }
  /// Returns the index in `depths` where the top-most variable used by this subterm is defined
  pub fn is_detachable_level(&mut self, mut term: &mut Term) -> usize {
    let mut complex = false;
    let dep = match &mut term {
      Term::Lnk { nam } => {
        self.depth_of(nam)
      },
      Term::Lam { tag, pat, bod } => {
        self.push_scope();
        self.walk_pattern(pat);
        let ret = self.is_detachable_level(bod);
        self.pop_scope();
        ret
      }
      Term::Let { pat, val, nxt } => {
        complex = true;
        let mut ret = self.is_detachable_level(val);
        self.push_scope();
        self.walk_pattern(pat);
        ret = ret.min(self.is_detachable_level(nxt));
        self.pop_scope();
        ret
      }
      Term::Match { scrutinee, arms } => {
        complex = true;
        let mut ret = self.is_detachable_level(scrutinee);
        for (pat, bod) in arms {
          self.push_scope();
          self.walk_pattern(pat);
          ret = ret.min(self.is_detachable_level(bod));
          self.pop_scope();
        };
        ret
      }
      term => {
        complex = true;
        let mut ret = usize::MAX;
        term.recurse_mut(|term| {
          ret = ret.min(self.is_detachable_level(term))
        }, |pat| todo!());
        ret
      }
    };
    if dep >= self.depths.len() && complex {
      let def_id = self.new_def_id();
      self.combinators.insert(def_id.clone(), Definition { def_id: def_id.clone(), rules: vec![
        Rule {
          pats: vec![],
          body: Term::Ref { def_id: def_id.clone() },
        }
      ]});
      // Swap the Ref with the term
      let Some(Definition { rules, .. }) = self.combinators.get_mut(&def_id) else { unreachable!() };
      let Rule { body, .. } = rules.first_mut().unwrap();
      core::mem::swap(body, term);
    }
    dep
  }
}

