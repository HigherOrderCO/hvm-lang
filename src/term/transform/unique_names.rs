// Pass to give all variables in a definition unique names.

use crate::term::{Book, Name, Pattern, Term};
use std::collections::HashMap;

impl Book {
  /// Makes all variables in each definition have a new unique name.
  /// Precondition: Definition references have been resolved, no unbound variables.
  pub fn make_var_names_unique(&mut self) {
    for def in self.defs.values_mut() {
      for rule in def.rules.iter_mut() {
        rule.body.make_var_names_unique()
      }
    }
  }
}

impl Term {
  pub fn make_var_names_unique(&mut self) {
    unique_var_names(self, &mut Default::default(), &mut 0);
  }
}

#[derive(Default)]
struct UniqueNameScope(HashMap<Name, Vec<u64>>);

// Recursive implementation of unique names pass.
fn unique_var_names(term: &mut Term, name_map: &mut UniqueNameScope, name_count: &mut u64) {
  match term {
    // Terms that create names
    Term::Lam { nam, bod, .. } => {
      // Put the name in scope and assign it a unique id.
      // Convert the lambda body and then remove it from scope.
      // Return a lambda with the newly created name
      name_map.push(nam.as_ref(), name_count);
      unique_var_names(bod, name_map, name_count);
      *nam = name_map.pop(nam.as_ref());
    }
    Term::Let { pat: Pattern::Var(nam), val, nxt } => {
      unique_var_names(val, name_map, name_count);

      name_map.push(nam.as_ref(), name_count);
      unique_var_names(nxt, name_map, name_count);
      *nam = name_map.pop(nam.as_ref());
    }
    Term::Dup { tag: _, fst, snd, val, nxt }
    | Term::Let { pat: Pattern::Tup(box Pattern::Var(fst), box Pattern::Var(snd)), val, nxt } => {
      unique_var_names(val, name_map, name_count);

      name_map.push(fst.as_ref(), name_count);
      name_map.push(snd.as_ref(), name_count);
      unique_var_names(nxt, name_map, name_count);
      *snd = name_map.pop(snd.as_ref());
      *fst = name_map.pop(fst.as_ref());
    }
    Term::Match { scrutinee, arms } => {
      unique_var_names(scrutinee, name_map, name_count);
      for (pat, term) in arms {
        pat.bound_names().for_each(|nam| name_map.push(Some(nam), name_count));
        unique_var_names(term, name_map, name_count);
        pat.bound_names_mut().rev().for_each(|nam| *nam = name_map.pop(Some(nam)).unwrap());
      }
    }

    // Terms that use names
    Term::Var { nam } => *nam = name_map.use_var(nam),

    // Others
    Term::App { fun: fst, arg: snd, .. }
    | Term::Sup { fst, snd, .. }
    | Term::Tup { fst, snd }
    | Term::Opx { fst, snd, .. } => {
      unique_var_names(fst, name_map, name_count);
      unique_var_names(snd, name_map, name_count);
    }
    // Global lam names are already unique, so no need to do anything
    Term::Chn { bod, .. } => unique_var_names(bod, name_map, name_count),
    Term::Lnk { .. } | Term::Ref { .. } | Term::Era | Term::Num { .. } | Term::Str { .. } => (),

    Term::Let { .. } => {
      unreachable!("Let terms other than tuple destruction should have been desugared already.")
    }
  }
}

impl UniqueNameScope {
  fn push(&mut self, nam: Option<&Name>, name_count: &mut u64) {
    if let Some(name) = nam {
      self.0.entry(name.clone()).or_default().push(*name_count);
      *name_count += 1;
    }
  }

  fn pop(&mut self, nam: Option<&Name>) -> Option<Name> {
    if let Some(name) = nam {
      let new_name = self.0.get_mut(name).unwrap().pop().unwrap();
      if self.0[name].is_empty() {
        self.0.remove(name);
      }
      Some(Name::from_num(new_name))
    } else {
      None
    }
  }

  fn use_var(&self, nam: &Name) -> Name {
    let vars = &self.0[nam];
    let var_id = *vars.last().unwrap();
    Name::from_num(var_id)
  }
}
