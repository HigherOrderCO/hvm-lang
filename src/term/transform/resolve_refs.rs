use std::collections::HashMap;

use crate::term::{Book, DefNames, Name, Term};

impl Book {
  /// Decides if names inside a term belong to a Var or to a Ref.
  /// Precondition: Refs are encoded as vars.
  /// Postcondition: Refs are encoded as refs, with the correct def id.
  pub fn resolve_refs(&mut self) {
    for def in self.defs.values_mut() {
      for rule in def.rules.iter_mut() {
        rule.body.resolve_refs(&self.def_names);
      }
    }
  }
}

impl Term {
  pub fn resolve_refs(&mut self, def_names: &DefNames) {
    resolve_refs(self, def_names, &mut HashMap::new())
  }
}

fn resolve_refs(term: &mut Term, def_names: &DefNames, scope: &mut HashMap<Name, usize>) {
  match term {
    Term::Lam { pat, bod, .. } => {
      for nam in pat.bound_names() {
        push_scope(nam.clone(), scope)
      }

      resolve_refs(bod, def_names, scope);

      for nam in pat.bound_names() {
        pop_scope(nam.clone(), scope)
      }
    }
    Term::Let { pat, val, nxt } => {
      resolve_refs(val, def_names, scope);

      for nam in pat.bound_names() {
        push_scope(nam.clone(), scope)
      }

      resolve_refs(nxt, def_names, scope);

      for nam in pat.bound_names() {
        pop_scope(nam.clone(), scope)
      }
    }

    // If variable not defined, we check if it's a ref and swap if it is.
    Term::Var { nam } => {
      if is_var_in_scope(nam.clone(), scope) {
        if let Some(def_id) = def_names.def_id(nam) {
          *term = Term::Ref { def_id };
        }
      }
    }
    Term::Chn { bod, .. } => resolve_refs(bod, def_names, scope),
    Term::App { fun: fst, arg: snd, .. }
    | Term::Sup { fst, snd, .. }
    | Term::Tup { fst, snd }
    | Term::Opx { fst, snd, .. } => {
      resolve_refs(fst, def_names, scope);
      resolve_refs(snd, def_names, scope);
    }
    Term::Match { scrutinee, arms } => {
      resolve_refs(scrutinee, def_names, scope);
      for (pat, term) in arms {
        for i in pat.bound_names() {
          push_scope(i.clone(), scope)
        }
        resolve_refs(term, def_names, scope);
        for i in pat.bound_names().rev() {
          pop_scope(i.clone(), scope)
        }
      }
    }
    Term::Lnk { .. } | Term::Ref { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => (),
  }
}

fn push_scope(name: Name, scope: &mut HashMap<Name, usize>) {
  let var_scope = scope.entry(name.clone()).or_default();
  *var_scope += 1;
}

fn pop_scope(name: Name, scope: &mut HashMap<Name, usize>) {
  let var_scope = scope.entry(name.clone()).or_default();
  *var_scope -= 1;
}

fn is_var_in_scope(name: Name, scope: &mut HashMap<Name, usize>) -> bool {
  *scope.entry(name.clone()).or_default() == 0
}
