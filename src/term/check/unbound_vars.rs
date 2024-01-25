use crate::term::{Book, MatchNum, Name, Pattern, Term};
use std::collections::HashMap;

impl Book {
  /// Checks that there are no unbound variables in all definitions.
  pub fn check_unbound_vars(&self) -> Result<(), String> {
    for def in self.defs.values() {
      // TODO: Enable when pattern matching is done
      // def.assert_no_pattern_matching_rules();
      def.rules[0].body.check_unbound_vars()?;
    }
    Ok(())
  }
}

impl Term {
  /// Checks that all variables are bound.
  /// Precondition: References have been resolved.
  pub fn check_unbound_vars(&self) -> Result<(), String> {
    let mut globals = HashMap::new();
    check_uses(self, &mut HashMap::new(), &mut globals)?;

    // Check global vars
    for (nam, (declared, used)) in globals.into_iter() {
      if used && !declared {
        return Err(format!("Unbound unscoped variable '${nam}'"));
      }
    }
    Ok(())
  }
}

/// Scope has the number of times a name was declared in the current scope
/// Globals has how many times a global var name was declared and used.
pub fn check_uses<'a>(
  term: &'a Term,
  scope: &mut HashMap<&'a Name, u64>,
  globals: &mut HashMap<&'a Name, (bool, bool)>,
) -> Result<(), String> {
  // TODO: Don't stop at the first error
  match term {
    Term::Lam { nam, bod, .. } => {
      if let Some(nam) = nam {
        push_scope(nam, scope)
      };
      check_uses(bod, scope, globals)?;
      if let Some(nam) = nam {
        pop_scope(nam, scope)
      };
    }
    Term::Var { nam } => {
      if !scope.contains_key(nam) {
        return Err(format!("Unbound variable '{nam}'"));
      }
    }
    Term::Chn { nam, bod, .. } => {
      globals.entry(nam).or_default().0 = true;
      check_uses(bod, scope, globals)?;
    }
    Term::Lnk { nam } => {
      globals.entry(nam).or_default().1 = true;
    }
    Term::Let { pat: Pattern::Var { nam }, val, nxt } => {
      check_uses(val, scope, globals)?;
      push_scope(nam, scope);
      check_uses(nxt, scope, globals)?;
      pop_scope(nam, scope);
    }
    Term::Let {
      pat: Pattern::Tup { fst: box Pattern::Var { nam: fst }, snd: box Pattern::Var { nam: snd } },
      val,
      nxt,
    } => {
      check_uses(val, scope, globals)?;
      push_scope(fst, scope);
      push_scope(snd, scope);
      check_uses(nxt, scope, globals)?;
      pop_scope(fst, scope);
      pop_scope(snd, scope);
    }
    Term::Dup { fst, snd, val, nxt, .. } => {
      check_uses(val, scope, globals)?;
      if let Some(fst) = fst {
        push_scope(fst, scope)
      };
      if let Some(snd) = snd {
        push_scope(snd, scope)
      };
      check_uses(nxt, scope, globals)?;
      if let Some(fst) = fst {
        pop_scope(fst, scope)
      };
      if let Some(snd) = snd {
        pop_scope(snd, scope)
      };
    }
    Term::Let { .. } => unreachable!(),
    Term::App { fun, arg, .. } => {
      check_uses(fun, scope, globals)?;
      check_uses(arg, scope, globals)?;
    }
    Term::Tup { fst, snd } | Term::Sup { fst, snd, .. } | Term::Opx { fst, snd, .. } => {
      check_uses(fst, scope, globals)?;
      check_uses(snd, scope, globals)?;
    }
    Term::Match { scrutinee, arms } => {
      check_uses(scrutinee, scope, globals)?;
      for (pat, term) in arms {
        for i in pat.bound_names() {
          push_scope(i, scope)
        }
        check_uses(term, scope, globals)?;
        for i in pat.bound_names().rev() {
          pop_scope(i, scope)
        }
      }
    }
    Term::Ref { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => (),
  }
  Ok(())
}

fn push_scope<'a>(nam: &'a Name, scope: &mut HashMap<&'a Name, u64>) {
  if let Some(n_declarations) = scope.get_mut(nam) {
    *n_declarations += 1;
  } else {
    scope.insert(nam, 1);
  }
}

fn pop_scope(nam: &Name, scope: &mut HashMap<&Name, u64>) {
  let n_declarations = scope.get_mut(nam).unwrap();
  *n_declarations -= 1;
  if *n_declarations == 0 {
    scope.remove(nam);
  }
}
