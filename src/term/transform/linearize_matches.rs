use crate::term::{Book, Name, NumCtr, Term};
use std::collections::{BTreeMap, BTreeSet};

impl Book {
  /// Linearizes the variables between match cases, transforming them into combinators when possible.
  pub fn linearize_matches(&mut self, lift_all_vars: bool) {
    for def in self.defs.values_mut() {
      for rule in def.rules.iter_mut() {
        rule.body.linearize_matches(lift_all_vars);
      }
    }
  }
}

impl Term {
  fn linearize_matches(&mut self, lift_all_vars: bool) {
    Term::recursive_call(move || {
      for child in self.children_mut() {
        child.linearize_matches(lift_all_vars);
      }

      if matches!(self, Term::Mat { .. } | Term::Swt { .. }) {
        lift_match_vars(self, lift_all_vars);
      }
    })
  }
}

/// Converts free vars inside the match arms into lambdas with applications to give them the external value.
/// Makes the rules extractable and linear (no need for dups when variable used in both rules)
///
/// If `lift_all_vars`, acts on all variables found in the arms,
/// Otherwise, only lift vars that are used on more than one arm.
///
/// Obs: This does not modify unscoped variables
pub fn lift_match_vars(match_term: &mut Term, lift_all_vars: bool) -> &mut Term {
  // Collect match arms with binds
  let arms: Vec<_> = match match_term {
    Term::Mat { arg: _, rules } => {
      rules.iter().map(|(_, binds, body)| (binds.iter().flatten().cloned().collect(), body)).collect()
    }
    Term::Swt { arg: _, rules } => rules
      .iter()
      .map(|(ctr, body)| match ctr {
        NumCtr::Num(_) => (vec![], body),
        NumCtr::Succ(None) => (vec![], body),
        NumCtr::Succ(Some(var)) => (vec![var.clone()], body),
      })
      .collect(),
    _ => unreachable!(),
  };

  // Collect all free vars in the match arms
  let mut free_vars = Vec::<Vec<_>>::new();
  for (binds, body) in arms {
    let mut arm_free_vars = body.free_vars();
    for bind in binds {
      arm_free_vars.remove(&bind);
    }
    free_vars.push(arm_free_vars.into_keys().collect());
  }

  // Collect the vars to lift
  // We need consistent iteration order.
  let vars_to_lift: BTreeSet<Name> = if lift_all_vars {
    free_vars.into_iter().flatten().collect()
  } else {
    // If not lifting all vars, lift only those that are used in more than one arm.
    let mut vars_to_lift = BTreeMap::<Name, u64>::new();
    for free_vars in free_vars {
      for free_var in free_vars {
        *vars_to_lift.entry(free_var).or_default() += 1;
      }
    }
    vars_to_lift
      .into_iter()
      .filter_map(|(var, arm_count)| if arm_count >= 2 { Some(var) } else { None })
      .collect()
  };

  // Add lambdas to the arms
  match match_term {
    Term::Mat { arg: _, rules } => {
      for rule in rules {
        let old_body = std::mem::take(&mut rule.2);
        rule.2 = vars_to_lift.iter().cloned().rfold(old_body, |body, nam| Term::named_lam(nam, body));
      }
    }
    Term::Swt { arg: _, rules } => {
      for rule in rules {
        let old_body = std::mem::take(&mut rule.1);
        rule.1 = vars_to_lift.iter().cloned().rfold(old_body, |body, nam| Term::named_lam(nam, body));
      }
    }
    _ => unreachable!(),
  }

  // Add apps to the match
  *match_term = vars_to_lift.into_iter().fold(std::mem::take(match_term), Term::arg_call);

  get_match_reference(match_term)
}

/// Get a reference to the match again
/// It returns a reference and not an owned value because we want
/// to keep the new surrounding Apps but still modify the match further.
fn get_match_reference(mut match_term: &mut Term) -> &mut Term {
  loop {
    match match_term {
      Term::App { tag: _, fun, arg: _ } => match_term = fun.as_mut(),
      Term::Swt { .. } | Term::Mat { .. } => return match_term,
      _ => unreachable!(),
    }
  }
}
