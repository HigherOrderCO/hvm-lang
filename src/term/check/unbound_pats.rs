use crate::term::{Book, Name, Pattern, Term};
use std::collections::HashSet;

impl Book {
  /// Check if the constructors in rule patterns or match patterns are defined.
  pub fn check_unbound_pats(&self) -> Result<(), String> {
    let is_ctr = |nam: &Name| self.def_names.contains_name(nam);
    for def in self.defs.values() {
      let def_name = self.def_names.name(&def.def_id).unwrap();
      for rule in &def.rules {
        for pat in &rule.pats {
          pat.check_unbounds(&is_ctr, def_name)?;
        }
      }
    }
    Ok(())
  }
}

impl Pattern {
  pub fn check_unbounds(&self, is_ctr: &impl Fn(&Name) -> bool, def_name: &Name) -> Result<(), String> {
    let unbounds = self.unbound_pats(is_ctr);
    if let Some(unbound) = unbounds.iter().next() {
      Err(format!("Unbound constructor '{unbound}' in definition '{def_name}'"))
    } else {
      Ok(())
    }
  }

  /// Given a possibly nested rule pattern, return a set of all used but not declared constructors.
  pub fn unbound_pats(&self, is_ctr: &impl Fn(&Name) -> bool) -> HashSet<Name> {
    let mut unbounds = HashSet::new();
    let mut check = vec![self];
    while let Some(pat) = check.pop() {
      match pat {
        Pattern::Ctr { nam, args } => {
          if !is_ctr(nam) {
            unbounds.insert(nam.clone());
          }
          check.extend(args.iter());
        }
        _ => ()
      }
    }
    unbounds
  }
}

impl Term {
  pub fn check_unbound_pats(&self, is_ctr: &impl Fn(&Name) -> bool, def_name: &Name) -> Result<(), String> {
    match self {
      Term::Let { pat, val, nxt } => {
        pat.check_unbounds(is_ctr, def_name)?;
        val.check_unbound_pats(is_ctr, def_name)?;
        nxt.check_unbound_pats(is_ctr, def_name)?;
      }
      Term::Match { scrutinee, arms } => {
        scrutinee.check_unbound_pats(is_ctr, def_name)?;
        for (pat, body) in arms {
          pat.check_unbounds(is_ctr, def_name)?;
          body.check_unbound_pats(is_ctr, def_name)?;
        }
      }
      Term::App { fun: fst, arg: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { fst, snd, .. } => {
        fst.check_unbound_pats(is_ctr, def_name)?;
        snd.check_unbound_pats(is_ctr, def_name)?;
      }
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => bod.check_unbound_pats(is_ctr, def_name)?,
      Term::Var { .. }
      | Term::Lnk { .. }
      | Term::Ref { .. }
      | Term::Num { .. }
      | Term::Str { .. }
      | Term::Era => (),
    }
    Ok(())
  }
}
