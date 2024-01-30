use crate::term::{Book, Name, Pattern, Term};

impl Book {
  /// Resolve Constructor names inside rule patterns and match patterns.
  /// When parsing a rule we don't have all the constructors yet,
  /// so no way to know if a particular name belongs to a constructor or is a matched variable.
  /// Therefore we must do it later, here.
  pub fn resolve_ctrs_in_pats(&mut self) {
    let is_ctr = |nam: &Name| self.ctrs.contains_key(nam);
    for def in self.defs.values_mut() {
      for rule in &mut def.rules {
        for pat in &mut rule.pats {
          pat.resolve_ctrs(&is_ctr);
        }
        rule.body.resolve_ctrs_in_pats(&is_ctr);
      }
    }
  }
}

impl Pattern {
  pub fn resolve_ctrs(&mut self, is_ctr: &impl Fn(&Name) -> bool) {
    match self {
      Pattern::Var { nam } => {
        if is_ctr(nam) {
          *self = Pattern::Ctr { nam: nam.clone(), args: vec![] }
        }
      }
      Pattern::Ctr { args, .. } => {
        for arg in args {
          arg.resolve_ctrs(is_ctr);
        }
      }
      Pattern::Era => (),
      Pattern::Num { .. } => (),
      Pattern::Lnk { .. } => (),
      Pattern::Tup { fst, snd } => {
        fst.resolve_ctrs(is_ctr);
        snd.resolve_ctrs(is_ctr);
      }
      Pattern::Sup { fst, snd, .. } => {
        fst.resolve_ctrs(is_ctr);
        snd.resolve_ctrs(is_ctr);
      }
      Pattern::Implicit => unreachable!(),
    }
  }
}

impl Term {
  pub fn resolve_ctrs_in_pats(&mut self, is_ctr: &impl Fn(&Name) -> bool) {
    match self {
      Term::Let { pat, val, nxt } => {
        pat.resolve_ctrs(is_ctr);
        val.resolve_ctrs_in_pats(is_ctr);
        nxt.resolve_ctrs_in_pats(is_ctr);
      }
      Term::Match { scrutinee, arms } => {
        scrutinee.resolve_ctrs_in_pats(is_ctr);
        for (pat, body) in arms {
          pat.resolve_ctrs(is_ctr);
          body.resolve_ctrs_in_pats(is_ctr);
        }
      }
      Term::App { fun: fst, arg: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { fst, snd, .. } => {
        fst.resolve_ctrs_in_pats(is_ctr);
        snd.resolve_ctrs_in_pats(is_ctr);
      }
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => bod.resolve_ctrs_in_pats(is_ctr),
      Term::Var { .. }
      | Term::Lnk { .. }
      | Term::Ref { .. }
      | Term::Num { .. }
      | Term::Str { .. }
      | Term::Era => (),
    }
  }
}
