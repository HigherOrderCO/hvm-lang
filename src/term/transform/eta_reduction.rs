use crate::term::*;

impl Book {
  /// Applies eta-reduction to all definitions, converting occurences of `@x (f x)` into just `f`.
  /// Assumes that variables are linear (used exactly once).
  pub fn eta_reduction(&mut self) {
    for def in self.defs.values_mut() {
      for rule in def.rules.iter_mut() {
        rule.body.eta_reduction();
      }
    }
  }
}

impl Term {
  /// Eta-reduces a term and any subterms.
  /// Expects variables to be linear.
  pub fn eta_reduction(&mut self) {
    match self {
      Term::Lam { tag: lam_tag, pat, bod } => {
        bod.eta_reduction();
        let pat_term: Term = pat.as_ref().into();
        match bod.as_mut() {
          Term::App { tag: arg_tag, fun, arg } if arg.as_ref() == &pat_term && lam_tag == arg_tag => {
            *self = std::mem::take(fun.as_mut());
          }
          _ => (),
        }
      }
      Term::Let { pat: _, val, nxt } => {
        val.eta_reduction();
        nxt.eta_reduction();
      }
      Term::App { fun: fst, arg: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { op: _, fst, snd } => {
        fst.eta_reduction();
        snd.eta_reduction();
      }
      Term::Match { scrutinee, arms } => {
        scrutinee.eta_reduction();
        for (_pat, term) in arms {
          term.eta_reduction();
        }
      }
      Term::Chn { bod, .. } => {
        bod.eta_reduction();
      }
      Term::Lnk { .. }
      | Term::Var { .. }
      | Term::Num { .. }
      | Term::Str { .. }
      | Term::Ref { .. }
      | Term::Era => {}
    }
  }
}
