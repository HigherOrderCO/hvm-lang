use crate::term::{Book, Name, Pattern, Term};

impl Book {
  /// Convert let destructor expressions like `let (a, b) = X` into the equivalent match expression.
  pub fn desugar_let_destructors(&mut self) {
    for def in self.defs.values_mut() {
      for rule in &mut def.rules {
        rule.body.desugar_let_destructors();
      }
    }
  }
}

impl Term {
  pub fn desugar_let_destructors(&mut self) {
    match self {
      Term::Let { pat: Pattern::Var { .. }, val: fst, nxt: snd }
      | Term::App { fun: fst, arg: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { fst, snd, .. } => {
        fst.desugar_let_destructors();
        snd.desugar_let_destructors();
      }
      Term::Match { scrutinee, arms } => {
        scrutinee.desugar_let_destructors();
        for (_, arm) in arms {
          arm.desugar_let_destructors();
        }
      }
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => {
        bod.desugar_let_destructors();
      }
      Term::Num { .. }
      | Term::Str { .. }
      | Term::Var { .. }
      | Term::Lnk { .. }
      | Term::Ref { .. }
      | Term::Era => (),

      Term::Let { .. } => {
        let Term::Let { pat, mut val, mut nxt } = std::mem::take(self) else { unreachable!() };

        val.desugar_let_destructors();
        nxt.desugar_let_destructors();

        let arms = vec![(pat, *nxt)];

        *self = match val.as_ref() {
          Term::Var { .. } => Term::Match { scrutinee: val, arms },
          _ => {
            let nam = Name::new("%temp%scrutinee");
            let pat = Pattern::Var(Some(nam.clone()));
            let scrutinee = Box::new(Term::Var { nam });
            Term::Let { pat, val, nxt: Box::new(Term::Match { scrutinee, arms }) }
          }
        };
      }
    }
  }
}
