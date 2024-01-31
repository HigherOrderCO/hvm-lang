use std::collections::BTreeMap;

use chumsky::container::Container;
use replace_with::replace_with_or_default;

use crate::term::{Book, Name, Pattern, Term};

impl Book {
  fn delinearize(&mut self) {
    for def in self.defs.values_mut() {
      for rule in &mut def.rules {
        rule.body.delinearize();
      }
    }
  }
}

impl Term {
  pub fn delinearize(&mut self) {
    let mut vars = BTreeMap::new();
    let mut rebinds = BTreeMap::new();
    self._delinearize_pass(&mut vars, &mut rebinds);
    // Plug in vars and rebinds
    for (k, v) in vars {
      let mut new_value = k.clone();
      while let Some(w) = rebinds.get(&new_value) {
        new_value = w.clone();
      }
      *v = new_value;
    }
  }
  fn _delinearize_pass<'t>(
    &'t mut self,
    vars: &mut BTreeMap<Name, &'t mut Name>,
    rebinds: &mut BTreeMap<Name, Name>,
  ) {
    match self {
      Term::Lnk { nam } => {
        vars.insert(nam.clone(), nam);
      }
      term @ Term::Let { .. } => {
        if let Term::Let {
          pat: Pattern::Sup { fst: box Pattern::Lnk { nam: fst }, snd: box Pattern::Lnk { nam: snd }, .. },
          val: box Term::Lnk { nam },
          nxt,
        } = term
        {
          rebinds.insert(fst.clone(), nam.clone());
          rebinds.insert(snd.clone(), nam.clone());
          replace_with_or_default(term, |term| {
            let Term::Let { nxt, .. } = term else { unreachable!() };
            *nxt
          });
          term._delinearize_pass(vars, rebinds);
        } else if let Term::Let {
          pat: Pattern::Lnk { nam: pat_nam },
          val: box Term::Lnk { nam: val_nam },
          nxt,
        } = term
        {
          rebinds.insert(pat_nam.clone(), val_nam.clone());
          replace_with_or_default(term, |term| {
            let Term::Let { nxt, .. } = term else { unreachable!() };
            *nxt
          });
          term._delinearize_pass(vars, rebinds);
        } else if let Term::Let { pat: Pattern::Era, val: _, nxt } = term {
          replace_with_or_default(term, |term| {
            let Term::Let { nxt, .. } = term else { unreachable!() };
            *nxt
          });
        } else {
          let Term::Let { pat, val, nxt } = term else { unreachable!() };
          val._delinearize_pass(vars, rebinds);
          nxt._delinearize_pass(vars, rebinds);
        }
      }
      Term::Lam { pat, bod, .. } => {
        bod._delinearize_pass(vars, rebinds);
      }

      Term::Sup { fst, snd, .. }
      | Term::Tup { fst, snd }
      | Term::Opx { fst, snd, .. }
      | Term::App { fun: fst, arg: snd, .. } => {
        fst._delinearize_pass(vars, rebinds);
        snd._delinearize_pass(vars, rebinds);
      }
      Term::Match { scrutinee, arms } => {
        scrutinee._delinearize_pass(vars, rebinds);
        for i in arms {
          i.1._delinearize_pass(vars, rebinds);
        }
      }
      Term::Ref { .. } | Term::Era | Term::Num { .. } | Term::Str { .. } => (),
      _ => unreachable!(),
    }
  }
}
