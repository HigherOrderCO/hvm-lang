use crate::term::{Adt, Book, MatchNum, Name, Pattern, Term};
use std::collections::{BTreeMap, HashMap};

impl Book {
  pub fn desugar_implicit_match_binds(&mut self) {
    for def in self.defs.values_mut() {
      for rule in &mut def.rules {
        rule.body.desugar_implicit_match_binds(&self.ctrs, &self.adts);
      }
    }
  }
}

impl Term {
  pub fn desugar_implicit_match_binds(&mut self, ctrs: &HashMap<Name, Name>, adts: &BTreeMap<Name, Adt>) {
    match self {
      Term::Match { scrutinee, .. } => {
        let scrutinee = match scrutinee.as_ref() {
          Term::Var { nam } => nam.clone(),
          _ => {
            let nam = Name::new("%temp%scrutinee");

            let Term::Match { scrutinee, arms } = std::mem::take(self) else { unreachable!() };

            *self = Term::Let {
              pat: Pattern::Var { nam: nam.clone() },
              val: scrutinee,
              nxt: Box::new(Term::Match { scrutinee: Box::new(Term::Var { nam: nam.clone() }), arms }),
            };

            nam
          }
        };

        let arms = match self {
          Term::Match { arms, .. } | Term::Let { nxt: box Term::Match { arms, .. }, .. } => arms,
          _ => unreachable!(),
        };

        for (pat, body) in arms {
          match pat {
            Pattern::Var { .. } => (),
            Pattern::Lnk { .. } => (),
            Pattern::Ctr { nam, args: pat_args } => {
              let adt = &ctrs[nam];
              let Adt { ctrs } = &adts[adt];
              let ctr_args = &ctrs[nam.as_ref()];
              if pat_args.is_empty() && !ctr_args.is_empty() {
                // Implicit ctr args
                *pat_args =
                  ctr_args.iter().map(|x| Pattern::Var { nam: Name(format!("{scrutinee}.{x}")) }).collect();
              }
            }
            Pattern::Num { .. } => (), // TODO
            Pattern::Tup { .. } => (),
            Pattern::Sup { .. } => (),
            Pattern::Implicit => (),
            Pattern::Era => (),
          }
          body.desugar_implicit_match_binds(ctrs, adts);
        }
      }
      Term::Let { pat: Pattern::Var { .. }, val: fst, nxt: snd }
      | Term::App { fun: fst, arg: snd, .. }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { fst, snd, .. } => {
        fst.desugar_implicit_match_binds(ctrs, adts);
        snd.desugar_implicit_match_binds(ctrs, adts);
      }
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => {
        bod.desugar_implicit_match_binds(ctrs, adts);
      }
      Term::Era
      | Term::Ref { .. }
      | Term::Num { .. }
      | Term::Str { .. }
      | Term::Lnk { .. }
      | Term::Var { .. } => (),
      Term::Let { pat: _, .. } => {
        unreachable!("Expected destructor let expressions to have been desugared already")
      }
    }
  }
}
