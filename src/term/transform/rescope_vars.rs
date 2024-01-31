use std::collections::{BTreeMap, BTreeSet};

use chumsky::container::Container;

use crate::term::{Name, Pattern, Term};

impl Term {
  pub fn rescope(&mut self) {
    #[derive(Default)]
    struct Rescoper<'t> {
      scope: Vec<Name>,
      scope_stack: Vec<usize>,
      unscoped: BTreeSet<Name>,
      bound: BTreeMap<Name, Vec<&'t mut Term>>,
      bound_pats: BTreeMap<Name, &'t mut Pattern>,
    }
    impl<'t> Rescoper<'t> {
      fn push_scope(&mut self) {
        self.scope_stack.push(self.scope.len());
      }
      fn pop_scope(&mut self) {
        self.scope.shrink_to(self.scope_stack.pop().unwrap())
      }
      fn rescope_pat(&mut self, pat: &'t mut Pattern) {
        match pat {
          pat @ Pattern::Lnk { .. } => {
            let nam = if let Pattern::Lnk { nam } = pat { nam.clone() } else { unreachable!() };
            self.scope.push(nam.clone());
            self.bound_pats.insert(nam, pat).ok_or(()).unwrap_err()
          }
          Pattern::Num { mat } => match mat {
            crate::term::MatchNum::Zero => (),
            crate::term::MatchNum::Succ(p) => {
              self.rescope_pat(p);
            }
          },
          Pattern::Tup { fst, snd } => {
            self.rescope_pat(fst);
            self.rescope_pat(snd);
          }
          Pattern::Sup { tag, fst, snd } => {
            self.rescope_pat(fst);
            self.rescope_pat(snd);
          }
          Pattern::Ctr { nam, args } => unreachable!(),
          Pattern::Var { .. } | Pattern::Era | Pattern::Implicit => (),
        }
      }
      fn rescope_term(&mut self, term: &'t mut Term) {
        match term {
          term @ Term::Lnk { .. } => {
            let nam = if let Term::Lnk { nam } = term { nam.clone() } else { unreachable!() };
            if !self.scope.contains(&nam) {
              self.unscoped.push(nam.clone())
            }
            self.bound.entry(nam).or_default().push(term);
          }
          Term::Let { pat, val, nxt } => {
            self.rescope_term(val);
            self.push_scope();
            self.rescope_pat(pat);
            self.rescope_term(nxt);
            self.pop_scope();
          }
          Term::Var { nam } => todo!(),
          Term::Lam { tag, pat, bod } => {
            self.push_scope();
            self.rescope_pat(pat);
            self.rescope_term(bod);
            self.pop_scope();
          }
          Term::Tup { fst, snd }
          | Term::Sup { fst, snd, .. }
          | Term::App { fun: fst, arg: snd, .. }
          | Term::Opx { fst, snd, .. } => {
            self.rescope_term(fst);
            self.rescope_term(snd);
          }
          Term::Match { scrutinee, arms } => {
            self.rescope_term(scrutinee);
            for i in arms {
              self.push_scope();
              self.rescope_pat(&mut i.0);
              self.rescope_term(&mut i.1);
              self.pop_scope();
            }
          }
          Term::Num { .. } | Term::Str { .. } | Term::Ref { .. } | Term::Era => (),
          _ => todo!(),
        }
      }
      fn finish(mut self) {
        for name in self.unscoped {
          self.bound.remove(&name);
          self.bound_pats.remove(&name);
        }
        for (k, v) in self.bound.into_iter() {
          for i in v {
            *i = Term::Var { nam: k.clone() }
          }
        }
        for (k, v) in self.bound_pats {
          *v = Pattern::Var { nam: k }
        }
      }
    }
    {
      let mut rescoper = Rescoper::default();
      rescoper.rescope_term(self);
      rescoper.finish();
    }
  }
}
