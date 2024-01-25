//! Pass that turns all variables into scopeless variables.

use indexmap::IndexMap;

use crate::term::{Term, Name, Pattern, Book, self};

#[derive(Default)]
pub struct Unscoper<'t> {
  scope: IndexMap<Name, Vec<Vec<&'t mut Name>>>,
  saved_depths: Vec<IndexMap<Name, usize>>,
}

impl Book {
  pub fn unscope_vars(&mut self) {
    for def in self.defs.values_mut() {
      for rule in def.rules.iter_mut() {
        let mut u = Unscoper::default();
        u.unscope_term(&mut rule.body);
      }
    }
  }
}

impl<'t> Unscoper<'t> {
  fn name_for(&self, name: &Name) -> Name {
    Name(format!("{}_{}", name.0, self.scope.get(name).map(|x| x.len() + 1).unwrap_or(0)))
  }
  fn push_scope(&mut self, name: &'t mut Name) {
    self.scope.entry(name.clone()).or_default().push(vec![name]);
  }
  fn push_var(&mut self, name: &'t mut Name) {
    self.scope.entry(name.clone()).or_default().last_mut().unwrap().push(name);
  }
  fn pop_scope(&mut self, name: &Name) {
    let new_name = self.name_for(name);
    let v = self.scope.entry(name.clone()).or_default().pop().unwrap();
    for i in v {
      *i = new_name.clone();
    }
  }
  fn pop_scope_until_len(&mut self, name: &Name, desired_len: usize) {
    for _ in 0..(self.scope.entry(name.clone()).or_default().len() - desired_len) {
      self.pop_scope(name)
    }
  }
  fn push_depths(&mut self) {
    self.saved_depths.push(self.scope.iter().map(|(k, v)| (k.clone(), v.len())).collect())
  }
  fn pop_depths(&mut self) {
    for (name, len) in self.saved_depths.pop().unwrap_or_default().into_iter() {
      self.pop_scope_until_len(&name, len)
    }
  }
  fn unscope_term(&mut self, term: &'t mut Term) {
    match term {
        term @ Term::Var { .. } => { 
          let Term::Var { nam } = term.clone() else { unreachable!() };
          *term = Term::Lnk { nam: nam.clone() };
          let Term::Lnk { nam } = term  else { unreachable!() };
          self.push_var(nam)
        },
        term @ Term::Lam { .. } => {
          replace_with::replace_with_or_default(term, |term| {
            let Term::Lam { tag, nam, bod } = term else { unreachable!() };
            Term::Chn { tag, nam: nam.unwrap(), bod }
          });
          let Term::Chn { nam, tag, bod } = term  else { unreachable!() };
          self.push_scope(nam);
          self.unscope_term(bod);
        },
        Term::Dup { tag, fst, snd, val, nxt } => {
          *fst = fst.as_mut().map(|x| self.name_for(x));
          *snd = snd.as_mut().map(|x| self.name_for(x));
          self.unscope_term(val);
          self.unscope_term(nxt);
        },

        Term::Sup { tag, fst, snd } => {
          self.unscope_term(fst);
          self.unscope_term(snd);
        },
        Term::App { tag, fun, arg } => {
          self.unscope_term(fun);
          self.unscope_term(arg);
        },
        Term::Let { pat, val, nxt } => {
          self.push_depths();
          self.unscope_term(val);
          self.unscope_pat(pat);
          self.unscope_term(nxt);
          self.pop_depths();
        },
        Term::Tup { fst, snd } => {
          self.unscope_term(fst);
          self.unscope_term(snd);
        },
        Term::Opx { op, fst, snd } => {
          self.unscope_term(fst);
          self.unscope_term(snd);
        },
        Term::Match { scrutinee, arms } => {
          for i in arms.iter_mut() {
            self.push_depths(); 
            self.unscope_pat(&mut i.0);
            self.unscope_term(&mut i.1);
            self.pop_depths();
          }
        },
        Term::Chn { .. } | Term::Lnk { .. } | Term::Era | Term::Ref { .. } | Term::Str { .. } | Term::Num { .. } => (),
    }
  }
  fn unscope_pat(&mut self, pat: &'t mut Pattern) {
    match pat {
        pat @ Pattern::Var { .. } => {
          let Pattern::Var { nam } = pat.clone() else { unreachable!() };
          *pat = Pattern::Lnk { nam: nam.clone() };
          let Pattern::Lnk { nam } = pat  else { unreachable!() };
          self.push_scope(nam)
        },
        Pattern::Ctr { nam, args } => todo!(),
        Pattern::Num { mat } => {
          match mat {
            term::MatchNum::Zero => (),
            term::MatchNum::Succ(p) => {
              self.unscope_pat(p)
            },
          }
        },
        Pattern::Sup { tag, fst, snd } => {
          self.unscope_pat(fst);
          self.unscope_pat(snd);
        },
        Pattern::Tup { fst, snd } => {
          self.unscope_pat(fst);
          self.unscope_pat(snd);
        },
        Pattern::Implicit => (),
        Pattern::Era => (),
        Pattern::Lnk { nam } => (),
    }
  }
}