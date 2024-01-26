use indexmap::IndexMap;
use replace_with::replace_with_or_default;

use crate::term::{Book, MatchNum, Name, Pattern, Tag, Term};
use std::collections::HashMap;

/// Erases variables that weren't used, dups the ones that were used more than once.
/// Precondition: All variables are bound and have unique names within each definition.
impl Book {
  pub fn linearize_vars(&mut self) {
    for def in self.defs.values_mut() {
      for rule in def.rules.iter_mut() {
        rule.body.linearize_vars();
      }
    }
  }
}

impl Term {
  pub fn linearize_vars(&mut self) {
    let mut linearizer = Linearizer::default();
    linearizer.linearize_term(self);
    linearizer.close_into(self);
  }
}

#[derive(Default)]
pub struct VarData {
  users: Vec<Name>,
  binders: Vec<Name>,
}

#[derive(Default)]
pub struct Linearizer {
  pub vars: IndexMap<Name, VarData>,
}

impl Linearizer {
  pub fn new_var(&mut self, var: Name) -> &mut VarData {
    self.vars.entry(var).or_default()
  }
  pub fn var_name(var: &Name, index: &usize, bind: bool) -> Name {
    Name(if bind { format!("{}$bind${}", var, index) } else { format!("{}$use${}", var, index) })
  }
  pub fn inner_var_name(var: &Name, index: &usize, bind: bool) -> Name {
    Name(if bind { format!("{}$inner_bind${}", var, index) } else { format!("{}$inner_use${}", var, index) })
  }
  pub fn new_bind(&mut self, var: Name) -> Name {
    let entry = self.new_var(var.clone());
    let nam = Self::var_name(&var, &entry.binders.len(), true);
    entry.binders.push(nam.clone());
    nam
  }
  pub fn new_usage(&mut self, var: Name) -> Name {
    let entry = self.new_var(var.clone());
    let nam = Self::var_name(&var, &entry.users.len(), false);
    entry.users.push(nam.clone());
    nam
  }
  pub fn linearize_pat(&mut self, pat: &mut Pattern) {
    match pat {
      Pattern::Lnk { nam } => {
        replace_with_or_default(nam, |x| self.new_bind(x));
      }
      Pattern::Num { mat } => match mat {
        MatchNum::Zero => (),
        MatchNum::Succ(pat) => self.linearize_pat(pat),
      },
      Pattern::Tup { fst, snd } => {
        self.linearize_pat(fst);
        self.linearize_pat(snd);
      }
      Pattern::Sup { fst, snd, .. } => {
        self.linearize_pat(fst);
        self.linearize_pat(snd);
      }
      Pattern::Era => (),
      _ => unreachable!("Found undesugared pattern: {:?}", pat),
    }
  }
  pub fn linearize_term(&mut self, term: &mut Term) {
    match term {
      Term::Chn { nam, bod, .. } => {
        replace_with_or_default(nam, |x| self.new_bind(x));
        self.linearize_term(bod)
      }
      Term::Lnk { nam } => {
        replace_with_or_default(nam, |x| self.new_usage(x));
      }
      Term::Ref { .. } | Term::Era | Term::Num { .. } => (),
      Term::Sup { tag, fst, snd } => {
        self.linearize_term(fst);
        self.linearize_term(snd);
      }
      Term::App { tag, fun, arg } => {
        self.linearize_term(fun);
        self.linearize_term(arg);
      }
      Term::Let { pat, val, nxt } => {
        self.linearize_term(val);
        self.linearize_term(nxt);
      }
      Term::Tup { fst, snd } => {
        self.linearize_term(fst);
        self.linearize_term(snd);
      }
      Term::Opx { op, fst, snd } => {
        self.linearize_term(fst);
        self.linearize_term(snd);
      }
      Term::Match { scrutinee, arms } => {
        self.linearize_term(scrutinee);
        for i in arms {
          self.linearize_pat(&mut i.0);
          self.linearize_term(&mut i.1);
        }
      }
      _ => unreachable!("Found undesugared term: {:?}", term),
    }
  }

  /// This function creates a tree of duplications from root name `root` and a set of names `names`
  pub fn create_dup_tree(&mut self, mut term: Term, root: Name, names: Vec<Name>, binder: bool) -> Term {
    let mut tail_name = root.clone();
    let mut i = names.into_iter().enumerate().peekable();
    if i.peek().is_some() {
      while let Some((idx, user)) = i.next() {
        let in_wire = Self::inner_var_name(&root, &idx, binder);
        let out_wire = Self::inner_var_name(&root, &(idx + 1), binder);
        if i.peek().is_some() {
          term = Term::Let {
            pat: if binder {
              Pattern::Lnk { nam: tail_name.clone() }
            } else {
              Pattern::Sup {
                tag: Tag::Auto,
                fst: Box::new(Pattern::Lnk { nam: user.clone() }),
                snd: Box::new(Pattern::Lnk { nam: out_wire.clone() }),
              }
            },
            val: Box::new(if binder {
              Term::Sup {
                tag: Tag::Auto,
                fst: Box::new(Term::Lnk { nam: user.clone() }),
                snd: Box::new(Term::Lnk { nam: out_wire.clone() }),
              }
            } else {
              Term::Lnk { nam: tail_name }
            }),
            nxt: Box::new(term),
          };
        } else {
          term = Term::Let {
            pat: Pattern::Lnk { nam: if binder { tail_name.clone() } else { user.clone() } },
            val: Box::new(Term::Lnk { nam: if binder { user.clone() } else { tail_name.clone() } }),
            nxt: Box::new(term),
          };
        };
        tail_name = out_wire;
      }
    } else {
      term = Term::Let {
        pat: if binder { Pattern::Era } else { Pattern::Lnk { nam: tail_name.clone() } },
        val: Box::new(if binder { Term::Lnk { nam: tail_name } } else { Term::Era }),
        nxt: Box::new(term),
      }
    }
    return term;
  }

  pub fn close_into(&mut self, term: &mut Term) {
    replace_with::replace_with_or_default(term, |mut term| {
      for (k, v) in core::mem::take(&mut self.vars).into_iter() {
        term = self.create_dup_tree(term, k.clone(), v.users, false);
        term = self.create_dup_tree(term, k, v.binders, true);
      }
      term
    })
  }
}
