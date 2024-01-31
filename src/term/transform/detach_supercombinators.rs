use std::collections::{BTreeMap, HashSet};

use crate::term::{Book, DefId, DefNames, Definition, Name, Pattern, Rule, Term};

/// Replaces closed Terms (i.e. without free variables) with a Ref to the extracted term
/// Precondition: Vars must have been sanitized
impl Book {
  pub fn detach_supercombinators(&mut self) {
    let mut combinators = Combinators::new();

    for def in self.defs.values_mut() {
      for rule in def.rules.iter_mut() {
        rule.body.detach_combinators(&def.def_id, &mut self.def_names, &mut combinators);
      }
    }

    // Definitions are not inserted to the book as they are defined to appease the borrow checker.
    // Since we are mut borrowing the rules we can't borrow the book to insert at the same time.
    self.defs.append(&mut combinators)
  }
}

type Combinators = BTreeMap<DefId, Definition>;

struct TermInfo<'d> {
  // Number of times a Term has been detached from the current Term
  counter: u32,
  rule_id: DefId,
  def_names: &'d mut DefNames,
  needed_names: HashSet<Name>,
  combinators: &'d mut Combinators,
}

impl<'d> TermInfo<'d> {
  fn new(rule_id: DefId, def_names: &'d mut DefNames, combinators: &'d mut Combinators) -> Self {
    Self { counter: 0, rule_id, def_names, needed_names: HashSet::new(), combinators }
  }
  fn request_name(&mut self, name: &Name) {
    self.needed_names.insert(name.to_owned());
  }

  fn provide(&mut self, name: &Name) {
    self.needed_names.remove(name);
  }

  fn check(&self) -> bool {
    self.needed_names.is_empty()
  }

  fn replace_scope(&mut self, new_scope: HashSet<Name>) -> HashSet<Name> {
    std::mem::replace(&mut self.needed_names, new_scope)
  }

  fn merge_scope(&mut self, target: HashSet<Name>) {
    self.needed_names.extend(target);
  }

  fn detach_term(&mut self, term: &mut Term) {
    let name = self.def_names.name(&self.rule_id).unwrap();
    let comb_name = Name(format!("{name}$S{}", self.counter));
    self.counter += 1;

    let comb_id = self.def_names.insert(comb_name);

    let comb_var = Term::Ref { def_id: comb_id.clone() };
    let extracted_term = std::mem::replace(term, comb_var);

    let rules = vec![Rule { body: extracted_term, pats: Vec::new() }];
    let rule = Definition { def_id: comb_id.clone(), rules };
    self.combinators.insert(comb_id, rule);
  }
}

impl Term {
  pub fn detach_combinators(
    &mut self,
    rule_id: &DefId,
    def_names: &mut DefNames,
    combinators: &mut Combinators,
  ) {
    fn go(term: &mut Term, depth: usize, term_info: &mut TermInfo) -> bool {
      match term {
        Term::Lam { pat, bod, .. } => {
          let parent_scope = term_info.replace_scope(HashSet::new());

          let is_super = go(bod, depth + 1, term_info);

          for i in pat.bound_names() {
            term_info.provide(i)
          }

          if is_super && !term.is_id() && depth != 0 && term_info.check() {
            term_info.detach_term(term);
          }

          term_info.merge_scope(parent_scope);

          is_super
        }
        Term::Var { nam } => {
          term_info.request_name(nam);
          true
        }
        Term::Chn { nam: _, bod, .. } => {
          go(bod, depth + 1, term_info);
          false
        }
        Term::Lnk { .. } => false,
        Term::Let { pat: Pattern::Var { nam }, val, nxt } => {
          let val_is_super = go(val, depth + 1, term_info);
          let nxt_is_super = go(nxt, depth + 1, term_info);
          term_info.provide(nam);

          val_is_super && nxt_is_super
        }
        Term::Let {
          pat: Pattern::Tup { fst: box Pattern::Var { nam: fst }, snd: box Pattern::Var { nam: snd } },
          val,
          nxt,
        } => {
          let val_is_super = go(val, depth + 1, term_info);
          let nxt_is_supper = go(nxt, depth + 1, term_info);

          term_info.provide(fst);
          term_info.provide(snd);

          val_is_super && nxt_is_supper
        }
        Term::Let { pat, val, nxt } => {
          let val_is_super = go(val, depth + 1, term_info);
          let nxt_is_supper = go(nxt, depth + 1, term_info);

          for i in pat.bound_names() {
            term_info.provide(i);
          }

          val_is_super && nxt_is_supper
        }
        Term::Match { scrutinee, arms } => {
          let is_super = go(scrutinee, depth + 1, term_info);

          for (_pat, _term) in arms {
            return false; // TODO

            is_super &= go(term, depth + 1, term_info);
          }

          is_super
        }
        Term::App { fun: fst, arg: snd, .. }
        | Term::Sup { fst, snd, .. }
        | Term::Tup { fst, snd }
        | Term::Opx { fst, snd, .. } => {
          let fst_is_super = go(fst, depth + 1, term_info);
          let snd_is_super = go(snd, depth + 1, term_info);

          fst_is_super && snd_is_super
        }
        Term::Ref { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => true,
      }
    }

    go(self, 0, &mut TermInfo::new(rule_id.clone(), def_names, combinators));
  }

  // We don't want to detach id function, since that's not a net gain in performance or space
  fn is_id(&self) -> bool {
    match self {
      Term::Lam { pat: box Pattern::Var { nam: lam_nam }, bod: box Term::Var { nam: var_nam }, .. } => {
        lam_nam == var_nam
      }
      _ => false,
    }
  }
}
