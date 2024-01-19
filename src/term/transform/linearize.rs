use crate::term::{Book, MatchNum, Name, Pattern, Tag, Term};
use std::collections::{hash_map::Entry, HashMap};

/// Erases variables that weren't used, dups the ones that were used more than once.
/// Substitutes lets into their variable use.
/// In details:
/// For all var declarations:
///   If they're used 0 times: erase the declaration
///   If they're used 1 time: leave them as-is
///   If they're used more times: insert dups to make var use affine
/// For all let vars:
///   If they're used 0 times: Discard the let
///   If they're used 1 time: substitute the body in the var use
///   If they're use more times: add dups for all the uses, put the let body at the root dup.
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
    let mut var_uses = HashMap::new();
    count_var_uses_in_term(self, &mut var_uses);
    term_to_affine(self, &mut var_uses, &mut HashMap::new());
  }
}

fn count_var_uses_in_term(term: &Term, uses: &mut HashMap<Name, u64>) {
  match term {
    // Var users
    Term::Var { nam } => {
      *uses.entry(nam.clone()).or_default() += 1;
    }
    // Var producers
    Term::Lam { nam, bod, .. } => {
      add_var(nam.as_ref(), uses);
      count_var_uses_in_term(bod, uses)
    }
    Term::Dup { fst, snd, val, nxt, .. }
    | Term::Let { pat: Pattern::Tup(box Pattern::Var(fst), box Pattern::Var(snd)), val, nxt } => {
      add_var(fst.as_ref(), uses);
      add_var(snd.as_ref(), uses);
      count_var_uses_in_term(val, uses);
      count_var_uses_in_term(nxt, uses);
    }
    Term::Let { pat: Pattern::Var(nam), val, nxt } => {
      add_var(nam.as_ref(), uses);
      count_var_uses_in_term(val, uses);
      count_var_uses_in_term(nxt, uses);
    }
    Term::Let { .. } => unreachable!(),
    // Others
    Term::Chn { bod, .. } => count_var_uses_in_term(bod, uses),
    Term::App { fun: fst, arg: snd, .. }
    | Term::Sup { fst, snd, .. }
    | Term::Tup { fst, snd }
    | Term::Opx { fst, snd, .. } => {
      count_var_uses_in_term(fst, uses);
      count_var_uses_in_term(snd, uses);
    }
    Term::Match { scrutinee, arms } => {
      count_var_uses_in_term(scrutinee, uses);
      for (rule, term) in arms {
        if let Pattern::Num(MatchNum::Succ(Some(nam))) = rule {
          add_var(nam.as_ref(), uses)
        }

        count_var_uses_in_term(term, uses);
      }
    }
    Term::Lnk { .. } | Term::Ref { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => (),
  }
}

/// We use a special named variable to only count the number of actual var uses on the resulting term
fn used_var_counter(var_name: &Name) -> Name {
  Name(format!("${var_name}$used"))
}

/// Var-declaring terms
fn term_with_bind_to_affine(
  term: &mut Term,
  nam: &mut Option<Name>,
  var_uses: &mut HashMap<Name, u64>,
  let_bodies: &mut HashMap<Name, Term>,
) {
  if let Some(nam_some) = nam {
    if let Some(mut uses) = var_uses.get(nam_some).copied() {
      term_to_affine(term, var_uses, let_bodies);

      // When a term is removed, the number of uses of a variable can change inside the term_to_affine call.
      // We check the updated count instead of using the one we caulculated initially
      if uses != 0 {
        let name = used_var_counter(nam_some);
        uses = var_uses.get(&name).copied().unwrap_or(0)
      };

      duplicate_lam(nam, term, uses);
      return;
    }
  }

  term_to_affine(term, var_uses, let_bodies);
}

fn term_to_affine(term: &mut Term, var_uses: &mut HashMap<Name, u64>, let_bodies: &mut HashMap<Name, Term>) {
  match term {
    Term::Lam { nam, bod, .. } => term_with_bind_to_affine(bod, nam, var_uses, let_bodies),

    Term::Let { pat: Pattern::Var(Some(nam)), val, nxt } => {
      let uses = var_uses[nam];
      match uses {
        0 => {
          // We are going to remove the val term,
          // so we need to remove the free variables it uses from the vars count
          for (var, used) in val.free_vars() {
            let Entry::Occupied(mut entry) = var_uses.entry(var) else { unreachable!() };

            if *entry.get() == 1 {
              entry.remove();
            } else {
              *entry.get_mut() -= used;
            }
          }

          term_to_affine(nxt, var_uses, let_bodies);
        }
        1 => {
          term_to_affine(val, var_uses, let_bodies);
          let_bodies.insert(nam.clone(), std::mem::take(val.as_mut()));
          term_to_affine(nxt, var_uses, let_bodies);
        }
        uses => {
          term_to_affine(val, var_uses, let_bodies);
          term_to_affine(nxt, var_uses, let_bodies);
          duplicate_let(nam, nxt, uses, val);
        }
      }
      *term = std::mem::take(nxt.as_mut());
    }

    Term::Let { pat: Pattern::Era, nxt, .. } => {
      *term = *nxt.clone();
    }

    Term::Dup { fst, snd, val, nxt, .. }
    | Term::Let { pat: Pattern::Tup(box Pattern::Var(fst), box Pattern::Var(snd)), val, nxt } => {
      let uses_fst = get_var_uses(fst.as_ref(), var_uses);
      let uses_snd = get_var_uses(snd.as_ref(), var_uses);
      term_to_affine(val, var_uses, let_bodies);
      term_to_affine(nxt, var_uses, let_bodies);
      duplicate_lam(fst, nxt, uses_fst);
      duplicate_lam(snd, nxt, uses_snd);
    }

    Term::Let { .. } => unreachable!(),

    // Var-using terms
    Term::Var { nam } => {
      let uses = var_uses[nam];
      *var_uses.get_mut(nam).unwrap() -= 1;
      if let Some(subst) = let_bodies.remove(nam) {
        *term = subst.clone();
      } else {
        let used_counter = used_var_counter(nam);

        *nam = dup_name(nam, uses);

        // Updates de actual var uses on the resulting term
        *var_uses.entry(used_counter).or_default() += 1;
      }
    }

    // Others
    Term::Chn { bod, .. } => term_to_affine(bod, var_uses, let_bodies),
    Term::App { fun: fst, arg: snd, .. }
    | Term::Sup { fst, snd, .. }
    | Term::Tup { fst, snd }
    | Term::Opx { fst, snd, .. } => {
      term_to_affine(fst, var_uses, let_bodies);
      term_to_affine(snd, var_uses, let_bodies);
    }
    Term::Match { scrutinee, arms } => {
      term_to_affine(scrutinee, var_uses, let_bodies);
      for (rule, term) in arms {
        match rule {
          Pattern::Num(MatchNum::Succ(Some(nam))) => {
            term_with_bind_to_affine(term, nam, var_uses, let_bodies)
          }
          Pattern::Num { .. } => term_to_affine(term, var_uses, let_bodies),
          _ => unreachable!(),
        }
      }
    }
    Term::Era | Term::Lnk { .. } | Term::Ref { .. } | Term::Num { .. } | Term::Str { .. } => (),
  };
}

fn get_var_uses(nam: Option<&Name>, var_uses: &HashMap<Name, u64>) -> u64 {
  if let Some(nam) = nam { *var_uses.get(nam).unwrap() } else { 0 }
}

fn make_dup_tree(nam: &Name, nxt: &mut Term, uses: u64, dup_body: Option<&mut Term>) {
  // TODO: Is there a difference between a list of dups and a complete binary tree of dups
  // Creates this: "dup x1 x1_dup = body; dup x2 x2_dup = x1_dup; dup x3 x4 = x2_dup; nxt"
  for i in (1 .. uses).rev() {
    let old_nxt = std::mem::replace(nxt, Term::Era);
    *nxt = Term::Dup {
      tag: Tag::Auto,
      fst: Some(dup_name(nam, i)),
      snd: if i == uses - 1 { Some(dup_name(nam, uses)) } else { Some(internal_dup_name(nam, uses)) },
      val: if i == 1 {
        if let Some(dup_body) = &dup_body {
          Box::new((*dup_body).clone()) // TODO: don't clone here
        } else {
          Box::new(Term::Var { nam: nam.clone() })
        }
      } else {
        Box::new(Term::Var { nam: internal_dup_name(nam, uses) })
      },
      nxt: Box::new(old_nxt),
    };
  }
}

fn duplicate_lam(nam: &mut Option<Name>, nxt: &mut Term, uses: u64) {
  match uses {
    0 => *nam = None,
    1 => *nam = Some(dup_name(nam.as_ref().unwrap(), 1)),
    uses => make_dup_tree(nam.as_ref().unwrap(), nxt, uses, None),
  }
}

fn duplicate_let(nam: &Name, nxt: &mut Term, uses: u64, let_body: &mut Term) {
  make_dup_tree(nam, nxt, uses, Some(let_body))
}

fn dup_name(nam: &Name, uses: u64) -> Name {
  Name(format!("{nam}_{uses}"))
}

fn internal_dup_name(nam: &Name, uses: u64) -> Name {
  Name(format!("{}_dup", dup_name(nam, uses)))
}

fn add_var(nam: Option<&Name>, uses: &mut HashMap<Name, u64>) {
  if let Some(nam) = nam {
    uses.entry(nam.clone()).or_insert(0);
  }
}
