// Pass for inlining functions that are just a reference to another one.

use crate::term::{Book, DefId, Term};
use std::collections::HashMap;

impl Book {
  // When we find a function that is simply directly calling another function,
  // substitutes all occurences of that function to the one being called, avoiding the unnecessary redirect.
  // In case there is a long chaing of ref-to-ref-to-ref, we substitute values by the last function in the chain.
  pub fn simplify_ref_to_ref(&mut self) -> Result<(), String> {
    let mut ref_map: HashMap<DefId, DefId> = HashMap::new();
    // Find to which defs we're mapping the ones that are just references.
    for def_id in self.def_names.def_ids() {
      //self.defs[def_id].assert_no_pattern_matching_rules();
      let mut ref_id = def_id;
      let mut is_ref_to_ref = false;
      while let Term::Ref { def_id: next_ref_id } = &self.defs.get(ref_id).unwrap().rules[0].body {
        if next_ref_id == def_id {
          return Err(format!(
            "Definition {} is a reference to itself",
            self.def_names.name(def_id).unwrap()
          ));
        }
        ref_id = next_ref_id;
        is_ref_to_ref = true;
      }
      if is_ref_to_ref {
        ref_map.insert(def_id.clone(), ref_id.clone());
      }
    }

    // Substitute all the occurences of ref-to-ref.
    for def_id in self.defs.keys().cloned().collect::<Vec<_>>() {
      let body = &mut self.defs.get_mut(&def_id).unwrap().rules[0].body;
      // Moving in and out so the borrow checker doesn't complain
      let mut subst_body = std::mem::take(body);
      subst_ref_to_ref(&mut subst_body, &ref_map);
      let body = &mut self.defs.get_mut(&def_id).unwrap().rules[0].body;
      *body = subst_body;
    }

    Ok(())
  }
}

fn subst_ref_to_ref(term: &mut Term, ref_map: &HashMap<DefId, DefId>) {
  match term {
    Term::Ref { def_id } => {
      if let Some(target_id) = ref_map.get(def_id) {
        *def_id = target_id.clone();
      }
    }
    Term::Lam { bod, .. } | Term::Chn { bod, .. } => subst_ref_to_ref(bod, ref_map),
    Term::App { fun: fst, arg: snd, .. }
    | Term::Let { val: fst, nxt: snd, .. }
    | Term::Sup { fst, snd, .. }
    | Term::Tup { fst, snd }
    | Term::Opx { fst, snd, .. } => {
      subst_ref_to_ref(fst, ref_map);
      subst_ref_to_ref(snd, ref_map);
    }
    Term::Match { scrutinee, arms } => {
      subst_ref_to_ref(scrutinee, ref_map);
      for (_, term) in arms {
        subst_ref_to_ref(term, ref_map);
      }
    }
    Term::Var { .. } | Term::Lnk { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => (),
  }
}
