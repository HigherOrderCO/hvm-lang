use std::collections::{BTreeMap, HashSet};

use crate::term::{Book, DefId, Definition, Term};

type Definitions = HashSet<DefId>;

impl Book {
  /// Removes all unused definitions starting from Main.
  pub fn prune(&mut self, main: &DefId) {
    let mut used = Definitions::new();

    let Definition { def_id, rules } = self.defs.get(main).unwrap();
    used.insert(def_id.clone());
    for rule in rules {
      rule.body.find_used_definitions(&mut used, &self.defs);
    }

    let ids = HashSet::from_iter(self.def_names.def_ids().cloned());
    let unused = ids.difference(&used);

    for unused_id in unused {
      self.remove_def(unused_id.clone());
    }
  }
}

impl Term {
  /// Finds all used definitions on every term that can have a def_id.
  fn find_used_definitions(&self, used: &mut Definitions, defs: &BTreeMap<DefId, Definition>) {
    let mut to_visit = vec![self];

    while let Some(term) = to_visit.pop() {
      match term {
        Term::Ref { def_id } => {
          if used.insert(def_id.clone()) {
            let Definition { rules, .. } = defs.get(def_id).unwrap();
            for rule in rules {
              to_visit.push(&rule.body);
            }
          }
        }
        Term::Lam { bod, .. } | Term::Chn { bod, .. } => bod.find_used_definitions(used, defs),
        Term::Let { val, nxt, .. } => {
          val.find_used_definitions(used, defs);
          nxt.find_used_definitions(used, defs);
        }
        Term::App { fun, arg, .. } => {
          fun.find_used_definitions(used, defs);
          arg.find_used_definitions(used, defs);
        }
        Term::Sup { fst, snd, .. } | Term::Tup { fst, snd } | Term::Opx { fst, snd, .. } => {
          fst.find_used_definitions(used, defs);
          snd.find_used_definitions(used, defs);
        }
        Term::Match { scrutinee, arms } => {
          scrutinee.find_used_definitions(used, defs);
          for (_, term) in arms {
            term.find_used_definitions(used, defs);
          }
        }
        Term::Var { .. } | Term::Lnk { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => (),
      }
    }
  }
}
