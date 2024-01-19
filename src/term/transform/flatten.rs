use crate::term::{Book, DefId, DefNames, Definition, Name, Pattern, Rule, Term};
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

impl Book {
  pub fn flatten_rules(&mut self) {
    for def_id in self.defs.keys().cloned().collect_vec() {
      let new_defs = flatten_def(&self.defs[&def_id], &mut self.def_names);
      for def in new_defs {
        self.defs.insert(def.def_id.clone(), def.clone());
      }
    }
  }
}

fn flatten_def(def: &Definition, def_names: &mut DefNames) -> Vec<Definition> {
  // Groups rules by function name
  let def_name = def_names.name(&def.def_id).unwrap().clone();

  // For each group, split its internal rules
  let rules = def.rules.iter().map(|r| (def_name.clone(), r.clone())).collect_vec();
  let new_rules = split_group(&rules, def_names);
  new_rules
    .into_iter()
    .map(|(name, rules)| {
      let def_id = def_names.def_id(&name).unwrap();
      Definition { def_id, rules }
    })
    .collect()
}

/// Checks true if every time that `a` matches, `b` will match too.
fn matches_together(a: &[Pattern], b: &[Pattern]) -> (bool, bool) {
  let mut matches_together = true;
  let mut same_shape = true;
  for (a, b) in a.iter().zip(b) {
    match (a, b) {
      (Pattern::Ctr(a_nam, a_args), Pattern::Ctr(b_nam, b_args)) => {
        if a_nam != b_nam || a_args.len() != b_args.len() {
          matches_together = false;
          same_shape = false;
        }
      }
      (Pattern::Ctr { .. } | Pattern::Num { .. } | Pattern::Tup { .. } | Pattern::Dup { .. }, Pattern::Var { .. }) => {
        same_shape = false;
      }
      (Pattern::Num(a_num), Pattern::Num(b_num)) => {
        if std::mem::discriminant(a_num) != std::mem::discriminant(b_num) {
          matches_together = false;
          same_shape = false;
        }
      }
      (
        Pattern::Ctr { .. } | Pattern::Num { .. } | Pattern::Dup { .. } | Pattern::Tup { .. },
        Pattern::Ctr { .. } | Pattern::Num { .. } | Pattern::Dup { .. } | Pattern::Tup { .. },
      ) => {
        if std::mem::discriminant(a) != std::mem::discriminant(b) {
          matches_together = false;
          same_shape = false;
        }
      }
      (Pattern::Var { .. }, _) => (),
    }
  }
  (matches_together, same_shape)
}

fn split_group(rules: &[(Name, Rule)], def_names: &mut DefNames) -> HashMap<Name, Vec<Rule>> {
  let mut skip: HashSet<usize> = HashSet::new();
  let mut new_rules: HashMap<Name, Vec<Rule>> = HashMap::new();
  let mut split_rule_count = 0;
  for i in 0 .. rules.len() {
    if !skip.contains(&i) {
      let (name, rule) = &rules[i];
      let must_split = rule.pats.iter().any(|pat| !pat.is_flat());
      if must_split {
        let new_split_name = Name(format!("{}$F{}", name, split_rule_count));
        split_rule_count += 1;
        let new_split_def_id = def_names.insert(new_split_name.clone());

        let old_rule = make_old_rule(&rule.pats, new_split_def_id);

        let mut new_group = vec![(name.clone(), old_rule)];
        //let mut new_group = vec![];

        for (j, (_, other)) in rules.iter().enumerate().skip(i) {
          let (compatible, same_shape) = matches_together(&rule.pats, &other.pats);
          if compatible {
            if same_shape {
              skip.insert(j); // avoids identical, duplicated clauses
            }
            let new_rule = make_split_rule(rule, other, def_names);
            new_group.push((new_split_name.clone(), new_rule));
          }
        }

        for (nam, mut rules) in split_group(&new_group, def_names) {
          new_rules.entry(nam).or_default().append(&mut rules);
        }
      } else {
        new_rules.entry(rules[i].0.clone()).or_default().push(rules[i].1.clone());
      }
    }
  }
  new_rules
}

/// Makes the rule that replaces the original.
/// The new version of the rule is flat and calls the next layer of pattern matching.
fn make_old_rule(pats: &[Pattern], new_split_def_id: DefId) -> Rule {
  //(Foo Tic (Bar a b) (Haz c d)) = A
  //(Foo Tic x         y)         = B
  //---------------------------------
  //(Foo Tic (Bar a b) (Haz c d)) = B[x <- (Bar a b), y <- (Haz c d)]
  //
  //(Foo.0 a b c d) = ...
  let mut new_pats = Vec::new();
  let mut new_body_args = Vec::new();
  let mut var_count = 0;

  for arg in pats {
    match arg {
      Pattern::Ctr(arg_name, arg_args) => {
        let mut new_arg_args = Vec::new();
        for field in arg_args {
          let var_name = match field {
            Pattern::Ctr { .. } | Pattern::Tup { .. } | Pattern::Dup { .. } | Pattern::Num { .. } | Pattern::Era => {
              make_var_name(&mut var_count)
            }
            Pattern::Var(Some(nam)) => nam.clone(),
          };
          new_arg_args.push(Pattern::Var(Some(var_name.clone())));
          new_body_args.push(Term::Var { nam: var_name });
        }
        new_pats.push(Pattern::Ctr(arg_name.clone(), new_arg_args));
      }
      Pattern::Tup(_, _) => {
        let fst = make_var_name(&mut var_count);
        let snd = make_var_name(&mut var_count);
        new_body_args.push(Term::Var { nam: fst.clone() });
        new_body_args.push(Term::Var { nam: snd.clone() });
        let fst = Pattern::Var(Some(fst));
        let snd = Pattern::Var(Some(snd));
        new_pats.push(Pattern::Tup { fst: Box::new(fst), snd: Box::new(snd) });
      }
      Pattern::Dup(tag, _, _) => {
        let fst = make_var_name(&mut var_count);
        let snd = make_var_name(&mut var_count);
        new_body_args.push(Term::Var { nam: fst.clone() });
        new_body_args.push(Term::Var { nam: snd.clone() });
        let fst = Pattern::Var(Some(fst));
        let snd = Pattern::Var(Some(snd));
        new_pats.push(Pattern::Dup { tag: tag.clone(), fst: Box::new(fst), snd: Box::new(snd) });
      }
      Pattern::Era => todo!(),
      Pattern::Var(Some(nam)) => {
        new_pats.push(Pattern::Var(Some(nam.clone())));
        new_body_args.push(Term::Var { nam: nam.clone() });
      }
      Pattern::Num { .. } => {
        // How to do this if num can be either a number or some sort of lambda? add a match? separate both cases?
        todo!();
      }
    }
  }
  let new_body = Term::call(Term::Ref { def_id: new_split_def_id }, new_body_args);
  Rule { pats: new_pats, body: new_body }
}

/// Makes one of the new rules, flattening one layer of the original pattern.
fn make_split_rule(old_rule: &Rule, other_rule: &Rule, def_names: &DefNames) -> Rule {
  // (Foo a     (B x P) (C y0 y1)) = F
  // (Foo (A k) (B x Q) y        ) = G
  // -----------------------------
  // (Foo a (B x u) (C y0 y1)) = (Foo.0 a x u y0 y1)
  //   (Foo.0 a     x P y0 y1) = F
  //   (Foo.0 (A k) x Q f0 f1) = G [y <- (C f0 f1)] // f0 and f1 are fresh
  let mut new_pats = Vec::new();
  let mut new_body = other_rule.body.clone();
  let mut var_count = 0;
  for (rule_arg, other_arg) in old_rule.pats.iter().zip(&other_rule.pats) {
    match (rule_arg, other_arg) {
      // We checked before that these two have the same constructor and match together
      (Pattern::Ctr { .. }, Pattern::Ctr { args: other_arg_args, .. }) => {
        for other_field in other_arg_args {
          new_pats.push(other_field.clone());
        }
      }
      (Pattern::Ctr { nam: rule_arg_name, args: rule_arg_args }, Pattern::Var(Some(other_arg))) => {
        let mut new_ctr_args = vec![];
        for _ in 0 .. rule_arg_args.len() {
          let new_nam = make_var_name(&mut var_count);
          new_ctr_args.push(Term::Var { nam: new_nam.clone() });
          new_pats.push(Pattern::Var { nam: new_nam });
        }
        let rule_arg_def_id = def_names.def_id(rule_arg_name).unwrap();
        let new_ctr = Term::call(Term::Ref { def_id: rule_arg_def_id }, new_ctr_args);
        new_body.subst(other_arg, &new_ctr);
      }
      // Since numbers don't have subpatterns this should be unreachable.
      (Pattern::Num { .. }, _) => unreachable!(),
      (Pattern::Tup(_, _), Pattern::Tup { fst, snd }) => {
        new_pats.push(*fst.clone());
        new_pats.push(*snd.clone());
      }
      (Pattern::Tup { .. }, Pattern::Var { nam: other_arg }) => {
        let fst_nam = make_var_name(&mut var_count);
        let snd_nam = make_var_name(&mut var_count);
        let fst_arg = Term::Var { nam: fst_nam.clone() };
        let snd_arg = Term::Var { nam: snd_nam.clone() };
        new_pats.push(Pattern::Var { nam: fst_nam });
        new_pats.push(Pattern::Var { nam: snd_nam });
        let new_ctr = Term::Tup { fst: Box::new(fst_arg), snd: Box::new(snd_arg) };
        new_body.subst(other_arg, &new_ctr);
      }
      (Pattern::Var { .. }, _) => new_pats.push(other_arg.clone()),
      // Unreachable cases, we only call this function if we know the two patterns match together
      (Pattern::Ctr { .. } | Pattern::Tup { .. }, Pattern::Ctr { .. } | Pattern::Num { .. } | Pattern::Tup { .. }) => {
        unreachable!()
      }
      (Pattern::Ctr(_, ctr_fields), Pattern::Era) => {
        for _ in ctr_fields {
          new_pats.push(Pattern::Era);
        }
      }
      (Pattern::Tup { .. }, Pattern::Era) => {
        new_pats.push(Pattern::Era);
        new_pats.push(Pattern::Era);
      }
      _ => todo!(),
    }
  }
  Rule { pats: new_pats, body: new_body }
}

fn make_var_name(var_count: &mut usize) -> Name {
  let nam = Name(format!("x${var_count}"));
  *var_count += 1;
  nam
}
