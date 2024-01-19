use super::type_check::{DefinitionTypes, Type};
use crate::term::{Adt, Book, MatchNum, Name, Pattern, Rule};
use std::collections::BTreeMap;

impl Book {
  /// For each pattern-matching definition, check that any given value will match at least one of the rules.
  /// We assume that all patterns have been type checked already.
  pub fn check_exhaustive_patterns(&self, def_types: &DefinitionTypes) -> Result<(), String> {
    for (def_id, def) in &self.defs {
      let def_name = self.def_names.name(def_id).unwrap();
      let types = &def_types[def_id];
      let rules_to_check = Vec::from_iter(0 .. def.rules.len());
      check_pattern(&mut vec![], &self.adts, &def.rules, types, rules_to_check, def_name)?;
    }
    Ok(())
  }
}

fn check_pattern(
  match_path: &mut Vec<Name>,
  adts: &BTreeMap<Name, Adt>,
  rules: &[Rule],
  types: &[Type],
  rules_to_check: Vec<usize>,
  def_name: &Name,
) -> Result<(), String> {
  if let Some(pat_type) = types.first() {
    // For each constructor of the pattern, which rules match with it.
    // If no rules match a given constructor, the pattern is non-exhaustive.
    let rules_matching_ctrs = match pat_type {
      // We can skip non pattern matching arguments
      Type::Any => BTreeMap::from([(Name::new("_"), rules_to_check)]),
      Type::Adt(adt_nam) => {
        let adt = &adts[adt_nam];
        // Find which rules match each constructor
        let mut next_rules_to_check: BTreeMap<Name, Vec<usize>> =
          BTreeMap::from_iter(adt.ctrs.keys().cloned().map(|ctr| (ctr, vec![])));
        for rule_idx in rules_to_check {
          let pat = &rules[rule_idx].pats[match_path.len()];
          match pat {
            // Rules with a var pattern are relevant to all constructors.
            Pattern::Var { .. } => next_rules_to_check.values_mut().for_each(|x| x.push(rule_idx)),
            Pattern::Ctr { nam: ctr_nam, .. } => next_rules_to_check.get_mut(ctr_nam).unwrap().push(rule_idx),
            // We already type checked, so no other patterns will appear here.
            _ => unreachable!(),
          }
        }
        next_rules_to_check
      }
      Type::Tup => BTreeMap::from([(Name::new("(_,_)"), rules_to_check)]),
      Type::Num => {
        let mut next_rules_to_check: BTreeMap<Name, Vec<usize>> =
          BTreeMap::from([(Name::new("0"), vec![]), (Name::new("+"), vec![])]);
        for rule_idx in rules_to_check {
          let pat = &rules[rule_idx].pats[match_path.len()];
          match pat {
            Pattern::Var { .. } => next_rules_to_check.values_mut().for_each(|x| x.push(rule_idx)),
            Pattern::Num { mat  } => {
              next_rules_to_check.get_mut(&match mat {
                MatchNum::Zero => Name::new("0"),
                MatchNum::Succ(_) => Name::new("+"),
              }).unwrap().push(rule_idx);
            },
            _ => unreachable!(),
          }
        }
        next_rules_to_check
      },
      _ => todo!(),
    };

    // Check that each constructor matches at least one rule and then check the next pattern recursively.
    for (ctr, matching_rules) in rules_matching_ctrs {
      if matching_rules.is_empty() {
        let missing = get_missing_pattern(match_path, ctr, &types[1 ..], adts);
        return Err(format!(
          "Non-exhaustive pattern at definition '{}'. Hint: ({} {}) not covered.",
          def_name, def_name, missing
        ));
      } else {
        let mut match_path = match_path.to_vec();
        match_path.push(ctr);
        check_pattern(&mut match_path, adts, rules, &types[1 ..], matching_rules, def_name)?;
      }
    }
  }
  Ok(())
}

/// Returns a string with the first pattern not covered by the definition.
fn get_missing_pattern(
  match_path: &[Name],
  missing_ctr: Name,
  remaining_types: &[Type],
  adts: &BTreeMap<Name, Adt>,
) -> String {
  let mut missing_set: Vec<_> = match_path.iter().map(|x| x.to_string()).collect();
  missing_set.push(missing_ctr.to_string());
  for typ in remaining_types {
    missing_set.push(first_ctr_of_type(typ, adts));
  }
  missing_set.join(" ")
}

fn first_ctr_of_type(typ: &Type, adts: &BTreeMap<Name, Adt>) -> String {
  match typ {
    Type::Any => "_".to_string(),
    Type::Tup => "(_,_)".to_string(),
    Type::Sup => "{_,_}".to_string(),
    Type::Num => "0".to_string(),
    Type::Adt(adt_name) => adts[adt_name].ctrs.keys().next().unwrap().to_string(),
  }
}
