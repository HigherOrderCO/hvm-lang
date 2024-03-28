use crate::{
  diagnostics::{Diagnostics, ToStringVerbose, WarningType},
  term::{Adts, Constructors, Ctx, Name, NumCtr, Term},
};
use std::collections::HashMap;

enum FixMatchErr {
  AdtMismatch { expected: Name, found: Name, ctr: Name },
  NonExhaustiveMatch { typ: Name, missing: Name },
  NumMismatch { expected: NumCtr, found: NumCtr },
  IrrefutableMatch { var: Option<Name> },
  UnreachableMatchArms { var: Option<Name> },
  ExtraSwitchArms,
  RedundantArm { ctr: Name },
}

impl Ctx<'_> {
  /// Convert all match and switch expressions to a normalized form.
  /// * For matches, resolve the constructors and create the name of the field variables.
  /// * For switches, resolve the succ case ("_") and create the name of the pred variable.
  /// * If the match arg is not a variable, it is separated into a let expression and bound to "%matched"
  /// * Check for redundant arms and non-exhaustive matches.
  ///
  /// Example:
  /// For the program
  /// ```hvm
  /// data MyList = (Cons h t) | Nil
  /// match x {
  ///   Cons: (A x.h x.t)
  ///   Nil: switch (Foo y) { 0: B; 1: C; _: D }
  /// }
  /// ```
  /// The following AST transformations will be made:
  /// * The binds `x.h` and `x.t` will be generated and stored in the match term.
  /// * `(Foo y)`` will be put in a let expression, bound to the variable `%matched`;
  /// * The bind `%matched-2` will be generated and stored in the switch term.
  /// * If either was missing one of the match cases (a number or a constructor), we'd get an error.
  /// * If either included one of the cases more than once (including wildcard patterns), we'd get a warning.
  /// ```hvm
  /// match x {
  ///   Cons: (A x.h x.t)
  ///   Nil: let %matched = (Foo y); switch %matched { 0: B; 1: C; _: D }
  /// }
  /// ```
  pub fn fix_match_terms(&mut self) -> Result<(), Diagnostics> {
    self.info.start_pass();

    for def in self.book.defs.values_mut() {
      for rule in def.rules.iter_mut() {
        let errs = rule.body.fix_match_terms(&self.book.ctrs, &self.book.adts);

        for err in errs {
          match err {
            FixMatchErr::ExtraSwitchArms { .. }
            | FixMatchErr::AdtMismatch { .. }
            | FixMatchErr::NumMismatch { .. }
            | FixMatchErr::NonExhaustiveMatch { .. } => self.info.add_rule_error(err, def.name.clone()),

            FixMatchErr::IrrefutableMatch { .. } => {
              self.info.add_rule_warning(err, WarningType::IrrefutableMatch, def.name.clone())
            }
            FixMatchErr::UnreachableMatchArms { .. } => {
              self.info.add_rule_warning(err, WarningType::UnreachableMatch, def.name.clone())
            }
            FixMatchErr::RedundantArm { .. } => {
              self.info.add_rule_warning(err, WarningType::RedundantMatch, def.name.clone())
            }
          }
        }
      }
    }

    self.info.fatal(())
  }
}

impl Term {
  fn fix_match_terms(&mut self, ctrs: &Constructors, adts: &Adts) -> Vec<FixMatchErr> {
    Term::recursive_call(move || {
      let mut errs = Vec::new();

      for child in self.children_mut() {
        let mut e = child.fix_match_terms(ctrs, adts);
        errs.append(&mut e);
      }

      if let Term::Mat { .. } = self {
        self.fix_match(&mut errs, ctrs, adts);
      } else if let Term::Swt { .. } = self {
        self.fix_switch(&mut errs);
      }

      errs
    })
  }

  fn fix_match(&mut self, errs: &mut Vec<FixMatchErr>, ctrs: &Constructors, adts: &Adts) {
    let Term::Mat { arg, rules } = self else { unreachable!() };

    let (arg_nam, arg) = extract_match_arg(arg);

    // Normalize arms
    if let Some(ctr_nam) = &rules[0].0
      && let Some(adt_nam) = ctrs.get(ctr_nam)
    {
      let adt_ctrs = &adts[adt_nam].ctrs;

      // For each arm, decide to which arm of the fixed match they map to.
      let mut bodies = HashMap::<&Name, Option<Term>>::from_iter(adt_ctrs.iter().map(|(ctr, _)| (ctr, None)));
      for rule_idx in 0 .. rules.len() {
        if let Some(ctr_nam) = &rules[rule_idx].0
          && let Some(found_adt) = ctrs.get(ctr_nam)
        {
          // Ctr arm
          if found_adt == adt_nam {
            let body = bodies.get_mut(ctr_nam).unwrap();
            if body.is_none() {
              // Use this rule for this constructor
              *body = Some(rules[rule_idx].2.clone());
            } else {
              errs.push(FixMatchErr::RedundantArm { ctr: ctr_nam.clone() });
            }
          } else {
            errs.push(FixMatchErr::AdtMismatch {
              expected: adt_nam.clone(),
              found: found_adt.clone(),
              ctr: ctr_nam.clone(),
            })
          }
        } else {
          // Var arm
          if rule_idx != rules.len() - 1 {
            errs.push(FixMatchErr::UnreachableMatchArms { var: rules[rule_idx].0.clone() });
            rules.truncate(rule_idx + 1);
          }
          // Use this rule for all remaining constructors
          for (ctr, body) in bodies.iter_mut() {
            if body.is_none() {
              let mut new_body = rules[rule_idx].2.clone();
              if let Some(var) = &rules[rule_idx].0 {
                new_body.subst(var, &rebuild_ctr(&arg_nam, ctr, &adts[adt_nam].ctrs[&**ctr]));
              }
              *body = Some(new_body);
            }
          }

          break;
        }
      }

      // Build the match arms, with all constructors
      let mut new_rules = vec![];
      for (ctr, fields) in adt_ctrs.iter() {
        let fields = fields.iter().map(|f| Some(match_field(&arg_nam, f))).collect::<Vec<_>>();
        let body = if let Some(Some(body)) = bodies.remove(ctr) {
          body
        } else {
          errs.push(FixMatchErr::NonExhaustiveMatch { typ: adt_nam.clone(), missing: ctr.clone() });
          Term::Err
        };
        new_rules.push((Some(ctr.clone()), fields, body));
      }
      *rules = new_rules;
    } else {
      errs.push(FixMatchErr::IrrefutableMatch { var: rules[0].0.clone() });

      let match_var = rules[0].0.take();
      *self = std::mem::take(&mut rules[0].2);
      if let Some(var) = match_var {
        self.subst(&var, &Term::Var { nam: arg_nam.clone() });
      }
    }

    *self = apply_arg(std::mem::take(self), arg_nam, arg);
  }

  /// For switches, the only necessary change is to add the implicit pred bind to the AST.
  ///
  /// Check that all numbers are in order and no cases are skipped.
  /// Also check that we have a default case at the end, binding the pred.
  fn fix_switch(&mut self, errs: &mut Vec<FixMatchErr>) {
    let Term::Swt { arg, rules } = self else { unreachable!() };

    let (arg_nam, arg) = extract_match_arg(arg);

    let mut has_num = false;
    let len = rules.len();
    for i in 0 .. len {
      let ctr = &mut rules[i].0;
      match ctr {
        NumCtr::Num(n) if i as u64 == *n => {
          has_num = true;
        }
        NumCtr::Num(n) => {
          errs.push(FixMatchErr::NumMismatch { expected: NumCtr::Num(i as u64), found: NumCtr::Num(*n) });
          break;
        }
        NumCtr::Succ(pred) => {
          if !has_num {
            errs.push(FixMatchErr::NumMismatch {
              expected: NumCtr::Num(i as u64),
              found: NumCtr::Succ(pred.clone()),
            });
            break;
          }
          *pred = Some(Name::new(format!("{arg_nam}-{i}")));
          if i != len - 1 {
            errs.push(FixMatchErr::ExtraSwitchArms);
            rules.truncate(i + 1);
            break;
          }
        }
      }
    }

    *self = apply_arg(std::mem::take(self), arg_nam, arg);
  }
}

fn extract_match_arg(arg: &mut Term) -> (Name, Option<Term>) {
  if let Term::Var { nam } = arg {
    (nam.clone(), None)
  } else {
    let nam = Name::from("%matched");
    let arg = std::mem::replace(arg, Term::Var { nam: nam.clone() });
    (nam, Some(arg))
  }
}

fn apply_arg(term: Term, arg_nam: Name, arg: Option<Term>) -> Term {
  if let Some(arg) = arg {
    Term::Let { nam: Some(arg_nam), val: Box::new(arg), nxt: Box::new(term) }
  } else {
    term
  }
}

fn match_field(arg: &Name, field: &Name) -> Name {
  Name::new(format!("{arg}.{field}"))
}

fn rebuild_ctr(arg: &Name, ctr: &Name, fields: &[Name]) -> Term {
  let ctr = Term::Ref { nam: ctr.clone() };
  let fields = fields.iter().map(|f| Term::Var { nam: match_field(arg, f) });
  Term::call(ctr, fields)
}

impl ToStringVerbose for FixMatchErr {
  fn to_string_verbose(&self, _verbose: bool) -> String {
    match self {
      FixMatchErr::AdtMismatch { expected, found, ctr } => format!(
        "Type mismatch in 'match' expression: Expected a constructor of type '{expected}', found '{ctr}' of type '{found}'"
      ),
      FixMatchErr::NonExhaustiveMatch { typ, missing } => {
        format!("Non-exhaustive 'match' expression of type '{typ}'. Case '{missing}' not covered.")
      }
      FixMatchErr::NumMismatch { expected, found } => {
        format!(
          "Malformed 'switch' expression. Expected case '{expected}', found '{found}'. Switch expressions must go from 0 to the desired value without skipping any cases and ending with the default case."
        )
      }
      FixMatchErr::IrrefutableMatch { var } => format!(
        "Irrefutable 'match' expression. All cases after '{}' will be ignored. If this is not a mistake, consider using a 'let' expression instead.",
        var.as_ref().unwrap_or(&Name::new("*"))
      ),
      FixMatchErr::UnreachableMatchArms { var } => format!(
        "Unreachable arms in 'match' expression. All cases after '{}' will be ignored.",
        var.as_ref().unwrap_or(&Name::new("*"))
      ),
      FixMatchErr::ExtraSwitchArms => {
        "Extra arms in 'switch' expression. No rules should come after the default.".to_string()
      }
      FixMatchErr::RedundantArm { ctr } => {
        format!("Redundant arm in 'match' expression. Case '{ctr}' appears more than once.")
      }
    }
  }
}
