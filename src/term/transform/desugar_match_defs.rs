use std::collections::{BTreeSet, HashSet};

use crate::{
  diagnostics::{Diagnostics, ToStringVerbose, WarningType},
  term::{builtins, Adts, Constructors, Ctx, Definition, Name, NumCtr, Pattern, Rule, Term},
};

pub enum DesugarMatchDefErr {
  AdtNotExhaustive { adt: Name, ctr: Name },
  NumMissingDefault,
  TypeMismatch { expected: Type, found: Type, pat: Pattern },
  RepeatedBind { bind: Name },
}

impl Ctx<'_> {
  pub fn desugar_match_defs(&mut self) -> Result<(), Diagnostics> {
    self.info.start_pass();

    for (def_name, def) in self.book.defs.iter_mut() {
      let errs = def.desugar_match_def(&self.book.ctrs, &self.book.adts);
      for err in errs {
        match err {
          DesugarMatchDefErr::AdtNotExhaustive { .. }
          | DesugarMatchDefErr::NumMissingDefault
          | DesugarMatchDefErr::TypeMismatch { .. } => self.info.add_rule_error(err, def_name.clone()),
          DesugarMatchDefErr::RepeatedBind { .. } => {
            self.info.add_rule_warning(err, WarningType::RepeatedBind, def_name.clone())
          }
        }
      }
    }

    self.info.fatal(())
  }
}

impl Definition {
  pub fn desugar_match_def(&mut self, ctrs: &Constructors, adts: &Adts) -> Vec<DesugarMatchDefErr> {
    let mut errs = vec![];

    let repeated_bind_errs = fix_repeated_binds(&mut self.rules);
    errs.extend(repeated_bind_errs);

    let args = (0 .. self.arity()).map(|i| Name::new(format!("%arg{i}"))).collect::<Vec<_>>();
    let rules = std::mem::take(&mut self.rules);
    match simplify_rule_match(args.clone(), rules, ctrs, adts) {
      Ok(body) => {
        let body = args.into_iter().rfold(body, |body, arg| Term::lam(Some(arg), body));
        self.rules = vec![Rule { pats: vec![], body }];
      }
      Err(e) => errs.push(e),
    }
    errs
  }
}

/// When a rule has repeated bind, the only one that is actually useful is the last one.
///
/// Example: In `(Foo x x x x) = x`, the function should return the fourth argument.
///
/// To avoid having to deal with this, we can just erase any repeated binds.
/// ```hvm
/// (Foo a (Succ a) (Cons a)) = (a a)
/// // After this transformation, becomes:
/// (Foo * (Succ *) (Cons a)) = (a a)
/// ```
fn fix_repeated_binds(rules: &mut [Rule]) -> Vec<DesugarMatchDefErr> {
  let mut errs = vec![];
  for rule in rules {
    let mut binds = HashSet::new();
    rule.pats.iter_mut().flat_map(|p| p.binds_mut()).rev().for_each(|nam| {
      if binds.contains(nam) {
        // Repeated bind, not reachable and can be erased.
        if let Some(nam) = nam {
          errs.push(DesugarMatchDefErr::RepeatedBind { bind: nam.clone() });
        }
        *nam = None;
        // TODO: Send a repeated bind warning
      } else {
        binds.insert(&*nam);
      }
    });
  }
  errs
}

/// Creates the match tree for a given pattern matching function definition.
/// For each constructor, a match case is created.
///
/// The match cases follow the same order as the order the constructors are in
/// the ADT declaration.
///
/// If there are constructors of different types for the same arg, returns a type error.
///
/// If no patterns match one of the constructors, returns a non-exhaustive match error.
///
/// ===========================================================================
///

///
/// Any nested subpatterns are extracted and moved into a nested match
/// expression, together with the remaining match arguments.
fn simplify_rule_match(
  args: Vec<Name>,
  mut rules: Vec<Rule>,
  ctrs: &Constructors,
  adts: &Adts,
) -> Result<Term, DesugarMatchDefErr> {
  if args.is_empty() {
    Ok(std::mem::take(&mut rules[0].body))
  } else if rules[0].pats.iter().all(|p| p.is_wildcard()) {
    Ok(irrefutable_fst_row_rule(args, std::mem::take(&mut rules[0])))
  } else {
    let typ = Type::infer_from_def_arg(&rules, 0, ctrs)?;
    match typ {
      Type::Any => var_rule(args, rules, ctrs, adts),
      Type::Tup(tup_len) => tup_rule(args, rules, tup_len, ctrs, adts),
      Type::Num => num_rule(args, rules, ctrs, adts),
      Type::Adt(adt_name) => switch_rule(args, rules, adt_name, ctrs, adts),
    }
  }
}

/// Irrefutable first row rule.
/// Short-circuits the encoding in case the first rule always matches.
/// This is useful to avoid unnecessary pattern matching.
fn irrefutable_fst_row_rule(args: Vec<Name>, rule: Rule) -> Term {
  let mut term = rule.body;
  for (arg, pat) in args.into_iter().zip(rule.pats.into_iter()) {
    let Pattern::Var(var) = pat else { unreachable!() };
    if let Some(var) = var {
      term.subst(&var, &Term::Var { nam: arg });
    }
  }
  term
}

/// Var rule.
/// `case x0 ... xN { var p1 ... pN: (Body var p1 ... pN) }`
/// becomes
/// `case x1 ... xN { p1 ... pN: use var = x0; (Body var p1 ... pN) }`
fn var_rule(
  mut args: Vec<Name>,
  rules: Vec<Rule>,
  ctrs: &Constructors,
  adts: &Adts,
) -> Result<Term, DesugarMatchDefErr> {
  let arg = args[0].clone();
  let new_args = args.split_off(1);

  let mut new_rules = vec![];
  for mut rule in rules {
    let new_pats = rule.pats.split_off(1);
    let pat = rule.pats.pop().unwrap();

    if let Pattern::Var(Some(nam)) = &pat {
      rule.body.subst(nam, &Term::Var { nam: arg.clone() });
    }

    let new_rule = Rule { pats: new_pats, body: rule.body };
    new_rules.push(new_rule);
  }

  simplify_rule_match(new_args, new_rules, ctrs, adts)
}

/// Tuple rule.
/// ```hvm
/// case x0 ... xN {
///   (p0_0, ... p0_M) p1 ... pN:
///     (Body p0_0 ... p0_M p1 ... pN)
/// }
/// ```
/// becomes
/// ```hvm
/// let (x0.0, ... x0.M) = x0;
/// case x0.0 ... x0.M x1 ... xN {
///   p0_0 ... p0_M p1 ... pN:
///     (Body p0_0 ... p0_M p1 ... pN)
/// }
/// ```
fn tup_rule(
  mut args: Vec<Name>,
  rules: Vec<Rule>,
  tup_len: usize,
  ctrs: &Constructors,
  adts: &Adts,
) -> Result<Term, DesugarMatchDefErr> {
  let arg = args[0].clone();
  let old_args = args.split_off(1);
  let new_args = (0 .. tup_len).map(|i| Name::new(format!("{arg}.{i}")));

  let mut new_rules = vec![];
  for mut rule in rules {
    let pat = rule.pats[0].clone();
    let old_pats = rule.pats.split_off(1);

    // Extract subpats from the tuple pattern
    let mut new_pats = match pat {
      Pattern::Tup(sub_pats) => sub_pats,
      Pattern::Var(var) => {
        if let Some(var) = var {
          // Rebuild the tuple if it was a var pattern
          let tup = Term::Tup { els: new_args.clone().map(|nam| Term::Var { nam }).collect() };
          rule.body.subst(&var, &tup);
        }
        new_args.clone().map(|nam| Pattern::Var(Some(nam))).collect()
      }
      _ => unreachable!(),
    };
    new_pats.extend(old_pats);

    let new_rule = Rule { pats: new_pats, body: rule.body };
    new_rules.push(new_rule);
  }

  let bnd = new_args.clone().map(Some).collect();
  let args = new_args.chain(old_args).collect();
  let nxt = simplify_rule_match(args, new_rules, ctrs, adts)?;
  let term = Term::Ltp { bnd, val: Box::new(Term::Var { nam: arg }), nxt: Box::new(nxt) };

  Ok(term)
}

fn num_rule(
  mut args: Vec<Name>,
  rules: Vec<Rule>,
  ctrs: &Constructors,
  adts: &Adts,
) -> Result<Term, DesugarMatchDefErr> {
  // Number match must always have a default case
  if !rules.iter().any(|r| r.pats[0].is_wildcard()) {
    return Err(DesugarMatchDefErr::NumMissingDefault);
  }

  let arg = args[0].clone();
  let args = args.split_off(1);

  let match_var = Name::new(format!("{arg}%matched"));
  let pred_var = Name::new(format!("{arg}%matched-1"));

  // Since numbers have infinite (2^60) constructors, they require special treatment.
  // We first iterate over each present number then get the default.
  let nums = rules
    .iter()
    .filter_map(|r| if let Pattern::Num(n) = r.pats[0] { Some(n) } else { None })
    .collect::<BTreeSet<_>>()
    .into_iter()
    .collect::<Vec<_>>();

  // Number cases
  let mut bodies = vec![];
  for num in nums.iter() {
    let mut new_rules = vec![];
    for rule in rules.iter() {
      match &rule.pats[0] {
        Pattern::Num(n) if n == num => {
          let body = rule.body.clone();
          let rule = Rule { pats: rule.pats[1 ..].to_vec(), body };
          new_rules.push(rule);
        }
        Pattern::Var(var) => {
          let mut body = rule.body.clone();
          if let Some(var) = var {
            body.subst(var, &Term::Num { val: *num });
          }
          let rule = Rule { pats: rule.pats[1 ..].to_vec(), body };
          new_rules.push(rule);
        }
        _ => (),
      }
    }
    let body = simplify_rule_match(args.clone(), new_rules, ctrs, adts)?;
    bodies.push(body);
  }

  // Default case
  let mut new_rules = vec![];
  for rule in rules {
    if let Pattern::Var(var) = &rule.pats[0] {
      let mut body = rule.body.clone();
      if let Some(var) = var {
        let last_num = *nums.last().unwrap();
        let var_recovered = Term::add_num(Term::Var { nam: pred_var.clone() }, 1 + last_num);
        body.subst(var, &var_recovered);
      }
      let rule = Rule { pats: rule.pats[1 ..].to_vec(), body };
      new_rules.push(rule);
    }
  }
  let default_body = simplify_rule_match(args, new_rules, ctrs, adts)?;

  let term = bodies.into_iter().enumerate().rfold(default_body, |term, (i, body)| {
    let zero = (NumCtr::Num(0), body);
    let succ = (NumCtr::Succ(Some(pred_var.clone())), term);
    let mut swt = Term::Swt { arg: Box::new(Term::Var { nam: match_var.clone() }), rules: vec![zero, succ] };

    let val = if i > 0 {
      // let %matched = (%matched-1 +1 +num_i-1 - num_i)
      //  switch %matched { 0: body_i; _: acc }
      // nums[i] >= nums[i-1]+1, so we do a sub here.
      Term::sub_num(Term::Var { nam: pred_var.clone() }, nums[i] - 1 - nums[i - 1])
    } else {
      // let %matched = (arg -num_0);
      //  switch %matched { 0: body_0; _: acc}
      Term::sub_num(Term::Var { nam: arg.clone() }, nums[i])
    };

    if let Term::Var { .. } = &val {
      // No need to create a let expression if it's just a rename.
      // We know that the bound value is a uniquely named var, so we can subst.
      swt.subst(&match_var, &val);
      swt
    } else {
      Term::Let { nam: Some(match_var.clone()), val: Box::new(val), nxt: Box::new(swt) }
    }
  });

  Ok(term)
}

/// When the first column has constructors, create a branch on the constructors
/// of the first arg.
///
/// The extracted nested patterns and remaining args are handled recursively in
/// a nested expression for each match arm.
///
/// If we imagine a complex match expression representing what's left of the
/// encoding of a pattern matching function:
/// ```hvm
/// data MyType = (CtrA ctrA_field0 ... ctrA_fieldA) | (CtrB ctrB_field0 ... ctrB_fieldB) | CtrC | ...
///
/// case x0 ... xN {
///   (CtrA p0_0_0 ... p0_A) p0_1 ... p0_N : (Body0 p0_0_0 ... p0_0_A p0_1 ... p0_N)
///   ...
///   varI pI_1 ... pI_N: (BodyI varI pI_1 ... pI_N)
///   ...
///   (CtrB pJ_0_0 ... pJ_0_B) pJ_1 ... pJ_N: (BodyJ pJ_0_0 ... pJ_0_B pJ_1 ... pJ_N)
///   ...
///   (CtrC) pK_1 ... pK_N: (BodyK p_1 ... pK_N)
///   ...
/// }
/// ```
/// is converted into
/// ```hvm
/// match x0 {
///   CtrA: case x.ctrA_field0 ... x.ctrA_fieldA x1 ... xN {
///     p0_0_0 ... p0_0_B p0_1 ... p0_N :
///       (Body0 p0_0_0 ... p0_0_B )
///     x.ctrA_field0 ... x.ctrA_fieldA pI_1 ... pI_N:
///       use varI = (CtrA x.ctrA_field0 ... x.ctrA_fieldN); (BodyI varI pI_1 ... pI_N)
///     ...
///   }
///   CtrB: case x.ctrB_field0 ... x.ctrB_fieldB x1 ... xN {
///     x.ctrB_field0 ... x.ctrB_fieldB pI_1 ... pI_N:
///       use varI = (CtrB x.ctrB_field0 ... x.ctrB_fieldB); (BodyI varI pI_1 ... pI_N)
///     pJ_0_0 ... pJ_0_B pJ_1 ... pJ_N :
///       (BodyJ pJ_0_0 ... pJ_0_B pJ_1 ... pJ_N)
///     ...
///   }
///   CtrC: case * x1 ... xN {
///     * pI_1 ... pI_N:
///       use varI = CtrC; (BodyI varI pI_1 ... pI_N)
///     * pK_1 ... pK_N:
///       (BodyK p_1 ... pK_N)
///     ...
///   }
///   ...
/// }
/// ```
/// Where `case` represents a call of the [`simplify_rule_match`] function.
fn switch_rule(
  mut args: Vec<Name>,
  rules: Vec<Rule>,
  adt_name: Name,
  ctrs: &Constructors,
  adts: &Adts,
) -> Result<Term, DesugarMatchDefErr> {
  let arg = args[0].clone();
  let old_args = args.split_off(1);

  let mut new_arms = vec![];
  for (ctr, fields) in &adts[&adt_name].ctrs {
    let new_args = fields.iter().map(|f| Name::new(format!("{arg}.{f}")));
    let args = new_args.clone().chain(old_args.clone()).collect();

    let mut new_rules = vec![];
    for rule in &rules {
      let old_pats = rule.pats[1 ..].to_vec();
      match &rule.pats[0] {
        // Same ctr, extract subpats.
        // (Ctr pat0_0 ... pat0_m) pat1 ... patN: body
        // becomes
        // pat0_0 ... pat0_m pat1 ... patN: body
        Pattern::Ctr(found_ctr, new_pats) if ctr == found_ctr => {
          let pats = new_pats.iter().cloned().chain(old_pats).collect();
          let body = rule.body.clone();
          let rule = Rule { pats, body };
          new_rules.push(rule);
        }
        // Var, match and rebuild the constructor.
        // var pat1 ... patN: body
        // becomes
        // arg0.field0 ... arg0.fieldM pat1 ... patN:
        //   use var = (Ctr arg0.field0 ... arg0.fieldM); body
        Pattern::Var(var) => {
          let new_pats = new_args.clone().map(|n| Pattern::Var(Some(n)));
          let pats = new_pats.chain(old_pats.clone()).collect();
          let mut body = rule.body.clone();
          let reconstructed_var =
            Term::call(Term::Ref { nam: ctr.clone() }, new_args.clone().map(|nam| Term::Var { nam }));
          if let Some(var) = var {
            body.subst(var, &reconstructed_var);
          }
          let rule = Rule { pats, body };
          new_rules.push(rule);
        }
        _ => (),
      }
    }

    if new_rules.is_empty() {
      return Err(DesugarMatchDefErr::AdtNotExhaustive { adt: adt_name, ctr: ctr.clone() });
    }

    let body = simplify_rule_match(args, new_rules, ctrs, adts)?;
    new_arms.push((Some(ctr.clone()), new_args.map(Some).collect(), body));
  }
  let term = Term::Mat { arg: Box::new(Term::Var { nam: arg }), rules: new_arms };
  Ok(term)
}

/// Pattern types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
  /// Variables/wildcards.
  Any,
  /// A native tuple.
  Tup(usize),
  /// A sequence of arbitrary numbers ending in a variable.
  Num,
  /// Adt constructors declared with the `data` syntax.
  Adt(Name),
}

impl Type {
  // Infers the type of a column of a pattern matrix, from the rules of a function def.
  fn infer_from_def_arg(
    rules: &[Rule],
    arg_idx: usize,
    ctrs: &Constructors,
  ) -> Result<Type, DesugarMatchDefErr> {
    let pats = rules.iter().map(|r| &r.pats[arg_idx]);
    let mut arg_type = Type::Any;
    for pat in pats {
      arg_type = match (arg_type, pat.to_type(ctrs)) {
        (Type::Any, found) => found,
        (expected, Type::Any) => expected,

        (Type::Adt(expected), Type::Adt(found)) if found == expected => Type::Adt(expected),

        (Type::Num, Type::Num) => Type::Num,

        (Type::Tup(a), Type::Tup(b)) if a == b => Type::Tup(a),

        (expected, found) => {
          return Err(DesugarMatchDefErr::TypeMismatch { expected, found, pat: pat.clone() });
        }
      };
    }
    Ok(arg_type)
  }
}

impl Pattern {
  fn to_type(&self, ctrs: &Constructors) -> Type {
    match self {
      Pattern::Var(_) => Type::Any,
      Pattern::Ctr(ctr_nam, _) => {
        let adt_nam = ctrs.get(ctr_nam).expect("Unknown constructor '{ctr_nam}'");
        Type::Adt(adt_nam.clone())
      }
      Pattern::Tup(args) => Type::Tup(args.len()),
      Pattern::Num(_) => Type::Num,
      Pattern::Lst(..) => Type::Adt(builtins::LIST.into()),
      Pattern::Str(..) => Type::Adt(builtins::STRING.into()),
    }
  }
}

impl std::fmt::Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Type::Any => write!(f, "any"),
      Type::Tup(n) => write!(f, "{n}-tuple"),
      Type::Num => write!(f, "number"),
      Type::Adt(nam) => write!(f, "{nam}"),
    }
  }
}

impl ToStringVerbose for DesugarMatchDefErr {
  fn to_string_verbose(&self, _verbose: bool) -> String {
    match self {
      DesugarMatchDefErr::AdtNotExhaustive { adt, ctr } => {
        format!("Non-exhaustive pattern matching rule. Constructor '{ctr}' of type '{adt}' not covered")
      }
      DesugarMatchDefErr::TypeMismatch { expected, found, pat } => {
        format!(
          "Type mismatch in pattern matching rule. Expected a constructor of type '{}', found '{}' with type '{}'.",
          expected, pat, found
        )
      }
      DesugarMatchDefErr::NumMissingDefault => {
        "Non-exhaustive pattern matching rule. Default case of number type not covered.".to_string()
      }
      DesugarMatchDefErr::RepeatedBind { bind } => {
        format!("Repeated bind in pattern matching rule: '{bind}'.")
      }
    }
  }
}
