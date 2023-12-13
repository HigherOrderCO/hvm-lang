use crate::term::{
  check::type_check::{DefinitionTypes, Type},
  Book, DefId, MatchNum, Name, Pattern, Rule, Tag, Term,
};

impl Book {
  pub fn encode_pattern_matching_functions(&mut self, def_types: &DefinitionTypes) {
    for def_id in self.defs.keys().copied().collect::<Vec<_>>() {
      let def_type = &def_types[&def_id];

      let is_matching_def = def_type.iter().any(|t| matches!(t, Type::Adt(_) | Type::Tup | Type::Num));
      if is_matching_def {
        make_pattern_matching_def(self, def_id, def_type);
      } else {
        // For functions with only one rule that doesnt pattern match,
        // we just move the variables from arg to body.
        make_non_pattern_matching_def(self, def_id);
      }
    }
  }
}

/// For functions that don't pattern match, just move the arg variables into the body.
fn make_non_pattern_matching_def(book: &mut Book, def_id: DefId) {
  let def = book.defs.get_mut(&def_id).unwrap();
  let rule = def.rules.first_mut().unwrap();
  for pat in rule.pats.iter().rev() {
    let Pattern::Var(var) = pat else { unreachable!() };
    let bod = std::mem::replace(&mut rule.body, Term::Era);
    rule.body = Term::Lam { tag: Tag::Static, nam: var.clone(), bod: Box::new(bod) };
  }
  rule.pats = vec![];
}

/// For function that do pattern match,
///  we break them into a tree of small matching functions
///  with the original rule bodies at the end.
fn make_pattern_matching_def(book: &mut Book, def_id: DefId, def_type: &[Type]) {
  let def_name = book.def_names.name(&def_id).unwrap().clone();
  let def = book.defs.get_mut(&def_id).unwrap();
  let crnt_rules = (0 .. def.rules.len()).collect();

  // First create a definition for each rule body
  let mut rule_bodies = vec![];
  for rule in def.rules.iter_mut() {
    let body = std::mem::replace(&mut rule.body, Term::Era);
    let body = make_rule_body(body, &rule.pats);
    rule_bodies.push(body);
  }
  for (rule_idx, body) in rule_bodies.into_iter().enumerate() {
    let rule_name = make_rule_name(&def_name, rule_idx);
    book.insert_def(rule_name, vec![Rule { pats: vec![], body }]);
  }

  // Generate scott-encoded pattern matching
  make_pattern_matching_case(book, def_type, def_id, &def_name, crnt_rules, vec![]);
}

fn make_rule_name(def_name: &Name, rule_idx: usize) -> Name {
  Name(format!("{def_name}$R{rule_idx}"))
}

fn make_rule_body(mut body: Term, pats: &[Pattern]) -> Term {
  // Add the lambdas for the pattern variables
  for pat in pats.iter().rev() {
    match pat {
      Pattern::Var(nam) => body = Term::Lam { tag: Tag::Static, nam: nam.clone(), bod: Box::new(body) },
      Pattern::Ctr(_, vars) => {
        for var in vars.iter().rev() {
          let Pattern::Var(nam) = var else { unreachable!() };
          body = Term::Lam { tag: Tag::Static, nam: nam.clone(), bod: Box::new(body) }
        }
      }
      Pattern::Num(MatchNum::Zero) => (),
      Pattern::Num(MatchNum::Succ(None)) => (),
      Pattern::Num(MatchNum::Succ(Some(nam))) => {
        body = Term::Lam { tag: Tag::Static, nam: nam.clone(), bod: Box::new(body) }
      }
      pat @ Pattern::Tup(..) => {
        let tup = Name::new("%0");
        body = Term::Lam {
          tag: Tag::Static,
          nam: Some(tup.clone()),
          bod: Term::Let { pat: pat.clone(), val: Box::new(Term::Var { nam: tup }), nxt: Box::new(body) }
            .into(),
        };
      }
    }
  }
  body
}

fn make_pattern_matching_case(
  book: &mut Book,
  def_type: &[Type],
  def_id: DefId,
  crnt_name: &Name,
  crnt_rules: Vec<usize>,
  match_path: Vec<Pattern>,
) {
  let def = &book.defs[&def_id];
  // This is safe since we check exhaustiveness earlier.
  let fst_rule_idx = crnt_rules[0];
  let fst_rule = &def.rules[fst_rule_idx];
  let crnt_arg_idx = match_path.len();

  // Check if we've reached the end for this subfunction.
  // We did if all the (possibly zero) remaining patterns are variables and not matches.
  let all_args_done = crnt_arg_idx >= fst_rule.arity();
  let is_fst_rule_irrefutable =
    all_args_done || fst_rule.pats[crnt_arg_idx ..].iter().all(|p| matches!(p, Pattern::Var(_)));

  if is_fst_rule_irrefutable {
    // First rule will always be selected, generate leaf case.
    make_leaf_pattern_matching_case(book, def_id, crnt_name, fst_rule_idx, match_path);
  } else {
    let is_adt_case =
      crnt_rules.iter().any(|rule_idx| matches!(def.rules[*rule_idx].pats[crnt_arg_idx], Pattern::Ctr(..)));
    let is_num_case =
      crnt_rules.iter().any(|rule_idx| matches!(def.rules[*rule_idx].pats[crnt_arg_idx], Pattern::Num(..)));
    if is_adt_case {
      // Current arg is pattern matching, encode the pattern matching call
      make_adt_pattern_matching_case(book, def_type, def_id, crnt_name, crnt_rules, match_path);
    } else if is_num_case {
      make_num_pattern_matching_case(book, def_type, def_id, crnt_name, crnt_rules, match_path);
    } else {
      // Current arg is not pattern matching, call next subfunction passing this arg.
      make_non_pattern_matching_case(book, def_type, def_id, crnt_name, crnt_rules, match_path);
    }
  }
}

/// Builds the function calling one of the original rule bodies.
fn make_leaf_pattern_matching_case(
  book: &mut Book,
  def_id: DefId,
  crnt_name: &Name,
  rule_idx: usize,
  match_path: Vec<Pattern>,
) {
  let def_name = book.def_names.name(&def_id).unwrap();
  let rule_def_name = make_rule_name(def_name, rule_idx);
  let rule_def_id = book.def_names.def_id(&rule_def_name).unwrap();
  let rule = &book.defs[&def_id].rules[rule_idx];

  // The term we're building
  let mut term = Term::Ref { def_id: rule_def_id };

  let (num_new_args, num_old_args) = get_pat_arg_count(&match_path);
  let old_args = (0 .. num_old_args).map(|x| Name(format!("x{x}")));
  let new_args = (0 .. num_new_args).map(|x| Name(format!("y{x}")));

  let mut arg_use = old_args.clone().chain(new_args.clone());

  // Add the applications to call the rule body
  term = match_path.iter().zip(&rule.pats).fold(term, |term, (matched, pat)| {
    match (matched, pat) {
      (Pattern::Var(_), Pattern::Var(_)) => Term::arg_call(term, arg_use.next().unwrap()),
      (Pattern::Ctr(_, vars), Pattern::Ctr(_, _)) => {
        vars.iter().fold(term, |term, _| Term::arg_call(term, arg_use.next().unwrap()))
      }
      // This particular rule was not matching on this arg but due to the other rules we had to match on a constructor.
      // So, to call the rule body we have to recreate the constructor.
      // (On scott encoding, if one of the cases is matched we must also match on all the other constructors for this arg)
      (Pattern::Ctr(ctr_nam, vars), Pattern::Var(_)) => {
        let ctr_ref_id = book.def_names.def_id(ctr_nam).unwrap();
        let ctr_args = vars.iter().map(|_| arg_use.next().unwrap());
        let ctr_term = ctr_args.fold(Term::Ref { def_id: ctr_ref_id }, Term::arg_call);
        Term::App { tag: Tag::Static, fun: Box::new(term), arg: Box::new(ctr_term) }
      }
      // As the destructuring of the tuple happens later, we just pass the tuple itself.
      (_, Pattern::Tup(..)) => Term::arg_call(term, arg_use.next().unwrap()),
      (Pattern::Tup(box Pattern::Var(fst), box Pattern::Var(snd)), Pattern::Var(..)) => {
        let fst = if let Some(nam) = fst { Term::Var { nam: nam.clone() } } else { Term::Era };
        let snd = if let Some(nam) = snd { Term::Var { nam: nam.clone() } } else { Term::Era };
        Term::Tup { fst: Box::new(fst), snd: Box::new(snd) }
      }
      (Pattern::Num(MatchNum::Zero), Pattern::Num(MatchNum::Zero)) => {
        arg_use.clone().fold(term, Term::arg_call)
      }
      (Pattern::Num(MatchNum::Succ { .. }), Pattern::Num(MatchNum::Succ { .. })) => {
        arg_use.clone().fold(term, Term::arg_call)
      }
      (Pattern::Var(..), Pattern::Num(..)) => term,
      (Pattern::Ctr(..), _) => unreachable!(),
      (Pattern::Var(_), _) => unreachable!(),
      (Pattern::Num(..), _) => todo!(),
      (Pattern::Tup(..), _) => todo!(),
    }
  });

  // Add the lambdas to get the matched variables
  term = old_args.rev().fold(term, |term, arg| Term::named_lam(arg, term));

  if num_new_args > 0 {
    term = add_tagged_new_args(term, match_path.last().unwrap(), &mut new_args.rev(), book);
  }

  add_case_to_book(book, crnt_name.clone(), term);
}

fn add_tagged_new_args(
  term: Term,
  pat: &Pattern,
  new_args: &mut impl Iterator<Item = Name>,
  book: &Book,
) -> Term {
  fn go(
    mut term: Term,
    pat: &Pattern,
    new_args: &mut impl Iterator<Item = Name>,
    book: &Book,
    tag: Option<String>,
  ) -> Term {
    match pat {
      Pattern::Var(field) => {
        if let Some((var, tag)) = field.clone().zip(tag) {
          let name = Name(format!("{}.{}", tag, var));
          term = Term::tagged_lam(new_args.next().unwrap(), term, Tag::Named(name))
        } else {
          term = Term::named_lam(new_args.next().unwrap(), term);
        }
      }
      Pattern::Ctr(ctr, new) => {
        let adt_name = &book.ctrs[ctr];

        for pattern in new.iter().rev() {
          term = go(term, pattern, new_args, book, Some(format!("{}.{}", adt_name, ctr)));
        }
      }
      Pattern::Num(_) => term = Term::named_lam(new_args.next().unwrap(), term),
      Pattern::Tup(..) => todo!(),
    }

    term
  }

  go(term, pat, new_args, book, None)
}

fn make_num_pattern_matching_case(
  book: &mut Book,
  def_type: &[Type],
  def_id: DefId,
  crnt_name: &Name,
  crnt_rules: Vec<usize>,
  match_path: Vec<Pattern>,
) {
  use MatchNum::*;

  fn filter_rules(def_rules: &[Rule], crnt_rules: &[usize], arg_idx: usize, num: &MatchNum) -> Vec<usize> {
    crnt_rules
      .iter()
      .copied()
      .filter(|&rule_idx| {
        matches!(
          (&def_rules[rule_idx].pats[arg_idx], num),
          (Pattern::Num(Zero), Zero) | (Pattern::Num(Succ { .. }), Succ { .. })
        )
      })
      .collect()
  }

  let make_next_fn_name = |ctr_name: &MatchNum| Name(format!("{crnt_name}$P{ctr_name}"));

  let arms = [Zero, Succ(None)]
    .into_iter()
    .map(|next_ctr| {
      let def = &book.defs[&def_id];
      let crnt_name = make_next_fn_name(&next_ctr);
      let crnt_rules = filter_rules(&def.rules, &crnt_rules, match_path.len(), &next_ctr);
      let new_vars = match next_ctr {
        Zero => Pattern::Num(Zero),
        Succ(_) => Pattern::Num(Succ(Some(Some(Name::new("pred$"))))),
      };
      let mut match_path = match_path.clone();
      match_path.push(new_vars);

      make_pattern_matching_case(book, def_type, def_id, &crnt_name, crnt_rules, match_path);

      let body = Term::Ref { def_id: book.def_names.def_id(&crnt_name).unwrap() };
      (Pattern::Num(next_ctr), body)
    })
    .collect();

  // Detach the pred variable by passing it as a variable of the matched path but not including it in this match expression
  let term = Term::Match { scrutinee: Box::new(Term::Var { nam: Name::new("x") }), arms };
  let term = add_arg_calls(term, &match_path);
  let term = Term::named_lam(Name::new("x"), term);
  let term = add_arg_lams(term, &match_path);

  add_case_to_book(book, crnt_name.clone(), term);
}

/// Builds a function for one of the pattern matches of the original one, as well as the next subfunctions recursively.
/// `(Rule ... (CtrA a0 ... an) ...) = ...`
/// to
/// `(Case) = λy1 .. λyn λx1 ... λxm λx (x Case$CtrA ... Case$CtrN x1 ... xm y1 ... yn)`
fn make_adt_pattern_matching_case(
  book: &mut Book,
  def_type: &[Type],
  def_id: DefId,
  crnt_name: &Name,
  crnt_rules: Vec<usize>,
  match_path: Vec<Pattern>,
) {
  fn filter_rules(def_rules: &[Rule], crnt_rules: &[usize], arg_idx: usize, ctr: &Name) -> Vec<usize> {
    crnt_rules
      .iter()
      .copied()
      .filter(|&rule_idx| match &def_rules[rule_idx].pats[arg_idx] {
        Pattern::Var(_) => true,
        Pattern::Ctr(nam, _) => nam == ctr,
        Pattern::Num(..) => todo!(),
        Pattern::Tup(..) => todo!(),
      })
      .collect()
  }
  let make_next_fn_name = |crnt_name, ctr_name| Name(format!("{crnt_name}$P{ctr_name}"));

  let crnt_arg_idx = match_path.len();
  let Type::Adt(next_type) = &def_type[crnt_arg_idx] else { unreachable!() };
  let next_ctrs = book.adts[next_type].ctrs.clone();
  let make_app =
    |term, arg| Term::App { tag: Tag::Named(next_type.clone()), fun: Box::new(term), arg: Box::new(arg) };

  // First we create the subfunctions
  // TODO: We could group together functions with same arity that map to the same (default) case.
  for (next_ctr, next_ctr_args) in next_ctrs.iter() {
    let def = &book.defs[&def_id];
    let crnt_name = make_next_fn_name(crnt_name, next_ctr);
    let crnt_rules = filter_rules(&def.rules, &crnt_rules, match_path.len(), next_ctr);
    let new_vars = Pattern::Ctr(
      next_ctr.clone(),
      next_ctr_args.iter().cloned().map(|name| Pattern::Var(Some(name))).collect(),
    );
    let mut match_path = match_path.clone();
    match_path.push(new_vars);
    make_pattern_matching_case(book, def_type, def_id, &crnt_name, crnt_rules, match_path);
  }

  // Pattern matching on current argument
  let term = Term::Var { nam: Name::new("x") };
  let term = next_ctrs.keys().fold(term, |term, ctr| {
    let name = make_next_fn_name(crnt_name, ctr);
    let def_id = book.def_names.def_id(&name).unwrap();
    make_app(term, Term::Ref { def_id })
  });

  let term = add_arg_calls(term, &match_path);

  // Lambda for pattern matched value
  let term = Term::named_lam(Name::new("x"), term);

  let term = add_arg_tagged_lams(term, &match_path, &book);

  add_case_to_book(book, crnt_name.clone(), term);
}

/// `(Rule ... y ...) = ...`
/// to
/// `(Case) = λy1 .. λyn λx1 ... λxm λx (NextCase x x1 ... xm y1 .. yn)`
fn make_non_pattern_matching_case(
  book: &mut Book,
  def_type: &[Type],
  def_id: DefId,
  crnt_name: &Name,
  crnt_rules: Vec<usize>,
  match_path: Vec<Pattern>,
) {
  let arg_name = Name::new("x");
  let nxt_def_name = Name(format!("{crnt_name}$P"));

  // Make next function
  let mut next_match_path = match_path.clone();
  next_match_path.push(Pattern::Var(Some(arg_name.clone())));
  make_pattern_matching_case(book, def_type, def_id, &nxt_def_name, crnt_rules, next_match_path);

  // Make call to next function
  let nxt_def_id = book.def_names.def_id(&nxt_def_name).unwrap();
  let term = Term::Ref { def_id: nxt_def_id };
  let term = Term::arg_call(term, arg_name.clone());
  let term = add_arg_calls(term, &match_path);

  // Lambda for pattern matched value
  let term = Term::named_lam(arg_name, term);

  let term = add_arg_lams(term, &match_path);

  add_case_to_book(book, crnt_name.clone(), term);
}

impl Term {
  fn named_lam(nam: Name, bod: Term) -> Term {
    Term::Lam { tag: Tag::Static, nam: Some(nam), bod: Box::new(bod) }
  }

  fn tagged_lam(nam: Name, bod: Term, tag: Tag) -> Term {
    Term::Lam { tag, nam: Some(nam), bod: Box::new(bod) }
  }

  fn arg_call(term: Term, arg: Name) -> Term {
    Term::App { tag: Tag::Static, fun: Box::new(term), arg: Box::new(Term::Var { nam: arg }) }
  }
}

fn add_case_to_book(book: &mut Book, nam: Name, body: Term) {
  if let Some(def_id) = book.def_names.def_id(&nam) {
    book.defs.get_mut(&def_id).unwrap().rules = vec![Rule { pats: vec![], body }];
  } else {
    book.insert_def(nam, vec![Rule { pats: vec![], body }]);
  }
}

// How many old arguments and how many new arguments in the match path
fn get_pat_arg_count(match_path: &[Pattern]) -> (usize, usize) {
  let pat_arg_count = |pat: &Pattern| match pat {
    Pattern::Var(_) => 1,
    Pattern::Ctr(_, vars) => vars.len(),
    Pattern::Num(MatchNum::Zero) => 0,
    Pattern::Num(MatchNum::Succ { .. }) => 1,
    Pattern::Tup(..) => 2,
  };
  if let Some((new_pat, old_pats)) = match_path.split_last() {
    let new_args = pat_arg_count(new_pat);
    let old_args = old_pats.iter().map(pat_arg_count).sum();
    (new_args, old_args)
  } else {
    (0, 0)
  }
}

/// Adds the argument calls to the term, with old args followed by new args.
fn add_arg_calls(term: Term, match_path: &[Pattern]) -> Term {
  let (num_new_args, num_old_args) = get_pat_arg_count(match_path);
  let old_args = (0 .. num_old_args).map(|x| Name(format!("x{x}")));
  let new_args = (0 .. num_new_args).map(|x| Name(format!("y{x}")));
  let args = old_args.chain(new_args);
  args.fold(term, Term::arg_call)
}

// Adds the argument lambdas to the term, with new args followed by old args.
fn add_arg_lams(term: Term, match_path: &[Pattern]) -> Term {
  let (num_new_args, num_old_args) = get_pat_arg_count(match_path);
  let old_args = (0 .. num_old_args).map(|x| Name(format!("x{x}")));
  let new_args = (0 .. num_new_args).map(|x| Name(format!("y{x}")));
  let args = new_args.chain(old_args);
  args.rev().fold(term, |term, arg| Term::named_lam(arg, term))
}

// Adds the argument lambdas to the term, with new args followed by old args.
fn add_arg_tagged_lams(term: Term, match_path: &[Pattern], book: &Book) -> Term {
  let (num_new_args, num_old_args) = get_pat_arg_count(&match_path);
  let old_args = (0 .. num_old_args).map(|x| Name(format!("x{x}")));
  let new_args = (0 .. num_new_args).map(|x| Name(format!("y{x}")));

  let mut term = old_args.rev().fold(term, |term, arg| Term::named_lam(arg, term));

  if num_new_args > 0 {
    term = add_tagged_new_args(term, match_path.last().unwrap(), &mut new_args.rev(), book);
  }

  term
}
