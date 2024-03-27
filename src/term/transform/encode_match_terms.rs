use crate::term::{AdtEncoding, Book, Constructors, Name, NumCtr, Tag, Term};

impl Book {
  /// Encodes pattern matching expressions in the book into their
  /// native/core form. Must be run after [`Ctr::fix_match_terms`].
  ///
  /// ADT matches are encoded based on `adt_encoding`.
  ///
  /// Num matches are encoded as a sequence of native num matches (on 0 and 1+).
  ///
  /// Var and pair matches become a let expression.
  pub fn encode_matches(&mut self, adt_encoding: AdtEncoding) {
    for def in self.defs.values_mut() {
      for rule in &mut def.rules {
        rule.body.encode_matches(&self.ctrs, adt_encoding);
      }
    }
  }
}

impl Term {
  pub fn encode_matches(&mut self, ctrs: &Constructors, adt_encoding: AdtEncoding) {
    Term::recursive_call(move || {
      for child in self.children_mut() {
        child.encode_matches(ctrs, adt_encoding)
      }

      if let Term::Mat { arg, rules } = self {
        let arg = std::mem::take(arg.as_mut());
        let rules = std::mem::take(rules);
        *self = encode_match(arg, rules, ctrs, adt_encoding);
      } else if let Term::Swt { arg, rules } = self {
        let arg = std::mem::take(arg.as_mut());
        let rules = std::mem::take(rules);
        *self = encode_switch(arg, rules);
      }
    })
  }
}

fn encode_match(
  arg: Term,
  rules: Vec<(Option<Name>, Vec<Option<Name>>, Term)>,
  ctrs: &Constructors,
  adt_encoding: AdtEncoding,
) -> Term {
  let adt = ctrs.get(rules[0].0.as_ref().unwrap()).unwrap();

  // ADT Encoding depends on compiler option
  match adt_encoding {
    // (x @field1 @field2 ... body1  @field1 body2 ...)
    AdtEncoding::Scott => {
      let mut arms = vec![];
      for rule in rules {
        let body = rule.1.iter().cloned().rfold(rule.2, |bod, nam| Term::lam(nam, bod));
        arms.push(body);
      }
      Term::call(arg, arms)
    }
    // #adt_name(x arm[0] arm[1] ...)
    AdtEncoding::TaggedScott => {
      let mut arms = vec![];
      for rule in rules.into_iter() {
        let body =
          rule.1.iter().cloned().rfold(rule.2, |bod, nam| Term::tagged_lam(Tag::adt_name(adt), nam, bod));
        arms.push(body);
      }
      Term::tagged_call(Tag::adt_name(adt), arg, arms)
    }
  }
}

/// Convert into a sequence of native matches, decrementing by 1 each match.
/// match n {0: A; 1: B; 2+: (C n-2)} converted to
/// match n {0: A; 1+: @%x match %x {0: B; 1+: @n-2 (C n-2)}}
fn encode_switch(arg: Term, mut rules: Vec<(NumCtr, Term)>) -> Term {
  let last_rule = rules.pop().unwrap();

  let match_var = Name::from("%x");

  // @n-2 (C n-2)
  let NumCtr::Succ(last_var) = last_rule.0 else { unreachable!() };
  let last_arm = Term::lam(last_var, last_rule.1);

  rules.into_iter().rfold(last_arm, |term, rule| {
    let zero = (NumCtr::Num(0), rule.1);
    let one = (NumCtr::Succ(None), term);
    let rules = vec![zero, one];

    let NumCtr::Num(num) = rule.0 else { unreachable!() };
    if num == 0 {
      Term::Swt { arg: Box::new(arg.clone()), rules }
    } else {
      let swt = Term::Swt { arg: Box::new(Term::Var { nam: match_var.clone() }), rules };
      Term::named_lam(match_var.clone(), swt)
    }
  })
}

/* /// Convert into a sequence of native matches on (- n num_case)
/// match n {a: A; b: B; n: (C n)} converted to
/// match (- n a) {0: A; 1+: @%p match (- %p b-a-1) { 0: B; 1+: @%p let n = (+ %p b+1); (C n)}}
fn encode_num(arg: Term, mut rules: Vec<Rule>) -> Term {
  fn go(
    mut rules: impl Iterator<Item = Rule>,
    last_rule: Rule,
    prev_num: Option<u64>,
    arg: Option<Term>,
  ) -> Term {
    let rule = rules.next();
    match (prev_num, rule) {
      // Num matches must have at least 2 rules (1 num and 1 var).
      // The first rule can't also be the last.
      (None, None) => unreachable!(),
      // First match
      // match (- n a) {0: A; 1+: ...}
      (None, Some(rule)) => {
        let Pattern::Num(NumCtr::Num(val)) = &rule.pats[0] else { unreachable!() };
        Term::switch(
          Term::sub_num(arg.unwrap(), *val),
          rule.body,
          go(rules, last_rule, Some(*val), None),
          None,
        )
      }
      // Middle match
      // @%p match (- %p b-a-1) { 0: B; 1+: ... }
      (Some(prev_num), Some(rule)) => {
        let Pattern::Num(NumCtr::Num(val)) = &rule.pats[0] else { unreachable!() };
        let pred_nam = Name::from("%p");
        Term::named_lam(
          pred_nam.clone(),
          Term::switch(
            Term::sub_num(Term::Var { nam: pred_nam }, val.wrapping_sub(prev_num).wrapping_sub(1)),
            rule.body,
            go(rules, last_rule, Some(*val), None),
            None,
          ),
        )
      }
      // Last match
      // @%p let n = (+ %p b+1); (C n)
      (Some(prev_num), None) => {
        let pred_nam = Name::from("%p");
        Term::named_lam(pred_nam.clone(), Term::Let {
          pat: last_rule.pats.into_iter().next().unwrap(),
          val: Box::new(Term::add_num(Term::Var { nam: pred_nam }, prev_num.wrapping_add(1))),
          nxt: Box::new(last_rule.body),
        })
      }
    }
  }

  let last_rule = rules.pop().unwrap();
  go(rules.into_iter(), last_rule, None, Some(arg))
}
 */
