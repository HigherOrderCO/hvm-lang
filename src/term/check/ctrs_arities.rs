use std::collections::HashMap;

use crate::{
  diagnostics::{Diagnostics, ToStringVerbose},
  term::{Book, Ctx, Name, Pattern},
};

pub struct CtrArityMismatchErr {
  ctr_name: Name,
  expected: usize,
  found: usize,
}

impl Ctx<'_> {
  /// Checks if every constructor pattern of every definition rule
  /// has the same arity from the defined adt constructor.
  ///
  /// Constructors should be already resolved.
  pub fn check_ctrs_arities(&mut self) -> Result<(), Diagnostics> {
    self.info.start_pass();

    let arities = self.book.ctr_arities();
    for (def_name, def) in self.book.defs.iter() {
      for rule in def.rules.iter() {
        for pat in rule.pats.iter() {
          let res = pat.check_ctrs_arities(&arities);
          self.info.take_rule_err(res, def_name.clone());
        }
      }
    }

    self.info.fatal(())
  }
}

impl Book {
  /// Returns a hashmap of the constructor name to its arity.
  pub fn ctr_arities(&self) -> HashMap<Name, usize> {
    let mut arities = HashMap::new();

    for adt in self.adts.values() {
      for (ctr_name, fields) in adt.ctrs.iter() {
        arities.insert(ctr_name.clone(), fields.len());
      }
    }

    arities
  }
}

impl Pattern {
  fn check_ctrs_arities(&self, arities: &HashMap<Name, usize>) -> Result<(), CtrArityMismatchErr> {
    let mut to_check = vec![self];

    while let Some(pat) = to_check.pop() {
      if let Pattern::Ctr(ctr_name, args) = pat {
        let expected = arities.get(ctr_name).unwrap();
        let found = args.len();
        if *expected != found {
          return Err(CtrArityMismatchErr { ctr_name: ctr_name.clone(), found, expected: *expected });
        }
      }
      for child in pat.children() {
        to_check.push(child);
      }
    }
    Ok(())
  }
}

impl ToStringVerbose for CtrArityMismatchErr {
  fn to_string_verbose(&self, _verbose: bool) -> String {
    format!(
      "Constructor arity mismatch in pattern matching. Constructor '{}' expects {} fields, found {}.",
      self.ctr_name, self.expected, self.found
    )
  }
}
