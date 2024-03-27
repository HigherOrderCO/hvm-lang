use crate::{
  diagnostics::Diagnostics,
  term::{Ctx, Pattern, Rule, Term},
};

impl Ctx<'_> {
  /// Applies the arguments to the program being run by applying them to the main function.
  ///
  /// Example:
  /// ```hvm
  /// main x1 x2 x3 = (MainBody x1 x2 x3)
  /// ```
  /// Calling with `hvml run <file> arg1 arg2 arg3`, it becomes:
  /// ```hvm
  /// main = (λx1 λx2 λx3 (MainBody x1 x2 x3) arg1 arg2 arg3)
  /// ```
  pub fn apply_args(&mut self, args: Option<Vec<Term>>) -> Result<(), Diagnostics> {
    self.info.start_pass();

    if let Some(entrypoint) = &self.book.entrypoint {
      let main_def = &mut self.book.defs[entrypoint];

      // Since we fatal error, no need to exit early
      let n_rules = main_def.rules.len();
      if n_rules != 1 {
        self.info.add_rule_error(
          format!("Expected the entrypoint function to have only one rule, found {n_rules}."),
          entrypoint.clone(),
        );
      }

      let mut main_body = std::mem::take(&mut main_def.rules[0].body);

      for pat in main_def.rules[0].pats.iter().rev() {
        if let Pattern::Var(var) = pat {
          main_body = Term::lam(var.clone(), main_body);
        } else {
          self.info.add_rule_error(
            format!("Expected the entrypoint function to only have variable patterns, found '{pat}'."),
            entrypoint.clone(),
          );
        }
      }

      if let Some(args) = args {
        main_body = Term::call(main_body, args);
      }

      main_def.rules = vec![Rule { pats: vec![], body: main_body }];
    }

    self.info.fatal(())
  }
}
