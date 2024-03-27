use crate::term::{Book, Name, Pattern};

impl Book {
  /// Resolve Constructor names inside rule patterns and match patterns,
  /// converting `Pattern::Var(Some(nam))` into `Pattern::Ctr(nam, vec![])`
  /// when the name is that of a constructor.
  ///
  /// When parsing a rule we don't have all the constructors yet, so no way to
  /// know if a particular name belongs to a constructor or is a matched variable.
  /// Therefore we must do it later, here.
  pub fn resolve_ctrs_in_pats(&mut self) {
    let is_ctr = |nam: &Name| self.ctrs.contains_key(nam);
    for def in self.defs.values_mut() {
      for rule in &mut def.rules {
        for pat in &mut rule.pats {
          pat.resolve_ctrs(&is_ctr);
        }
      }
    }
  }
}

impl Pattern {
  pub fn resolve_ctrs(&mut self, is_ctr: &impl Fn(&Name) -> bool) {
    let mut to_resolve = vec![self];

    while let Some(pat) = to_resolve.pop() {
      if let Pattern::Var(Some(nam)) = pat {
        if is_ctr(nam) {
          *pat = Pattern::Ctr(nam.clone(), vec![]);
        }
      }

      to_resolve.extend(pat.children_mut());
    }
  }
}
