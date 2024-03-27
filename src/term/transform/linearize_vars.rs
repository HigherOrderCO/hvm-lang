use crate::term::{Book, Name, Tag, Term};
use std::collections::HashMap;

/// Erases variables that weren't used, dups the ones that were used more than once.
/// Substitutes lets into their variable use.
/// In details:
/// For all var declarations:
///   If they're used 0 times: erase the declaration
///   If they're used 1 time: leave them as-is
///   If they're used more times: insert dups to make var use affine
/// For all let vars:
///   If they're used 0 times: Discard the let
///   If they're used 1 time: substitute the body in the var use
///   If they're use more times: add dups for all the uses, put the let body at the root dup.
/// Precondition: All variables are bound and have unique names within each definition.
impl Book {
  pub fn linearize_vars(&mut self) {
    for def in self.defs.values_mut() {
      def.rule_mut().body.linearize_vars();
    }
  }
}

impl Term {
  pub fn linearize_vars(&mut self) {
    term_to_affine(self, &mut HashMap::new());
  }

  /// Returns false whether the term has no unscoped terms,
  /// or all its unscoped binds and usage pairs are within the term.
  fn has_unscoped(&self) -> bool {
    let (decl, uses) = self.unscoped_vars();
    decl.symmetric_difference(&uses).count() > 0
  }
}

fn term_to_affine(term: &mut Term, var_uses: &mut HashMap<Name, u64>) {
  Term::recursive_call(move || match term {
    Term::Let { nam: Some(nam), val, nxt } => {
      // TODO: This is swapping the order of how the bindings are
      // used, since it's not following the usual AST order (first
      // val, then nxt). Doesn't change behaviour, but looks strange.
      term_to_affine(nxt, var_uses);

      match get_var_uses(Some(nam), var_uses) {
        0 => {
          if val.has_unscoped() {
            term_to_affine(val, var_uses);

            let Term::Let { val, nxt, .. } = term else { unreachable!() };
            let val = std::mem::take(val);
            let nxt = std::mem::take(nxt);

            *term = Term::Let { nam: None, val, nxt };
          } else {
            *term = std::mem::take(nxt.as_mut());
          }
        }
        1 => {
          term_to_affine(val, var_uses);
          nxt.subst(nam, val.as_ref());
          *term = std::mem::take(nxt.as_mut());
        }
        instantiated_count => {
          term_to_affine(val, var_uses);
          duplicate_term(nam, nxt, instantiated_count, Some(val));
          *term = std::mem::take(nxt.as_mut());
        }
      }
    }

    Term::Let { nam: None, val, nxt } => {
      term_to_affine(nxt, var_uses);

      if val.has_unscoped() {
        term_to_affine(val, var_uses);
      } else {
        let Term::Let { nxt, .. } = term else { unreachable!() };
        let nxt = std::mem::take(nxt.as_mut());
        *term = nxt;
      }
    }

    Term::Var { nam } => {
      let instantiated_count = var_uses.entry(nam.clone()).or_default();
      *instantiated_count += 1;
      *nam = dup_name(nam, *instantiated_count);
    }

    _ => {
      for (child, binds) in term.children_mut_with_binds_mut() {
        term_to_affine(child, var_uses);

        for bind in binds {
          let uses = get_var_uses(bind.as_ref(), var_uses);
          match uses {
            // Erase binding
            0 => *bind = None,
            // Keep as-is
            1 => (),
            // Duplicate binding
            uses => duplicate_term(bind.as_ref().unwrap(), child, uses, None),
          }
        }
      }
    }
  })
}

fn get_var_uses(nam: Option<&Name>, var_uses: &HashMap<Name, u64>) -> u64 {
  nam.and_then(|nam| var_uses.get(nam).copied()).unwrap_or_default()
}

/// Creates the duplication bindings for variables used multiple times.
///
/// Example:
///
/// `@x (x x x x)` becomes `@x let {x0 x1 x2 x3} = x; (x0 x1 x2 x3)`.
///
/// `let x = @y y; (x x x)` becomes `let {x0 x1 x2} = @y y; (x0 x1 x2)`.
fn duplicate_term(nam: &Name, nxt: &mut Term, uses: u64, dup_body: Option<&mut Term>) {
  debug_assert!(uses > 1);

  *nxt = Term::Dup {
    tag: Tag::Auto,
    bnd: (1 .. uses + 1).map(|i| Some(dup_name(nam, i))).collect(),
    val: Box::new(dup_body.map_or_else(|| Term::Var { nam: nam.clone() }, std::mem::take)),
    nxt: Box::new(std::mem::take(nxt)),
  }
}

fn dup_name(nam: &Name, uses: u64) -> Name {
  if uses == 1 { nam.clone() } else { Name::new(format!("{nam}_{uses}")) }
}
