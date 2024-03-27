use std::collections::VecDeque;

use crate::{
  diagnostics::ToStringVerbose,
  term::{Adt, AdtEncoding, Book, Name, Tag, Term},
};

pub enum AdtReadbackError {
  MalformedCtr(Name),
  MalformedMatch(Name),
  UnexpectedTag(Tag, Tag),
}

impl Term {
  pub fn resugar_adts(&mut self, book: &Book, adt_encoding: AdtEncoding) -> Vec<AdtReadbackError> {
    let mut errs = Default::default();
    match adt_encoding {
      // No way of resugaring simple scott encoded terms.
      AdtEncoding::Scott => (),
      AdtEncoding::TaggedScott => self.resugar_tagged_scott(book, &mut errs),
    };
    errs
  }

  fn resugar_tagged_scott(&mut self, book: &Book, errs: &mut Vec<AdtReadbackError>) {
    Term::recursive_call(move || match self {
      Term::Lam { tag: Tag::Named(adt_name), bod, .. } | Term::Chn { tag: Tag::Named(adt_name), bod, .. } => {
        if let Some((adt_name, adt)) = book.adts.get_key_value(adt_name) {
          self.resugar_ctr_tagged_scott(book, adt, adt_name, errs);
        } else {
          bod.resugar_tagged_scott(book, errs);
        }
      }

      Term::App { tag: Tag::Named(adt_name), fun, arg } => {
        if let Some((adt_name, adt)) = book.adts.get_key_value(adt_name) {
          self.resugar_match_tagged_scott(book, adt_name, adt, errs);
        } else {
          fun.resugar_tagged_scott(book, errs);
          arg.resugar_tagged_scott(book, errs);
        }
      }

      _ => {
        for child in self.children_mut() {
          child.resugar_tagged_scott(book, errs);
        }
      }
    })
  }

  /// Reconstructs adt-tagged lambdas as their constructors
  ///
  /// # Example
  ///
  /// ```hvm
  /// data Option = (Some val) | None
  ///
  /// // This value:
  /// (Some (Some None))
  ///
  /// // Gives the following readback:
  /// #Option λa #Option λ* #Option (a #Option λb #Option λ* #Option (b #Option λ* #Option λc c))
  ///
  /// // Which gets resugared as:
  /// (Some (Some None))
  /// ```
  fn resugar_ctr_tagged_scott(
    &mut self,
    book: &Book,
    adt: &Adt,
    adt_name: &Name,
    errs: &mut Vec<AdtReadbackError>,
  ) {
    let mut app = &mut *self;
    let mut current_arm = None;

    // One lambda per ctr of this adt
    for ctr in &adt.ctrs {
      match app {
        Term::Lam { tag: Tag::Named(tag), nam, bod } if tag == adt_name => {
          if let Some(nam) = nam {
            if current_arm.is_some() {
              errs.push(AdtReadbackError::MalformedCtr(adt_name.clone()));
              return;
            }
            current_arm = Some((nam.clone(), ctr));
          }
          app = bod;
        }
        _ => {
          errs.push(AdtReadbackError::MalformedCtr(adt_name.clone()));
          return;
        }
      }
    }

    let Some((arm_name, (ctr, ctr_args))) = current_arm else {
      errs.push(AdtReadbackError::MalformedCtr(adt_name.clone()));
      return;
    };

    let mut cur = &mut *app;

    // One app per field of this constructor
    for _ in ctr_args.iter().rev() {
      let expected_tag = Tag::adt_name(adt_name);

      match cur {
        Term::App { tag, .. } if tag == &expected_tag => {
          let Term::App { tag, fun, .. } = cur else { unreachable!() };
          *tag = Tag::Static;
          cur = fun.as_mut();
        }
        Term::App { tag, .. } => {
          errs.push(AdtReadbackError::UnexpectedTag(expected_tag, tag.clone()));
          return;
        }
        _ => {
          errs.push(AdtReadbackError::MalformedCtr(adt_name.clone()));
          return;
        }
      }
    }

    match cur {
      Term::Var { nam } if nam == &arm_name => {}
      _ => {
        errs.push(AdtReadbackError::MalformedCtr(adt_name.clone()));
        return;
      }
    }

    *cur = Term::r#ref(ctr);
    *self = std::mem::take(app);

    self.resugar_tagged_scott(book, errs);
  }

  /// Reconstructs adt-tagged applications as a match term
  ///
  /// # Example
  ///
  /// ```hvm
  /// data Option = (Some val) | None
  ///
  /// // Compiling this match expression:
  /// Option.and = @a @b match a {
  ///   Some: match b {
  ///     Some: 1
  ///     None: 2
  ///   }
  ///   None: 3
  /// }
  ///
  /// // Gives the following readback:
  /// λa λb (#Option (a #Option λ* λc #Option (c #Option λ* 1 2) λ* 3) b)
  ///
  /// // Which gets resugared as:
  /// λa λb (match a {
  ///   Some: λc match c {
  ///     Some: 1;
  ///     None: 2
  ///   };
  ///   None: λ* 3
  /// } b)
  /// ```
  fn resugar_match_tagged_scott(
    &mut self,
    book: &Book,
    adt_name: &Name,
    adt: &Adt,
    errs: &mut Vec<AdtReadbackError>,
  ) {
    // TODO: This is too complex, refactor this.

    let mut cur = &mut *self;
    let mut arms = VecDeque::new();
    // Since we don't have access to the match arg when first reading
    // the arms, we must store the position of the fields that have
    // to be applied to the arm body.
    let expected_tag = Tag::adt_name(adt_name);

    // For each match arm, we expect an application where the arm body is the app arg.
    // If matching a constructor with N fields, the body should start with N tagged lambdas.
    for (ctr, ctr_args) in adt.ctrs.iter().rev() {
      match cur {
        Term::App { tag: Tag::Named(tag), fun, arg } if tag == adt_name => {
          // We expect a lambda for each field. If we got anything
          // else, we have to create an eta-reducible match to get
          // the same behaviour.
          let mut has_all_fields = true;
          let mut fields = Vec::new();
          let mut arm = arg.as_mut();
          for _ in ctr_args.iter() {
            match arm {
              Term::Lam { tag, .. } if tag == &expected_tag => {
                let Term::Lam { nam, bod, .. } = arm else { unreachable!() };
                fields.push(nam.clone());
                arm = bod;
              }

              Term::Lam { tag, .. } => {
                errs.push(AdtReadbackError::UnexpectedTag(expected_tag.clone(), tag.clone()));
                has_all_fields = false;
                break;
              }
              _ => {
                has_all_fields = false;
                break;
              }
            }
          }

          if has_all_fields {
            arm.resugar_tagged_scott(book, errs);
            arms.push_front((Some(ctr.clone()), fields, std::mem::take(arm)));
          } else {
            // If we didn't find lambdas for all the fields, create the eta-reducible match.
            arg.resugar_tagged_scott(book, errs);
            let fields = ctr_args.iter().map(|f| Name::new(format!("%{f}")));
            let applied_arm = Term::tagged_call(
              expected_tag.clone(),
              std::mem::take(arg.as_mut()),
              fields.clone().map(|f| Term::Var { nam: f }),
            );
            arms.push_front((Some(ctr.clone()), fields.map(Some).collect(), applied_arm));
          }

          cur = &mut *fun;
        }
        _ => {
          // Looked like a match but doesn't cover all constructors.
          errs.push(AdtReadbackError::MalformedMatch(adt_name.clone()));
          return;
        }
      }
    }

    // Resugar the argument.
    cur.resugar_tagged_scott(book, errs);

    // If the match is on a non-var we have to extract it to get usable ctr fields.
    // Here we get the arg name and separate the term if it's not a variable.
    let (arg, bind) = if let Term::Var { nam } = cur {
      (nam.clone(), None)
    } else {
      (Name::from("%matched"), Some(std::mem::take(cur)))
    };

    // Subst the unique readback names for the field names.
    // ex: reading `@a(a @b@c(b c))` we create `@a match a{A: (a.field1 a.field2)}`,
    // changing `b` to `a.field1` and `c` to `a.field2`.
    for (ctr, fields, body) in arms.iter_mut() {
      let mut new_fields = vec![];
      for (field_idx, field) in fields.iter().enumerate() {
        if let Some(old_field) = field {
          let field_name = &adt.ctrs[ctr.as_ref().unwrap()][field_idx];
          let new_field = Name::new(format!("{arg}.{field_name}"));
          new_fields.push(Some(new_field.clone()));
          body.subst(old_field, &Term::Var { nam: new_field });
        }
      }
      *fields = new_fields;
    }

    let arms = arms.into_iter().collect::<Vec<_>>();

    *self = if let Some(bind) = bind {
      Term::Let {
        nam: Some(arg.clone()),
        val: Box::new(bind),
        nxt: Box::new(Term::Mat { arg: Box::new(Term::Var { nam: arg }), rules: arms }),
      }
    } else {
      Term::Mat { arg: Box::new(Term::Var { nam: arg }), rules: arms }
    };
  }
}

impl ToStringVerbose for AdtReadbackError {
  fn to_string_verbose(&self, _verbose: bool) -> String {
    match self {
      AdtReadbackError::MalformedCtr(adt) => format!("Encountered malformed constructor of type '{adt}'."),
      AdtReadbackError::MalformedMatch(adt) => {
        format!("Encountered malformed 'match' expression of type '{adt}'")
      }
      AdtReadbackError::UnexpectedTag(expected, found) => {
        let found = if let Tag::Static = found { "no tag".to_string() } else { format!("'{found}'") };
        format!("Unexpected tag found during Adt readback, expected '{}', but found {}.", expected, found)
      }
    }
  }
}
