use crate::term::{Book, DefId, Definition, Name, Pattern};
use core::fmt;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
  Any,
  Tup,
  Num,
  Sup,
  Adt(Name),
}

pub type DefinitionTypes = HashMap<DefId, Vec<Type>>;

impl Book {
  /// Returns a HashMap from the definition id to the inferred pattern types
  /// and checks the rules arities based on the first rule arity.
  /// Expects patterns to be flattened.
  pub fn infer_def_types(&self) -> Result<DefinitionTypes, String> {
    let mut def_types = HashMap::new();
    for (def_id, def) in &self.defs {
      let def_type = def.infer_type(&self.ctrs)?;
      def_types.insert(def_id.clone(), def_type);
    }
    Ok(def_types)
  }
}

impl Definition {
  pub fn infer_type(&self, ctrs: &HashMap<Name, Name>) -> Result<Vec<Type>, String> {
    let mut arg_types = vec![];

    for arg_idx in 0 .. self.arity() {
      let pats = self.rules.iter().map(|r| &r.pats[arg_idx]);
      arg_types.push(infer_arg_type(pats, ctrs)?);
    }
    Ok(arg_types)
  }
}

pub fn infer_arg_type<'a>(
  pats: impl Iterator<Item = &'a Pattern>,
  ctrs: &HashMap<Name, Name>,
) -> Result<Type, String> {
  let mut arg_type = Type::Any;
  for pat in pats {
    let pat_type = match pat {
      Pattern::Var { .. } => Type::Any,
      Pattern::Ctr(ctr_nam, _) => {
        if let Some(adt_nam) = ctrs.get(ctr_nam) {
          Type::Adt(adt_nam.clone())
        } else {
          return Err(format!("Unknown constructor '{ctr_nam}'"));
        }
      }
      Pattern::Tup { .. } => Type::Tup,
      Pattern::Dup { .. } => Type::Sup,
      Pattern::Num { .. } => Type::Num,
    };
    unify(pat_type, &mut arg_type)?
  }
  Ok(arg_type)
}

fn unify(new: Type, old: &mut Type) -> Result<(), String> {
  match (new, &old) {
    (Type::Adt(new), Type::Adt(old)) if &new != old => {
      return Err(format!("Type mismatch. Found '{}' expected {}.", new, old));
    }
    (new, Type::Any) => *old = new,
    _ => (),
  };
  Ok(())
}

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Type::Any => write!(f, "any"),
      Type::Tup => write!(f, "tup"),
      Type::Num => write!(f, "num"),
      Type::Sup => write!(f, "sup"),
      Type::Adt(nam) => write!(f, "{nam}"),
    }
  }
}

impl Book {
  pub fn check_arity(&self) -> Result<(), String> {
    for def in self.defs.values() {
      def.check_arity()?;
    }
    Ok(())
  }
}

impl Definition {
  pub fn check_arity(&self) -> Result<(), String> {
    let expected_arity = self.arity();
    for rule in &self.rules {
      if rule.arity() != expected_arity {
        return Err("Arity error.".to_string());
      }
    }
    Ok(())
  }
}
