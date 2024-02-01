use hvmc::ast::num_to_str;
use indexmap::IndexMap;
use itertools::Itertools;
use shrinkwraprs::Shrinkwrap;
use std::collections::{BTreeMap, HashMap};

pub mod check;
pub mod display;
pub mod encoder;
pub mod load_book;
pub mod parser;
pub mod readback;
pub mod transform;

/// The representation of a program.
#[derive(Debug, Clone, Default)]
pub struct Book {
  /// Mapping of definition names to ids.
  pub def_names: DefNames,

  /// The function definitions.
  pub defs: BTreeMap<DefId, Definition>,

  /// The algebraic datatypes defined by the program
  pub adts: BTreeMap<Name, Adt>,

  /// To which type does each constructor belong to.
  pub ctrs: HashMap<Name, Name>,
}

#[derive(Debug)]
pub enum ReadbackError {
  InvalidNumericMatch,
  ReachedRoot,
  Cyclic,
  InvalidBind,
  InvalidAdt,
  InvalidAdtMatch,
  InvalidStrTerm,
}

#[derive(Debug, Clone, Default)]
pub struct DefNames {
  id_to_name: HashMap<DefId, Name>,
  name_to_id: HashMap<Name, DefId>,
  id_count: u32,
}

/// A pattern matching function definition.
#[derive(Debug, Clone)]
pub struct Definition {
  pub def_id: DefId,
  pub rules: Vec<Rule>,
}

/// A pattern matching rule of a definition.
#[derive(Debug, Clone)]
pub struct Rule {
  pub pats: Vec<Pattern>,
  pub body: Term,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchNum {
  Zero,
  Succ(Box<Pattern>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tag {
  Named(Name),
  Numeric(u32),
  Auto,
  Static,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum Term {
  /// Like a scopeless lambda, where the variable can occur outside the body
  Chn {
    tag: Tag,
    nam: Name,
    bod: Box<Term>,
  },
  /// The use of a Channel variable.
  Lnk {
    nam: Name,
  },
  Sup {
    tag: Tag,
    fst: Box<Term>,
    snd: Box<Term>,
  },
  App {
    tag: Tag,
    fun: Box<Term>,
    arg: Box<Term>,
  },
  Let {
    pat: Pattern,
    val: Box<Term>,
    nxt: Box<Term>,
  },

  Var {
    nam: Name,
  },
  Lam {
    tag: Tag,
    pat: Box<Pattern>,
    bod: Box<Term>,
  },
  Tup {
    fst: Box<Term>,
    snd: Box<Term>,
  },

  Num {
    val: u64,
  },
  Str {
    val: String,
  },
  /// A numeric operation between built-in numbers.
  Opx {
    op: Op,
    fst: Box<Term>,
    snd: Box<Term>,
  },
  Match {
    scrutinee: Box<Term>,
    arms: Vec<(Pattern, Term)>,
  },
  Ref {
    def_id: DefId,
  },
  #[default]
  Era,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
  Lnk {
    nam: Name,
  },
  Var {
    nam: Name,
  },
  Ctr {
    nam: Name,
    args: Vec<Pattern>,
  },
  Num {
    mat: MatchNum,
  },
  Tup {
    fst: Box<Pattern>,
    snd: Box<Pattern>,
  },
  Sup {
    tag: Tag,
    fst: Box<Pattern>,
    snd: Box<Pattern>,
  },
  /// Implicit variable.
  Implicit,
  Era,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
  ADD,
  SUB,
  MUL,
  DIV,
  MOD,
  EQ,
  NE,
  LT,
  GT,
  LTE,
  GTE,
  AND,
  OR,
  XOR,
  LSH,
  RSH,
  NOT,
}

/// A user defined  datatype
#[derive(Debug, Clone, Default)]
pub struct Adt {
  pub ctrs: IndexMap<Name, Vec<Name>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Shrinkwrap, Hash, PartialOrd, Ord, Default)]
pub struct Name(pub String);

#[derive(Debug, PartialEq, Eq, Clone, Shrinkwrap, Hash, PartialOrd, Ord, Default)]
pub struct DefId(pub String);

impl Name {
  pub fn new(value: &str) -> Self {
    Name(value.to_string())
  }
  pub fn from_num(value: u64) -> Self {
    Self(num_to_str(value as usize))
  }
}

impl Tag {
  pub fn string() -> Self {
    Self::Named(Name::new("String"))
  }

  pub fn string_scons_head() -> Self {
    Self::Named(Name::new("String.SCons.head"))
  }
}

impl Book {
  pub fn new() -> Self {
    Default::default()
  }

  pub fn insert_def(&mut self, name: Name, rules: Vec<Rule>) -> DefId {
    let def_id = self.def_names.insert(name);
    let def = Definition { def_id: def_id.clone(), rules };
    self.defs.insert(def_id.clone(), def);
    def_id
  }

  pub fn remove_def(&mut self, def_id: DefId) -> Option<(Name, Definition)> {
    let def = self.defs.remove(&def_id);
    let name = self.def_names.remove(def_id);
    name.zip(def)
  }
}

impl DefNames {
  pub const ENTRY_POINT: &'static str = "main";
  pub const HVM1_ENTRY_POINT: &'static str = "Main";

  pub fn new() -> Self {
    Default::default()
  }

  pub fn name(&self, def_id: &DefId) -> Option<&Name> {
    if def_id.0 == Self::ENTRY_POINT
      && self.id_to_name.contains_key(&DefId(String::from(Self::HVM1_ENTRY_POINT)))
    {
      self.id_to_name.get(&DefId(String::from(Self::HVM1_ENTRY_POINT)))
    } else {
      self.id_to_name.get(def_id)
    }
  }

  pub fn def_id(&self, name: &Name) -> Option<DefId> {
    self.name_to_id.get(name).cloned()
  }

  pub fn contains_name(&self, name: &Name) -> bool {
    self.name_to_id.contains_key(name)
  }

  pub fn contains_def_id(&self, def_id: &DefId) -> bool {
    self.id_to_name.contains_key(def_id)
  }

  pub fn insert(&mut self, name: Name) -> DefId {
    let def_id = DefId(self.make_unique(&name));
    self.id_count += 1;
    self.id_to_name.insert(def_id.clone(), name.clone());
    self.name_to_id.insert(name, def_id.clone());
    def_id
  }

  pub fn remove(&mut self, def_id: DefId) -> Option<Name> {
    let nam = self.id_to_name.remove(&def_id);
    if let Some(nam) = &nam {
      self.name_to_id.remove(nam);
    }
    nam
  }

  pub fn names(&self) -> impl Iterator<Item = &Name> {
    self.name_to_id.keys()
  }

  pub fn def_ids(&self) -> impl Iterator<Item = &DefId> {
    self.id_to_name.keys()
  }

  pub fn make_unique(&mut self, name: &Name) -> String {
    if !self.contains_name(name) {
      return name.clone().0;
    }
    let id = 0;
    loop {
      let new_name = Name(format!("{name}_{id}"));
      if !self.contains_name(&new_name) {
        return new_name.0;
      }
    }
  }
}

impl Term {
  /// Make a call term by folding args around a called function term with applications.
  pub fn call(called: Term, args: impl IntoIterator<Item = Term>) -> Self {
    args.into_iter().fold(called, |acc, arg| Term::App {
      tag: Tag::Static,
      fun: Box::new(acc),
      arg: Box::new(arg),
    })
  }

  /// Substitute the occurences of a non-scopeless variable in a term with the given term.
  pub fn subst(&mut self, from: &Name, to: &Term) {
    match self {
      Term::Lam { bod, pat, .. } => {
        if !pat.bound_names().contains(from) {
          bod.subst(from, to)
        }
      }
      Term::Var { nam } if nam == from => *self = to.clone(),
      Term::Var { .. } => (),
      // Only substitute scoped variables.
      Term::Chn { bod, .. } => bod.subst(from, to),
      Term::Lnk { .. } => (),
      Term::Let { pat, val, nxt } => {
        val.subst(from, to);
        if !pat.occurs(from) {
          nxt.subst(from, to);
        }
      }
      Term::Match { scrutinee, arms } => {
        scrutinee.subst(from, to);

        for (rule, term) in arms {
          if !rule.bound_names().contains(from) {
            term.subst(from, to);
          }
        }
      }
      Term::App { fun: fst, arg: snd, .. }
      | Term::Sup { fst, snd, .. }
      | Term::Tup { fst, snd }
      | Term::Opx { fst, snd, .. } => {
        fst.subst(from, to);
        snd.subst(from, to);
      }
      Term::Ref { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => (),
    }
  }

  /// Collects all the free variables that a term has
  /// and the number of times each var is used
  pub fn free_vars(&self) -> IndexMap<Name, u64> {
    fn go(term: &Term, free_vars: &mut IndexMap<Name, u64>) {
      match term {
        Term::Lam { pat, bod, .. } => {
          let mut new_scope = IndexMap::new();
          go(bod, &mut new_scope);
          for i in pat.bound_names() {
            new_scope.remove(i);
          }

          free_vars.extend(new_scope);
        }
        Term::Var { nam } => *free_vars.entry(nam.clone()).or_default() += 1,
        Term::Chn { bod, .. } => go(bod, free_vars),
        Term::Lnk { .. } => {}
        Term::Let { pat, val, nxt } => {
          go(val, free_vars);

          let mut new_scope = IndexMap::new();
          go(nxt, &mut new_scope);

          for bind in pat.bound_names() {
            new_scope.remove(bind);
          }

          free_vars.extend(new_scope);
        }
        Term::App { fun: fst, arg: snd, .. }
        | Term::Tup { fst, snd }
        | Term::Sup { fst, snd, .. }
        | Term::Opx { op: _, fst, snd } => {
          go(fst, free_vars);
          go(snd, free_vars);
        }
        Term::Match { scrutinee, arms } => {
          go(scrutinee, free_vars);

          for (rule, term) in arms {
            let mut new_scope = IndexMap::new();
            go(term, &mut new_scope);

            for nam in rule.bound_names() {
              new_scope.remove(nam);
            }

            free_vars.extend(new_scope);
          }
        }
        Term::Ref { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => {}
      }
    }

    let mut free_vars = IndexMap::new();
    go(self, &mut free_vars);
    free_vars
  }

  /// Creates a new [`Term::Match`] from the given terms.
  /// If `scrutinee` is not a `Term::Var`, creates a let binding containing the match in its body
  pub fn new_native_match(
    scrutinee: Self,
    zero_term: Self,
    succ_label: Option<Name>,
    succ_term: Self,
  ) -> Self {
    let zero = (Pattern::Num { mat: MatchNum::Zero }, zero_term);
    let succ =
      (Pattern::Num { mat: MatchNum::Succ(Box::new(Pattern::Var { nam: succ_label.unwrap() })) }, succ_term);
    Term::Match { scrutinee: Box::new(scrutinee), arms: vec![zero, succ] }
  }

  pub fn recurse_mut<'a>(&'a mut self, mut term: impl FnMut(&'a mut Self), mut pattern: impl FnMut(&'a mut Pattern)) {
    match self {
        Term::Chn { tag, nam, bod } => {
            term(bod);
        },
        Term::Lam { tag, pat, bod } => {
            pattern(pat);
            term(bod);
        },
        Term::Let { pat, val, nxt } => {
          pattern(pat);
          term(val);
          term(nxt);
        },
        
        Term::Tup { fst, snd }
        | Term::Opx { fst, snd, .. }
        | Term::Sup { fst, snd, .. }
        | Term::App { fun: fst, arg: snd, .. } => {
            term(fst);
            term(snd);
        },
        Term::Match { scrutinee, arms } => {
          term(scrutinee);
          for (pat, bod) in arms {
            pattern(pat);
            term(bod);
          }
        },
        Term::Num { .. }
        | Term::Lnk { .. }
        | Term::Var { .. }
        | Term::Str { .. }
        | Term::Ref { .. }
        | Term::Era => (),
    }
  }
}

impl Pattern {
  pub fn occurs(&self, name: &Name) -> bool {
    self.bound_names().any(|x| x == name)
  }

  pub fn bound_names(&self) -> impl DoubleEndedIterator<Item = &Name> {
    fn go<'a>(pat: &'a Pattern, set: &mut Vec<&'a Name>) {
      match pat {
        Pattern::Var { nam } => set.push(nam),
        Pattern::Lnk { nam } => set.push(nam),
        Pattern::Ctr { nam: _, args } => {
          args.iter().for_each(|x| go(x, set));
        }
        Pattern::Num { mat: MatchNum::Zero } => {}
        Pattern::Num { mat: MatchNum::Succ(succ) } => {
          go(succ, set);
        }
        Pattern::Tup { fst, snd } => {
          go(fst, set);
          go(snd, set);
        }
        Pattern::Sup { tag: _, fst, snd } => {
          go(fst, set);
          go(snd, set);
        }
        Pattern::Era => (),
        Pattern::Implicit => (),
      }
    }
    let mut set = Vec::new();
    go(self, &mut set);
    set.into_iter()
  }

  pub fn bound_names_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut Name> {
    fn go<'a>(pat: &'a mut Pattern, set: &mut Vec<&'a mut Name>) {
      match pat {
        Pattern::Var { nam } => set.push(nam),
        Pattern::Lnk { nam } => set.push(nam),
        Pattern::Ctr { nam: _, args } => {
          args.iter_mut().for_each(|x| go(x, set));
        }
        Pattern::Num { mat: _ } => {
          todo!();
        }
        Pattern::Tup { fst, snd } => {
          go(fst, set);
          go(snd, set);
        }
        Pattern::Sup { tag: _, fst, snd } => {
          go(fst, set);
          go(snd, set);
        }
        Pattern::Era => (),
        Pattern::Implicit => (),
      }
    }
    let mut set = Vec::new();
    go(self, &mut set);
    set.into_iter()
  }
  pub fn is_var_like(&self) -> bool {
    match self {
      Pattern::Lnk { .. } | Pattern::Var { .. } | Pattern::Era => true,
      _ => true,
    }
  }
  pub fn is_flat(&self) -> bool {
    match self {
      Pattern::Var { .. } | Pattern::Lnk { .. } | Pattern::Implicit | Pattern::Era => true,
      Pattern::Tup { fst, snd } | Pattern::Sup { fst, snd, .. } => fst.is_var_like() && snd.is_var_like(),
      Pattern::Ctr { args, .. } => args.iter().all(|x| x.is_flat()),
      Pattern::Num { mat: MatchNum::Zero } => true,
      Pattern::Num { mat: MatchNum::Succ(p) } => p.is_var_like(),
    }
  }
  pub fn recurse_mut(&mut self, mut pattern: impl FnMut(&mut Pattern)) {
    match self {
        Pattern::Ctr { nam, args } => {
          for i in args {
            pattern(i);
          }
        },
        Pattern::Num { mat: MatchNum::Zero } => (),
        Pattern::Num { mat: MatchNum::Succ(p) } => {
          pattern(p)
        },
        Pattern::Tup { fst, snd }
        | Pattern::Sup { fst, snd, .. } => {
          pattern(fst);
          pattern(snd);
        },
        Pattern::Lnk { .. }
        | Pattern::Var { .. }
        | Pattern::Implicit
        | Pattern::Era => todo!(),
    }
  }
}

impl Rule {
  pub fn arity(&self) -> usize {
    self.pats.len()
  }
}

impl Definition {
  pub fn arity(&self) -> usize {
    self.rules[0].arity()
  }

  pub fn assert_no_pattern_matching_rules(&self) {
    assert!(self.rules.len() == 1, "Definition rules should have been removed in earlier pass");
  }
}

impl From<&Pattern> for Term {
  fn from(value: &Pattern) -> Self {
    match value {
      Pattern::Var { nam } => Term::Var { nam: nam.clone() },
      Pattern::Lnk { nam } => Term::Lnk { nam: nam.clone() },
      Pattern::Ctr { nam: _, args: _ } => todo!(),
      Pattern::Num { mat: _ } => todo!(),
      Pattern::Tup { fst, snd } => {
        Term::Tup { fst: Box::new(fst.as_ref().into()), snd: Box::new(snd.as_ref().into()) }
      }
      Pattern::Sup { tag, fst, snd } => {
        Term::Sup { tag: tag.clone(), fst: Box::new(fst.as_ref().into()), snd: Box::new(snd.as_ref().into()) }
      }
      Pattern::Era => Term::Era,
      Pattern::Implicit => todo!(),
    }
  }
}
