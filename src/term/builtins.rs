use super::{parser::parse_book, Book, Name, Pattern, Term};

const BUILTINS: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/src/term/builtins.hvm"));

pub const LIST: &str = "List";
pub const LCONS: &str = "List.cons";
pub const LNIL: &str = "List.nil";

pub const HEAD: &str = "head";
pub const TAIL: &str = "tail";

pub const STRING: &str = "String";
pub const SCONS: &str = "String.cons";
pub const SNIL: &str = "String.nil";

pub const RESULT: &str = "Result";
pub const RESULT_OK: &str = "Result.ok";
pub const RESULT_ERR: &str = "Result.err";

pub const NAT: &str = "Nat";
pub const NAT_SUCC: &str = "Nat.succ";
pub const NAT_ZERO: &str = "Nat.zero";

impl Book {
  pub fn builtins() -> Book {
    parse_book(BUILTINS, Book::default, true).expect("Error parsing builtin file, this should not happen")
  }

  pub fn encode_builtins(&mut self) {
    for def in self.defs.values_mut() {
      for rule in def.rules.iter_mut() {
        rule.pats.iter_mut().for_each(Pattern::encode_builtins);
        rule.body.encode_builtins();
      }
    }
  }
}

impl Term {
  fn encode_builtins(&mut self) {
    Term::recursive_call(move || match self {
      Term::Lst { els } => *self = Term::encode_list(std::mem::take(els)),
      Term::Str { val } => *self = Term::encode_str(val),
      Term::Nat { val } => *self = Term::encode_nat(*val),
      _ => {
        for child in self.children_mut() {
          child.encode_builtins();
        }
      }
    })
  }

  fn encode_list(elements: Vec<Term>) -> Term {
    elements.into_iter().rfold(Term::r#ref(LNIL), |acc, mut nxt| {
      nxt.encode_builtins();
      Term::call(Term::r#ref(LCONS), [nxt, acc])
    })
  }

  pub fn encode_str(val: &str) -> Term {
    val.chars().rfold(Term::r#ref(SNIL), |acc, char| {
      Term::call(Term::r#ref(SCONS), [Term::Num { val: u64::from(char) }, acc])
    })
  }

  pub fn encode_nat(val: u64) -> Term {
    (0 .. val).fold(Term::r#ref(NAT_ZERO), |acc, _| Term::app(Term::r#ref(NAT_SUCC), acc))
  }

  pub fn encode_ok(val: Term) -> Term {
    Term::call(Term::r#ref(RESULT_OK), [val])
  }

  pub fn encode_err(val: Term) -> Term {
    Term::call(Term::r#ref(RESULT_ERR), [val])
  }
}

impl Pattern {
  pub fn encode_builtins(&mut self) {
    match self {
      Pattern::Lst(pats) => *self = Self::encode_list(std::mem::take(pats)),
      Pattern::Str(str) => *self = Self::encode_str(str),
      Pattern::Ctr(_, pats) | Pattern::Tup(pats) => {
        for pat in pats {
          pat.encode_builtins();
        }
      }
      Pattern::Var(..) | Pattern::Num(..) => {}
    }
  }

  fn encode_list(elements: Vec<Pattern>) -> Pattern {
    let lnil = Pattern::Ctr(Name::from(LNIL), vec![]);

    elements.into_iter().rfold(lnil, |acc, mut nxt| {
      nxt.encode_builtins();
      Pattern::Ctr(Name::from(LCONS), vec![nxt, acc])
    })
  }

  fn encode_str(str: &str) -> Pattern {
    let lnil = Pattern::Ctr(Name::from(SNIL), vec![]);

    str.chars().rfold(lnil, |tail, head| {
      let head = Pattern::Num(head as u64);
      Pattern::Ctr(Name::from(SCONS), vec![head, tail])
    })
  }
}
