use indexmap::IndexMap;

use crate::term::{Adt, Book, Name, Tag, Term};

const STRING: &'static str = "String";
const SNIL: &'static str = "SNil";
const SCONS: &'static str = "SCons";
const HEAD: &'static str = "head";
const TAIL: &'static str = "tail";

impl Book {
  pub fn encode_strs(&mut self) {
    self.ctrs.insert(Name::new(SNIL), Name::new(STRING));
    self.ctrs.insert(Name::new(SCONS), Name::new(STRING));

    self.adts.insert(Name::new(STRING), Adt {
      ctrs: IndexMap::from([
        (Name::new(SCONS), vec![Name::new(HEAD), Name::new(TAIL)]),
        (Name::new(SNIL), vec![]),
      ]),
    });

    for def in self.defs.values_mut() {
      for rule in &mut def.rules {
        rule.body.encode_str();
      }
    }
  }
}

impl Term {
  fn encode_str(&mut self) {
    match self {
      Term::Str { val } => {
        let chars = val.chars();
        let snil = Term::Var { nam: Name::new(SNIL) };
        *self = chars.rfold(snil, |acc, char| {
          let char = Term::Num { val: u64::from(char) };
          let scons_app = Term::App {
            tag: Tag::Static,
            fun: Box::new(Term::Var { nam: Name::new(SCONS) }),
            arg: Box::new(char),
          };
          Term::App { tag: Tag::Static, fun: Box::new(scons_app), arg: Box::new(acc) }
        });
      }
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => bod.encode_str(),
      Term::App { fun: fst, arg: snd, .. }
      | Term::Let { val: fst, nxt: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { fst, snd, .. } => {
        fst.encode_str();
        snd.encode_str();
      }
      Term::Match { arms, .. } => {
        for arm in arms {
          arm.1.encode_str();
        }
      }
      Term::Lnk { .. } | Term::Num { .. } | Term::Var { .. } | Term::Ref { .. } | Term::Era => {}
    }
  }
}
