use std::fmt::{self, Display};

use crate::term::Name;

use super::{Book, DefId, DefNames, Definition, MatchNum, Op, Pattern, Rule, Tag, Term};

macro_rules! display {
  ($($x:tt)*) => {
    DisplayFn(move |f| write!(f, $($x)*))
  };
}

impl Term {
  fn display_app<'a>(&'a self, tag: &'a Tag, def_names: &'a DefNames) -> impl Display + 'a {
    DisplayFn(move |f| match self {
      Term::App { tag: tag2, fun, arg } if tag2 == tag => {
        write!(f, "{} {}", fun.display_app(tag, def_names), arg.display(def_names))
      }
      _ => write!(f, "{}", self.display(def_names)),
    })
  }
  pub fn display<'a>(&'a self, def_names: &'a DefNames) -> impl Display + 'a {
    DisplayFn(move |f| match self {
      Term::Lam { tag, nam, bod } => {
        write!(
          f,
          "{}λ{} {}",
          tag.display_padded(),
          nam.clone().unwrap_or(Name::new("*")),
          bod.display(def_names)
        )
      }
      Term::Var { nam } => write!(f, "{nam}"),
      Term::Chn { tag, nam, bod } => {
        write!(f, "{}λ${} {}", tag.display_padded(), nam, bod.display(def_names))
      }
      Term::Lnk { nam } => write!(f, "${nam}"),
      Term::Let { pat, val, nxt } => {
        write!(f, "let {} = {}; {}", pat, val.display(def_names), nxt.display(def_names))
      }
      Term::Ref { def_id } => write!(f, "{}", def_names.name(def_id).unwrap()),
      Term::App { tag, fun, arg } => {
        write!(f, "{}({} {})", tag.display_padded(), fun.display_app(tag, def_names), arg.display(def_names))
      }
      Term::Match { scrutinee, arms } => {
        write!(
          f,
          "match {} {{ {} }}",
          scrutinee.display(def_names),
          DisplayJoin(
            || arms.iter().map(|(pat, term)| display!("{}: {}", pat, term.display(def_names))),
            "; "
          ),
        )
      }
      Term::Dup { tag, fst, snd, val, nxt } => write!(
        f,
        "let{} {{{} {}}} = {}; {}",
        tag.display(),
        fst.as_ref().map(|x| x.as_str()).unwrap_or("*"),
        snd.as_ref().map(|x| x.as_str()).unwrap_or("*"),
        val.display(def_names),
        nxt.display(def_names)
      ),
      Term::Sup { tag, fst, snd } => {
        write!(f, "{}{{{} {}}}", tag.display_padded(), fst.display(def_names), snd.display(def_names))
      }
      Term::Era => write!(f, "*"),
      Term::Num { val } => write!(f, "{val}"),
      Term::Str { val } => write!(f, "{val:?}"),
      Term::Opx { op, fst, snd } => {
        write!(f, "({} {} {})", op, fst.display(def_names), snd.display(def_names))
      }
      Term::Tup { fst, snd } => write!(f, "({}, {})", fst.display(def_names), snd.display(def_names)),
    })
  }
}

impl Tag {
  pub fn display_padded(&self) -> impl Display + '_ {
    DisplayFn(move |f| match self {
      Tag::Named(name) => write!(f, "#{name} "),
      Tag::Numeric(num) => write!(f, "#{num} "),
      Tag::Auto => Ok(()),
      Tag::Static => Ok(()),
    })
  }
  pub fn display(&self) -> impl Display + '_ {
    DisplayFn(move |f| match self {
      Tag::Named(name) => write!(f, "#{name}"),
      Tag::Numeric(num) => write!(f, "#{num}"),
      Tag::Auto => Ok(()),
      Tag::Static => Ok(()),
    })
  }
}

impl fmt::Display for Pattern {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Pattern::Var { nam } => write!(f, "{}", nam),
      Pattern::Ctr {
        nam, args
        } => {
        write!(f, "({}{})", nam, DisplayJoin(|| args.iter().map(|p| display!(" {p}")), ""))
      }
      Pattern::Num { mat } => write!(f, "{mat}"),
      Pattern::Tup { fst, snd } => write!(f, "({}, {})", fst, snd,),
      Pattern::Sup { tag, fst, snd } => write!(f, "{} {{{} {}}}", tag.display(), fst, snd),
      Pattern::Era => write!(f, "*"),
      Pattern::Implicit => Ok(()),
    }
  }
}

impl Rule {
  pub fn display<'a>(&'a self, def_id: &'a DefId, def_names: &'a DefNames) -> impl Display + 'a {
    display!(
      "({}{}) = {}",
      def_names.name(def_id).unwrap(),
      DisplayJoin(|| self.pats.iter().map(|x| display!(" {x}")), ""),
      self.body.display(def_names)
    )
  }
}

impl Definition {
  pub fn display<'a>(&'a self, def_names: &'a DefNames) -> impl Display + 'a {
    DisplayJoin(|| self.rules.iter().map(|x| x.display(&self.def_id, def_names)), "\n")
  }
}

impl fmt::Display for Book {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", DisplayJoin(|| self.defs.values().map(|x| x.display(&self.def_names)), "\n\n"))
  }
}

impl fmt::Display for MatchNum {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      MatchNum::Zero => write!(f, "0"),
      MatchNum::Succ(pat) => write!(f, "+{pat}"),
    }
  }
}

impl fmt::Display for Op {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Op::ADD => write!(f, "+"),
      Op::SUB => write!(f, "-"),
      Op::MUL => write!(f, "*"),
      Op::DIV => write!(f, "/"),
      Op::MOD => write!(f, "%"),
      Op::EQ => write!(f, "=="),
      Op::NE => write!(f, "!="),
      Op::LT => write!(f, "<"),
      Op::GT => write!(f, ">"),
      Op::LTE => write!(f, "<="),
      Op::GTE => write!(f, ">="),
      Op::AND => write!(f, "&"),
      Op::OR => write!(f, "|"),
      Op::XOR => write!(f, "^"),
      Op::LSH => write!(f, "<<"),
      Op::RSH => write!(f, ">>"),
      Op::NOT => write!(f, "~"),
    }
  }
}

impl fmt::Display for Name {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.fmt(f)
  }
}

struct DisplayFn<F: Fn(&mut fmt::Formatter) -> fmt::Result>(F);

impl<F: Fn(&mut fmt::Formatter) -> fmt::Result> Display for DisplayFn<F> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0(f)
  }
}

pub struct DisplayJoin<F, S>(pub F, pub S);

impl<F, I, S> Display for DisplayJoin<F, S>
where
  F: (Fn() -> I),
  I: Iterator,
  I::Item: Display,
  S: Display,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (i, x) in self.0().enumerate() {
      if i != 0 {
        self.1.fmt(f)?;
      }
      x.fmt(f)?;
    }
    Ok(())
  }
}
