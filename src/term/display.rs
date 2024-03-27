use super::{Book, Definition, Name, NumCtr, Op, Pattern, Rule, Tag, Term};
use std::{fmt, ops::Deref};

/* Some aux structures for things that are not so simple to display */

pub struct DisplayFn<F: Fn(&mut fmt::Formatter) -> fmt::Result>(pub F);

impl<F: Fn(&mut fmt::Formatter) -> fmt::Result> fmt::Display for DisplayFn<F> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0(f)
  }
}

pub struct DisplayJoin<F, S>(pub F, pub S);

impl<F, I, S> fmt::Display for DisplayJoin<F, S>
where
  F: (Fn() -> I),
  I: IntoIterator,
  I::Item: fmt::Display,
  S: fmt::Display,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (i, x) in self.0().into_iter().enumerate() {
      if i != 0 {
        self.1.fmt(f)?;
      }
      x.fmt(f)?;
    }
    Ok(())
  }
}

macro_rules! display {
  ($($x:tt)*) => {
    DisplayFn(move |f| write!(f, $($x)*))
  };
}

/* The actual display implementations */

impl fmt::Display for Term {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    Term::recursive_call(move || match self {
      Term::Lam { tag, nam, bod } => {
        write!(f, "{}λ{} {}", tag.display_padded(), var_as_str(nam), bod)
      }
      Term::Var { nam } => write!(f, "{nam}"),
      Term::Chn { tag, nam, bod } => {
        write!(f, "{}λ${} {}", tag.display_padded(), var_as_str(nam), bod)
      }
      Term::Lnk { nam } => write!(f, "${nam}"),
      Term::Let { nam, val, nxt } => {
        write!(f, "let {} = {}; {}", var_as_str(nam), val, nxt)
      }
      Term::Use { nam, val, nxt } => {
        write!(f, "use {} = {}; {}", nam, val, nxt)
      }
      Term::Ref { nam: def_name } => write!(f, "{def_name}"),
      Term::App { tag, fun, arg } => {
        write!(f, "{}({} {})", tag.display_padded(), fun.display_app(tag), arg)
      }
      Term::Mat { arg, rules } => {
        write!(
          f,
          "match {} {{ {} }}",
          arg,
          DisplayJoin(|| rules.iter().map(|rule| display!("{}: {}", var_as_str(&rule.0), rule.2)), "; "),
        )
      }
      Term::Swt { arg, rules } => {
        write!(
          f,
          "switch {} {{ {} }}",
          arg,
          DisplayJoin(|| rules.iter().map(|rule| display!("{}: {}", rule.0, rule.1)), "; "),
        )
      }
      Term::Ltp { bnd, val, nxt } => {
        write!(f, "let ({}) = {}; {}", DisplayJoin(|| bnd.iter().map(var_as_str), ", "), val, nxt)
      }
      Term::Tup { els } => write!(f, "({})", DisplayJoin(|| els.iter(), ", "),),
      Term::Dup { tag, bnd, val, nxt } => {
        write!(f, "let {}{{{}}} = {}; {}", tag, DisplayJoin(|| bnd.iter().map(var_as_str), " "), val, nxt)
      }
      Term::Sup { tag, els } => {
        write!(f, "{}{{{}}}", tag, DisplayJoin(|| els, " "))
      }
      Term::Era => write!(f, "*"),
      Term::Num { val } => write!(f, "{val}"),
      Term::Nat { val } => write!(f, "#{val}"),
      Term::Str { val } => write!(f, "{val:?}"),
      Term::Opx { op, fst, snd } => {
        write!(f, "({} {} {})", op, fst, snd)
      }
      Term::Lst { els } => write!(f, "[{}]", DisplayJoin(|| els.iter(), ", "),),
      Term::Err => write!(f, "<Invalid>"),
    })
  }
}

impl fmt::Display for Tag {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Tag::Named(name) => write!(f, "#{name}"),
      Tag::Numeric(num) => write!(f, "#{num}"),
      Tag::Auto => Ok(()),
      Tag::Static => Ok(()),
    }
  }
}

impl fmt::Display for Pattern {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Pattern::Var(None) => write!(f, "*"),
      Pattern::Var(Some(nam)) => write!(f, "{nam}"),
      Pattern::Ctr(nam, pats) => {
        write!(f, "({}{})", nam, DisplayJoin(|| pats.iter().map(|p| display!(" {p}")), ""))
      }
      Pattern::Num(num) => write!(f, "{num}"),
      Pattern::Tup(pats) => write!(f, "({})", DisplayJoin(|| pats, ", ")),
      Pattern::Lst(pats) => write!(f, "[{}]", DisplayJoin(|| pats, ", ")),
      Pattern::Str(str) => write!(f, "\"{str}\""),
    }
  }
}

impl Rule {
  pub fn display<'a>(&'a self, def_name: &'a Name) -> impl fmt::Display + 'a {
    display!(
      "({}{}) = {}",
      def_name,
      DisplayJoin(|| self.pats.iter().map(|x| display!(" {x}")), ""),
      self.body
    )
  }
}

impl fmt::Display for Definition {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", DisplayJoin(|| self.rules.iter().map(|x| x.display(&self.name)), "\n"))
  }
}

impl fmt::Display for Book {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", DisplayJoin(|| self.defs.values(), "\n\n"))
  }
}

impl fmt::Display for NumCtr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      NumCtr::Num(n) => write!(f, "{n}"),
      NumCtr::Succ(_) => write!(f, "_"),
    }
  }
}

impl fmt::Display for Op {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Op::Add => write!(f, "+"),
      Op::Sub => write!(f, "-"),
      Op::Mul => write!(f, "*"),
      Op::Div => write!(f, "/"),
      Op::Mod => write!(f, "%"),
      Op::Eq => write!(f, "=="),
      Op::Ne => write!(f, "!="),
      Op::Lt => write!(f, "<"),
      Op::Gt => write!(f, ">"),
      Op::Lte => write!(f, "<="),
      Op::Gte => write!(f, ">="),
      Op::And => write!(f, "&"),
      Op::Or => write!(f, "|"),
      Op::Xor => write!(f, "^"),
      Op::Shl => write!(f, "<<"),
      Op::Shr => write!(f, ">>"),
    }
  }
}

impl fmt::Display for Name {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.fmt(f)
  }
}

impl Term {
  fn display_app<'a>(&'a self, tag: &'a Tag) -> impl fmt::Display + 'a {
    DisplayFn(move |f| match self {
      Term::App { tag: tag2, fun, arg } if tag2 == tag => {
        write!(f, "{} {}", fun.display_app(tag), arg)
      }
      _ => write!(f, "{}", self),
    })
  }
}

impl Tag {
  pub fn display_padded(&self) -> impl fmt::Display + '_ {
    DisplayFn(move |f| match self {
      Tag::Named(name) => write!(f, "#{name} "),
      Tag::Numeric(num) => write!(f, "#{num} "),
      Tag::Auto => Ok(()),
      Tag::Static => Ok(()),
    })
  }
}

fn var_as_str(nam: &Option<Name>) -> &str {
  nam.as_ref().map_or("*", Name::deref)
}
