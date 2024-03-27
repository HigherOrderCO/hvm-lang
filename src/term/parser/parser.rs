use crate::term::{
  parser::lexer::{LexingError, Token},
  Adt, Book, Definition, Name, NumCtr, Op, Pattern, Rule, Tag, Term, LNIL, SNIL,
};
use chumsky::{
  error::{Error, RichReason},
  extra,
  input::{Emitter, SpannedInput, Stream, ValueInput},
  prelude::{Input, Rich},
  primitive::{any, choice, just},
  recursive::recursive,
  select,
  span::SimpleSpan,
  util::MaybeRef,
  IterParser, Parser,
};
use indexmap::map::Entry;
use logos::{Logos, SpannedIter};
use std::{iter::Map, ops::Range, path::Path};

use super::lexer::STRINGS;

// hvml grammar description:
// <Book>    ::= <TopLevel>*
// <TopLevel> ::= (<Def> | <Data>)
// <Def>     ::= <Rule> (<Rule>)*
// <Data>    ::= "data" <Name> "=" (<Name> | "(" <Name> (<Name>)* ")")+
// <Rule>    ::= ("(" <Name> <Pattern>* ")" | <Name> <Pattern>*) "=" (<InlineNumOp> | <InlineApp>)
// <Pattern> ::= "(" <Name> <Pattern>* ")" | <NameEra> | <Number>
// <Term>    ::= <Var> | <GlobalVar> | <Number> | <Lam> | <GlobalLam> | <Dup> | <Tup> | <Let> | <Match> | <NumOp> | <App>
// <Lam>     ::= ("λ"|"@") <NameEra> <Term>
// <GlobalLam> ::= ("λ"|"@") "$" <Name> <Term>
// <Dup>    ::= "dup" <Tag>? <NameEra> <NameEra> "=" <Term> ";" <Term>
// <Tup>    ::= "(" <Term> "," <Term> ")"
// <Let>    ::= "let" <LetPat> "=" <Term> ";" <Term>
// <LetPat> ::= <Name> | "(" <NameEra> "," <NameEra> ")"
// <Match>  ::= "match" (<Term> | <Name> "=" <Term>) "{" <match_arm>+ "}"
// <match_arm> ::= "|"? <Pattern> ":" <Term> ";"?
// <NumOp>  ::= "(" <numop_token> <Term> <Term> ")"
// <App>    ::= "(" <Term> (<Term>)* ")"
// <Var>    ::= <Name>
// <GlobalVar> ::= "$" <Name>
// <NameEra> ::= <Name> | "*"
// <Name>   ::= <name_token> // [_a-zA-Z][_a-zA-Z0-9]{0..7}
// <Number> ::= <number_token> // [0-9]+
// <Tag>    ::= "#" <Name>

pub fn parse_book(
  code: &str,
  default_book: impl Fn() -> Book,
  builtin: bool,
) -> Result<Book, Vec<Rich<Token>>> {
  book(default_book, builtin).parse(token_stream(code)).into_result()
}

pub fn parse_term(code: &str) -> Result<Term, Vec<Rich<Token>>> {
  // TODO: Make a function that calls a parser. I couldn't figure out how to type it correctly.
  term().parse(token_stream(code)).into_result()
}

/// Converts a Chumsky parser error into a message.
pub fn error_to_msg(err: &Rich<'_, Token>, code: &str, path: &Path) -> String {
  let Range { start, end } = err.span().into_range();
  let (lin, col) = line_and_col_of_byte(start, code);
  let reason = match err.reason() {
    // When many reasons, the first one is the most relevant.
    // Otherwise we just get 'multiple errors'.
    RichReason::Many(errs) => &errs[0],
    _ => err.reason(),
  };
  let path = format!("{}:{lin}:{col}", path.display());
  format!("At {}: {}\n{}", path, reason, highlight_error::highlight_error(usize::min(start, end), end, code))
}

fn line_and_col_of_byte(until: usize, src: &str) -> (usize, usize) {
  // Line and column numbers starts at 1.
  let mut line = 1;
  let mut col = 1;
  let mut gone = 0;
  for char in src.chars() {
    if gone >= until {
      break;
    }
    let char_len = char.len_utf8();
    gone += char_len;
    if char == '\n' {
      line += 1;
      col = 1;
    } else {
      col += char_len;
    }
  }
  (line, col)
}

fn token_stream(
  code: &str,
) -> SpannedInput<
  Token,
  SimpleSpan,
  Stream<
    Map<SpannedIter<Token>, impl FnMut((Result<Token, LexingError>, Range<usize>)) -> (Token, SimpleSpan)>,
  >,
> {
  // TODO: Maybe change to just using chumsky.
  let token_iter = Token::lexer(code).spanned().map(|(token, span)| match token {
    Ok(t) => (t, SimpleSpan::from(span)),
    Err(e) => (Token::Error(e), SimpleSpan::from(span)),
  });
  Stream::from_iter(token_iter).spanned(SimpleSpan::from(code.len() .. code.len()))
}

// Parsers

fn soft_keyword<'a, I>(keyword: &'static str) -> impl Parser<'a, I, (), extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  any().filter(move |t| matches!(t, Token::Name(n) if n == keyword)).to(()).labelled(keyword)
}

fn name<'a, I>() -> impl Parser<'a, I, Name, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  // FIXME: bug with chumsky when using with `.repeated`
  // select!(Token::Name(name) => Name::from(name)).labelled("<Name>")

  any()
    .filter(|t| matches!(t, Token::Name(_)))
    .map(|t| {
      let Token::Name(n) = t else { unreachable!() };
      Name(n)
    })
    .labelled("<Name>")
}

/// A top level name that not accepts `-`.
fn tl_name<'a, I>() -> impl Parser<'a, I, Name, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  any()
    .filter(|t| matches!(t, Token::Name(n) if n != "data"))
    .map(|t| {
      let Token::Name(name) = t else { unreachable!() };
      name
    })
    .validate(|out, span, emitter| {
      if out.contains('-') {
        emitter.emit(Rich::custom(span, "Names with '-' are not supported at top level."));
      }
      Name(out)
    })
    .labelled("<Name>")
}

fn tag<'a, I>(default: Tag) -> impl Parser<'a, I, Tag, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  just(Token::Hash).ignore_then(name()).or_not().map(move |x| x.map_or_else(|| default.clone(), Tag::Named))
}

fn name_or_era<'a, I>() -> impl Parser<'a, I, Option<Name>, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  choice((any().filter(|a| matches!(a, Token::Asterisk)).to(None), name().map(Some)))
}

fn num_oper<'a, I>() -> impl Parser<'a, I, Op, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  select! {
    Token::Add => Op::Add,
    Token::Sub => Op::Sub,
    Token::Asterisk => Op::Mul,
    Token::Div => Op::Div,
    Token::Mod => Op::Mod,
    Token::EqualsEquals => Op::Eq,
    Token::NotEquals => Op::Ne,
    Token::Ltn => Op::Lt,
    Token::Gtn => Op::Gt,
    Token::Lte => Op::Lte,
    Token::Gte => Op::Gte,
    Token::And => Op::And,
    Token::Or => Op::Or,
    Token::Xor => Op::Xor,
    Token::Shl => Op::Shl,
    Token::Shr => Op::Shr,
  }
}

fn term<'a, I>() -> impl Parser<'a, I, Term, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  let var = name().map(|name| Term::Var { nam: name }).boxed();
  let unscoped_var = just(Token::Dollar).ignore_then(name()).map(|name| Term::Lnk { nam: name }).boxed();

  let number = select!(Token::Num(num) => num).or(
    select!(Token::Error(LexingError::InvalidNumberLiteral) => ()).validate(|_, span, emit| {
      emit.emit(Rich::custom(span, "found invalid number literal expected number"));
      0
    }),
  );

  let nat: chumsky::Boxed<I, Term, extra::Err<Rich<_>>> = just(Token::Hash)
    .ignore_then(select!(Token::Num(num) => Term::Nat { val: num }).or(
      select!(Token::Error(LexingError::InvalidNumberLiteral) => ()).validate(|_, span, emit| {
        emit.emit(Rich::custom(span, "found invalid nat literal expected number"));
        Term::Nat { val: 0 }
      }),
    ))
    .boxed();

  let num_term = number.map(|val| Term::Num { val });

  let term_sep = just(Token::Semicolon).or_not();

  recursive(|term| {
    // *
    let era = just(Token::Asterisk).to(Term::Era).boxed();

    // #tag? λx body
    let lam = tag(Tag::Static)
      .then_ignore(just(Token::Lambda))
      .then(name_or_era())
      .then(term.clone())
      .map(|((tag, nam), bod)| Term::Lam { tag, nam, bod: Box::new(bod) })
      .boxed();

    // #tag? λ$x body
    let unscoped_lam = tag(Tag::Static)
      .then_ignore(just(Token::Lambda))
      .then(just(Token::Dollar).ignore_then(name_or_era()))
      .then(term.clone())
      .map(|((tag, nam), bod)| Term::Chn { tag, nam, bod: Box::new(bod) })
      .boxed();

    // #tag {fst snd}
    let sup = tag(Tag::Auto)
      .then_ignore(just(Token::LBracket))
      .then(term.clone().separated_by(just(Token::Comma).or_not()).at_least(2).collect())
      .then_ignore(just(Token::RBracket))
      .map(|(tag, els)| Term::Sup { tag, els })
      .boxed();

    // let #tag? {x1 x2} = body; next
    let dup = just(Token::Let)
      .ignore_then(tag(Tag::Auto))
      .then_ignore(just(Token::LBracket))
      .then(name_or_era().separated_by(just(Token::Comma).or_not()).at_least(2).collect())
      .then_ignore(just(Token::RBracket))
      .then_ignore(just(Token::Equals))
      .then(term.clone())
      .then_ignore(term_sep.clone())
      .then(term.clone())
      .map(|(((tag, bnd), val), next)| Term::Dup { tag, bnd, val: Box::new(val), nxt: Box::new(next) })
      .boxed();

    // let nam = term; term
    let let_ = just(Token::Let)
      .ignore_then(name_or_era())
      .then_ignore(just(Token::Equals))
      .then(term.clone())
      .then_ignore(term_sep.clone())
      .then(term.clone())
      .map(|((nam, val), nxt)| Term::Let { nam, val: Box::new(val), nxt: Box::new(nxt) })
      .boxed();

    // use a = val ';'? nxt
    let use_ = just(Token::Use)
      .ignore_then(name())
      .then_ignore(just(Token::Equals))
      .then(term.clone())
      .then_ignore(term_sep.clone())
      .then(term.clone())
      .map(|((nam, val), nxt)| Term::Use { nam, val: Box::new(val), nxt: Box::new(nxt) })
      .boxed();

    // (name '=')? term
    let match_arg = name().then_ignore(just(Token::Equals)).or_not().then(term.clone()).boxed();

    let lnil = just(Token::LBrace)
      .ignore_then(just(Token::RBrace))
      .ignored()
      .map(|_| Some(Name::from(LNIL)))
      .labelled("List.nil");
    let snil =
      select!(Token::Str(s) if s.is_empty() => ()).map(|_| Some(Name::from(SNIL))).labelled("String.nil");
    let match_pat = choice((name_or_era(), lnil, snil));

    // '|'? name: term
    let match_rule = just(Token::Or)
      .or_not()
      .ignore_then(match_pat)
      .labelled("<Match pattern>")
      .then_ignore(just(Token::Colon))
      .then(term.clone())
      .map(|(nam, body)| (nam, vec![], body));
    let match_rules = match_rule.separated_by(term_sep.clone()).at_least(1).allow_trailing().collect();

    // match ((scrutinee | <name> = value),?)+ { pat+: term;... }
    let match_ = just(Token::Match)
      .ignore_then(match_arg.clone())
      .then_ignore(just(Token::LBracket))
      .then(match_rules)
      .then_ignore(just(Token::RBracket))
      .map(|((bind, arg), rules)| {
        if let Some(bind) = bind {
          Term::Let {
            nam: Some(bind.clone()),
            val: Box::new(arg),
            nxt: Box::new(Term::Mat { arg: Box::new(Term::Var { nam: bind }), rules }),
          }
        } else {
          Term::Mat { arg: Box::new(arg), rules }
        }
      })
      .boxed();

    let switch_ctr = choice((number.map(NumCtr::Num), soft_keyword("_").map(|_| NumCtr::Succ(None))))
      .labelled("<Switch pattern>");

    let switch_rule =
      just(Token::Or).or_not().ignore_then(switch_ctr).then_ignore(just(Token::Colon)).then(term.clone());
    let switch_rules = switch_rule.separated_by(term_sep.clone()).at_least(1).allow_trailing().collect();

    let switch = just(Token::Switch)
      .ignore_then(match_arg)
      .then_ignore(just(Token::LBracket))
      .then(switch_rules)
      .then_ignore(just(Token::RBracket))
      .map(|((bind, arg), rules)| {
        if let Some(bind) = bind {
          Term::Let {
            nam: Some(bind.clone()),
            val: Box::new(arg),
            nxt: Box::new(Term::Swt { arg: Box::new(Term::Var { nam: bind }), rules }),
          }
        } else {
          Term::Swt { arg: Box::new(arg), rules }
        }
      })
      .boxed();

    // #tag? (f arg1 arg2 ...)
    let app = tag(Tag::Static)
      .then_ignore(just(Token::LParen))
      .then(term.clone())
      .foldl(term.clone().repeated(), |(tag, fun), arg| {
        (tag.clone(), Term::App { tag, fun: Box::new(fun), arg: Box::new(arg) })
      })
      .then_ignore(just(Token::RParen))
      .map(|(_, app)| app)
      .boxed();

    let num_op = num_oper()
      .then(term.clone())
      .then(term.clone())
      .delimited_by(just(Token::LParen), just(Token::RParen))
      .map(|((op, fst), snd)| Term::Opx { op, fst: Box::new(fst), snd: Box::new(snd) })
      .boxed();

    // (x, ..n)
    let tup = term
      .clone()
      .separated_by(just(Token::Comma))
      .at_least(2)
      .collect::<Vec<Term>>()
      .delimited_by(just(Token::LParen), just(Token::RParen))
      .map(|els| Term::Tup { els })
      .boxed();

    // let (x, ..n) = term; term
    let let_tup = just(Token::Let)
      .ignore_then(just(Token::LParen))
      .ignore_then(name_or_era().separated_by(just(Token::Comma)).at_least(2).collect())
      .then_ignore(just(Token::RParen))
      .then_ignore(just(Token::Equals))
      .then(term.clone())
      .then_ignore(term_sep.clone())
      .then(term.clone())
      .map(|((bnd, val), next)| Term::Ltp { bnd, val: Box::new(val), nxt: Box::new(next) })
      .boxed();

    let str = select!(Token::Str(s) => Term::Str { val: s }).boxed();
    let chr = select!(Token::Char(c) => Term::Num { val: c }).boxed();

    let list = term
      .clone()
      .separated_by(just(Token::Comma).or_not())
      .collect()
      .delimited_by(just(Token::LBrace), just(Token::RBrace))
      .map(|els| Term::Lst { els })
      .boxed();

    choice((
      num_op,
      app,
      tup,
      unscoped_var,
      var,
      nat,
      num_term,
      list,
      str,
      chr,
      sup,
      unscoped_lam,
      lam,
      dup,
      use_,
      let_tup,
      let_,
      match_,
      switch,
      era,
    ))
    .labelled("term")
  })
}

fn rule_pattern<'a, I>() -> impl Parser<'a, I, Pattern, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  recursive(|pattern| {
    let var = name_or_era().map(Pattern::Var).boxed();

    let ctr = tl_name()
      .then(pattern.clone().repeated().collect())
      .map(|(nam, xs)| Pattern::Ctr(nam, xs))
      .delimited_by(just(Token::LParen), just(Token::RParen))
      .boxed();

    let tup = pattern
      .clone()
      .separated_by(just(Token::Comma))
      .at_least(2)
      .collect::<Vec<Pattern>>()
      .delimited_by(just(Token::LParen), just(Token::RParen))
      .map(Pattern::Tup)
      .boxed();

    let list = pattern
      .clone()
      .separated_by(just(Token::Comma).or_not())
      .collect()
      .delimited_by(just(Token::LBrace), just(Token::RBrace))
      .map(Pattern::Lst)
      .boxed();

    let num_val = any().filter(|t| matches!(t, Token::Num(_))).map(|t| {
      let Token::Num(n) = t else { unreachable!() };
      n
    });

    let num = num_val.map(Pattern::Num).labelled("<Num>");

    let chr = select!(Token::Char(c) => Pattern::Num(c)).labelled("<Char>").boxed();

    let str = select!(Token::Str(s) => Pattern::Str(s)).labelled("<String>").boxed();

    choice((num, chr, str, var, ctr, list, tup))
  })
  .labelled("<Rule pattern>")
}

fn rule_lhs<'a, I>() -> impl Parser<'a, I, (Name, Vec<Pattern>), extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  let lhs = tl_name().then(rule_pattern().repeated().collect()).boxed();

  let just_lhs = lhs.clone().then_ignore(just(Token::Equals).map_err(|err: Rich<'a, Token>| {
    Error::<I>::expected_found(
      [
        Some(MaybeRef::Val(Token::Add)),
        Some(MaybeRef::Val(Token::LParen)),
        Some(MaybeRef::Val(Token::LBrace)),
        Some(MaybeRef::Val(Token::Equals)),
      ],
      None,
      *err.span(),
    )
  }));

  let paren_lhs = just(Token::LParen)
    .ignore_then(lhs.clone().map_err(|err| map_unexpected_eof(err, Token::Name(STRINGS.get("<Name>")))))
    .then_ignore(just(Token::RParen))
    .then_ignore(just(Token::Equals).map_err(|err| map_unexpected_eof(err, Token::Equals)));

  choice((just_lhs, paren_lhs))
}

fn rule<'a, I>() -> impl Parser<'a, I, TopLevel, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  rule_lhs().then(term()).map(move |((name, pats), body)| TopLevel::Rule((name, Rule { pats, body })))
}

fn datatype<'a, I>() -> impl Parser<'a, I, TopLevel, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  let arity_0 = tl_name().map_with_span(|nam, span| ((nam, vec![]), span));
  let arity_n = tl_name()
    .then(name().repeated().collect::<Vec<_>>())
    .delimited_by(just(Token::LParen), just(Token::RParen))
    .map_with_span(|(nam, args), span| ((nam, args), span));

  let ctrs = arity_0.or(arity_n).separated_by(just(Token::Or)).at_least(1).collect();
  let data_name = tl_name().map_with_span(|name, span| (name, span));

  soft_keyword("data")
    .ignore_then(data_name.map_err(|err| map_unexpected_eof(err, Token::Name(STRINGS.get("<Name>")))))
    .then_ignore(just(Token::Equals))
    .then(ctrs.map_err(|err| map_unexpected_eof(err, Token::Name(STRINGS.get("constructor")))))
    .map(move |(name, ctrs)| TopLevel::Adt(name, ctrs))
}

fn map_unexpected_eof(err: Rich<Token>, expected_token: Token) -> Rich<Token> {
  if err.found().is_none() {
    // Not using Error::expected_found here to not merge with other expected_found errors
    Rich::custom(*err.span(), format!("found end of input expected {}", expected_token))
  } else {
    err
  }
}

fn book<'a, I>(
  default_book: impl Fn() -> Book,
  builtin: bool,
) -> impl Parser<'a, I, Book, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  choice((datatype(), rule()))
    .repeated()
    .collect()
    .validate(move |program, _, emit| collect_book(default_book(), program, builtin, emit))
}

/// Collect rules and adts into a book
fn collect_book(
  mut book: Book,
  program: Vec<TopLevel>,
  builtin: bool,
  emit: &mut Emitter<Rich<'_, Token>>,
) -> Book {
  for top_level in program {
    match top_level {
      TopLevel::Rule((name, rule)) => {
        if let Some(def) = book.defs.get_mut(&name) {
          def.rules.push(rule);
        } else {
          book.defs.insert(name.clone(), Definition { name, rules: vec![rule], builtin });
        }
      }
      TopLevel::Adt((nam, nam_span), adt) => match book.adts.get(&nam) {
        None => {
          let (ctrs, spans): (Vec<(_, _)>, Vec<_>) = adt.into_iter().unzip();

          for ((ctr, _), span) in ctrs.iter().zip(spans.into_iter()) {
            match book.ctrs.entry(ctr.clone()) {
              Entry::Vacant(e) => _ = e.insert(nam.clone()),
              Entry::Occupied(e) => emit.emit(Rich::custom(
                span,
                if book.adts.get(e.get()).is_some_and(|adt| adt.builtin) {
                  format!("{} is a built-in constructor and should not be overridden.", e.key())
                } else {
                  format!("Repeated constructor '{}'", e.key())
                },
              )),
            }
          }

          let adt = Adt { ctrs: ctrs.into_iter().collect(), builtin };
          book.adts.insert(nam.clone(), adt);
        }
        Some(adt) => emit.emit(Rich::custom(
          nam_span,
          if adt.builtin {
            format!("{} is a built-in datatype and should not be overridden.", nam)
          } else {
            format!("Repeated datatype '{}'", nam)
          },
        )),
      },
    }
  }
  book
}

enum TopLevel {
  Rule((Name, Rule)),
  Adt((Name, SimpleSpan), Vec<((Name, Vec<Name>), SimpleSpan)>),
}
