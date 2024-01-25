use super::lexer::{LexingError, Token};
use crate::term::{Adt, Book, MatchNum, Name, Op, Pattern, Rule, Tag, Term};
use chumsky::{
  extra,
  input::{SpannedInput, Stream, ValueInput},
  prelude::{Input, Rich},
  primitive::{choice, just},
  recursive::recursive,
  select,
  span::SimpleSpan,
  IterParser, Parser,
};
use logos::{Logos, SpannedIter};
use std::{collections::hash_map::Entry, iter::Map, ops::Range};

/// <Book>    ::= <TopLevel>*
/// <TopLevel> ::= (<Def> | <Data>)
/// <Def>     ::= <Rule> (<Rule>)*
/// <Data>    ::= "data" <Name> "=" (<Name> | "(" <Name> (<Name>)* ")")+
/// <Rule>    ::= ("(" <Name> <Pattern>* ")" | <Name> <Pattern>*) "=" (<InlineNumOp> | <InlineApp>)
/// <Pattern> ::= "(" <Name> <Pattern>* ")" | <NameEra> | <Number>
/// <Term>    ::= <Var> | <GlobalVar> | <Number> | <Lam> | <GlobalLam> | <Dup> | <Tup> | <Let> | <NumOp> | <App>
/// <Lam>     ::= ("λ"|"@") <NameEra> <Term>
/// <GlobalLam> ::= ("λ"|"@") "$" <Name> <Term>
/// <Dup>    ::= "dup" <Tag>? <NameEra> <NameEra> "=" <Term> ";" <Term>
/// <Tup>    ::= "(" <Term> "," <Term> ")"
/// <Let>    ::= "let" <LetPat> "=" <Term> ";" <Term>
/// <LetPat> ::= <Name> | "(" <NameEra> "," <NameEra> ")"
/// <NumOp>  ::= "(" <numop_token> <Term> <Term> ")"
/// <App>    ::= "(" <Term> (<Term>)* ")"
/// <Var>    ::= <Name>
/// <GlobalVar> ::= "$" <Name>
/// <NameEra> ::= <Name> | "*"
/// <Name>   ::= <name_token> // [_a-zA-Z][_a-zA-Z0-9]{0..7}
/// <Number> ::= <number_token> // [0-9]+
/// <Tag>    ::= "#" <Name>
pub fn parse_definition_book(code: &str) -> Result<Book, Vec<Rich<Token>>> {
  book().parse(token_stream(code)).into_result()
}

pub fn parse_term(code: &str) -> Result<Term, Vec<Rich<Token>>> {
  // TODO: Make a function that calls a parser. I couldn't figure out how to type it correctly.
  term().parse(token_stream(code)).into_result()
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

fn soft_keyword<'a, I>(keyword: &'a str) -> impl Parser<'a, I, (), extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  name().try_map(move |Name(nam), span| if nam == keyword { Ok(()) } else { Err(Rich::custom(span, "")) })
}

fn name<'a, I>() -> impl Parser<'a, I, Name, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  select!(Token::Name(name) => Name(name))
}

fn tag<'a, I>(default: Tag) -> impl Parser<'a, I, Tag, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  just(Token::Hash).ignore_then(name()).or_not().map(move |x| x.map(Tag::Named).unwrap_or(default.clone()))
}

fn name_or_era<'a, I>() -> impl Parser<'a, I, Option<Name>, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  choice((select!(Token::Asterisk => None), name().map(Some)))
}

fn num_oper<'a, I>() -> impl Parser<'a, I, Op, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  select! {
    Token::Add => Op::ADD,
    Token::Sub => Op::SUB,
    Token::Asterisk => Op::MUL,
    Token::Div => Op::DIV,
    Token::Mod => Op::MOD,
    Token::EqualsEquals => Op::EQ,
    Token::NotEquals => Op::NE,
    Token::Ltn => Op::LT,
    Token::Gtn => Op::GT,
    Token::Lte => Op::LTE,
    Token::Gte => Op::GTE,
    Token::And => Op::AND,
    Token::Or => Op::OR,
    Token::Xor => Op::XOR,
    Token::Tilde => Op::NOT,
    Token::Shl => Op::LSH,
    Token::Shr => Op::RSH,
  }
}

fn term<'a, I>() -> impl Parser<'a, I, Term, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  let var = name().map(|name| Term::Var { nam: name }).boxed();
  let global_var = just(Token::Dollar).ignore_then(name()).map(|name| Term::Lnk { nam: name }).boxed();
  let number = select!(Token::Num(num) => Term::Num{val: num});
  let term_sep = just(Token::Semicolon).or_not();

  recursive(|term| {
    // <Name>-1
    let pred = select!(Token::Pred(s) => Term::Var { nam: Name(s) }).boxed();

    // *
    let era = just(Token::Asterisk).to(Term::Era).boxed();

    // #tag? λx body
    let lam = tag(Tag::Static)
      .then_ignore(just(Token::Lambda))
      .then(name_or_era())
      .then(term.clone())
      .map(|((tag, name), body)| Term::Lam { tag, nam: name, bod: Box::new(body) })
      .boxed();

    // #tag? λ$x body
    let global_lam = tag(Tag::Static)
      .then_ignore(just(Token::Lambda))
      .then(just(Token::Dollar).ignore_then(name()))
      .then(term.clone())
      .map(|((tag, name), body)| Term::Chn { tag, nam: name, bod: Box::new(body) })
      .boxed();

    // #tag {fst snd}
    let sup = tag(Tag::Auto)
      .then_ignore(just(Token::LBracket))
      .then(term.clone())
      .then(term.clone())
      .then_ignore(just(Token::RBracket))
      .map(|((tag, fst), snd)| Term::Sup { tag, fst: Box::new(fst), snd: Box::new(snd) })
      .boxed();

    // let #tag? {x1 x2} = body; next
    let dup = just(Token::Let)
      .ignore_then(tag(Tag::Auto))
      .then_ignore(just(Token::LBracket))
      .then(name_or_era())
      .then(name_or_era())
      .then_ignore(just(Token::RBracket))
      .then_ignore(just(Token::Equals))
      .then(term.clone())
      .then_ignore(term_sep.clone())
      .then(term.clone())
      .map(|((((tag, fst), snd), val), next)| Term::Dup {
        tag,
        fst,
        snd,
        val: Box::new(val),
        nxt: Box::new(next),
      })
      .boxed();

    // (x, y)
    let tup = term
      .clone()
      .then_ignore(just(Token::Comma))
      .then(term.clone())
      .delimited_by(just(Token::LParen), just(Token::RParen))
      .map(|(fst, snd)| Term::Tup { fst: Box::new(fst), snd: Box::new(snd) })
      .boxed();

    // let a = ...
    // let (a, b) = ...
    let let_ = just(Token::Let)
      .ignore_then(pattern())
      .validate(|pat, span, emit| {
        if matches!(&pat, Pattern::Num { .. }) {
          emit.emit(Rich::custom(span, "Numbers not supported in let."));
        }
        pat
      })
      .then_ignore(just(Token::Equals))
      .then(term.clone())
      .then_ignore(term_sep.clone())
      .then(term.clone())
      .map(|((pat, val), nxt)| Term::Let { pat, val: Box::new(val), nxt: Box::new(nxt) })
      .boxed();

    // pat: term
    let match_arm = pattern()
      .or(just(Token::Add).map(|_| Pattern::Num { mat: MatchNum::Succ(Box::new(Pattern::Era)) }))
      .then_ignore(just(Token::Colon))
      .then(term.clone())
      .boxed();

    // match scrutinee { pat: term;... }
    let match_ = just(Token::Match)
      .ignore_then(term.clone())
      .then_ignore(just(Token::LBracket))
      .then(match_arm.separated_by(term_sep.clone()).allow_trailing().collect())
      .then_ignore(just(Token::RBracket))
      .map(|(scrutinee, arms)| Term::Match { scrutinee: Box::new(scrutinee), arms })
      .boxed();

    let native_match = just(Token::Match)
      .ignore_then(name())
      .then_ignore(just(Token::LBracket))
      .then_ignore(select!(Token::Num(0) => ()))
      .then_ignore(just(Token::Colon))
      .then(term.clone())
      .then_ignore(term_sep.clone())
      .then_ignore(just(Token::Add))
      .then_ignore(just(Token::Colon))
      .then(term.clone())
      .then_ignore(term_sep.clone())
      .then_ignore(just(Token::RBracket))
      .map(|((cond, zero), succ)| Term::Match {
        scrutinee: Box::new(Term::Var { nam: cond.clone() }),
        arms: vec![
          (Pattern::Num { mat: MatchNum::Zero }, zero),
          (Pattern::Num { mat: MatchNum::Succ(Box::new(Pattern::Era)) }, succ),
        ],
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

    let str = select!(Token::Str(s) => Term::Str { val: s }).boxed();
    let chr = select!(Token::Char(c) => Term::Num { val: c }).boxed();

    choice((
      global_var,
      var,
      number,
      str,
      chr,
      sup,
      tup,
      global_lam,
      lam,
      dup,
      let_,
      native_match,
      match_,
      num_op,
      app,
      era,
      pred,
    ))
  })
}

fn pattern<'a, I>() -> impl Parser<'a, I, Pattern, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  recursive(|pattern| {
    let var =
      name_or_era().map(|nam| if let Some(nam) = nam { Pattern::Var { nam } } else { Pattern::Era }).boxed();

    let ctr = name()
      .then(pattern.clone().repeated().collect())
      .map(|(nam, xs)| Pattern::Ctr { nam, args: xs })
      .delimited_by(just(Token::LParen), just(Token::RParen))
      .boxed();

    let tup = pattern
      .clone()
      .then_ignore(just(Token::Comma))
      .then(pattern.clone())
      .delimited_by(just(Token::LParen), just(Token::RParen))
      .map(|(fst, snd)| Pattern::Tup { fst: Box::new(fst), snd: Box::new(snd) })
      .boxed();

    let zero = select!(Token::Num(0) => Pattern::Num { mat: MatchNum::Zero });

    let succ = just(Token::Add)
      .ignore_then(name_or_era())
      .map(|nam| Pattern::Num {
        mat: MatchNum::Succ(Box::new(if let Some(nam) = nam {
          Pattern::Var { nam }
        } else {
          Pattern::Implicit
        })),
      })
      .boxed();

    choice((zero, succ, var, ctr, tup))
  })
}

fn rule<'a, I>() -> impl Parser<'a, I, (Name, Rule), extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  let lhs = name().then(pattern().repeated().collect()).boxed();
  let lhs = choice((lhs.clone(), lhs.clone().delimited_by(just(Token::LParen), just(Token::RParen))));

  lhs.then_ignore(just(Token::Equals)).then(term()).map(|((name, pats), body)| (name, Rule { pats, body }))
}

fn datatype<'a, I>() -> impl Parser<'a, I, (Name, Adt), extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  let arity_0 = name().map(|nam| (nam, vec![]));
  let arity_n = name()
    .then(name().repeated().collect::<Vec<_>>())
    .delimited_by(just(Token::LParen), just(Token::RParen))
    .map(|(nam, args)| (nam, args));
  let ctr = arity_0.or(arity_n);

  let data = soft_keyword("data");

  data
    .ignore_then(name())
    .then_ignore(just(Token::Equals))
    .then(ctr.separated_by(just(Token::Or)).collect::<Vec<(Name, Vec<Name>)>>())
    .map(|(name, ctrs)| (name, Adt { ctrs: ctrs.into_iter().collect() }))
}

fn book<'a, I>() -> impl Parser<'a, I, Book, extra::Err<Rich<'a, Token>>>
where
  I: ValueInput<'a, Token = Token, Span = SimpleSpan>,
{
  let top_level = choice((datatype().map(TopLevel::Adt), rule().map(TopLevel::Rule)));

  top_level.repeated().collect::<Vec<_>>().try_map(|program, span| {
    let mut book = Book::new();

    // Collect rules and adts into a book
    for top_level in program {
      match top_level {
        TopLevel::Rule((nam, rule)) => {
          if let Some(def_id) = book.def_names.def_id(&nam) {
            book.defs.get_mut(&def_id).unwrap().rules.push(rule);
          } else {
            book.insert_def(nam, vec![rule]);
          }
        }
        TopLevel::Adt((nam, adt)) => {
          if !book.adts.contains_key(&nam) {
            book.adts.insert(nam.clone(), adt.clone());
            for (ctr, _) in adt.ctrs {
              if let Entry::Vacant(e) = book.ctrs.entry(ctr) {
                e.insert(nam.clone());
              } else {
                return Err(Rich::custom(span, format!("Repeated constructor '{}'", nam)));
              }
            }
          } else {
            return Err(Rich::custom(span, format!("Repeated datatype '{}'", nam)));
          }
        }
      }
    }

    Ok(book)
  })
}

enum TopLevel {
  Rule((Name, Rule)),
  Adt((Name, Adt)),
}
