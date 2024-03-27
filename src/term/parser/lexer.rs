use interner::global::{GlobalPool, GlobalString};
use logos::{FilterResult, Lexer, Logos};
use std::{fmt, num::ParseIntError};

pub static STRINGS: GlobalPool<String> = GlobalPool::new();

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(error=LexingError)]
#[logos(skip r"[ \t\r\n\f]+")]
pub enum Token {
  #[regex("[_.a-zA-Z][_.a-zA-Z0-9-]*", |lex| lex.slice().parse().ok().map(|s: String| STRINGS.get(s)))]
  Name(GlobalString),

  #[regex("@|λ")]
  Lambda,

  #[token("$")]
  Dollar,

  #[token("let")]
  Let,

  #[token("use")]
  Use,

  #[token("match")]
  Match,

  #[token("switch")]
  Switch,

  #[token("=")]
  Equals,

  #[regex("0[bB][0-9a-zA-Z_]+", |lex| from_radix(2, lex))]
  #[regex("0[xX][0-9a-zA-Z_]+", |lex| from_radix(16, lex))]
  #[regex("[0-9][0-9a-zA-Z_]*", |lex| from_radix(10, lex))]
  Num(u64),

  #[regex(r#""([^"\\]|\\[0tunr'"\\])*""#, |lex| normalized_string(lex).ok())]
  #[regex(r#"`([^`\\]|\\[0tunr`'"\\])*`"#, |lex| normalized_string(lex).ok())]
  Str(GlobalString),

  #[regex(r#"'\\U[0-9a-fA-F]{1,8}'"#, normalized_char, priority = 2)]
  // Since '.' is just covering any ascii char, we need to make the
  // regex match any possible character of the unicode general category
  #[regex(
    r#"'(\p{L}|\p{M}|\p{N}|\p{P}|\p{S}|\p{Z}|\p{C}|\p{Emoji}|\\u[0-9a-fA-F]{1,4}|\\[0tunr`'"\\])'"#,
    normalized_char
  )]
  Char(u64),

  #[token("#")]
  Hash,

  #[token("+")]
  Add,

  #[token("-")]
  Sub,

  #[token("*")]
  Asterisk,

  #[token("/")]
  Div,

  #[token("%")]
  Mod,

  #[token("~")]
  Tilde,

  #[token("&")]
  And,

  #[token("|")]
  Or,

  #[token("^")]
  Xor,

  #[token("<<")]
  Shl,

  #[token(">>")]
  Shr,

  #[token("<")]
  Ltn,

  #[token(">")]
  Gtn,

  #[token("<=")]
  Lte,

  #[token(">=")]
  Gte,

  #[token("==")]
  EqualsEquals,

  #[token("!=")]
  NotEquals,

  #[token(";")]
  Semicolon,

  #[token(":")]
  Colon,

  #[token(",")]
  Comma,

  #[token("(")]
  LParen,

  #[token(")")]
  RParen,

  #[token("{")]
  LBracket,

  #[token("}")]
  RBracket,

  #[token("[")]
  LBrace,

  #[token("]")]
  RBrace,

  #[regex("//.*", logos::skip)]
  SingleLineComment,

  #[token("/*", comment)]
  MultiLineComment,

  Error(LexingError),
}

fn from_radix(radix: u32, lexer: &mut Lexer<Token>) -> Result<u64, ParseIntError> {
  let slice = if radix == 10 { lexer.slice() } else { &lexer.slice()[2 ..] };
  let slice = &slice.replace('_', "");
  u64::from_str_radix(slice, radix)
}

#[derive(Default, Debug, PartialEq, Clone)]
pub enum LexingError {
  UnclosedComment,

  #[default]
  InvalidCharacter,

  InvalidNumberLiteral,
}

impl From<ParseIntError> for LexingError {
  fn from(_: ParseIntError) -> Self {
    LexingError::InvalidNumberLiteral
  }
}

// Lexer for nested multi-line comments
#[derive(Logos)]
pub enum MultiLineComment {
  #[token("/*")]
  Open,

  #[token("*/")]
  Close,

  #[regex("(?s).")]
  Other,
}

fn comment(lexer: &mut Lexer<'_, Token>) -> FilterResult<(), LexingError> {
  let start = lexer.remainder();
  let mut comment = MultiLineComment::lexer(start);
  let mut depth = 1; // Already matched an Open token, so count it
  loop {
    if let Some(token) = comment.next() {
      match token {
        Ok(MultiLineComment::Open) => depth += 1,
        Ok(MultiLineComment::Close) => depth -= 1,
        Ok(MultiLineComment::Other) => {}
        Err(()) => unreachable!(),
      }
    } else {
      // Unclosed comment
      return FilterResult::Error(LexingError::UnclosedComment);
    }
    if depth <= 0 {
      break;
    }
  }
  let end = comment.remainder();
  let span = (end as *const str as *const () as usize) - (start as *const str as *const () as usize);
  lexer.bump(span);
  FilterResult::Skip
}

fn normalized_string(lexer: &mut Lexer<Token>) -> Result<GlobalString, ParseIntError> {
  let slice = lexer.slice();
  let slice = &slice[1 .. slice.len() - 1];

  let mut s = String::new();
  let chars = &mut slice.chars();

  while let Some(char) = chars.next() {
    match char {
      '\\' => match chars.next() {
        Some('\\') => s.push('\\'),
        Some('`') => s.push('`'),
        Some('\'') => s.push('\''),
        Some('\"') => s.push('\"'),
        Some('n') => s.push('\n'),
        Some('r') => s.push('\r'),
        Some('t') => s.push('\t'),
        Some('u') | Some('U') => {
          let hex = chars.take(8).collect::<String>();
          let hex_val = u32::from_str_radix(&hex, 16)?;
          let char = char::from_u32(hex_val).unwrap_or(char::REPLACEMENT_CHARACTER);
          s.push(char);
        }
        Some('0') => s.push('\0'),
        Some(other) => {
          s.push('\\');
          s.push(other);
        }
        None => s.push('\\'),
      },
      other => s.push(other),
    }
  }
  Ok(STRINGS.get(s))
}

fn normalized_char(lexer: &mut Lexer<Token>) -> Option<u64> {
  let slice = lexer.slice();
  let slice = &slice[1 .. slice.len() - 1];
  let chars = &mut slice.chars();
  let c = match chars.next()? {
    '\\' => match chars.next() {
      Some('\\') => '\\',
      Some('`') => '`',
      Some('\"') => '\"',
      Some('\'') => '\'',
      Some('n') => '\n',
      Some('r') => '\r',
      Some('t') => '\t',
      Some('u') | Some('U') => {
        let hex = chars.take(8).collect::<String>();
        let hex_val = u32::from_str_radix(&hex, 16).unwrap();
        char::from_u32(hex_val).unwrap_or(char::REPLACEMENT_CHARACTER)
      }
      Some('0') => '\0',
      Some(..) => return None,
      None => '\\',
    },
    other => other,
  };
  Some(u64::from(c))
}

impl fmt::Display for Token {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Name(s) => write!(f, "{}", s),
      Self::Lambda => write!(f, "λ"),
      Self::Dollar => write!(f, "$"),
      Self::Let => write!(f, "let"),
      Self::Use => write!(f, "use"),
      Self::Match => write!(f, "match"),
      Self::Switch => write!(f, "switch"),
      Self::Equals => write!(f, "="),
      Self::Num(num) => write!(f, "{num}"),
      Self::Str(s) => write!(f, "\"{s}\""),
      Self::Char(c) => write!(f, "'{c}'"),
      Self::Hash => write!(f, "#"),
      Self::Add => write!(f, "+"),
      Self::Sub => write!(f, "-"),
      Self::Asterisk => write!(f, "*"),
      Self::Div => write!(f, "/"),
      Self::Mod => write!(f, "%"),
      Self::Tilde => write!(f, "~"),
      Self::And => write!(f, "&"),
      Self::Or => write!(f, "|"),
      Self::Xor => write!(f, "^"),
      Self::Shl => write!(f, "<<"),
      Self::Shr => write!(f, ">>"),
      Self::Ltn => write!(f, "<"),
      Self::Gtn => write!(f, ">"),
      Self::Lte => write!(f, "<="),
      Self::Gte => write!(f, ">="),
      Self::NotEquals => write!(f, "!="),
      Self::EqualsEquals => write!(f, "=="),
      Self::Colon => write!(f, ":"),
      Self::Comma => write!(f, ","),
      Self::Semicolon => write!(f, ";"),
      Self::LParen => write!(f, "("),
      Self::RParen => write!(f, ")"),
      Self::LBracket => write!(f, "{{"),
      Self::RBracket => write!(f, "}}"),
      Self::LBrace => write!(f, "["),
      Self::RBrace => write!(f, "]"),
      Self::SingleLineComment => write!(f, "<SingleLineComment>"),
      Self::MultiLineComment => write!(f, "<MultiLineComment>"),
      Self::Error(LexingError::InvalidNumberLiteral) => write!(f, "<InvalidNumberLiteral>"),
      Self::Error(LexingError::InvalidCharacter) => write!(f, "<InvalidCharacter>"),
      Self::Error(LexingError::UnclosedComment) => write!(f, "<UnclosedComment>"),
    }
  }
}
