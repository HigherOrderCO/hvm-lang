use crate::term::{display::DisplayFn, Name};
use std::{
  collections::BTreeMap,
  fmt::{Display, Formatter},
};

pub const ERR_INDENT_SIZE: usize = 2;

#[derive(Debug, Clone, Default)]
pub struct Diagnostics {
  err_counter: usize,
  pub diagnostics: BTreeMap<DiagnosticOrigin, Vec<Diagnostic>>,
  config: DiagnosticsConfig,
}

#[derive(Debug, Clone, Copy)]
pub struct DiagnosticsConfig {
  pub verbose: bool,
  pub irrefutable_match: Severity,
  pub redundant_match: Severity,
  pub unreachable_match: Severity,
  pub unused_definition: Severity,
  pub repeated_bind: Severity,
  pub mutual_recursion_cycle: Severity,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
  message: String,
  severity: Severity,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum DiagnosticOrigin {
  /// An error from the relationship between multiple top-level definitions.
  Book,
  /// An error in a pattern-matching function definition rule.
  Rule(Name),
  /// An error in a compiled inet.
  Inet(String),
  /// An error during readback of hvm-core run results.
  Readback,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Severity {
  Error,
  Warning,
  Allow,
}

#[derive(Debug, Clone, Copy)]
pub enum WarningType {
  IrrefutableMatch,
  RedundantMatch,
  UnreachableMatch,
  UnusedDefinition,
  RepeatedBind,
  MutualRecursionCycle,
}

pub trait ToStringVerbose {
  fn to_string_verbose(&self, verbose: bool) -> String;
}

impl Diagnostics {
  pub fn new(config: DiagnosticsConfig) -> Self {
    Self { err_counter: 0, diagnostics: Default::default(), config }
  }

  pub fn add_book_error(&mut self, err: impl ToStringVerbose) {
    self.err_counter += 1;
    self.add_diagnostic(err, Severity::Error, DiagnosticOrigin::Book);
  }

  pub fn add_rule_error(&mut self, err: impl ToStringVerbose, def_name: Name) {
    self.err_counter += 1;
    self.add_diagnostic(err, Severity::Error, DiagnosticOrigin::Rule(def_name));
  }

  pub fn add_inet_error(&mut self, err: impl ToStringVerbose, def_name: String) {
    self.err_counter += 1;
    self.add_diagnostic(err, Severity::Error, DiagnosticOrigin::Inet(def_name));
  }

  pub fn add_rule_warning(&mut self, warn: impl ToStringVerbose, warn_type: WarningType, def_name: Name) {
    let severity = self.config.warning_severity(warn_type);
    if severity == Severity::Error {
      self.err_counter += 1;
    }
    self.add_diagnostic(warn, severity, DiagnosticOrigin::Rule(def_name));
  }

  pub fn add_book_warning(&mut self, warn: impl ToStringVerbose, warn_type: WarningType) {
    let severity = self.config.warning_severity(warn_type);
    if severity == Severity::Error {
      self.err_counter += 1;
    }
    self.add_diagnostic(warn, severity, DiagnosticOrigin::Book);
  }

  pub fn add_diagnostic(&mut self, msg: impl ToStringVerbose, severity: Severity, orig: DiagnosticOrigin) {
    let diag = Diagnostic { message: msg.to_string_verbose(self.config.verbose), severity };
    self.diagnostics.entry(orig).or_default().push(diag)
  }

  pub fn take_rule_err<T, E: ToStringVerbose>(&mut self, result: Result<T, E>, def_name: Name) -> Option<T> {
    match result {
      Ok(t) => Some(t),
      Err(e) => {
        self.add_rule_error(e, def_name);
        None
      }
    }
  }

  pub fn take_inet_err<T, E: ToStringVerbose>(
    &mut self,
    result: Result<T, E>,
    def_name: String,
  ) -> Option<T> {
    match result {
      Ok(t) => Some(t),
      Err(e) => {
        self.add_inet_error(e, def_name);
        None
      }
    }
  }

  pub fn has_severity(&self, severity: Severity) -> bool {
    self.diagnostics.values().any(|errs| errs.iter().any(|e| e.severity == severity))
  }

  pub fn has_errors(&self) -> bool {
    self.has_severity(Severity::Error)
  }

  /// Resets the internal counter
  pub fn start_pass(&mut self) {
    self.err_counter = 0;
  }

  /// Checks if any error was emitted since the start of the pass,
  /// Returning all the current information as a `Err(Info)`, replacing `&mut self` with an empty one.
  /// Otherwise, returns the given arg as an `Ok(T)`.
  pub fn fatal<T>(&mut self, t: T) -> Result<T, Diagnostics> {
    if self.err_counter == 0 { Ok(t) } else { Err(std::mem::take(self)) }
  }

  /// Returns a Display that prints the diagnostics with one of the given severities.
  pub fn display_with_severity(&self, severity: Severity) -> impl std::fmt::Display + '_ {
    DisplayFn(move |f| {
      fn filter<'a>(
        errs: impl IntoIterator<Item = &'a Diagnostic>,
        severity: Severity,
      ) -> impl Iterator<Item = &'a Diagnostic> {
        errs.into_iter().filter(move |err| err.severity == severity)
      }

      let mut has_msg = false;
      for (orig, errs) in &self.diagnostics {
        let mut errs = filter(errs, severity).peekable();
        if errs.peek().is_some() {
          match orig {
            DiagnosticOrigin::Book => {
              for err in errs {
                writeln!(f, "{err}")?;
              }
            }
            DiagnosticOrigin::Rule(nam) => {
              writeln!(f, "In definition '{nam}':")?;
              for err in errs {
                writeln!(f, "{:ERR_INDENT_SIZE$}{err}", "")?;
              }
            }
            DiagnosticOrigin::Inet(nam) => {
              writeln!(f, "In compiled inet '{nam}':")?;
              for err in errs {
                writeln!(f, "{:ERR_INDENT_SIZE$}{err}", "")?;
              }
            }
            DiagnosticOrigin::Readback => {
              writeln!(f, "During readback:")?;
              for err in errs {
                writeln!(f, "{:ERR_INDENT_SIZE$}{err}", "")?;
              }
            }
          }
          has_msg = true;
        }
      }
      if has_msg {
        writeln!(f)?;
      }
      Ok(())
    })
  }
}

impl Display for Diagnostics {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    if self.has_severity(Severity::Warning) {
      write!(f, "Warnings:\n{}", self.display_with_severity(Severity::Warning))?;
    }
    if self.has_severity(Severity::Error) {
      write!(f, "Errors:\n{}", self.display_with_severity(Severity::Error))?;
    }
    Ok(())
  }
}

impl From<String> for Diagnostics {
  fn from(value: String) -> Self {
    Self {
      diagnostics: BTreeMap::from_iter([(DiagnosticOrigin::Book, vec![Diagnostic {
        message: value,
        severity: Severity::Error,
      }])]),
      ..Default::default()
    }
  }
}

impl DiagnosticsConfig {
  pub fn new(severity: Severity, verbose: bool) -> Self {
    Self {
      irrefutable_match: severity,
      redundant_match: severity,
      unreachable_match: severity,
      unused_definition: severity,
      repeated_bind: severity,
      mutual_recursion_cycle: severity,
      verbose,
    }
  }

  pub fn warning_severity(&self, warn: WarningType) -> Severity {
    match warn {
      WarningType::UnusedDefinition => self.unused_definition,
      WarningType::RepeatedBind => self.repeated_bind,
      WarningType::MutualRecursionCycle => self.mutual_recursion_cycle,
      WarningType::IrrefutableMatch => self.irrefutable_match,
      WarningType::RedundantMatch => self.redundant_match,
      WarningType::UnreachableMatch => self.unreachable_match,
    }
  }
}

impl Default for DiagnosticsConfig {
  fn default() -> Self {
    Self::new(Severity::Warning, false)
  }
}

impl Display for Diagnostic {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.message)
  }
}

impl ToStringVerbose for &str {
  fn to_string_verbose(&self, _verbose: bool) -> String {
    self.to_string()
  }
}

impl ToStringVerbose for String {
  fn to_string_verbose(&self, _verbose: bool) -> String {
    self.clone()
  }
}
