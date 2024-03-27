use clap::{Args, CommandFactory, Parser, Subcommand};
use hvml::{
  check_book, compile_book, desugar_book,
  diagnostics::{Diagnostics, DiagnosticsConfig, Severity},
  load_file_to_book, run_book,
  term::{AdtEncoding, Book, Name},
  CompileOpts, OptLevel, RunInfo, RunOpts,
};
use std::path::{Path, PathBuf};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
  #[command(subcommand)]
  pub mode: Mode,

  #[arg(short, long, global = true)]
  pub verbose: bool,

  #[arg(short = 'e', long, global = true, help = "Use other entrypoint rather than main or Main")]
  pub entrypoint: Option<Name>,
}

#[derive(Subcommand, Clone, Debug)]
enum Mode {
  /// Checks that the program is syntactically and semantically correct.
  Check {
    #[arg(help = "Path to the input file")]
    path: PathBuf,
  },
  /// Compiles the program to hvmc and prints to stdout.
  Compile {
    #[arg(
      short = 'O',
      value_delimiter = ' ',
      action = clap::ArgAction::Append,
      long_help = r#"Enables or disables the given optimizations
      float_combinators is enabled by default on strict mode."#,
    )]
    comp_opts: Vec<OptArgs>,

    #[arg(short = 'L', help = "Lazy mode")]
    lazy_mode: bool,

    #[command(flatten)]
    warn_opts: CliWarnOpts,

    #[arg(help = "Path to the input file")]
    path: PathBuf,
  },
  /// Compiles the program and runs it with the hvm.
  Run {
    #[arg(short = 'm', long = "mem", help = "How much memory to allocate for the runtime", value_parser = mem_parser)]
    max_memory: Option<usize>,

    #[arg(short = 'r', long = "rwts", help = "Maximum amount of rewrites", value_parser = mem_parser)]
    max_rewrites: Option<usize>,

    #[arg(short = 'd', help = "Debug mode (print each reduction step)")]
    debug: bool,

    #[arg(short = '1', help = "Single-core mode (no parallelism)")]
    single_core: bool,

    #[arg(short = 'L', help = "Lazy mode")]
    lazy_mode: bool,

    #[arg(short = 'l', help = "Linear readback (show explicit dups)")]
    linear: bool,

    #[arg(short = 's', long = "stats", help = "Shows runtime stats and rewrite counts")]
    arg_stats: bool,

    #[arg(help = "Path to the input file")]
    path: PathBuf,

    #[arg(
      short = 'O',
      value_delimiter = ' ',
      action = clap::ArgAction::Append,
      long_help = r#"Enables or disables the given optimizations
      float_combinators is enabled by default on strict mode."#,
    )]
    comp_opts: Vec<OptArgs>,

    #[arg(value_parser = |arg: &str| hvml::term::parser::parse_term(arg)
      .map_err(|e| match e[0].reason() {
        chumsky::error::RichReason::Many(errs) => format!("{}", &errs[0]),
        _ => format!("{}", e[0].reason()),
      }))]
    arguments: Option<Vec<hvml::term::Term>>,

    #[command(flatten)]
    warn_opts: CliWarnOpts,
  },
  /// Runs the lambda-term level desugaring passes.
  Desugar {
    #[arg(
      short = 'O',
      value_delimiter = ' ',
      action = clap::ArgAction::Append,
      long_help = r#"Enables or disables the given optimizations
      float_combinators is enabled by default on strict mode."#,
    )]
    comp_opts: Vec<OptArgs>,

    #[arg(short = 'L', help = "Lazy mode")]
    lazy_mode: bool,

    #[command(flatten)]
    warn_opts: CliWarnOpts,

    #[arg(help = "Path to the input file")]
    path: PathBuf,
  },
}

#[derive(Args, Debug, Clone)]
#[group(multiple = true)]
struct CliWarnOpts {
  #[arg(
    short = 'W',
    long = "warn",
    value_delimiter = ' ',
    action = clap::ArgAction::Append,
    help = "Show the specified compilation warning",
  )]
  pub warns: Vec<WarningArgs>,

  #[arg(
    short = 'D',
    long = "deny",
    value_delimiter = ' ',
    action = clap::ArgAction::Append,
    help = "Deny the specified compilation warning",
  )]
  pub denies: Vec<WarningArgs>,

  #[arg(
    short = 'A',
    long = "allow",
    value_delimiter = ' ',
    action = clap::ArgAction::Append,
    help = "Allow the specified compilation warning",
  )]
  pub allows: Vec<WarningArgs>,
}

#[derive(clap::ValueEnum, Clone, Debug)]
pub enum OptArgs {
  All,
  NoAll,
  Eta,
  NoEta,
  Prune,
  NoPrune,
  RefToRef,
  NoRefToRef,
  PreReduce,
  NoPreReduce,
  LinearizeMatches,
  LinearizeMatchesExtra,
  NoLinearizeMatches,
  FloatCombinators,
  NoFloatCombinators,
  SimplifyMain,
  NoSimplifyMain,
  Merge,
  NoMerge,
  Inline,
  NoInline,
  AdtScott,
  AdtTaggedScott,
}

impl OptArgs {
  fn opts_from_cli(args: &Vec<Self>) -> CompileOpts {
    use OptArgs::*;
    let mut opts = CompileOpts::light();
    for arg in args {
      match arg {
        All => opts = opts.set_all(),
        NoAll => opts = opts.set_no_all(),
        Eta => opts.eta = true,
        NoEta => opts.eta = false,
        Prune => opts.prune = true,
        NoPrune => opts.prune = false,
        RefToRef => opts.ref_to_ref = true,
        NoRefToRef => opts.ref_to_ref = false,
        PreReduce => opts.pre_reduce = true,
        NoPreReduce => opts.pre_reduce = false,
        FloatCombinators => opts.float_combinators = true,
        NoFloatCombinators => opts.float_combinators = false,
        SimplifyMain => opts.simplify_main = true,
        NoSimplifyMain => opts.simplify_main = false,
        Merge => opts.merge = true,
        NoMerge => opts.merge = false,
        Inline => opts.inline = true,
        NoInline => opts.inline = false,

        AdtScott => opts.adt_encoding = AdtEncoding::Scott,
        AdtTaggedScott => opts.adt_encoding = AdtEncoding::TaggedScott,

        LinearizeMatches => opts.linearize_matches = OptLevel::Enabled,
        LinearizeMatchesExtra => opts.linearize_matches = OptLevel::Extra,
        NoLinearizeMatches => opts.linearize_matches = OptLevel::Disabled,
      }
    }
    opts
  }
}

#[derive(clap::ValueEnum, Clone, Debug)]
pub enum WarningArgs {
  All,
  IrrefutableMatch,
  RedundantMatch,
  UnreachableMatch,
  UnusedDefinition,
  RepeatedBind,
  MutualRecursionCycle,
}

fn main() {
  #[cfg(not(feature = "cli"))]
  compile_error!("The 'cli' feature is needed for the hvm-lang cli");

  let cli = Cli::parse();

  if let Err(diagnostics) = execute_cli_mode(cli) {
    eprint!("{diagnostics}")
  }
}

fn execute_cli_mode(mut cli: Cli) -> Result<(), Diagnostics> {
  let arg_verbose = cli.verbose;
  let entrypoint = cli.entrypoint.take();

  let load_book = |path: &Path| -> Result<Book, Diagnostics> {
    let mut book = load_file_to_book(path)?;
    book.entrypoint = entrypoint;

    if arg_verbose {
      println!("{book}");
    }

    Ok(book)
  };

  match cli.mode {
    Mode::Check { path } => {
      let mut book = load_book(&path)?;
      check_book(&mut book)?;
    }

    Mode::Compile { path, comp_opts, warn_opts, lazy_mode } => {
      let diagnostics_cfg = set_warning_cfg_from_cli(
        DiagnosticsConfig::new(Severity::Warning, arg_verbose),
        lazy_mode,
        warn_opts,
      );

      let mut opts = OptArgs::opts_from_cli(&comp_opts);
      if lazy_mode {
        opts.lazy_mode();
      }

      let mut book = load_book(&path)?;
      let compile_res = compile_book(&mut book, opts, diagnostics_cfg, None)?;

      eprint!("{}", compile_res.diagnostics);
      println!("{}", compile_res.core_book);
    }

    Mode::Desugar { path, comp_opts, warn_opts, lazy_mode } => {
      let diagnostics_cfg = set_warning_cfg_from_cli(
        DiagnosticsConfig::new(Severity::Warning, arg_verbose),
        lazy_mode,
        warn_opts,
      );

      let mut opts = OptArgs::opts_from_cli(&comp_opts);
      if lazy_mode {
        opts.lazy_mode();
      }

      let mut book = load_book(&path)?;
      let diagnostics = desugar_book(&mut book, opts, diagnostics_cfg, None)?;

      eprint!("{diagnostics}");
      println!("{book}");
    }

    Mode::Run {
      path,
      max_memory,
      max_rewrites,
      debug,
      mut single_core,
      linear,
      arg_stats,
      comp_opts,
      warn_opts,
      lazy_mode,
      arguments,
    } => {
      if debug && lazy_mode {
        return Err(Diagnostics::from(
          "Unsupported configuration, can not use debug mode `-d` with lazy mode `-L`".to_string(),
        ));
      }

      let diagnostics_cfg =
        set_warning_cfg_from_cli(DiagnosticsConfig::new(Severity::Allow, arg_verbose), lazy_mode, warn_opts);

      let mut compile_opts = OptArgs::opts_from_cli(&comp_opts);
      compile_opts.check(lazy_mode);

      if lazy_mode {
        single_core = true;
        compile_opts.lazy_mode();
      }

      let run_opts = RunOpts { single_core, debug, linear, lazy_mode, max_memory, max_rewrites };

      let book = load_book(&path)?;
      let (res_term, RunInfo { stats, diagnostics, net, book: _, labels: _ }) =
        run_book(book, max_memory, run_opts, compile_opts, diagnostics_cfg, arguments)?;

      let total_rewrites = stats.rewrites.total() as f64;
      let rps = total_rewrites / stats.run_time / 1_000_000.0;
      let size = stats.used;

      if cli.verbose {
        println!("{net}");
      }

      eprint!("{diagnostics}");
      println!("{res_term}");

      if arg_stats {
        println!("\nRWTS   : {}", total_rewrites);
        println!("- ANNI : {}", stats.rewrites.anni);
        println!("- COMM : {}", stats.rewrites.comm);
        println!("- ERAS : {}", stats.rewrites.eras);
        println!("- DREF : {}", stats.rewrites.dref);
        println!("- OPER : {}", stats.rewrites.oper);
        println!("TIME   : {:.3} s", stats.run_time);
        println!("RPS    : {:.3} m", rps);
        println!("SIZE   : {} nodes", size);
      }
    }
  };
  Ok(())
}

fn mem_parser(arg: &str) -> Result<usize, String> {
  let (base, mult) = match arg.to_lowercase().chars().last() {
    None => return Err("Mem size argument is empty".to_string()),
    Some('k') => (&arg[0 .. arg.len() - 1], 1 << 10),
    Some('m') => (&arg[0 .. arg.len() - 1], 1 << 20),
    Some('g') => (&arg[0 .. arg.len() - 1], 1 << 30),
    Some(_) => (arg, 1),
  };
  let base = base.parse::<usize>().map_err(|e| e.to_string())?;
  Ok(base * mult)
}

fn set_warning_cfg_from_cli(
  mut cfg: DiagnosticsConfig,
  lazy_mode: bool,
  warn_opts: CliWarnOpts,
) -> DiagnosticsConfig {
  fn set(cfg: &mut DiagnosticsConfig, severity: Severity, cli_val: WarningArgs, lazy_mode: bool) {
    match cli_val {
      WarningArgs::All => {
        cfg.irrefutable_match = severity;
        cfg.redundant_match = severity;
        cfg.unreachable_match = severity;
        cfg.unused_definition = severity;
        cfg.repeated_bind = severity;
        if !lazy_mode {
          cfg.mutual_recursion_cycle = severity;
        }
      }
      WarningArgs::IrrefutableMatch => cfg.irrefutable_match = severity,
      WarningArgs::RedundantMatch => cfg.redundant_match = severity,
      WarningArgs::UnreachableMatch => cfg.unreachable_match = severity,
      WarningArgs::UnusedDefinition => cfg.unused_definition = severity,
      WarningArgs::RepeatedBind => cfg.repeated_bind = severity,
      WarningArgs::MutualRecursionCycle => cfg.mutual_recursion_cycle = severity,
    }
  }

  if !lazy_mode {
    cfg.mutual_recursion_cycle = Severity::Warning;
  }

  let cmd = Cli::command();
  let matches = cmd.get_matches();
  let subcmd_name = matches.subcommand_name().expect("To have a subcommand");
  let arg_matches = matches.subcommand_matches(subcmd_name).expect("To have a subcommand");

  if let Some(warn_opts_ids) = arg_matches.get_many::<clap::Id>("CliWarnOpts") {
    let mut allows = warn_opts.allows.into_iter();
    let mut warns = warn_opts.warns.into_iter();
    let mut denies = warn_opts.denies.into_iter();
    for id in warn_opts_ids {
      match id.as_ref() {
        "allows" => set(&mut cfg, Severity::Allow, allows.next().unwrap(), lazy_mode),
        "denies" => set(&mut cfg, Severity::Error, denies.next().unwrap(), lazy_mode),
        "warns" => set(&mut cfg, Severity::Warning, warns.next().unwrap(), lazy_mode),
        _ => unreachable!(),
      }
    }
  }
  cfg
}
