use hvml::{
  compile_book, desugar_book,
  diagnostics::{Diagnostics, DiagnosticsConfig, Severity, ToStringVerbose},
  net::{hvmc_to_net::hvmc_to_net, net_to_hvmc::net_to_hvmc},
  run_book,
  term::{
    load_book::do_parse_book, net_to_term::net_to_term, parser::parse_term, term_to_compat_net,
    term_to_net::Labels, AdtEncoding, Book, Ctx, Name, Term,
  },
  CompileOpts, RunOpts,
};
use insta::assert_snapshot;
use itertools::Itertools;
use std::{
  collections::HashMap,
  fmt::Write,
  io::Read,
  path::{Path, PathBuf},
  str::FromStr,
};
use stdext::function_name;
use walkdir::WalkDir;

fn format_output(output: std::process::Output) -> String {
  format!("{}{}", String::from_utf8_lossy(&output.stderr), String::from_utf8_lossy(&output.stdout))
}

fn do_parse_term(code: &str) -> Result<Term, String> {
  parse_term(code).map_err(|errs| errs.into_iter().map(|e| e.to_string()).join("\n"))
}

fn do_parse_net(code: &str) -> Result<hvmc::ast::Net, String> {
  hvmc::ast::Net::from_str(code)
}

const TESTS_PATH: &str = "/tests/golden_tests/";

type RunFn = dyn Fn(&str, &Path) -> Result<String, Diagnostics>;

fn run_single_golden_test(path: &Path, run: &[&RunFn]) -> Result<(), String> {
  let code = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
  let file_name = path.to_str().and_then(|path| path.rsplit_once(TESTS_PATH)).unwrap().1;

  // unfortunately we need to do this
  let file_path = format!("{}{}", &TESTS_PATH[1 ..], file_name);
  let file_path = Path::new(&file_path);

  let mut results: HashMap<&Path, Vec<String>> = HashMap::new();
  for fun in run {
    let result = fun(&code, file_path).unwrap_or_else(|err| err.to_string());
    results.entry(file_path).or_default().push(result);
  }
  let results = results.into_values().map(|v| v.join("\n")).collect_vec();

  let mut settings = insta::Settings::clone_current();
  settings.set_prepend_module_to_snapshot(false);
  settings.set_omit_expression(true);
  settings.set_input_file(path);

  settings.bind(|| {
    for result in results {
      assert_snapshot!(file_name, result);
    }
  });

  Ok(())
}

fn run_golden_test_dir(test_name: &str, run: &RunFn) {
  run_golden_test_dir_multiple(test_name, &[run])
}

fn run_golden_test_dir_multiple(test_name: &str, run: &[&RunFn]) {
  let root = PathBuf::from(format!(
    "{}{TESTS_PATH}{}",
    env!("CARGO_MANIFEST_DIR"),
    test_name.rsplit_once(':').unwrap().1
  ));

  let walker = WalkDir::new(&root).sort_by_file_name().max_depth(2).into_iter().filter_entry(|e| {
    let path = e.path();
    path == root || path.is_dir() || (path.is_file() && path.extension().is_some_and(|x| x == "hvm"))
  });

  for entry in walker {
    let entry = entry.unwrap();
    let path = entry.path();
    if path.is_file() {
      eprintln!("Testing {}", path.display());
      run_single_golden_test(path, run).unwrap();
    }
  }
}

#[test]
fn compile_term() {
  run_golden_test_dir(function_name!(), &|code, _| {
    let mut term = do_parse_term(code)?;
    let mut vec = Vec::new();
    term.check_unbound_vars(&mut HashMap::new(), &mut vec);

    if !vec.is_empty() {
      return Err(vec.into_iter().map(|e| e.to_string_verbose(true)).join("\n").into());
    }

    term.make_var_names_unique();
    term.linearize_vars();
    let compat_net = term_to_compat_net(&term, &mut Default::default());
    let net = net_to_hvmc(&compat_net).map_err(|e| e.to_string_verbose(true))?;

    Ok(format!("{}", net))
  })
}

#[test]
fn compile_file_o_all() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let diagnostics_cfg = DiagnosticsConfig::new(Severity::Warning, true);
    let mut book = do_parse_book(code, path)?;
    let res = compile_book(&mut book, CompileOpts::heavy(), diagnostics_cfg, None)?;
    Ok(format!("{}{}", res.diagnostics, res.core_book))
  })
}
#[test]
fn compile_file() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let diagnostics_cfg = DiagnosticsConfig::new(Severity::Warning, true);
    let mut book = do_parse_book(code, path)?;
    let res = compile_book(&mut book, CompileOpts::light(), diagnostics_cfg, None)?;
    Ok(format!("{}{}", res.diagnostics, res.core_book))
  })
}

#[test]
fn linear_readback() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let diagnostics_cfg = DiagnosticsConfig::new(Severity::Error, true);
    let book = do_parse_book(code, path)?;
    let (res, info) = run_book(
      book,
      None,
      RunOpts { linear: true, ..Default::default() },
      CompileOpts::heavy(),
      diagnostics_cfg,
      None,
    )?;
    Ok(format!("{}{}", info.diagnostics, res))
  });
}
#[test]
fn run_file() {
  run_golden_test_dir_multiple(function_name!(), &[
    (&|_code, path| {
      let output = std::process::Command::new(env!("CARGO_BIN_EXE_hvml"))
        .args(["run", path.to_str().unwrap(), "-Dall", "-Oall", "-L"])
        .output()
        .expect("Run process");

      Ok(format!("Lazy mode:\n{}", format_output(output)))
    }),
    (&|_code, path| {
      let output = std::process::Command::new(env!("CARGO_BIN_EXE_hvml"))
        .args(["run", path.to_str().unwrap(), "-Dall", "-Oall"])
        .output()
        .expect("Run process");

      Ok(format!("Strict mode:\n{}", format_output(output)))
    }),
  ])
}

#[test]
fn run_lazy() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let diagnostics_cfg = DiagnosticsConfig {
      mutual_recursion_cycle: Severity::Allow,
      ..DiagnosticsConfig::new(Severity::Error, true)
    };
    let book = do_parse_book(code, path)?;

    let mut desugar_opts = CompileOpts::heavy();
    let run_opts = RunOpts::lazy();
    desugar_opts.lazy_mode();

    // 1 million nodes for the test runtime. Smaller doesn't seem to make it any faster
    let (res, info) = run_book(book, None, run_opts, desugar_opts, diagnostics_cfg, None)?;
    Ok(format!("{}{}", info.diagnostics, res))
  })
}

#[test]
fn readback_lnet() {
  run_golden_test_dir(function_name!(), &|code, _| {
    let net = do_parse_net(code)?;
    let book = Book::default();
    let compat_net = hvmc_to_net(&net);
    let mut diags = Diagnostics::default();
    let term = net_to_term(&compat_net, &book, &Labels::default(), false, &mut diags);
    Ok(format!("{}{}", diags, term))
  })
}

#[test]
fn simplify_matches() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let diagnostics_cfg = DiagnosticsConfig::new(Severity::Error, true);
    let mut book = do_parse_book(code, path)?;
    let mut ctx = Ctx::new(&mut book, diagnostics_cfg);
    ctx.check_shared_names();
    ctx.set_entrypoint();
    ctx.book.encode_adts(AdtEncoding::TaggedScott);
    ctx.book.encode_builtins();
    ctx.book.resolve_ctrs_in_pats();
    ctx.resolve_refs()?;
    ctx.check_match_arity()?;
    ctx.check_unbound_pats()?;
    ctx.book.convert_match_def_to_term();
    ctx.book.desugar_let_destructors();
    ctx.book.desugar_implicit_match_binds();
    ctx.check_ctrs_arities()?;
    ctx.check_unbound_vars()?;
    ctx.simplify_matches()?;
    ctx.book.linearize_simple_matches(true);
    ctx.check_unbound_vars()?;
    ctx.book.make_var_names_unique();
    ctx.book.linearize_vars();
    ctx.prune(false, AdtEncoding::TaggedScott);
    Ok(ctx.book.to_string())
  })
}

#[test]
fn parse_file() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let book = do_parse_book(code, path)?;
    Ok(book.to_string())
  })
}

#[test]
fn encode_pattern_match() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let mut result = String::new();
    for adt_encoding in [AdtEncoding::TaggedScott, AdtEncoding::Scott] {
      let diagnostics_cfg = DiagnosticsConfig::new(Severity::Error, true);
      let mut book = do_parse_book(code, path)?;
      let mut ctx = Ctx::new(&mut book, diagnostics_cfg);
      ctx.check_shared_names();
      ctx.set_entrypoint();
      ctx.book.encode_adts(adt_encoding);
      ctx.book.encode_builtins();
      ctx.book.resolve_ctrs_in_pats();
      ctx.resolve_refs()?;
      ctx.check_match_arity()?;
      ctx.check_unbound_pats()?;
      ctx.book.convert_match_def_to_term();
      ctx.book.desugar_let_destructors();
      ctx.book.desugar_implicit_match_binds();
      ctx.check_ctrs_arities()?;
      ctx.check_unbound_vars()?;
      ctx.simplify_matches()?;
      ctx.book.linearize_simple_matches(true);
      ctx.book.encode_simple_matches(adt_encoding);
      ctx.check_unbound_vars()?;
      ctx.book.make_var_names_unique();
      ctx.book.linearize_vars();
      ctx.prune(false, adt_encoding);

      writeln!(result, "{adt_encoding:?}:").unwrap();
      writeln!(result, "{}\n", ctx.book).unwrap();
    }
    Ok(result)
  })
}

#[test]
fn desugar_file() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let mut diagnostics_cfg = DiagnosticsConfig::new(Severity::Error, true);
    diagnostics_cfg.unused_definition = Severity::Allow;
    let mut book = do_parse_book(code, path)?;
    desugar_book(&mut book, CompileOpts::light(), diagnostics_cfg, None)?;
    Ok(book.to_string())
  })
}

#[test]
#[ignore = "to not delay golden tests execution"]
fn hangs() {
  let expected_normalization_time = 5;

  run_golden_test_dir(function_name!(), &move |code, path| {
    let diagnostics_cfg = DiagnosticsConfig::new(Severity::Warning, true);
    let book = do_parse_book(code, path)?;

    let thread = std::thread::spawn(move || {
      run_book(book, None, RunOpts::default(), CompileOpts::heavy(), diagnostics_cfg, None)
    });
    std::thread::sleep(std::time::Duration::from_secs(expected_normalization_time));

    if !thread.is_finished() { Ok("Hangs".into()) } else { Err("Doesn't hang".to_string().into()) }
  })
}

#[test]
fn compile_entrypoint() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let diagnostics_cfg = DiagnosticsConfig::new(Severity::Error, true);
    let mut book = do_parse_book(code, path)?;
    book.entrypoint = Some(Name::from("foo"));
    let res = compile_book(&mut book, CompileOpts::light(), diagnostics_cfg, None)?;
    Ok(format!("{}{}", res.diagnostics, res.core_book))
  })
}

#[test]
fn run_entrypoint() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let diagnostics_cfg = DiagnosticsConfig::new(Severity::Error, true);
    let mut book = do_parse_book(code, path)?;
    book.entrypoint = Some(Name::from("foo"));
    let (res, info) = run_book(book, None, RunOpts::default(), CompileOpts::heavy(), diagnostics_cfg, None)?;
    Ok(format!("{}{}", info.diagnostics, res))
  })
}

#[test]
fn cli() {
  run_golden_test_dir(function_name!(), &|_code, path| {
    let mut args_path = PathBuf::from(path);
    assert!(args_path.set_extension("args"));

    let mut args_buf = String::with_capacity(16);
    let mut args_file = std::fs::File::open(args_path).expect("File exists");
    args_file.read_to_string(&mut args_buf).expect("Read args");
    let args = args_buf.lines();

    let output =
      std::process::Command::new(env!("CARGO_BIN_EXE_hvml")).args(args).output().expect("Run command");

    Ok(format_output(output))
  })
}

#[test]
fn mutual_recursion() {
  run_golden_test_dir(function_name!(), &|code, path| {
    let diagnostics_cfg = DiagnosticsConfig {
      mutual_recursion_cycle: Severity::Error,
      ..DiagnosticsConfig::new(Severity::Allow, true)
    };
    let mut book = do_parse_book(code, path)?;
    let mut opts = CompileOpts::light();
    opts.merge = true;
    let res = compile_book(&mut book, opts, diagnostics_cfg, None)?;
    Ok(format!("{}{}", res.diagnostics, res.core_book))
  })
}
