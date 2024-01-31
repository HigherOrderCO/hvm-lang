use hvmc::{
  ast::{parse_net, show_net, Host},
  run::Net,
};
use hvml::{
  compile_book, encode_pattern_matching, run_book,
  term::{
    encoder::{book_to_tree, term_to_compat_net, Labels},
    parser::{parse_definition_book, parse_term},
    readback::readback_and_resugar,
    Book, Term,
  },
  OptimizationLevel,
};
use insta::assert_snapshot;
use itertools::Itertools;
use std::{
  collections::BTreeMap,
  fs,
  path::{Path, PathBuf},
};
use stdext::function_name;
use walkdir::WalkDir;

fn do_parse_book(code: &str) -> Result<Book, String> {
  match parse_definition_book(code) {
    Ok(book) => Ok(book),
    Err(errs) => Err(errs.into_iter().map(|e| e.to_string()).join("\n")),
  }
}

fn do_parse_term(code: &str) -> Result<Term, String> {
  parse_term(code).map_err(|errs| errs.into_iter().map(|e| e.to_string()).join("\n"))
}

fn do_parse_net(code: &str) -> Result<hvmc::ast::Net, String> {
  parse_net(&mut code.chars().peekable())
}

const TESTS_PATH: &str = "/tests/golden_tests/";

fn run_single_golden_test(path: &Path, run: &dyn Fn(&str) -> Result<String, String>) -> Result<(), String> {
  let code = fs::read_to_string(path).map_err(|e| e.to_string())?;
  let file_name = path.to_str().and_then(|path| path.rsplit_once(TESTS_PATH)).unwrap().1;

  let result: String = run(&code).unwrap_or_else(|err| err);

  let mut settings = insta::Settings::clone_current();
  settings.set_prepend_module_to_snapshot(false);
  settings.set_omit_expression(true);
  settings.set_input_file(path);

  settings.bind(|| {
    assert_snapshot!(file_name, result);
  });

  Ok(())
}

fn run_golden_test_dir(test_name: &str, run: &dyn Fn(&str) -> Result<String, String>) {
  let root = PathBuf::from(format!(
    "{}{TESTS_PATH}{}",
    env!("CARGO_MANIFEST_DIR"),
    test_name.rsplit_once(':').unwrap().1
  ));

  let walker = WalkDir::new(&root).sort_by_file_name().max_depth(2).into_iter().filter_entry(|e| {
    let path = e.path();
    path == root || (path.is_file() && path.extension().is_some_and(|x| x == "hvm"))
  });

  for entry in walker {
    let entry = entry.unwrap();
    let path = entry.path();
    if path.is_file() {
      run_single_golden_test(path, run).unwrap();
    }
  }
}

#[test]
fn compile_term() {
  run_golden_test_dir(function_name!(), &|code| {
    let mut term = do_parse_term(code)?;

    let net = term_to_compat_net(&term, &mut Labels::default());

    let result = show_net(&net);

    Ok(result)
  })
}

#[test]
fn compile_file() {
  run_golden_test_dir(function_name!(), &|code| {
    let mut book = do_parse_book(code)?;
    let compiled = compile_book(&mut book, OptimizationLevel::Heavy)?;
    Ok(format!("{:?}", compiled))
  })
}

#[test]
fn compile_file_o0() {
  run_golden_test_dir(function_name!(), &|code| {
    let mut book = do_parse_book(code)?;
    let compiled = compile_book(&mut book, OptimizationLevel::Light)?;
    Ok(format!("{:?}", compiled))
  })
}

#[test]
fn run_file() {
  run_golden_test_dir(function_name!(), &|code| {
    let book = do_parse_book(code)?;
    // 1 million nodes for the test runtime. Smaller doesn't seem to make it any faster
    let (res, def_names, info) = run_book(book, 1 << 20, true, false, false, OptimizationLevel::Heavy)?;
    let res = if info.readback_errors.is_empty() {
      res.display(&def_names).to_string()
    } else {
      format!("Invalid readback: {:?}\n{}", info.readback_errors, res.display(&def_names))
    };
    Ok(res)
  })
}

#[test]
fn readback_lnet() {
  run_golden_test_dir(function_name!(), &|code| {
    let net = do_parse_net(code)?;
    let book = Book::default();
    let term = {
      let mut host = Host::new(&[(String::from("main"), net)].into_iter().collect());

      let heap = Net::init_heap(1 << 16);
      let mut rt_net = Net::new(&heap);
      rt_net.boot(host.defs.get_mut("main").as_mut().unwrap());
      readback_and_resugar(&mut rt_net, &Labels::default(), &host, &book)
    };
    let x = Ok(term.display(&book.def_names).to_string());
    x
  })
}

#[test]
fn flatten_rules() {
  run_golden_test_dir(function_name!(), &|code| {
    let mut book = do_parse_book(code)?;
    book.check_shared_names()?;
    book.resolve_ctrs_in_pats();
    book.generate_scott_adts();
    book.desugar_let_destructors();
    book.desugar_implicit_match_binds();
    book.check_unbound_pats()?;
    book.extract_matches()?;
    book.flatten_rules();
    Ok(book.to_string())
  })
}

#[test]
fn encode_pattern_match() {
  run_golden_test_dir(function_name!(), &|code| {
    let mut book = do_parse_book(code)?;
    book.check_shared_names()?;
    book.encode_strs();
    book.generate_scott_adts();
    book.resolve_refs();
    encode_pattern_matching(&mut book)?;
    Ok(book.to_string())
  })
}
