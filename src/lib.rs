#![feature(box_patterns)]

use std::time::Instant;

use hvmc::{
  ast::{show_book, Host, Net},
  run::{Area, Net as RtNet, Rewrites},
};
use hvmc_net::{pre_reduce::pre_reduce_book, prune::prune_defs};
use loaned::LoanedMut;
use term::{
  encoder::{book_to_tree, Labels},
  Book, DefId, DefNames, ReadbackError, Term,
};

pub mod hvmc_net;
pub mod term;

pub use term::load_book::load_file_to_book;

pub fn check_book(mut book: Book) -> Result<(), String> {
  // TODO: Do the checks without having to do full compilation
  compile_book(&mut book, OptimizationLevel::Light)?;
  Ok(())
}

pub fn compile_book(book: &mut Book, opt_level: OptimizationLevel) -> Result<CompileResult, String> {
  let main = desugar_book(book, opt_level)?;
  let mut core_book = book_to_tree(book, main);
  pre_reduce_book(&mut core_book, opt_level >= OptimizationLevel::Heavy)?;
  if opt_level >= OptimizationLevel::Heavy {
    prune_defs(&mut core_book);
  }

  Ok(CompileResult { core_book, labels: Labels::default(), warnings: vec![] })
}

pub fn desugar_book(book: &mut Book, opt_level: OptimizationLevel) -> Result<DefId, String> {
  let main = book.check_has_main()?;
  book.check_shared_names()?;
  book.encode_strs();
  book.generate_scott_adts();
  book.resolve_refs();
  encode_pattern_matching(book)?;
  println!("POST DESUGAR:\n{}", book);
  book.unscope_vars();

  println!("POST UNSCOPE:\n{}", book);
  book.linearize_vars();
  println!("POST LINEARIZE\n{}", book);
  if opt_level >= OptimizationLevel::Heavy {
    book.eta_reduction();
  }
  book.detach_supercombinators();
  if opt_level >= OptimizationLevel::Heavy {
    book.simplify_ref_to_ref()?;
  }
  if opt_level >= OptimizationLevel::Heavy {
    book.prune(&main);
  }
  Ok(main)
}

pub fn encode_pattern_matching(book: &mut Book) -> Result<(), String> {
  book.desugar_implicit_match_binds();
  book.resolve_ctrs_in_pats();
  book.check_unbound_pats()?;
  //  book.desugar_let_destructors();
  book.extract_matches()?;
  book.flatten_rules();
  let def_types = book.infer_def_types()?;
  book.check_exhaustive_patterns(&def_types)?;
  book.encode_pattern_matching_functions(&def_types);
  Ok(())
}

pub fn run_book(
  mut book: Book,
  mem_size: usize,
  parallel: bool,
  _debug: bool,
  _linear: bool,
  opt_level: OptimizationLevel,
) -> Result<(Term, DefNames, RunInfo), String> {
  let CompileResult { core_book, labels, warnings } = compile_book(&mut book, opt_level)?;

  if !warnings.is_empty() {
    for warn in warnings {
      eprintln!("{}", warn);
    }
    return Err("Could not run the code because of the previous warnings".into());
  }

  /*
    fn debug_hook(net: &Net, book: &Book, labels: &Labels, linear: bool) {
      let net = hvmc_to_net(net);
      let (res_term, errors) = net_to_term(&net, book, labels, linear);
      println!(
        "{}{}\n---------------------------------------",
        if errors.is_empty() { "".to_string() } else { format!("Invalid readback: {:?}\n", errors) },
        res_term.display(&book.def_names)
      );
    }
    let debug_hook = if debug { Some(|net: &_| debug_hook(net, &book, &labels, linear)) } else { None };
  */
  let debug_hook = Some(|_a: &hvmc::ast::Net| ());
  let host = Host::new(&core_book);
  let ((area, mut res_inet), stats) = run_compiled(&host, mem_size, parallel, debug_hook);
  let res_term = crate::term::readback::readback_and_resugar(&mut res_inet, &labels, &host, &book);
  let info = RunInfo { stats, readback_errors: vec![], net: Net::default() };
  area.place(&mut None);
  Ok((*res_term, book.def_names, info))
}

pub fn run_compiled<'t>(
  host: &Host,
  mem_size: usize,
  parallel: bool,
  hook: Option<impl FnMut(&Net)>,
) -> ((LoanedMut<'t, Box<Box<Area>>>, RtNet<'t>), RunStats) {
  let (heap_ref, heap_own) = LoanedMut::loan(Box::new(RtNet::init_heap(mem_size)));
  // Weaken reference so we can share it.
  let heap_ref: &'t Area = heap_ref;
  let mut root = RtNet::new(&heap_ref);
  // Expect won't be reached because there's
  // a pass that checks this.
  root.boot(host.defs.get(DefNames::ENTRY_POINT).expect("No main function."));

  let start_time = Instant::now();

  if let Some(mut hook) = hook {
    root.expand();
    while !root.rdex.is_empty() {
      hook(&host.readback(&root));
      root.reduce(1);
      root.expand();
    }
  } else if parallel {
    root.parallel_normal();
  } else {
    root.normal()
  }

  let elapsed = start_time.elapsed().as_secs_f64();

  let rwts = root.rwts;
  let _net = host.readback(&root);

  // TODO I don't quite understand this code
  // How would it be implemented in the new version?
  // let def = runtime_net_to_runtime_def(&root);
  let stats = RunStats { rewrites: rwts, used: 0, run_time: elapsed };
  ((heap_own, root), stats)
}

pub fn total_rewrites(rwrts: &Rewrites) -> usize {
  rwrts.anni + rwrts.comm + rwrts.eras + rwrts.dref + rwrts.oper
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub enum OptimizationLevel {
  /// The minimum amount of transformations to produce valid hvmc outputs.
  Light,
  /// More aggressive optimizations.
  Heavy,
}

impl From<usize> for OptimizationLevel {
  fn from(value: usize) -> Self {
    if value == 0 { OptimizationLevel::Light } else { OptimizationLevel::Heavy }
  }
}

pub struct CompileResult {
  pub core_book: hvmc::ast::Book,
  pub labels: Labels,
  pub warnings: Vec<Warning>,
}

impl std::fmt::Debug for CompileResult {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for warn in &self.warnings {
      writeln!(f, "// WARNING: {}", warn)?;
    }
    write!(f, "{}", show_book(&self.core_book))
  }
}

pub enum Warning {}

impl std::fmt::Display for Warning {
  fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {}
  }
}

pub struct RunInfo {
  pub stats: RunStats,
  pub readback_errors: Vec<ReadbackError>,
  pub net: Net,
}

pub struct RunStats {
  pub rewrites: Rewrites,
  pub used: usize,
  pub run_time: f64,
}
