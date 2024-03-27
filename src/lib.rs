#![feature(box_patterns)]
#![feature(let_chains)]

use builtins::create_host;
use diagnostics::{DiagnosticOrigin, Diagnostics, DiagnosticsConfig, Severity};
use hvmc::{
  ast::Net,
  dispatch_dyn_net,
  host::Host,
  run::{DynNet, Heap, Rewrites},
};
use hvmc_net::{mutual_recursion, prune::prune_defs};
use net::{hvmc_to_net::hvmc_to_net, net_to_hvmc::nets_to_hvmc};
use std::{
  sync::{Arc, Mutex},
  time::Instant,
};
use term::{book_to_nets, net_to_term::net_to_term, term_to_net::Labels, AdtEncoding, Book, Ctx, Term};

pub mod builtins;
pub mod diagnostics;
pub mod hvmc_net;
pub mod net;
pub mod term;

pub use term::load_book::load_file_to_book;

pub const ENTRY_POINT: &str = "main";
pub const HVM1_ENTRY_POINT: &str = "Main";

pub fn check_book(book: &mut Book) -> Result<(), Diagnostics> {
  // TODO: Do the checks without having to do full compilation
  let res = compile_book(book, CompileOpts::light(), DiagnosticsConfig::new(Severity::Warning, false), None)?;
  print!("{}", res.diagnostics);
  Ok(())
}

pub fn compile_book(
  book: &mut Book,
  opts: CompileOpts,
  diagnostics_cfg: DiagnosticsConfig,
  args: Option<Vec<Term>>,
) -> Result<CompileResult, Diagnostics> {
  let mut diagnostics = desugar_book(book, opts, diagnostics_cfg, args)?;
  let (nets, labels) = book_to_nets(book);

  let mut core_book = nets_to_hvmc(nets, &mut diagnostics)?;

  if opts.pre_reduce {
    core_book.pre_reduce(&|x| x == book.hvmc_entrypoint(), None, 100_000);
  }
  if opts.prune {
    prune_defs(&mut core_book, book.hvmc_entrypoint().to_string());
  }
  mutual_recursion::check_cycles(&core_book, &mut diagnostics)?;

  Ok(CompileResult { core_book, labels, diagnostics })
}

pub fn desugar_book(
  book: &mut Book,
  opts: CompileOpts,
  diagnostics_cfg: DiagnosticsConfig,
  args: Option<Vec<Term>>,
) -> Result<Diagnostics, Diagnostics> {
  let mut ctx = Ctx::new(book, diagnostics_cfg);

  ctx.check_shared_names();

  ctx.set_entrypoint();

  ctx.book.encode_adts(opts.adt_encoding);

  ctx.book.resolve_ctrs_in_pats();
  ctx.check_unbound_ctr()?;
  ctx.check_ctrs_arities()?;

  ctx.apply_args(args)?;
  ctx.book.apply_use();

  ctx.book.encode_builtins();

  ctx.resolve_refs()?;

  ctx.fix_match_terms()?;
  ctx.desugar_match_defs()?;

  ctx.check_unbound_vars()?;

  if opts.linearize_matches.enabled() {
    ctx.book.linearize_matches(opts.linearize_matches.is_extra());
  }

  ctx.book.encode_matches(opts.adt_encoding);

  // sanity check
  ctx.check_unbound_vars()?;

  ctx.book.make_var_names_unique();
  ctx.book.linearize_vars();

  // sanity check
  ctx.check_unbound_vars()?;

  // Optimizing passes
  if opts.eta {
    ctx.book.eta_reduction();
  }
  if opts.float_combinators {
    ctx.book.float_combinators();
  }
  if opts.ref_to_ref {
    ctx.simplify_ref_to_ref()?;
  }
  if opts.simplify_main {
    ctx.book.simplify_main_ref();
  }

  ctx.prune(opts.prune, opts.adt_encoding);

  if opts.inline {
    ctx.book.inline();
  }
  if opts.merge {
    ctx.book.merge_definitions();
  }

  if !ctx.info.has_errors() { Ok(ctx.info) } else { Err(ctx.info) }
}

pub fn run_book(
  mut book: Book,
  max_memory: Option<usize>,
  run_opts: RunOpts,
  compile_opts: CompileOpts,
  diagnostics_cfg: DiagnosticsConfig,
  args: Option<Vec<Term>>,
) -> Result<(Term, RunInfo), Diagnostics> {
  let CompileResult { core_book, labels, diagnostics } =
    compile_book(&mut book, compile_opts, diagnostics_cfg, args)?;

  // TODO: Printing should be taken care by the cli module, but we'd
  // like to print any warnings before running so that the user can
  // cancel the run if a problem is detected.
  eprint!("{diagnostics}");

  // Turn the book into an Arc so that we can use it for logging, debugging, etc.
  // from anywhere else in the program
  // This "freezes" the book and prevents further modification.
  let book = Arc::new(book);
  let labels = Arc::new(labels);

  // Run
  let debug_hook = run_opts.debug_hook(&book, &labels);
  let host = create_host(book.clone(), labels.clone(), compile_opts.adt_encoding);
  host.lock().unwrap().insert_book(&core_book);

  let (res_lnet, stats) = run_compiled(host, max_memory, run_opts, debug_hook, book.hvmc_entrypoint());

  let (res_term, diagnostics) =
    readback_hvmc(&res_lnet, &book, &labels, run_opts.linear, compile_opts.adt_encoding);

  let info = RunInfo { stats, diagnostics, net: res_lnet, book, labels };
  Ok((res_term, info))
}

/// Utility function to count the amount of nodes in an hvm-core AST net
pub fn count_nodes<'l>(net: &'l hvmc::ast::Net) -> usize {
  let mut visit: Vec<&'l hvmc::ast::Tree> = vec![&net.root];
  let mut count = 0usize;
  for (l, r) in &net.redexes {
    visit.push(l);
    visit.push(r);
  }
  while let Some(tree) = visit.pop() {
    // If it is not 0-ary, then we'll count it as a node.
    if tree.children().next().is_some() {
      count += 1;
    }
    for subtree in tree.children() {
      visit.push(subtree);
    }
  }
  count
}

pub fn run_compiled(
  host: Arc<Mutex<Host>>,
  mem_size: Option<usize>,
  run_opts: RunOpts,
  hook: Option<impl FnMut(&Net)>,
  entrypoint: &str,
) -> (Net, RunStats) {
  let heap = Heap::new(mem_size).expect("memory allocation failed");
  let mut root = DynNet::new(&heap, run_opts.lazy_mode);
  let max_rwts = run_opts.max_rewrites.map(|x| x.clamp(usize::MIN, usize::MAX));
  // Expect won't be reached because there's
  // a pass that checks this.
  dispatch_dyn_net!(&mut root => {
    root.boot(host.lock().unwrap().defs.get(entrypoint).expect("No main function."));

    let start_time = Instant::now();

    if let Some(mut hook) = hook {
      while !root.redexes.is_empty() {
        let readback = host.lock().unwrap().readback(root);
        hook(&readback);
        root.reduce(1);
      }
    } else if let Some(mut max_rwts) = max_rwts {
      if run_opts.lazy_mode {
        panic!("Lazy mode does not yet support rewrite limit");
      }
      if !run_opts.single_core {
        panic!("Parallel mode does not yet support rewrite limit");
      }
      root.expand();
      while !root.redexes.is_empty() {
        let old_rwts = root.rwts.total();
        root.reduce(max_rwts);
        let delta_rwts = root.rwts.total() - old_rwts;
        if (max_rwts as u64) < delta_rwts {
          eprintln!("Warning: Exceeded max rwts");
          break;
        }
        max_rwts -= delta_rwts as usize;
        root.expand();
      }
    } else if !run_opts.single_core {
      root.parallel_normal();
    } else {
      root.normal();
    }
    let elapsed = start_time.elapsed().as_secs_f64();


    let net = host.lock().unwrap().readback(root);

    // TODO I don't quite understand this code
    // How would it be implemented in the new version?
    let stats = RunStats { rewrites: root.rwts, used: count_nodes(&net), run_time: elapsed };
    (net, stats)
  })
}

pub fn readback_hvmc(
  net: &Net,
  book: &Arc<Book>,
  labels: &Arc<Labels>,
  linear: bool,
  adt_encoding: AdtEncoding,
) -> (Term, Diagnostics) {
  let mut diags = Diagnostics::default();
  let net = hvmc_to_net(net);
  let mut term = net_to_term(&net, book, labels, linear, &mut diags);

  let resugar_errs = term.resugar_adts(book, adt_encoding);
  term.resugar_builtins();

  for err in resugar_errs {
    diags.add_diagnostic(err, Severity::Warning, DiagnosticOrigin::Readback);
  }

  (term, diags)
}

#[derive(Clone, Copy, Debug, Default)]
pub struct RunOpts {
  pub single_core: bool,
  pub debug: bool,
  pub linear: bool,
  pub lazy_mode: bool,
  pub max_memory: Option<usize>,
  pub max_rewrites: Option<usize>,
}

impl RunOpts {
  pub fn lazy() -> Self {
    Self { lazy_mode: true, single_core: true, ..Self::default() }
  }

  fn debug_hook<'a>(&'a self, book: &'a Book, labels: &'a Labels) -> Option<impl FnMut(&Net) + 'a> {
    self.debug.then_some({
      |net: &_| {
        let net = hvmc_to_net(net);
        let mut diags = Diagnostics::default();
        let res_term = net_to_term(&net, book, labels, self.linear, &mut diags);
        eprint!("{diags}");
        println!("{}\n---------------------------------------", res_term);
      }
    })
  }
}

#[derive(Clone, Copy, Debug, Default)]
pub enum OptLevel {
  #[default]
  Disabled,
  Enabled,
  Extra,
}

impl OptLevel {
  pub fn enabled(&self) -> bool {
    !matches!(self, OptLevel::Disabled)
  }

  pub fn is_extra(&self) -> bool {
    matches!(self, OptLevel::Extra)
  }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CompileOpts {
  /// Selects the encoding for the ADT syntax.
  pub adt_encoding: AdtEncoding,

  /// Enables [term::transform::eta_reduction].
  pub eta: bool,

  /// Enables [term::transform::simplify_ref_to_ref].
  pub ref_to_ref: bool,

  /// Enables [term::transform::definition_pruning] and [hvmc_net::prune].
  pub prune: bool,

  /// Enables [hvmc_net::pre_reduce].
  pub pre_reduce: bool,

  /// Enables [term::transform::linearize_matches].
  pub linearize_matches: OptLevel,

  /// Enables [term::transform::float_combinators].
  pub float_combinators: bool,

  /// Enables [term::transform::simplify_main_ref].
  pub simplify_main: bool,

  /// Enables [term::transform::definition_merge]
  pub merge: bool,

  /// Enables [term::transform::inline].
  pub inline: bool,
}

impl CompileOpts {
  /// All optimizations enabled.
  pub fn heavy() -> Self {
    Self {
      eta: true,
      ref_to_ref: true,
      prune: true,
      pre_reduce: true,
      float_combinators: true,
      simplify_main: true,
      merge: true,
      inline: true,
      adt_encoding: Default::default(),
      linearize_matches: OptLevel::Extra,
    }
  }

  /// Set all opts as true and keep the current adt encoding.
  pub fn set_all(self) -> Self {
    Self { adt_encoding: self.adt_encoding, ..Self::heavy() }
  }

  /// Set all opts as false and keep the current adt encoding.
  pub fn set_no_all(self) -> Self {
    Self { adt_encoding: self.adt_encoding, ..Self::default() }
  }

  /// All optimizations disabled, except float_combinators and linearize_matches
  pub fn light() -> Self {
    Self { float_combinators: true, linearize_matches: OptLevel::Extra, ..Self::default() }
  }

  // Disable optimizations that don't work or are unnecessary on lazy mode
  pub fn lazy_mode(&mut self) {
    self.float_combinators = false;
    if self.linearize_matches.is_extra() {
      self.linearize_matches = OptLevel::Enabled;
    }
    self.pre_reduce = false;
  }
}

impl CompileOpts {
  pub fn check(&self, lazy_mode: bool) {
    if !lazy_mode {
      if !self.float_combinators {
        println!(
          "Warning: Running in strict mode without enabling the float_combinators pass can lead to some functions expanding infinitely."
        );
      }
      if !self.linearize_matches.enabled() {
        println!(
          "Warning: Running in strict mode without enabling the linearize_matches pass can lead to some functions expanding infinitely."
        );
      }
    }
  }
}

pub struct CompileResult {
  pub diagnostics: Diagnostics,
  pub core_book: hvmc::ast::Book,
  pub labels: Labels,
}

pub struct RunInfo {
  pub stats: RunStats,
  pub diagnostics: Diagnostics,
  pub net: Net,
  pub book: Arc<Book>,
  pub labels: Arc<Labels>,
}

pub struct RunStats {
  pub rewrites: Rewrites,
  pub used: usize,
  pub run_time: f64,
}
