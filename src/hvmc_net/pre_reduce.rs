// Reduce the compiled networks, solving any annihilations and commutations.
// This is a useful optimization on its own, but also required by an hvm-core optimization.

use crate::term::DefNames;
use hvmc::{ast::Host, run::Tag};
use std::collections::BTreeMap;

const MAX_ITERS: usize = 100_000;

/// Reduces the definitions in the book individually, except for main.
/// If cross_refs, will deref and try to find the smallest net.
/// Otherwise, just apply node~node interactions.
pub fn pre_reduce_book(book: &mut BTreeMap<String, hvmc::ast::Net>, cross_refs: bool) -> Result<(), String> {
  let host = Host::new(book);
  for (nam, net) in book.iter_mut() {
    // Skip unnecessary work
    if net.rdex.is_empty() {
      continue;
    }
    let area = hvmc::run::Net::init_heap(1 << 18);
    let mut rt = hvmc::run::Net::new(&area);
    rt.boot(host.defs.get(nam).expect("No function."));
    rt.expand();

    let fully_reduce = cross_refs && nam != DefNames::ENTRY_POINT;
    let iters = if fully_reduce {
      let mut iters = 0;
      // TODO: If I just call `rt.normal` some terms expand infinitely, so I put this workaround.
      // But I don't think this is the right way (even if it works).
      loop {
        iters += rt.reduce(MAX_ITERS);
        if rt.root.load_target().tag() == Tag::Ref {
          rt.expand();
        } else {
          break;
        }
      }
      iters
    } else {
      reduce_without_deref(&mut rt, MAX_ITERS)
    };
    if iters > MAX_ITERS {
      return Err(format!("Unable to pre-reduce definition {nam} in under {MAX_ITERS} iterations"));
    }
    *net = host.readback(&rt);
  }
  Ok(())
}

/// Normalizes a runtime net, except for derefs.
fn reduce_without_deref(net: &mut hvmc::run::Net<'_>, limit: usize) -> usize {
  let mut collected_redexes = vec![];
  let mut iters = 0;

  // Separate the derefing interactions, reduce all the others.
  // Also, always put the Ref on the left side (first element).
  // The mem::replace thing implements a queue using 2 vecs.
  let mut rdexes = std::mem::take(&mut net.rdex);
  while !rdexes.is_empty() {
    for (a, b) in rdexes {
      match (a.tag() as u8, b.tag() as u8) {
        // But things would start to grow pretty quickly and we need some criteria for which net to choose and when to stop.
        (2 /* Tag::Ref as u8 */, 4 .. /* Tag::Op2 as u8 */) | (4 .., 2) => collected_redexes.push((a, b)),
        _ => net.interact(a, b),
      }
      if iters >= limit {
        break;
      }
      iters += 1;
    }
    rdexes = std::mem::take(&mut net.rdex);
  }
  // Move the collected redexes back to the net
  net.rdex = collected_redexes;

  iters
}
