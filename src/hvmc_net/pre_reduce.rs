// Reduce the compiled networks, solving any annihilations and commutations.
// This is a useful optimization on its own, but also required by an hvm-core optimization.

use hvmc::{
  ast::{net_from_runtime, net_to_runtime},
  run::{Heap, NUM, OP2, REF},
};
use std::collections::BTreeMap;

pub fn pre_reduce_book(book: &mut BTreeMap<String, hvmc::ast::Net>) -> Result<(), String> {
  for (nam, net) in book.iter_mut() {
    pre_reduce_net(nam, net)?;
  }
  Ok(())
}

pub fn pre_reduce_net(nam: &str, net: &mut hvmc::ast::Net) -> Result<(), String> {
  let heap = Heap::init(1 << 18);
  let mut rt = hvmc::run::Net::new(&heap);
  net_to_runtime(&mut rt, net);
  pre_reduce_run_net(nam, &mut rt)?;
  *net = net_from_runtime(&rt);
  Ok(())
}

pub fn pre_reduce_run_net(nam: &str, net: &mut hvmc::run::Net) -> Result<(), String> {
  // Note: not calling Book::new() since that takes super long (~600ms).
  // We know it's okay in this specific case since we are sure no derefs will occur.
  let book = hvmc::run::Book { defs: vec![] };
  let mut collected_redexes = vec![];
  const MAX_ITERS: usize = 100_000_000;
  let mut num_iters = 0;

  // Separate the derefing interactions, reduce all the others.
  // Also, always put the Ref on the left side (first element).
  let mut rdexes: Vec<_> = net.rdex.drain(|n| n).map(Iterator::collect).unwrap_or(vec![]);
  while !rdexes.is_empty() {
    for (a, b) in rdexes {
      match (a.tag(), b.tag()) {
        // TODO: We don't need to necessarily stop at derefs/function calls.
        // But things would start to grow pretty quickly and we need some criteria for which net to choose and when to stop.
        (REF, _) | (_, REF) => collected_redexes.push((a, b)),
        // TODO: Because OP1 is mangled with OP2 during readback, I decided to not process it here.
        // Instead, we could undo OP1s before doing readback and that would allow a little bit more optimization.
        (NUM, OP2) | (OP2, NUM) => collected_redexes.push((a, b)),
        _ => net.interact(&book, a, b),
      }

      if num_iters >= MAX_ITERS {
        return Err(format!(
          "Unable to reduce definition '{}' to the required hvmc form in {} reductions",
          nam, MAX_ITERS
        ));
      }
      num_iters += 1;
    }
    rdexes = net.rdex.drain(|n| n).map(Iterator::collect).unwrap_or(vec![]);
  }
  // Move the collected redexes back to the net
  net.rdex.extend(collected_redexes);

  Ok(())
}
