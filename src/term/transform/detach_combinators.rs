// TODO

// use std::collections::BTreeMap;

// use crate::term::{Book, DefId, DefNames, Definition, Name, Op, Pattern, Rule, Term};

// impl Book {
//   /// Applies bracket abstraction to remove lambdas form rule bodies,
//   /// replacing it with applications with [`combinators`][Combinator]
//   ///
//   /// This pass should be used after [`DefinitionBook::sanitize_vars`]
//   pub fn detach_combinators(&mut self) {
//     let mut comb = Combinators::new();

//     for def in self.defs.values_mut() {
//       for rule in def.rules.iter_mut() {
//         rule.body.abstract_lambdas(&mut self.def_names, &mut comb);
//       }
//     }

//     // Definitions are not inserted to the book as they are defined to appease the borrow checker.
//     // Since we are mut borrowing the rules we can't borrow the book to insert at the same time.
//     self.defs.append(&mut comb);
//   }
// }

// type Combinators = BTreeMap<DefId, Definition>;

// impl Term {
//   pub fn abstract_lambdas(&mut self, names: &mut DefNames, defs: &mut Combinators) {
//     fn go(term: &mut Term, depth: usize, names: &mut DefNames, defs: &mut Combinators) {
//       match term {
//         Term::Lam { nam: Some(_), bod } => {
//           if !(depth == 0 && bod.is_simple()) {
//             term.abstract_lambda(names, defs)
//           }
//         }
//         Term::Lam { nam: _, bod } => go(bod, depth + 1, names, defs),
//         Term::Chn { nam: _, bod } => go(bod, depth + 1, names, defs),
//         Term::Let { pat: _, val, nxt } => {
//           go(val, depth + 1, names, defs);
//           go(nxt, depth + 1, names, defs);
//         }
//         Term::App { fun, arg } => {
//           go(fun, depth + 1, names, defs);
//           go(arg, depth + 1, names, defs);
//         }
//         Term::Match { .. } => todo!(),
//         Term::Dup { tag: _, fst: _, snd: _, val, nxt } => {
//           go(val, depth + 1, names, defs);
//           go(nxt, depth + 1, names, defs);
//         }
//         Term::Opx { fst, snd, .. } => {
//           go(fst, depth + 1, names, defs);
//           go(snd, depth + 1, names, defs);
//         }
//         Term::Sup { .. } => todo!(),
//         Term::Var { .. } | Term::Lnk { .. } | Term::Ref { .. } | Term::Era | Term::Num { .. } => {}
//         Term::Tup { .. } => todo!(),
//       }
//     }

//     go(self, 0, names, defs)
//   }

//   /// Heuristics for when a term is simple enough to not need to be abstracted.
//   fn is_simple(&self) -> bool {
//     match self {
//       Self::Lam { nam: _, bod } => bod.is_simple(),
//       Self::Chn { nam: _, bod } => bod.is_simple(),
//       Self::App { fun, arg } => fun.is_simple() && arg.is_simple(),
//       Self::Match { .. } => todo!(), /*cond.is_simple() && zero.is_simple() && succ.is_simple(),*/
//       Self::Var { .. } => true,
//       Self::Lnk { .. } => true,
//       Self::Ref { .. } => true,
//       Self::Opx { .. } => true,
//       Self::Num { .. } => true,
//       Self::Era => true,
//       Self::Let { .. } => false,
//       Self::Dup { .. } => false,
//       Self::Sup { .. } => false,
//       Self::Tup { .. } => todo!(),
//     }
//   }

//   /// Replaces a reference to a [`Term::Lam`] with its abstracted body.
//   /// If [`Term::channel_check`] finds a channel subterm with the lambda variable in its body,
//   /// it returns the lambda without change
//   fn abstract_lambda(&mut self, names: &mut DefNames, defs: &mut Combinators) {
//     let extracted = std::mem::take(self);
//     let Self::Lam { nam: Some(name), bod } = extracted else { panic!("Not a lambda term") };

//     *self = if bod.channel_check(&name) {
//       Self::Lam { nam: Some(name), bod }
//     } else {
//       let mut abstracted = bod.abstract_by(&name);
//       abstracted.reduce();
//       abstracted.into_term(names, defs)
//     };
//   }

//   fn occurs_check(&self, name: &str) -> bool {
//     if name.is_empty() {
//       return false;
//     };

//     match self {
//       Self::Var { nam: Name(n) } => n == name,
//       Self::Lam { nam, bod } => !nam.as_ref().is_some_and(|Name(n)| n == name) && bod.occurs_check(name),
//       Self::Chn { nam: _, bod } => bod.occurs_check(name),
//       Self::App { fun, arg } => fun.occurs_check(name) || arg.occurs_check(name),
//       Self::Sup { fst, snd, .. } => fst.occurs_check(name) || snd.occurs_check(name),
//       Self::Let { pat: Pattern::Var(Some(Name(n))), val, nxt } => {
//         val.occurs_check(name) || (n != name && nxt.occurs_check(name))
//       }
//       Self::Let { pat: Pattern::Tup { .. }, .. } => todo!(),
//       Self::Let { .. } => todo!(),
//       Self::Dup { tag: _, fst, snd, val, nxt } => {
//         val.occurs_check(name)
//           || (!fst.as_ref().is_some_and(|Name(n)| n == name)
//             && !snd.as_ref().is_some_and(|Name(n)| n == name)
//             && nxt.occurs_check(name))
//       }
//       Self::Opx { fst, snd, .. } => fst.occurs_check(name) || snd.occurs_check(name),
//       Self::Lnk { .. } | Self::Ref { .. } | Self::Num { .. } | Self::Era => false,
//       Self::Match { .. } => todo!(),
//       Self::Tup { .. } => todo!(),
//     }
//   }

//   /// Checks if the term has a [`Term::Chn`] subterm
//   /// with the given name occurring as a variable inside its body
//   fn channel_check(&self, name: &str) -> bool {
//     fn check(term: &Term, name: &str, inside_chn: bool) -> bool {
//       match term {
//         Term::Var { nam: Name(n) } => inside_chn && n == name,
//         Term::Lam { nam, bod } => {
//           !nam.as_ref().is_some_and(|Name(n)| n == name) && check(bod, name, inside_chn)
//         }
//         Term::Chn { nam: _, bod } => check(bod, name, true),
//         Term::App { fun, arg } => check(fun, name, inside_chn) || check(arg, name, inside_chn),
//         Term::Sup { fst, snd, .. } => check(fst, name, inside_chn) || check(snd, name, inside_chn),
//         Term::Let { pat: Pattern::Var(Some(Name(n))), val, nxt } => {
//           check(val, name, inside_chn) || (n != name && check(nxt, name, inside_chn))
//         }
//         Term::Let { .. } => todo!(),
//         Term::Dup { tag: _, fst, snd, val, nxt } => {
//           if val.occurs_check(name) {
//             if let Some(f) = fst {
//               if check(nxt, f, inside_chn) {
//                 return true;
//               };
//             }
//             if let Some(s) = snd {
//               if check(nxt, s, inside_chn) {
//                 return true;
//               };
//             }
//           }

//           check(val, name, inside_chn)
//             || (!fst.as_ref().is_some_and(|Name(n)| n == name)
//               && !snd.as_ref().is_some_and(|Name(n)| n == name)
//               && check(nxt, name, inside_chn))
//         }
//         Term::Opx { fst, snd, .. } => fst.channel_check(name) || snd.channel_check(name),
//         Term::Lnk { .. } => false,
//         Term::Ref { .. } => false,
//         Term::Num { .. } => false,
//         Term::Era => false,
//         Term::Tup { .. } => todo!(),
//         Term::Match { .. } => todo!(),
//       }
//     }

//     check(self, name, false)
//   }

//   fn is_var(&self, name: &str) -> bool {
//     matches!(self, Term::Var { nam: Name(n) } if n == name)
//   }

//   fn lam(name: &str, body: Self) -> Self {
//     Self::Lam { nam: Some(Name::new(name)), bod: Box::new(body) }
//   }

//   fn app(fun: Self, arg: Self) -> Self {
//     Self::App { fun: Box::new(fun), arg: Box::new(arg) }
//   }

//   fn var(name: &str) -> Self {
//     Self::Var { nam: Name::new(name) }
//   }

//   /// Creates a lambda of the term on the form: `λxλyλz self`
//   fn xyz_lambda(self) -> Self {
//     Self::lam("x", Self::lam("y", Self::lam("z", self)))
//   }

//   /// Creates a lambda of the term on the form:
//   /// `λdλxλyλz ((d f) a)` when the term is a `App { f, a }`,
//   /// or otherwise `λdλxλyλz d self`
//   fn dxyz_lambda(self) -> Self {
//     let term = match self {
//       Self::App { fun, arg } => {
//         Self::App { fun: Box::new(Self::App { fun: Box::new(Self::var("d")), arg: fun }), arg }
//       }
//       other => Self::App { fun: Box::new(Self::var("d")), arg: Box::new(other) },
//     };

//     Self::lam("d", term.xyz_lambda())
//   }
// }

// #[derive(Debug)]
// enum Combinator {
//   /// λxλy x
//   K,
//   /// λx x
//   I,
//   /// λxλyλz (x (y z))
//   B,
//   /// λxλyλz (x z y)
//   C,
//   /// λxλyλz ((x z)(y z))
//   S,
//   /// λdλxλyλz ((d x) (y z))
//   B_,
//   /// λdλxλyλz ((d (x z)) y)
//   C_,
//   /// λdλxλyλz ((d (x z)) (y z))
//   S_,
// }

// impl Combinator {
//   /// Gets the [`Term::Ref`] of the combinator if it already has one,
//   /// or registers it to a new DefId, adding its definition to the the vec of definitions,
//   /// and returning the new ref
//   fn comb_ref(self, names: &mut DefNames, defs: &mut Combinators) -> Term {
//     let name = Name::new(&format!("${:?}", self));
//     let def_id = names.def_id(&name).unwrap_or_else(|| {
//       let def_id = names.insert(name);
//       let body = self.into();
//       let rules = vec![Rule { pats: Vec::new(), body }];
//       defs.insert(def_id, Definition { def_id, rules });

//       def_id
//     });

//     Term::Ref { def_id }
//   }
// }

// impl From<Combinator> for Term {
//   fn from(value: Combinator) -> Self {
//     match value {
//       Combinator::K => Self::lam("x", Self::Lam { nam: None, bod: Box::new(Self::var("x")) }),
//       Combinator::I => Self::lam("x", Self::var("x")),

//       Combinator::B => Self::app(Self::var("x"), Self::app(Self::var("y"), Self::var("z"))).xyz_lambda(),
//       Combinator::B_ => Self::app(Self::var("x"), Self::app(Self::var("y"), Self::var("z"))).dxyz_lambda(),
//       Combinator::C => Self::app(Self::app(Self::var("x"), Self::var("z")), Self::var("y")).xyz_lambda(),
//       Combinator::C_ => Self::app(Self::app(Self::var("x"), Self::var("z")), Self::var("y")).dxyz_lambda(),

//       Combinator::S => Self::Dup {
//         tag: None,
//         fst: Some(Name::new("z1")),
//         snd: Some(Name::new("z2")),
//         val: Box::new(Self::var("z")),
//         nxt: Box::new(Self::app(
//           Self::app(Self::var("x"), Self::var("z1")),
//           Self::app(Self::var("y"), Self::var("z2")),
//         )),
//       }
//       .xyz_lambda(),

//       Combinator::S_ => Self::lam(
//         "d",
//         Self::Dup {
//           tag: None,
//           fst: Some(Name::new("z1")),
//           snd: Some(Name::new("z2")),
//           val: Box::new(Self::var("z")),
//           nxt: Box::new(Self::app(
//             Self::app(Self::var("d"), Self::app(Self::var("x"), Self::var("z1"))),
//             Self::app(Self::var("y"), Self::var("z2")),
//           )),
//         }
//         .xyz_lambda(),
//       ),
//     }
//   }
// }

// /// Abstracted version of [Term].
// /// Can contain terms that could not be abstracted,
// /// combinators and applications with itself.
// #[derive(Debug)]
// enum AbsTerm {
//   Term(Term),
//   Comb(Combinator),
//   Opx(Op),
//   App(Box<AbsTerm>, Box<AbsTerm>),
// }

// impl From<Term> for AbsTerm {
//   fn from(value: Term) -> Self {
//     Self::Term(value)
//   }
// }

// impl From<Combinator> for AbsTerm {
//   fn from(value: Combinator) -> Self {
//     Self::Comb(value)
//   }
// }

// impl From<Op> for AbsTerm {
//   fn from(value: Op) -> Self {
//     Self::Opx(value)
//   }
// }

// impl AbsTerm {
//   fn occurs_check(&self, name: &str) -> bool {
//     match self {
//       Self::Term(term) => term.occurs_check(name),
//       Self::Comb(_) => false,
//       Self::App(fun, arg) => fun.occurs_check(name) || arg.occurs_check(name),
//       Self::Opx(_) => false,
//     }
//   }

//   /// Checks the applications inside the AbsTerm for known possible reductions,
//   /// and apply those that it finds;
//   fn reduce(&mut self) {
//     use Combinator as C;

//     match self {
//       Self::App(
//         box Self::App(box Self::App(box Self::Comb(C::C_), box Self::Comb(c)), box Self::Comb(C::I)),
//         box Self::Comb(C::I),
//       ) => match c {
//         C::C_ => *self = Self::Comb(C::C), // (C_ C_ I I) => C
//         C::S_ => *self = Self::Comb(C::S), // (C_ S_ I I) => S
//         _ => {}
//       },

//       Self::App(
//         box Self::App(box Self::Comb(C::C_), box Self::App(box Self::Comb(C::C), box Self::Comb(C::I))),
//         box Self::Comb(C::I),
//       ) => *self = Self::Comb(C::I), // (C_ (C_ I) I) => I

//       Self::App(f, a) => {
//         f.reduce();
//         a.reduce();
//       }

//       _ => {}
//     }
//   }

//   /// Make a call AbsTerm by folding args around a called function Combinator with applications.
//   fn call<C: Into<AbsTerm>>(called: C, args: impl IntoIterator<Item = AbsTerm>) -> Self {
//     args.into_iter().fold(called.into(), |acc, arg| AbsTerm::App(Box::new(acc), Box::new(arg)))
//   }

//   fn into_term(self, names: &mut DefNames, defs: &mut Combinators) -> Term {
//     match self {
//       Self::Term(term) => term,
//       Self::Comb(c) => c.comb_ref(names, defs),

//       Self::App(box Self::App(box Self::Opx(op), a), b) => {
//         Term::Opx { op, fst: Box::new(a.into_term(names, defs)), snd: Box::new(b.into_term(names, defs)) }
//       }

//       Self::App(box Self::Opx(op), a) => Term::lam("$b", Term::Opx {
//         op,
//         fst: Box::new(a.into_term(names, defs)),
//         snd: Box::new(Term::var("$b")),
//       }),

//       Self::App(k, args) => Term::app(k.into_term(names, defs), args.into_term(names, defs)),

//       Self::Opx(op) => Term::lam(
//         "$a",
//         Term::lam("$b", Term::Opx { op, fst: Box::new(Term::var("$a")), snd: Box::new(Term::var("$b")) }),
//       ),
//     }
//   }

//   /// Abstracted version of the abcdef implementation in [`Term::abstract_by`].
//   /// Check the full function for more details about the arms labels.
//   fn abstract_by(self, name: &str) -> Self {
//     match self {
//       Self::Term(term) => term.abstract_by(name),

//       // [name] Combinator => K Combinator
//       Self::Comb(_) => Self::call(Combinator::K, [self]),

//       // (a)
//       e if !e.occurs_check(name) => Self::call(Combinator::K, vec![e]),

//       // (c)
//       Self::App(fun, box Self::Term(Term::Var { nam: Name(_) })) if !fun.occurs_check(name) => *fun,

//       // (d', e', f')
//       Self::App(box Self::App(fun, arg), arg2) if !fun.occurs_check(name) => {
//         match (arg.occurs_check(name), arg2.occurs_check(name)) {
//           (false, true) => Self::call(Combinator::B_, vec![*fun, *arg, arg2.abstract_by(name)]),
//           (true, false) => Self::call(Combinator::C_, vec![*fun, arg.abstract_by(name), *arg2]),
//           (true, true) => {
//             Self::call(Combinator::S_, vec![*fun, arg.abstract_by(name), arg2.abstract_by(name)])
//           }
//           (false, false) => unreachable!(),
//         }
//       }

//       // (d, e, f)
//       Self::App(fun, arg) => match (fun.occurs_check(name), arg.occurs_check(name)) {
//         (false, true) => Self::call(Combinator::B, vec![*fun, arg.abstract_by(name)]),
//         (true, false) => Self::call(Combinator::C, vec![fun.abstract_by(name), *arg]),
//         (true, true) => Self::call(Combinator::S, vec![fun.abstract_by(name), arg.abstract_by(name)]),
//         (false, false) => unreachable!(),
//       },

//       Self::Opx(_) => unreachable!(),
//     }
//   }
// }

// impl Term {
//   /// Implementation of the abcdef algorithm - pp. 42–67 of the second volume of Combinatory Logic
//   fn abstract_by(self, name: &str) -> AbsTerm {
//     use AbsTerm as A;
//     use Combinator as C;

//     match self {
//       // The reference did not include abstraction of lambdas inside lambdas.
//       // In the next branches we take care of abstracting them away,
//       // before continuing the abstraction by the current lambda if necessary

//       // If the lambda body contains a channel with the lambda variable inside,
//       // we can not abstract it, so we just wrap it inside the AbsTerm
//       Self::Lam { nam: Some(ref n), ref bod } if bod.channel_check(n) => A::Term(self),

//       // [name] Lam { n, bod } => [name] ([n] bod)
//       Self::Lam { nam: Some(n), bod } => bod.abstract_by(&n).abstract_by(name),

//       // [name] Lam { _, bod } => [name] (K bod)
//       Self::Lam { nam: None, bod } => {
//         A::App(Box::new(C::K.into()), Box::new((*bod).into())).abstract_by(name)
//       }

//       // [name] App { Lam { n, bod }, arg }
//       Self::App { fun: box Self::Lam { nam: Some(n), bod }, arg } => {
//         if bod.channel_check(&n) {
//           // (Lam { n, bod } ([name] arg))
//           A::App(Box::new(A::Term(Self::Lam { nam: Some(n), bod })), Box::new(arg.abstract_by(name)))
//         } else {
//           // ([name] ([n] bod) arg)
//           A::App(Box::new(bod.abstract_by(&n)), Box::new((*arg).into())).abstract_by(name)
//         }
//       }

//       // [name] App { fun, Lam { n, bod } }
//       Self::App { fun, arg: box Self::Lam { nam: Some(n), bod } } => {
//         if bod.channel_check(&n) {
//           // (([name] arg) Lam { n, bod })
//           A::App(Box::new(fun.abstract_by(name)), Box::new(A::Term(Self::Lam { nam: Some(n), bod })))
//         } else {
//           // ([name] arg ([n] bod))
//           A::App(Box::new((*fun).into()), Box::new(bod.abstract_by(&n))).abstract_by(name)
//         }
//       }

//       // abcdef branches starts here.
//       // The abstraction function is represented by enclosing the abstraction variable with brackets.
//       // The abstracted variable cannot occur in terms E or F, but it has to occur in terms X and Y.
//       // Other symbols (S K I B C S' B' and C') represents the use of Combinators

//       // (a)
//       // [name] E => K E
//       e if !e.occurs_check(name) => A::call(C::K, vec![e.into()]),

//       // (b)
//       // [name] Var { name } => I
//       // We know it is the abstracted var because it did not match case (a)
//       Self::Var { .. } => C::I.into(),

//       // (c)
//       // [name] App { E, Var { name } } => E
//       Self::App { fun, arg } if arg.is_var(name) && !fun.occurs_check(name) => (*fun).into(),

//       Self::App { fun: box Self::App { fun, arg }, arg: arg2 } if !fun.occurs_check(name) => {
//         match (arg.occurs_check(name), arg2.occurs_check(name)) {
//           // (d')
//           // [name] App { App { E, F }, X } => B' E F ([name] X)
//           (false, true) => A::call(C::B_, vec![(*fun).into(), (*arg).into(), arg2.abstract_by(name)]),
//           // (e')
//           // [name] App { App { E, X }, F } => C' E ([name] X) F
//           (true, false) => A::call(C::C_, vec![(*fun).into(), arg.abstract_by(name), (*arg2).into()]),
//           // (f')
//           // [name] App { App { E, X }, Y } => S' E ([name] X) ([name] Y)
//           (true, true) => A::call(C::S_, vec![(*fun).into(), arg.abstract_by(name), arg2.abstract_by(name)]),
//           // Taken care by case (a)
//           (false, false) => unreachable!(),
//         }
//       }

//       // (d)
//       // [name] App { E, X } => B E ([name] X)
//       Self::App { fun, arg } if !fun.occurs_check(name) && arg.occurs_check(name) => {
//         A::call(C::B, vec![(*fun).into(), arg.abstract_by(name)])
//       }

//       // (e)
//       // [name] App { X, E } => C ([name] X) E
//       Self::App { fun, arg } if fun.occurs_check(name) && !arg.occurs_check(name) => {
//         A::call(C::C, vec![fun.abstract_by(name), (*arg).into()])
//       }

//       // (f)
//       // [name] App { X, Y } => S ([name] X) ([name] Y)
//       Self::App { fun, arg } if fun.occurs_check(name) && arg.occurs_check(name) => {
//         A::call(C::S, vec![fun.abstract_by(name), arg.abstract_by(name)])
//       }

//       // Additions to the algorithm to support terms not included in the reference:

//       // [name] Dup { fst, snd, val, nxt } => ([name] ([fst|snd] nxt) val)
//       Self::Dup { tag: _, fst: Some(nam), snd: Some(s), val, mut nxt } => {
//         nxt.subst(&s, &Term::Var { nam: nam.clone() });
//         A::App(Box::new(nxt.abstract_by(&nam)), Box::new((*val).into())).abstract_by(name)
//       }

//       // [name] Dup { fst, _, val, nxt } => ([name] ([fst] nxt) val)
//       // [name] Dup { _, snd, val, nxt } => ([name] ([snd] nxt) val)
//       Self::Dup { tag: _, fst: Some(nam), snd: None, val, nxt }
//       | Self::Dup { tag: _, fst: None, snd: Some(nam), val, nxt } => {
//         A::App(Box::new(nxt.abstract_by(&nam)), Box::new((*val).into())).abstract_by(name)
//       }

//       // [name] Dup { _, _, val, nxt } => [name] nxt
//       Self::Dup { tag: _, fst: None, snd: None, val: _, nxt } => nxt.abstract_by(name),

//       // [name] Let { nam, val, nxt } => ([name] ([nam] nxt) val)
//       Self::Let { pat: Pattern::Var(Some(nam)), val, nxt } => {
//         A::App(Box::new(nxt.abstract_by(&nam)), Box::new((*val).into())).abstract_by(name)
//       }

//       Self::Let { .. } => todo!(),

//       // [name] Opx { op, fst, snd } => [name] (op fst snd)
//       Self::Opx { op, fst, snd } => A::call(op, [(*fst).into(), (*snd).into()]).abstract_by(name),

//       Self::Sup { .. } => todo!(),

//       Self::Match { .. } => unimplemented!("Not suported here, should run sanitize_vars pass first"),

//       // Term::channel_check invalidates abstraction of lambdas that have their variables inside of a channel
//       Self::Chn { .. } => unreachable!(),

//       // All cases of application are taken care by previous branches
//       Self::App { .. } => unreachable!(),

//       // The abstraction variable can not occur inside these, so case (a) catches all the next branches
//       Self::Ref { .. } | Self::Lnk { .. } | Self::Num { .. } | Self::Era => unreachable!(),
//       Self::Tup { .. } => todo!(),
//     }
//   }
// }
