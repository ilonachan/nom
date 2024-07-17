//! Combinators to parse expressions with operator precedence, using a
//! **Pratt Parser** algorithm.
//!
//! See [`pratt`] for the parser itself, and [`unary_op`] and [`binary_op`]
//! for the building blocks to define operators.

#[cfg(test)]
mod tests;

use std::borrow::BorrowMut;

use crate::{combinator::map, error::ParseError, IResult, Parser};

use super::{Assoc, OperatorCall};

/// Defines a Unary Operator match for use in a Pratt parser combinator.
/// Produced as the matching result of a [`unary_op`] parser.
pub struct UnaryDef<V, Q: Ord + Copy> {
  /// The return value of the parser used to match the operator's token
  value: V,
  /// The binding power of the operator (left if postfix, right if prefix)
  binding_power: Q,
}

/// Defines a Binary/Infix Operator match for use in a Pratt parser combinator.
/// Produced as the matching result of a [`binary_op`] parser.
pub struct BinaryDef<V, Q: Ord + Copy> {
  /// The return value of the parser used to match the operator's token
  value: V,
  /// The left and right binding power of the operator.
  binding_power: (Q, Q),
}

/// Defines any one of the three operator types for use in a Pratt parser combinator.
/// These seem to be unused now, but in theory could allow mixing postfix and infix
/// operators into one input parser for more control over parsing priority
/// (infix is always handled separately however).
pub enum OperatorDef<Op1, Op2, Op3, Q: Ord + Copy> {
  /// Infix operator, e.g. `a + b`
  Infix(BinaryDef<Op1, Q>),
  /// Prefix operator, e.g. `-a` (binding power applies to the right side)
  Prefix(UnaryDef<Op2, Q>),
  /// Postfix operator, e.g. `a++` (binding power applies to the left side)
  Postfix(UnaryDef<Op3, Q>),
}
impl<Op1, Op2, Op3, Q: Ord + Copy> OperatorDef<Op1, Op2, Op3, Q> {
  /// Left binding power, where applicable (for infix and postfix)
  pub fn left_bp(&self) -> Option<Q> {
    match self {
      OperatorDef::Infix(BinaryDef {
        binding_power: (l_bp, _),
        ..
      }) => Some(*l_bp),
      OperatorDef::Prefix(_) => None,
      OperatorDef::Postfix(UnaryDef {
        binding_power: l_bp,
        ..
      }) => Some(*l_bp),
    }
  }
  /// Right binding power, where applicable (for infix and prefix)
  pub fn right_bp(&self) -> Option<Q> {
    match self {
      OperatorDef::Infix(BinaryDef {
        binding_power: (_, r_bp),
        ..
      }) => Some(*r_bp),
      OperatorDef::Prefix(UnaryDef {
        binding_power: r_bp,
        ..
      }) => Some(*r_bp),
      OperatorDef::Postfix(_) => None,
    }
  }
  /// The associativity of the operator; only applicable to binary operators,
  /// [`Assoc::None`] otherwise.
  ///
  /// Computed from the binding power, using the fact that `left_bp < right_bp`
  /// causes left-associativity.
  pub fn assoc(&self) -> Assoc {
    match self {
      OperatorDef::Infix(BinaryDef {
        binding_power: (l_bp, r_bp),
        ..
      }) if l_bp < r_bp => Assoc::Left,
      OperatorDef::Infix(BinaryDef {
        binding_power: (l_bp, r_bp),
        ..
      }) if l_bp > r_bp => Assoc::Right,
      _ => Assoc::None,
    }
  }
}

/// Transforms the wrapped parser such that its return value is the definition of a unary operator with
/// the specified left/right binding power. Intended for use with [`pratt`], to define the `prefix` and `postfix`
/// input parsers.
///
/// The parsers produced by this function can of course be composed using standard Nom parser combinators,
/// such as commonly [`alt`](nom::branch::alt) to watch for any one from a list of defined unary operators.
pub fn unary_op<I, O, Q: Ord + Copy, P>(
  op: P,
  bp: Q,
) -> impl Parser<I, Output = UnaryDef<O, Q>, Error = P::Error>
where
  P: Parser<I, Output = O>,
{
  map(op, move |o| UnaryDef {
    value: o,
    binding_power: bp,
  })
}

/// Transforms the wrapped parser such that its return value is the definition of a binary operator with
/// the specified binding power. Intended for use with [`pratt`], to define the `infix` input parser.
///
/// The parsers produced by this function can of course be composed using standard Nom parser combinators,
/// such as commonly [`alt`](nom::branch::alt) to watch for any one from a list of defined binary operators.
pub fn binary_op<I, O, Q: Ord + Copy, P>(
  op: P,
  lbp: Q,
  rbp: Q,
) -> impl Parser<I, Output = BinaryDef<O, Q>, Error = P::Error>
where
  P: Parser<I, Output = O>,
{
  map(op, move |o| BinaryDef {
    value: o,
    binding_power: (lbp, rbp),
  })
}

/// Construct a Pratt Parser matching the specified `operand` and operators.
/// 
/// TODO: documentation
pub fn pratt<'a, I, O, E, Op1, Op2, Op3, Q, P, P1, P2, P3, F>(
  mut operand: impl BorrowMut<P>,
  mut infix: impl BorrowMut<P1>,
  mut prefix: impl BorrowMut<P2>,
  mut postfix: impl BorrowMut<P3>,
  mut fold: impl BorrowMut<F>,
  min_bp: Q,
) -> impl Parser<I, Output = O, Error = E>
where
  I: Clone + 'a,
  E: ParseError<I>,
  Q: Ord + Copy,
  P: Parser<I, Output = O, Error = E>,
  P1: Parser<I, Output = BinaryDef<Op1, Q>, Error = E>,
  P2: Parser<I, Output = UnaryDef<Op2, Q>, Error = E>,
  P3: Parser<I, Output = UnaryDef<Op3, Q>, Error = E>,
  F: FnMut(I, OperatorCall<Op1, Op2, Op3, O>) -> IResult<I, O, E>,
{
  move |i: I| {
    let (mut i, mut lhs) = if let Ok(r) = operand.borrow_mut().parse(i.clone()) {
      r
    } else {
      let (
        i,
        UnaryDef {
          value: op,
          binding_power: r_bp,
        },
      ) = prefix.borrow_mut().parse(i)?;
      let (i, rhs) = pratt::<_, _, _, _, _, _, _, P, P1, P2, P3, F>(
        operand.borrow_mut(),
        infix.borrow_mut(),
        prefix.borrow_mut(),
        postfix.borrow_mut(),
        fold.borrow_mut(),
        r_bp,
      )
      .parse(i)?;
      fold.borrow_mut()(i, OperatorCall::Prefix(op, rhs))?
    };

    loop {
      if let Ok((
        new_i,
        UnaryDef {
          value: op,
          binding_power: l_bp,
        },
      )) = postfix.borrow_mut().parse(i.clone())
      {
        if l_bp < min_bp {
          break;
        }

        (i, lhs) = fold.borrow_mut()(new_i, OperatorCall::Postfix(lhs, op))?;
      } else if let Ok((
        new_i,
        BinaryDef {
          value: op,
          binding_power: (l_bp, r_bp),
        },
      )) = infix.borrow_mut().parse(i.clone())
      {
        if l_bp < min_bp {
          break;
        }

        i = new_i;
        let rhs;
        (i, rhs) = pratt::<_, _, _, _, _, _, _, P, P1, P2, P3, F>(
          operand.borrow_mut(),
          infix.borrow_mut(),
          prefix.borrow_mut(),
          postfix.borrow_mut(),
          fold.borrow_mut(),
          r_bp,
        )
        .parse(i)?;

        (i, lhs) = fold.borrow_mut()(i, OperatorCall::Infix(lhs, op, rhs))?;
      } else {
        break;
      }
    }

    Ok((i, lhs))
  }
}

#[cfg(feature = "alloc")]
mod closure_ops {
  use std::{cell::RefCell, rc::Rc};

  use crate::{combinator::map, error::ParseError, IResult, Parser};

  use super::{binary_op, unary_op, BinaryDef, OperatorCall, UnaryDef};

  /// Trait alias for `FnMut(I, Op, O) -> IResult<I, O, E> + 'a`
  ///
  /// Its purpose is as a [`flat_map`](crate::combinator::flat_map)-like continuation parser,
  /// called when a unary operator is fully read in (as far as the parser knows so far)
  /// with the operator and operand provided.
  ///
  /// TODO: return a [`Parser`](crate::Parser) instead
  pub trait UnaryDefFn<'a, I: 'a, O, E, Op>: FnMut(I, Op, O) -> IResult<I, O, E> + 'a {}
  impl<'a, T, I: 'a, O, E, Op> UnaryDefFn<'a, I, O, E, Op> for T where
    T: FnMut(I, Op, O) -> IResult<I, O, E> + 'a
  {
  }

  /// Trait alias for `FnMut(I, Op, O, O) -> IResult<I, O, E> + 'a`
  ///
  /// Its purpose is as a [`flat_map`](crate::combinator::flat_map)-like continuation parser,
  /// called when a binary operator is fully read in (as far as the parser knows so far)
  /// with the operator and both operands provided.
  ///
  /// TODO: return a [`Parser`](crate::Parser) instead
  pub trait BinaryDefFn<'a, I: 'a, O, E, Op>: FnMut(I, Op, O, O) -> IResult<I, O, E> + 'a {}
  impl<'a, T, I: 'a, O, E, Op> BinaryDefFn<'a, I, O, E, Op> for T where
    T: FnMut(I, Op, O, O) -> IResult<I, O, E> + 'a
  {
  }

  /// Central dispatcher for the *attached closure paradigm*.
  /// 
  /// # Using [`pratt`](super::pratt) with attached closures
  /// 
  /// Using [`binary_closure`] and [`unary_closure`] as counterparts to [`binary_op`] and [`unary_op`] respectively, a closure with
  /// fold logic can be attached to each individual matchable operator. Using `consume_closures` as the `fold` input to the
  /// [`pratt`](super::pratt) parser, the correct closure for each matched operator is then automatically dispatched.
  /// 
  /// This system is fully opt-in and can easily be replicated; its advantage is a close semantic coupling of each operator with the
  /// fold operation it produces, which may be more readable and less boilerplate-heavy in certain situations.
  /// 
  /// Using this function changes all operator output types to have closures attached: this means if one branch uses this feature,
  /// all other branches must either use it too, or be made compatible with it. This can be done by wrapping the ordinary output parsers
  /// in [`binary_nop`] and [`unary_nop`] respectively, which will make them not be dispatched and instead fall through into the
  /// fallback fold function passed as an argument to `consume_closures`. If no such case exists, the fallback closure may be
  /// `|_,_| unreachable!()`.
  pub fn consume_closures<'a, I: Clone + 'a, O, E, Op1, Op2, Op3, F>(
    mut f: F,
  ) -> impl FnMut(
    I,
    OperatorCall<
      (Op1, Option<Rc<RefCell<dyn BinaryDefFn<'a, I, O, E, Op1>>>>),
      (Op2, Option<Rc<RefCell<dyn UnaryDefFn<'a, I, O, E, Op2>>>>),
      (Op3, Option<Rc<RefCell<dyn UnaryDefFn<'a, I, O, E, Op3>>>>),
      O,
    >,
  ) -> IResult<I, O, E>
  where
    F: FnMut(I, OperatorCall<Op1, Op2, Op3, O>) -> IResult<I, O, E> + 'a,
  {
    move |i, opcall| match opcall {
      OperatorCall::Infix(lhs, (op1, Some(f1)), rhs) => f1.as_ref().borrow_mut()(i, op1, lhs, rhs),
      OperatorCall::Infix(lhs, (op1, None), rhs) => f(i, OperatorCall::Infix(lhs, op1, rhs)),
      OperatorCall::Prefix((op2, Some(f2)), val) => f2.as_ref().borrow_mut()(i, op2, val),
      OperatorCall::Prefix((op2, None), val) => f(i, OperatorCall::Prefix(op2, val)),
      OperatorCall::Postfix(val, (op3, Some(f3))) => f3.as_ref().borrow_mut()(i, op3, val),
      OperatorCall::Postfix(val, (op3, None)) => f(i, OperatorCall::Postfix(val, op3)),
    }
  }

  /// Counterpart to [`binary_op`] in the *attached closure paradigm*: attaches this operator's fold logic to it,
  /// so it can be automatically dispatched by [`consume_closures`] (see there for more information).
  pub fn binary_closure<'a, I: Clone + 'a, O, E, Op, Q: Ord + Copy, P, F>(
    op: P,
    lbp: Q,
    rbp: Q,
    fold: F,
  ) -> impl Parser<
    I,
    Output = BinaryDef<(Op, Option<Rc<RefCell<dyn BinaryDefFn<'a, I, O, E, Op>>>>), Q>,
    Error = E,
  >
  where
    P: Parser<I, Output = Op, Error = E>,
    E: ParseError<I>,
    F: BinaryDefFn<'a, I, O, E, Op>,
  {
    let fold: Rc<RefCell<dyn BinaryDefFn<'a, I, O, E, Op>>> = Rc::new(RefCell::new(fold));
    binary_op(op.map(move |op| (op, Some(fold.clone()))), lbp, rbp)
  }
  /// Counterpart to [`unary_op`] in the *attached closure paradigm*: attaches this operator's fold logic to it,
  /// so it can be automatically dispatched by [`consume_closures`] (see there for more information).
  pub fn unary_closure<'a, I: Clone + 'a, O, E, Op, Q: Ord + Copy, P, F>(
    op: P,
    rbp: Q,
    fold: F,
  ) -> impl Parser<
    I,
    Output = UnaryDef<(Op, Option<Rc<RefCell<dyn UnaryDefFn<'a, I, O, E, Op>>>>), Q>,
    Error = E,
  >
  where
    P: Parser<I, Output = Op, Error = E>,
    E: ParseError<I>,
    F: UnaryDefFn<'a, I, O, E, Op>,
  {
    let fold: Rc<RefCell<dyn UnaryDefFn<'a, I, O, E, Op>>> = Rc::new(RefCell::new(fold));
    unary_op(op.map(move |op| (op, Some(fold.clone()))), rbp)
  }

  /// Wrapper for parser branches that don't have closures attached using [`binary_closure`],
  /// so they can be used together in combinators and ultimately handled by [`consume_closures`]
  /// (see there for more information).
  pub fn binary_nop<'a, I: Clone + 'a, O, E, Op, Q: Ord + Copy, P>(
    op: P,
  ) -> impl Parser<
    I,
    Output = BinaryDef<(Op, Option<Rc<RefCell<dyn BinaryDefFn<'a, I, O, E, Op>>>>), Q>,
    Error = E,
  >
  where
    P: Parser<I, Output = BinaryDef<Op, Q>, Error = E>,
    E: ParseError<I>,
  {
    map(op, |o| BinaryDef {
      value: (o.value, None),
      binding_power: o.binding_power,
    })
  }
  /// Wrapper for parser branches that don't have closures attached using [`unary_closure`],
  /// so they can be used together in combinators and ultimately handled by [`consume_closures`]
  /// (see there for more information).
  pub fn unary_nop<'a, I: Clone + 'a, O, E, Op, Q: Ord + Copy, P>(
    op: P,
  ) -> impl Parser<
    I,
    Output = UnaryDef<(Op, Option<Rc<RefCell<dyn UnaryDefFn<'a, I, O, E, Op>>>>), Q>,
    Error = E,
  >
  where
    P: Parser<I, Output = UnaryDef<Op, Q>, Error = E>,
    E: ParseError<I>,
  {
    map(op, |o| UnaryDef {
      value: (o.value, None),
      binding_power: o.binding_power,
    })
  }
}
#[cfg(feature = "alloc")]
pub use closure_ops::*;
