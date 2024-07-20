//! Combinators to parse expressions with operator precedence, using a
//! **Shunting-Yard** algorithm.
//!
//! See [`shunting_yard`] for the parser itself, and [`unary_op`] and [`binary_op`]
//! for the building blocks to define operators.
//!
//! Only available on targets where memory for an operator stack/"shunting yard"
//! can be allocated.
#![cfg(feature = "alloc")]
#![cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]

#[cfg(test)]
mod tests;

use std::borrow::BorrowMut;

use crate::combinator::map;
use crate::error::{ErrorKind, FromExternalError, ParseError};
use crate::lib::std::vec::Vec;
use crate::{Err, IResult, Parser};

use super::{Assoc, OperatorCall};

/// Defines a Unary Operator match for use in a Shunting-Yard parser combinator.
/// Produced as the matching result of a [`unary_op`] parser.
pub struct UnaryDef<V, Q: Ord + Copy> {
  /// The return value of the parser used to match the operator's token
  value: V,
  /// The precedence of the operator
  precedence: Q,
}

/// Defines a Binary/Infix Operator match for use in a Shunting-Yard parser combinator.
/// Produced as the matching result of a [`binary_op`] parser.
pub struct BinaryDef<V, Q: Ord + Copy> {
  /// The return value of the parser used to match the operator's token
  value: V,
  /// The precedence of the operator
  precedence: Q,
  /// The associativity of the operator
  assoc: Assoc,
}

/// Defines any one of the three operator types for use in a Shunting-Yard parser combinator.
/// Internally, these will be collected and placed on the operator stack/"shunting yard".
pub enum OperatorDef<Op1, Op2, Op3, Q: Ord + Copy> {
  /// Infix operator, e.g. `a + b`
  Infix(BinaryDef<Op1, Q>),
  /// Prefix operator, e.g. `-a` (binding power applies to the right side)
  Prefix(UnaryDef<Op2, Q>),
  /// Postfix operator, e.g. `a++` (binding power applies to the left side)
  Postfix(UnaryDef<Op3, Q>),
}
impl<Op1, Op2, Op3, Q: Ord + Copy> OperatorDef<Op1, Op2, Op3, Q> {
  /// The precedence of the operator (applicable to all types)
  pub fn precedence(&self) -> Q {
    match self {
      OperatorDef::Infix(BinaryDef { precedence: p, .. }) => *p,
      OperatorDef::Prefix(UnaryDef { precedence: p, .. }) => *p,
      OperatorDef::Postfix(UnaryDef { precedence: p, .. }) => *p,
    }
  }
  /// The associativity of the operator; only applicable to binary operators,
  /// [`Assoc::None`] otherwise.
  pub fn assoc(&self) -> Assoc {
    match self {
      OperatorDef::Infix(BinaryDef { assoc, .. }) => *assoc,
      _ => Assoc::None,
    }
  }
}

/// Transforms the wrapped parser such that its return value is the definition of a unary operator with
/// the specified precedence. Intended for use with [shunting_yard], to define the `prefix` and `postfix`
/// input parsers.
///
/// The parsers produced by this function can of course be composed using standard Nom parser combinators,
/// such as commonly [`alt`](nom::branch::alt) to watch for any one from a list of defined unary operators.
pub fn unary_op<I, O, Q: Ord + Copy, P>(
  parser: P,
  precedence: Q,
) -> impl Parser<I, Output = UnaryDef<O, Q>, Error = P::Error>
where
  P: Parser<I, Output = O>,
{
  map(parser, move |value| UnaryDef { value, precedence })
}

/// Transforms the wrapped parser such that its return value is the definition of a binary operator with
/// the specified precedence and associativity. Intended for use with [shunting_yard], to define the `infix`
/// input parser.
///
/// The parsers produced by this function can of course be composed using standard Nom parser combinators,
/// such as commonly [`alt`](nom::branch::alt) to watch for any one from a list of defined binary operators.
pub fn binary_op<I, O, Q: Ord + Copy, P>(
  parser: P,
  precedence: Q,
  assoc: Assoc,
) -> impl Parser<I, Output = BinaryDef<O, Q>, Error = P::Error>
where
  P: Parser<I, Output = O>,
{
  map(parser, move |value| BinaryDef {
    value,
    precedence,
    assoc,
  })
}

/// Parses an expression with operator precedence using a **Shunting-Yard** algorithm.
///
/// Supports prefix, postfix and binary operators. Operators are applied in ascending precedence.
///
/// The parser will track its current position inside the expression and call the respective
/// operand/operator parsers. The prefix and postfix parsers are called repeatedly until they fail before
/// execution moves on to the operand or binary parser.
///
/// Expressions are folded as soon as possible. The result will be reused as another operand. After the
/// expression has been read completely any remaining operations are folded and the resulting, single
/// operand is returned as the result.
///
/// # Arguments
/// * `operand` Parser for operands.
/// * `binary` Parser for binary operators.
/// * `prefix` Parser for prefix unary operators.
/// * `postfix` Parser for postfix unary operators.
/// * `fold` Function that evaluates a single operation and returns the result.
///
/// # Errors
///
/// It will return `Err(Err:Error((_, ErrorKind::Precedence)))` if:
/// * the `fold` function returns an `Err`.
/// * more than one or no operands remain after the expression has been evaluated completely.
/// * the input does not match the pattern: `prefix* operand postfix* (binary prefix* operand postfix*)*`
///
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, IResult};
/// # use nom::character::complete::digit1;
/// # use nom::combinator::{map_res, fail};
/// # use nom::sequence::delimited;
/// # use nom::bytes::complete::tag;
/// # use nom::branch::alt;
/// #
/// # // todo: this would probably be the correct package if merged
/// use nom::precedence::{shunting_yard::{shunting_yard, unary_op, binary_op}, Assoc, OperatorCall};
///
/// fn parser(i: &str) -> IResult<&str, i64> {
///   shunting_yard(
///     // operand
///     alt((
///       map_res(digit1, |s: &str| s.parse::<i64>()),
///       delimited(tag("("), parser, tag(")")),
///     )),
///     // infix/binary operators
///     alt((
///       binary_op(tag("*"), 2, Assoc::Left),
///       binary_op(tag("/"), 2, Assoc::Left),
///       binary_op(tag("+"), 3, Assoc::Left),
///       binary_op(tag("-"), 3, Assoc::Left),
///     )),
///     // prefix operators
///     unary_op(tag("-"), 1),
///     // postfix operators (none in this case)
///     fail,
///     // fold
///     |op: OperatorCall<&str, &str, &str, i64>| {
///       use nom::precedence::OperatorCall::*;
///       match op {
///         Prefix("-", o) => Ok(-o),
///         Binary(lhs, "*", rhs) => Ok(lhs * rhs),
///         Binary(lhs, "/", rhs) => Ok(lhs / rhs),
///         Binary(lhs, "+", rhs) => Ok(lhs + rhs),
///         Binary(lhs, "-", rhs) => Ok(lhs - rhs),
///         _ => Err("Invalid combination"),
///       }
///     }
///   )(i)
/// }
///
/// assert_eq!(parser("8-2*2"), Ok(("", 4)));
/// assert_eq!(parser("4-(2+2)"), Ok(("", 0)));
/// assert_eq!(parser("3-(2*3)+7+2*2-(2*(2+4))"), Ok(("", -4)));
/// # // todo: put some error cases?
/// ```
///
/// # Evaluation order
/// This parser reads expressions from left to right and folds operations as soon as possible. This
/// behaviour is only important when using an operator grammar that allows for ambigious expressions.
///
/// For example, the expression `-a++**b` is ambigious with the following precedence.
///
/// | Operator | Position | Precedence | Associativity |
/// |----------|----------|------------|---------------|
/// | **       | Binary   | 1          | Right         |
/// | -        | Prefix   | 2          | N/A           |
/// | ++       | Postfix  | 3          | N/A           |
///
/// The expression can be parsed in two ways: `-((a++)**b)` or `((-a)++)**b`. This parser will always
/// parse it as the latter because of how it evaluates expressions:
/// * It reads, left-to-right, the first two operators `-a++`.
/// * Because the minus takes precedence over the increment it is evaluated immediately `(-a)++`.
/// * It then reads the remaining input and evaluates the increment next in order to preserve its
///   position in the expression \
///   `((-a)++)**b`.
pub fn shunting_yard<I, O, E, E2, Op1, Op2, Op3, Q, P, P1, P2, P3, F>(
  mut operand: impl BorrowMut<P>,
  mut infix: impl BorrowMut<P1>,
  mut prefix: impl BorrowMut<P2>,
  mut postfix: impl BorrowMut<P3>,
  mut fold: impl BorrowMut<F>,
) -> impl Parser<I, Output = O, Error = E>
where
  I: Clone + PartialEq,
  E: ParseError<I> + FromExternalError<I, E2>,
  Q: Ord + Copy,
  P: Parser<I, Output = O, Error = E>,
  P1: Parser<I, Output = BinaryDef<Op1, Q>, Error = E>,
  P2: Parser<I, Output = UnaryDef<Op2, Q>, Error = E>,
  P3: Parser<I, Output = UnaryDef<Op3, Q>, Error = E>,
  F: FnMut(OperatorCall<Op1, Op2, Op3, O>) -> Result<O, E2>,
{
  let mut prefix = (move |i: I| prefix.borrow_mut().parse(i)).map(OperatorDef::Prefix);
  let mut infix = (move |i: I| infix.borrow_mut().parse(i)).map(OperatorDef::Infix);
  let mut postfix = (move |i: I| postfix.borrow_mut().parse(i)).map(OperatorDef::Postfix);

  move |mut i: I| {
    let mut operands = Vec::new();
    let mut operators = Vec::new();
    let mut i1 = i.clone();

    let pop_operator =
      |start_i: I, cur_i: I, operands: &mut Vec<O>, operators: &mut Vec<_>, fold: &mut F| {
        let value = match operands.pop() {
          Some(o) => o,
          None => {
            return Err(Err::Error(E::from_error_kind(
              start_i,
              ErrorKind::Precedence,
            )))
          }
        };
        let operation = match operators.pop().unwrap() {
          OperatorDef::Prefix(UnaryDef { value: op, .. }) => OperatorCall::Prefix(op, value),
          OperatorDef::Postfix(UnaryDef { value: op, .. }) => OperatorCall::Postfix(value, op),
          OperatorDef::Infix(BinaryDef { value: op, .. }) => match operands.pop() {
            Some(lhs) => OperatorCall::Infix(lhs, op, value),
            None => return Err(Err::Error(E::from_error_kind(cur_i, ErrorKind::Precedence))),
          },
        };
        let result = match fold.borrow_mut()(operation) {
          Err(e) => {
            return Err(Err::Error(E::from_external_error(
              start_i,
              ErrorKind::Precedence,
              e,
            )))
          }
          Ok(r) => r,
        };
        operands.push(result);
        Ok(())
      };

    let process_new_operator = |new_res: IResult<I, OperatorDef<_, _, _, _>, _>,
                                start_i: I,
                                cur_i: &mut I,
                                operands: &mut Vec<O>,
                                operators: &mut Vec<_>,
                                fold: &mut F|
     -> Result<bool, Err<E>> {
      match new_res {
        Err(Err::Error(_)) => Ok(false),
        Err(e) => Err(e),
        Ok((new_i, new_operator)) => {
          // infinite loop check: the parser must always consume
          if &new_i == cur_i {
            return Err(Err::Error(E::from_error_kind(
              cur_i.clone(),
              ErrorKind::Precedence,
            )));
          }
          // do the popping
          while operators
            .last()
            .map(|op: &OperatorDef<_, _, _, _>| match &new_operator {
              OperatorDef::Prefix(_) => false,
              OperatorDef::Postfix(o) => op.precedence() <= o.precedence,
              OperatorDef::Infix(o) => {
                op.precedence() < o.precedence
                  || (o.assoc == Assoc::Left && op.precedence() == o.precedence)
                  || matches!(op, OperatorDef::Postfix(_))
              }
            })
            .unwrap_or(false)
          {
            pop_operator(start_i.clone(), cur_i.clone(), operands, operators, fold)?;
          }
          operators.push(new_operator);
          *cur_i = new_i;
          Ok(true)
        }
      }
    };

    'main: loop {
      while process_new_operator(
        prefix.parse(i1.clone()),
        i.clone(),
        &mut i1,
        &mut operands,
        &mut operators,
        fold.borrow_mut(),
      )? {}

      let (i2, o) = match operand.borrow_mut().parse(i1.clone()) {
        Ok((i, o)) => (i, o),
        Err(Err::Error(e)) => return Err(Err::Error(E::append(i, ErrorKind::Precedence, e))),
        Err(e) => return Err(e),
      };
      operands.push(o);
      i1 = i2;

      while process_new_operator(
        postfix.parse(i1.clone()),
        i.clone(),
        &mut i1,
        &mut operands,
        &mut operators,
        fold.borrow_mut(),
      )? {}

      if !process_new_operator(
        infix.parse(i1.clone()),
        i.clone(),
        &mut i1,
        &mut operands,
        &mut operators,
        fold.borrow_mut(),
      )? {
        break 'main;
      }

      i = i1.clone();
    }

    // process remaining operators
    while !operators.is_empty() {
      pop_operator(
        i.clone(),
        i.clone(),
        &mut operands,
        &mut operators,
        fold.borrow_mut(),
      )?;
    }

    if operands.len() == 1 {
      Ok((i1, operands.pop().unwrap()))
    } else {
      Err(Err::Error(E::from_error_kind(i, ErrorKind::Precedence)))
    }
  }
}

mod closure_ops {
  use std::{cell::RefCell, rc::Rc};

  use crate::{
    combinator::map,
    error::{FromExternalError, ParseError},
    Parser,
  };

  use super::{binary_op, unary_op, Assoc, BinaryDef, OperatorCall, UnaryDef};

  /// Trait alias for `FnMut(Op, O) -> Result<O, E> + 'a`
  ///r
  /// Its purpose is as a [`map_res`](crate::combinator::map_res)-like mapping function,
  /// called when a unary operator is fully read in (as far as the parser knows so far)
  /// with the operator and operand provided.
  ///
  /// TODO: I would love this to mirror the [`Parser`](crate::Parser)-like interface of the [`pratt`](super::pratt) module
  pub trait UnaryDefFn<'a, I: 'a, O, E, Op>: FnMut(Op, O) -> Result<O, E> + 'a {}
  impl<'a, T, I: 'a, O, E, Op> UnaryDefFn<'a, I, O, E, Op> for T where
    T: FnMut(Op, O) -> Result<O, E> + 'a
  {
  }

  /// Trait alias for `FnMut(Op, O, O) -> Result<O, E> + 'a`
  ///
  /// Its purpose is as a [`map_res`](crate::combinator::map_res)-like mapping function,
  /// called when a binary operator is fully read in (as far as the parser knows so far)
  /// with the operator and both operands provided.
  ///
  /// TODO: I would love this to mirror the [`Parser`](crate::Parser)-like interface of the [`pratt`](super::pratt) module
  pub trait BinaryDefFn<'a, I: 'a, O, E, Op>: FnMut(Op, O, O) -> Result<O, E> + 'a {}
  impl<'a, T, I: 'a, O, E, Op> BinaryDefFn<'a, I, O, E, Op> for T where
    T: FnMut(Op, O, O) -> Result<O, E> + 'a
  {
  }

  /// Central dispatcher for the *attached closure paradigm*.
  ///
  /// # Using [`shunting_yard`](super::shunting_yard) with attached closures
  ///
  /// Using [`binary_closure`] and [`unary_closure`] as counterparts to [`binary_op`] and [`unary_op`] respectively, a closure with
  /// fold logic can be attached to each individual matchable operator. Using `consume_closures` as the `fold` input to the
  /// [`shunting_yard`](super::shunting_yard) parser, the correct closure for each matched operator is then automatically dispatched.
  ///
  /// This system is fully opt-in and can easily be replicated; its advantage is a close semantic coupling of each operator with the
  /// fold operation it produces, which may be more readable and less boilerplate-heavy in certain situations.
  ///
  /// Using this function changes all operator output types to have closures attached: this means if one branch uses this feature,
  /// all other branches must either use it too, or be made compatible with it. This can be done by wrapping the ordinary output parsers
  /// in [`binary_nop`] and [`unary_nop`] respectively, which will make them not be dispatched and instead fall through into the
  /// fallback fold function passed as an argument to `consume_closures`. If no such case exists, the fallback closure may be
  /// `|_,_| unreachable!()`.
  pub fn consume_closures<'a, I: Clone + 'a, O, E, E2, Op1, Op2, Op3, F>(
    mut f: F,
  ) -> impl FnMut(
    OperatorCall<
      (Op1, Option<Rc<RefCell<dyn BinaryDefFn<'a, I, O, E2, Op1>>>>),
      (Op2, Option<Rc<RefCell<dyn UnaryDefFn<'a, I, O, E2, Op2>>>>),
      (Op3, Option<Rc<RefCell<dyn UnaryDefFn<'a, I, O, E2, Op3>>>>),
      O,
    >,
  ) -> Result<O, E2>
  where
    F: FnMut(OperatorCall<Op1, Op2, Op3, O>) -> Result<O, E2> + 'a,
    E: FromExternalError<I, E2>,
  {
    move |opcall| match opcall {
      OperatorCall::Infix(lhs, (op1, Some(f1)), rhs) => f1.as_ref().borrow_mut()(op1, lhs, rhs),
      OperatorCall::Infix(lhs, (op1, None), rhs) => f(OperatorCall::Infix(lhs, op1, rhs)),
      OperatorCall::Prefix((op2, Some(f2)), val) => f2.as_ref().borrow_mut()(op2, val),
      OperatorCall::Prefix((op2, None), val) => f(OperatorCall::Prefix(op2, val)),
      OperatorCall::Postfix(val, (op3, Some(f3))) => f3.as_ref().borrow_mut()(op3, val),
      OperatorCall::Postfix(val, (op3, None)) => f(OperatorCall::Postfix(val, op3)),
    }
  }

  /// Counterpart to [`binary_op`] in the *attached closure paradigm*: attaches this operator's fold logic to it,
  /// so it can be automatically dispatched by [`consume_closures`] (see there for more information).
  pub fn binary_closure<'a, I: Clone + 'a, O, E, E2, Op, Q: Ord + Copy, P, F>(
    parser: P,
    precedence: Q,
    assoc: Assoc,
    fold: F,
  ) -> impl Parser<
    I,
    Output = BinaryDef<(Op, Option<Rc<RefCell<dyn BinaryDefFn<'a, I, O, E2, Op>>>>), Q>,
    Error = E,
  >
  where
    P: Parser<I, Output = Op, Error = E>,
    F: BinaryDefFn<'a, I, O, E2, Op>,
    E: ParseError<I> + FromExternalError<I, E2>,
  {
    let fold: Rc<RefCell<dyn BinaryDefFn<'a, I, O, E2, Op>>> = Rc::new(RefCell::new(fold));
    binary_op(
      parser.map(move |op| (op, Some(fold.clone()))),
      precedence,
      assoc,
    )
  }
  /// Counterpart to [`unary_op`] in the *attached closure paradigm*: attaches this operator's fold logic to it,
  /// so it can be automatically dispatched by [`consume_closures`] (see there for more information).
  pub fn unary_closure<'a, I: Clone + 'a, O, E, E2, Op, Q: Ord + Copy, P, F>(
    parser: P,
    precedence: Q,
    fold: F,
  ) -> impl Parser<
    I,
    Output = UnaryDef<(Op, Option<Rc<RefCell<dyn UnaryDefFn<'a, I, O, E2, Op>>>>), Q>,
    Error = E,
  >
  where
    P: Parser<I, Output = Op, Error = E>,
    F: UnaryDefFn<'a, I, O, E2, Op>,
    E: ParseError<I> + FromExternalError<I, E2>,
  {
    let fold: Rc<RefCell<dyn UnaryDefFn<'a, I, O, E2, Op>>> = Rc::new(RefCell::new(fold));
    unary_op(parser.map(move |op| (op, Some(fold.clone()))), precedence)
  }

  /// Wrapper for parser branches that don't have closures attached using [`binary_closure`],
  /// so they can be used together in combinators and ultimately handled by [`consume_closures`]
  /// (see there for more information).
  pub fn binary_nop<'a, I: Clone + 'a, O, E, E2, Op, Q: Ord + Copy, P>(
    parser: P,
  ) -> impl Parser<
    I,
    Output = BinaryDef<(Op, Option<Rc<RefCell<dyn BinaryDefFn<'a, I, O, E2, Op>>>>), Q>,
    Error = E,
  >
  where
    P: Parser<I, Output = BinaryDef<Op, Q>, Error = E>,
    E: ParseError<I> + FromExternalError<I, E2>,
  {
    map(parser, |o| BinaryDef {
      value: (o.value, None),
      precedence: o.precedence,
      assoc: o.assoc,
    })
  }
  /// Wrapper for parser branches that don't have closures attached using [`unary_closure`],
  /// so they can be used together in combinators and ultimately handled by [`consume_closures`]
  /// (see there for more information).
  pub fn unary_nop<'a, I: Clone + 'a, O, E, E2, Op, Q: Ord + Copy, P>(
    op: P,
  ) -> impl Parser<
    I,
    Output = UnaryDef<(Op, Option<Rc<RefCell<dyn UnaryDefFn<'a, I, O, E2, Op>>>>), Q>,
    Error = E,
  >
  where
    P: Parser<I, Output = UnaryDef<Op, Q>, Error = E>,
    E: ParseError<I> + FromExternalError<I, E2>,
  {
    map(op, |o| UnaryDef {
      value: (o.value, None),
      precedence: o.precedence,
    })
  }
}
pub use closure_ops::*;
