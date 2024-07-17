//! Parser combinators modeling some well-known algorithms for
//! precedence-based expression parsing (namely [Pratt Parsing](`pratt`) and
//! the [Shunting-Yard Algorithm](`shunting_yard`))

pub mod pratt;
pub mod shunting_yard;


/// Describes an instance of operator application, after correct parsing
/// with precedence and associativity. Contains both the operator itself
/// along with its operand(s)' parser output, for use in the `fold` closure
/// of the parser combinator.
pub enum OperatorCall<Op1, Op2, Op3, O> {
  /// Infix Operator
  Infix(O, Op1, O),
  /// Prefix Operator
  Prefix(Op2, O),
  /// Postfix Operator
  Postfix(O, Op3),
}

/// Associativity for binary operators, i.e. how a string of operators of the
/// same type will be parenthesized.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Assoc {
  /// Left associative: `a + b + c + d => (((a + b) + c ) + d)`.
  /// 
  /// Examples: addition, multiplication, indexing,...
  Left,
  /// Right associative: `a ^ b ^ c ^ ... => (a ^ (b ^ (c ^ d)))`
  /// 
  /// Examples: exponentiation, function application,...
  Right,
  /// Undefined associativity: returned for unary operators, which do not
  /// have associativity. Not recommended for binary operators,
  /// because which associativity any given algorithm will default to
  /// is undefined behavior.
  None,
}