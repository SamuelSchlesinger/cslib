/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init

@[expose] public section

/-! # Circuit Basis

A `Basis` defines the set of operations (gates) available in a circuit or formula.
Each operation declares an `Arity` — how many inputs it accepts — and provides
evaluation semantics via `Basis.eval`.

## Design

The key design choice is that `Basis.eval` requires a proof that the input list length
satisfies the operation's arity (`(arity op).admits bs.length`). This makes it impossible
to evaluate a gate with the wrong number of inputs at the type level. Because `Arity.admits`
has a `Decidable` instance, callers can obtain the proof via a run-time check when the
arity is not statically known.

The `StdOp` basis demonstrates this pattern: AND and OR have arity `.exactly 2`, NOT has
arity `.exactly 1`, and `eval` uses dependent pattern matching so Lean's equation compiler
verifies exhaustiveness against the arity constraint.

## Main definitions

- `Arity` — either a fixed natural number (`.exactly k`) or unbounded (`.any`)
- `Arity.admits` — predicate: does an arity accept a given input count?
- `Basis` — typeclass pairing an `arity` function with a type-safe `eval`
- `StdOp` — standard Boolean operations: AND, OR, NOT
- `Basis StdOp` — standard basis instance with fixed arities

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

namespace Cslib.Circuits

/-- An `Arity` specifies how many inputs a gate operation accepts:
either exactly `k` inputs, or any number of inputs. -/
inductive Arity where
  /-- The gate accepts exactly `k` inputs. -/
  | exactly : Nat → Arity
  /-- The gate accepts any number of inputs. -/
  | any : Arity
  deriving DecidableEq, Repr

/-- Predicate stating that arity `a` accepts `n` inputs.
For `.exactly k`, this requires `n = k`; for `.any`, it is always `True`. -/
@[simp]
def Arity.admits : Arity → Nat → Prop
  | .exactly k, n => n = k
  | .any, _ => True

instance (a : Arity) (n : Nat) : Decidable (a.admits n) :=
  match a with
  | .exactly k => if h : n = k then isTrue h else isFalse h
  | .any => isTrue trivial

/-- A `Basis` defines the arity and evaluation semantics for a set of gate operations.
Each operation declares its arity, and `eval` requires a proof that the input list
has the correct length. -/
class Basis (Op : Type*) where
  /-- The arity of a gate operation. -/
  arity : Op → Arity
  /-- Evaluate a gate operation on a list of Boolean inputs of the correct length. -/
  eval : (op : Op) → (bs : List Bool) → (arity op).admits bs.length → Bool

/-- Standard Boolean operations: AND (binary conjunction), OR (binary disjunction),
and NOT (unary negation). These form a functionally complete basis for Boolean logic. -/
inductive StdOp where
  /-- Boolean conjunction. -/
  | and
  /-- Boolean disjunction. -/
  | or
  /-- Boolean negation. -/
  | not
  deriving DecidableEq, Repr

/-- The standard basis assigns arity 2 to AND and OR, arity 1 to NOT, and evaluates
them by pattern matching on the appropriately-sized input list. -/
instance : Basis StdOp where
  arity
    | .and => .exactly 2
    | .or => .exactly 2
    | .not => .exactly 1
  eval
    | .and, [a, b], _ => a && b
    | .or, [a, b], _ => a || b
    | .not, [b], _ => !b

end Cslib.Circuits
