/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Circuits.Formula.Measures

@[expose] public section

/-! # Standard-Basis Boolean Formulas

Convenience constructors and evaluation/measure lemmas for formulas over the standard
basis (`StdOp`): binary AND, binary OR, and unary NOT.

The smart constructors `Formula.and`, `Formula.or`, and `Formula.not` build formulas
with the correct number of children for each operation, so the arity check in
`Formula.eval` always succeeds for formulas built this way.

## Main definitions

- `Formula.and`, `Formula.or`, `Formula.not` — smart constructors that guarantee
  correct arity
- `eval_and`, `eval_or`, `eval_not` — evaluation reduces to native Boolean operations
- `eval_not_not` — double negation elimination
- `deMorgan_and`, `deMorgan_or` — De Morgan's laws at the formula level
- `size_and`, `size_or`, `size_not` — size of standard constructs
- `depth_and`, `depth_or`, `depth_not` — depth of standard constructs

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

namespace Cslib.Circuits

namespace Formula

variable {Var : Type*}

/-- Binary AND of two formulas over the standard basis.
Constructs `.gate .and [a, b]`, which has exactly 2 children matching `StdOp.and`'s arity. -/
@[scoped grind =]
def and (a b : Formula Var StdOp) : Formula Var StdOp := .gate .and [a, b]

/-- Binary OR of two formulas over the standard basis.
Constructs `.gate .or [a, b]`, which has exactly 2 children matching `StdOp.or`'s arity. -/
@[scoped grind =]
def or (a b : Formula Var StdOp) : Formula Var StdOp := .gate .or [a, b]

/-- Negation of a formula over the standard basis.
Constructs `.gate .not [a]`, which has exactly 1 child matching `StdOp.not`'s arity. -/
@[scoped grind =]
def not (a : Formula Var StdOp) : Formula Var StdOp := .gate .not [a]

/-! ### Evaluation lemmas -/

@[simp, scoped grind =]
theorem eval_and (v : Var → Bool) (a b : Formula Var StdOp) :
    (Formula.and a b).eval v = (a.eval v && b.eval v) := by
  simp [Formula.and, eval, Basis.eval, Arity.admits]

@[simp, scoped grind =]
theorem eval_or (v : Var → Bool) (a b : Formula Var StdOp) :
    (Formula.or a b).eval v = (a.eval v || b.eval v) := by
  simp [Formula.or, eval, Basis.eval, Arity.admits]

@[simp, scoped grind =]
theorem eval_not (v : Var → Bool) (a : Formula Var StdOp) :
    (Formula.not a).eval v = !(a.eval v) := by
  simp [Formula.not, eval, Basis.eval, Arity.admits]

/-! ### Double negation -/

@[simp, scoped grind =]
theorem eval_not_not (v : Var → Bool) (a : Formula Var StdOp) :
    (Formula.not (Formula.not a)).eval v = a.eval v := by
  simp [eval_not, Bool.not_not]

/-! ### De Morgan's laws -/

@[scoped grind =]
theorem deMorgan_and (v : Var → Bool) (a b : Formula Var StdOp) :
    (Formula.not (Formula.and a b)).eval v =
    (Formula.or (Formula.not a) (Formula.not b)).eval v := by
  simp [eval_not, eval_and, eval_or]

@[scoped grind =]
theorem deMorgan_or (v : Var → Bool) (a b : Formula Var StdOp) :
    (Formula.not (Formula.or a b)).eval v =
    (Formula.and (Formula.not a) (Formula.not b)).eval v := by
  simp [eval_not, eval_and, eval_or]

/-! ### Measure lemmas for standard constructors -/

@[simp, scoped grind =]
theorem size_and (a b : Formula Var StdOp) :
    (Formula.and a b).size = 1 + a.size + b.size := by
  simp [Formula.and, size, List.map, List.sum]; omega

@[simp, scoped grind =]
theorem size_or (a b : Formula Var StdOp) :
    (Formula.or a b).size = 1 + a.size + b.size := by
  simp [Formula.or, size, List.map, List.sum]; omega

@[simp, scoped grind =]
theorem size_not (a : Formula Var StdOp) :
    (Formula.not a).size = 1 + a.size := by
  simp [Formula.not, size, List.map, List.sum]

@[simp, scoped grind =]
theorem depth_and (a b : Formula Var StdOp) :
    (Formula.and a b).depth = 1 + max a.depth b.depth := by
  simp [Formula.and, depth, List.map, List.foldl, Nat.max_def]

@[simp, scoped grind =]
theorem depth_or (a b : Formula Var StdOp) :
    (Formula.or a b).depth = 1 + max a.depth b.depth := by
  simp [Formula.or, depth, List.map, List.foldl, Nat.max_def]

@[simp, scoped grind =]
theorem depth_not (a : Formula Var StdOp) :
    (Formula.not a).depth = 1 + a.depth := by
  simp [Formula.not, depth, List.map, List.foldl]

end Formula

end Cslib.Circuits
