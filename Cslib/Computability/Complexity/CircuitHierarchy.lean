/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Complexity.NonUniform
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# Circuit Complexity Hierarchy: NC and AC

This file defines the circuit complexity classes **NC** and **AC**
via size and depth bounds on circuit families, and proves basic
containment relations in the hierarchy.

## Main Definitions

* `SizeDepth Op s d` — languages decidable by circuit families over `Op`
  with size ≤ `s(n)` and depth ≤ `d(n)`
* `NC k` — poly size, O(log^k n) depth, bounded fan-in
* `AC k` — poly size, O(log^k n) depth, unbounded fan-in

## Design Notes

The depth bound uses `(Nat.log 2 n + 1) ^ k` rather than `(Nat.log 2 n) ^ k`.
Since `Nat.log 2 0 = 0` and `Nat.log 2 1 = 0`, the bare `log` would make the
depth bound zero for small inputs when `k ≥ 1`, which is pathological. Adding 1
ensures the base is always ≥ 1, making the hierarchy monotone (`NC^k ⊆ NC^(k+1)`)
provable by simple exponent comparison.

## Main Results

* `SizeDepth_mono_size` — monotone in size bound
* `SizeDepth_mono_depth` — monotone in depth bound
* `NC_mono` — NC^k ⊆ NC^(k+1)
* `AC_mono` — AC^k ⊆ AC^(k+1)
* `NC_subset_SIZE` — NC^k ⊆ P/poly
* `AC_subset_SIZE` — AC^k ⊆ P/poly

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

open Cslib.Circuits Polynomial

variable {Op : Type*} [Basis Op]

/-- `SizeDepth Op s d` is the class of languages decidable by circuit
families over basis `Op` whose circuit at input size `n` has at most
`s n` gates and depth at most `d n`. -/
def SizeDepth (Op : Type*) [Basis Op]
    (s d : ℕ → ℕ) : Set (Set (List Bool)) :=
  { L | ∃ C : CircuitFamily Op,
    C.Decides L ∧ (∀ n, (C n).size ≤ s n) ∧ (∀ n, (C n).depth ≤ d n) }

/-- **NC^k** is the class of languages decidable by polynomial-size,
O(log^k n)-depth circuit families with bounded fan-in (at most 2).

We parameterize by a size polynomial `p` and a depth constant `c`
and require `size ≤ p(n)` and `depth ≤ c · (log₂ n + 1)^k`. -/
def NC (k : ℕ) : Set (Set (List Bool)) :=
  { L | ∃ (p : Polynomial ℕ) (c : ℕ),
    L ∈ SizeDepth NCOp
      (fun n => p.eval n)
      (fun n => c * (Nat.log 2 n + 1) ^ k) }

/-- **AC^k** is the class of languages decidable by polynomial-size,
O(log^k n)-depth circuit families with unbounded fan-in. -/
def AC (k : ℕ) : Set (Set (List Bool)) :=
  { L | ∃ (p : Polynomial ℕ) (c : ℕ),
    L ∈ SizeDepth ACOp
      (fun n => p.eval n)
      (fun n => c * (Nat.log 2 n + 1) ^ k) }

end

open Cslib.Circuits Polynomial

/-! ### Monotonicity of SizeDepth -/

/-- `SizeDepth` is monotone in the size bound. -/
theorem SizeDepth_mono_size {Op : Type*} [Basis Op]
    {s s' d : ℕ → ℕ} (h : ∀ n, s n ≤ s' n) :
    SizeDepth Op s d ⊆ SizeDepth Op s' d := by
  intro L ⟨C, hDec, hSize, hDepth⟩
  exact ⟨C, hDec, fun n => (hSize n).trans (h n), hDepth⟩

/-- `SizeDepth` is monotone in the depth bound. -/
theorem SizeDepth_mono_depth {Op : Type*} [Basis Op]
    {s d d' : ℕ → ℕ} (h : ∀ n, d n ≤ d' n) :
    SizeDepth Op s d ⊆ SizeDepth Op s d' := by
  intro L ⟨C, hDec, hSize, hDepth⟩
  exact ⟨C, hDec, hSize, fun n => (hDepth n).trans (h n)⟩

/-! ### NC hierarchy -/

/-- **NC^k ⊆ NC^(k+1)**: the NC hierarchy is monotone.

Since the depth bound uses `(log₂ n + 1)^k` and `log₂ n + 1 ≥ 1`,
we have `(log₂ n + 1)^k ≤ (log₂ n + 1)^(k+1)` by exponent monotonicity. -/
public theorem NC_mono {k : ℕ} : NC k ⊆ NC (k + 1) := by
  intro L ⟨p, c, C, hDec, hSize, hDepth⟩
  exact ⟨p, c, C, hDec, hSize, fun n => (hDepth n).trans
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ k)))⟩

/-! ### AC hierarchy -/

/-- **AC^k ⊆ AC^(k+1)**: the AC hierarchy is monotone. -/
public theorem AC_mono {k : ℕ} : AC k ⊆ AC (k + 1) := by
  intro L ⟨p, c, C, hDec, hSize, hDepth⟩
  exact ⟨p, c, C, hDec, hSize, fun n => (hDepth n).trans
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ k)))⟩

/-! ### NC, AC ⊆ P/poly -/

/-- **NC^k ⊆ P/poly**: NC circuits have polynomial size,
so they are captured by P/poly. -/
public theorem NC_subset_SIZE {k : ℕ} :
    NC k ⊆ PPoly (Op := NCOp) := by
  intro L ⟨p, _, C, hDec, hSize, _⟩
  exact ⟨C, p, hDec, hSize⟩

/-- **AC^k ⊆ P/poly**: AC circuits have polynomial size,
so they are captured by P/poly. -/
public theorem AC_subset_SIZE {k : ℕ} :
    AC k ⊆ PPoly (Op := ACOp) := by
  intro L ⟨p, _, C, hDec, hSize, _⟩
  exact ⟨C, p, hDec, hSize⟩
