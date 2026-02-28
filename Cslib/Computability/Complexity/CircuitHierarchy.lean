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

* `SizeDepth Op s d` — languages decidable by well-formed circuit families over `Op`
  with size ≤ `s(n)` and depth ≤ `d(n)`
* `NC k` — poly size, O(log^k n) depth, bounded fan-in
* `AC k` — poly size, O(log^k n) depth, unbounded fan-in

## Design Notes

The depth bound uses `(Nat.log 2 n + 1) ^ k` rather than `(Nat.log 2 n) ^ k`.
Since `Nat.log 2 0 = 0` and `Nat.log 2 1 = 0`, the bare `log` would make the
depth bound zero for small inputs when `k ≥ 1`, which is pathological. Adding 1
ensures the base is always ≥ 1, making the hierarchy monotone (`NC^k ⊆ NC^(k+1)`)
provable by simple exponent comparison.

`SizeDepth` includes a `GatesWellFormed` condition ensuring every gate's input list
has a length admitted by its operation's arity. This matches the standard mathematical
convention that circuit gates are well-formed, and is essential for proving
`NC^k ⊆ AC^k` (the gate embedding preserves evaluation only for well-formed gates).

## Main Results

* `SizeDepth_mono_size` — monotone in size bound
* `SizeDepth_mono_depth` — monotone in depth bound
* `NC_mono` — NC^k ⊆ NC^(k+1)
* `AC_mono` — AC^k ⊆ AC^(k+1)
* `NC_subset_AC` — NC^k ⊆ AC^k
* `NC_subset_SIZE` — NC^k ⊆ P/poly
* `AC_subset_SIZE` — AC^k ⊆ P/poly

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

open Cslib.Circuits Polynomial

variable {Op : Type*} [Basis Op]

/-- `SizeDepth Op s d` is the class of languages decidable by well-formed circuit
families over basis `Op` whose circuit at input size `n` has at most
`s n` gates and depth at most `d n`.

The well-formedness condition (`GatesWellFormed`) requires that every gate's
input list has a length admitted by its operation's arity. This matches the
standard mathematical convention and ensures that circuit evaluation never
falls back to the defensive `false` default for arity mismatches. -/
def SizeDepth (Op : Type*) [Basis Op]
    (s d : ℕ → ℕ) : Set (Set (List Bool)) :=
  { L | ∃ C : CircuitFamily Op,
    C.Decides L ∧ (∀ n, (C n).GatesWellFormed) ∧
    (∀ n, (C n).size ≤ s n) ∧ (∀ n, (C n).depth ≤ d n) }

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
  intro L ⟨C, hDec, hWF, hSize, hDepth⟩
  exact ⟨C, hDec, hWF, fun n => (hSize n).trans (h n), hDepth⟩

/-- `SizeDepth` is monotone in the depth bound. -/
theorem SizeDepth_mono_depth {Op : Type*} [Basis Op]
    {s d d' : ℕ → ℕ} (h : ∀ n, d n ≤ d' n) :
    SizeDepth Op s d ⊆ SizeDepth Op s d' := by
  intro L ⟨C, hDec, hWF, hSize, hDepth⟩
  exact ⟨C, hDec, hWF, hSize, fun n => (hDepth n).trans (h n)⟩

/-! ### NC hierarchy -/

/-- **NC^k ⊆ NC^(k+1)**: the NC hierarchy is monotone.

Since the depth bound uses `(log₂ n + 1)^k` and `log₂ n + 1 ≥ 1`,
we have `(log₂ n + 1)^k ≤ (log₂ n + 1)^(k+1)` by exponent monotonicity. -/
public theorem NC_mono {k : ℕ} : NC k ⊆ NC (k + 1) := by
  intro L ⟨p, c, C, hDec, hWF, hSize, hDepth⟩
  exact ⟨p, c, C, hDec, hWF, hSize, fun n => (hDepth n).trans
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ k)))⟩

/-! ### AC hierarchy -/

/-- **AC^k ⊆ AC^(k+1)**: the AC hierarchy is monotone. -/
public theorem AC_mono {k : ℕ} : AC k ⊆ AC (k + 1) := by
  intro L ⟨p, c, C, hDec, hWF, hSize, hDepth⟩
  exact ⟨p, c, C, hDec, hWF, hSize, fun n => (hDepth n).trans
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ k)))⟩

/-! ### NC^k ⊆ AC^k -/

/-- Embed bounded fan-in operations into unbounded fan-in operations. -/
private def ncToAc : NCOp → ACOp
  | .and => .and
  | .or  => .or
  | .not => .not

/-- The embedding preserves arity admissibility: if NCOp admits an input count,
so does the corresponding ACOp (since `.atMost 2` implies `.any`). -/
private theorem ncToAc_admits (op : NCOp) (n : ℕ) :
    (Basis.arity op).admits n → (Basis.arity (ncToAc op)).admits n := by
  cases op <;> simp [ncToAc, Basis.arity]

/-- The embedding preserves evaluation: on admitted inputs, NCOp and ACOp
compute the same Boolean function (both use the same foldl semantics). -/
private theorem ncToAc_eval (op : NCOp) (bs : List Bool)
    (h : (Basis.arity op).admits bs.length) :
    Basis.eval (ncToAc op) bs (ncToAc_admits op bs.length h) =
    Basis.eval op bs h := by
  cases op with
  | and => simp [ncToAc, Basis.eval]
  | or  => simp [ncToAc, Basis.eval]
  | not =>
    -- h : bs.length = 1, so bs = [b] for some b
    simp only [Arity.admits] at h
    match bs, h with
    | [b], _ => simp [ncToAc, Basis.eval]

/-- The embedding preserves circuit evaluation for well-formed circuits.

Well-formedness ensures every gate has the correct number of inputs for its
NCOp arity (≤ 2 for AND/OR, exactly 1 for NOT). Since ACOp admits at least as
many inputs, the embedded circuit computes the same function. -/
private theorem ncToAc_circuit_eval {n : ℕ} (C : Circuit NCOp n)
    (hWF : C.GatesWellFormed)
    (input : Fin n → Bool) :
    (C.mapOp ncToAc).eval input = C.eval input := by
  simp only [Circuit.eval, Circuit.mapOp]
  -- We prove the stronger statement that the full wire lists agree after
  -- processing any prefix of gates, as long as all processed gates are well-formed.
  suffices ∀ (gs : List (Gate NCOp))
    (hgs : ∀ g ∈ gs, (Basis.arity g.op).admits g.inputs.length)
    (acc : List Bool),
    (gs.map (Gate.mapOp ncToAc)).foldl
      (fun wires gate =>
        wires ++ [if h : (Basis.arity gate.op).admits
                    (gate.inputs.map (wires.getD · false)).length
                  then Basis.eval gate.op (gate.inputs.map (wires.getD · false)) h
                  else false])
      acc =
    gs.foldl
      (fun wires gate =>
        wires ++ [if h : (Basis.arity gate.op).admits
                    (gate.inputs.map (wires.getD · false)).length
                  then Basis.eval gate.op (gate.inputs.map (wires.getD · false)) h
                  else false])
      acc by
    exact congr_arg (·.getD C.outputWire false) (this C.gates hWF _)
  intro gs hgs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons, Gate.mapOp]
    -- The gate g is well-formed: its NCOp arity admits g.inputs.length
    have hg_wf : (Basis.arity g.op).admits g.inputs.length :=
      hgs g (by simp)
    -- The number of inputs doesn't change (mapOp preserves inputs)
    set bs := g.inputs.map (acc.getD · false)
    -- NCOp admits the input list length (same as g.inputs.length)
    have hbs : (Basis.arity g.op).admits bs.length := by
      simp only [bs, List.length_map]; exact hg_wf
    -- ACOp also admits it
    have hbs' : (Basis.arity (ncToAc g.op)).admits bs.length :=
      ncToAc_admits g.op bs.length hbs
    -- Both sides evaluate the gate (no defensive false)
    have h_output :
      (if h : (Basis.arity (ncToAc g.op)).admits bs.length
       then Basis.eval (ncToAc g.op) bs h
       else false) =
      (if h : (Basis.arity g.op).admits bs.length
       then Basis.eval g.op bs h
       else false) := by
      rw [dif_pos hbs', dif_pos hbs]
      exact ncToAc_eval g.op bs hbs
    rw [h_output]
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _

/-- **NC^k ⊆ AC^k**: every language computable by polynomial-size,
O(log^k n)-depth bounded fan-in circuits is also computable by
polynomial-size, O(log^k n)-depth unbounded fan-in circuits.

The proof maps each NCOp gate to the corresponding ACOp gate via `ncToAc`.
Since bounded fan-in AND/OR/NOT compute the same functions as their
unbounded fan-in counterparts (just with a tighter arity constraint),
the mapped circuit computes the same function with the same size and depth. -/
public theorem NC_subset_AC {k : ℕ} : NC k ⊆ AC k := by
  intro L ⟨p, c, C, hDec, hWF, hSize, hDepth⟩
  refine ⟨p, c, fun n => (C n).mapOp ncToAc, ?_, ?_, ?_, ?_⟩
  · -- Decides: the mapped circuit decides the same language
    intro x
    rw [hDec x]
    exact ⟨fun h => by rw [ncToAc_circuit_eval (C x.length) (hWF x.length)]; exact h,
           fun h => by rw [ncToAc_circuit_eval (C x.length) (hWF x.length)] at h; exact h⟩
  · -- WellFormed: the mapping preserves well-formedness
    intro n
    exact Circuit.GatesWellFormed_mapOp ncToAc (C n) ncToAc_admits (hWF n)
  · -- Size: mapOp preserves size
    intro n; simp only [Circuit.size_mapOp]; exact hSize n
  · -- Depth: mapOp preserves depth
    intro n; rw [Circuit.depth_mapOp]; exact hDepth n

/-! ### NC, AC ⊆ P/poly -/

/-- **NC^k ⊆ P/poly**: NC circuits have polynomial size,
so they are captured by P/poly. -/
public theorem NC_subset_SIZE {k : ℕ} :
    NC k ⊆ PPoly (Op := NCOp) := by
  intro L ⟨p, _, C, hDec, _, hSize, _⟩
  exact ⟨C, p, hDec, hSize⟩

/-- **AC^k ⊆ P/poly**: AC circuits have polynomial size,
so they are captured by P/poly. -/
public theorem AC_subset_SIZE {k : ℕ} :
    AC k ⊆ PPoly (Op := ACOp) := by
  intro L ⟨p, _, C, hDec, _, hSize, _⟩
  exact ⟨C, p, hDec, hSize⟩
