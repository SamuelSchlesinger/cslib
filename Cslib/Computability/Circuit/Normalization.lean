/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Dependency
public import Cslib.Computability.Circuit.Synthesis

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card

/-!
# Semantic circuit normalization

Merging gates that compute the same function preserves wire values and does not
increase circuit size. A gate duplicating an earlier wire, or read by neither a gate
nor the output, can be removed to obtain a strictly smaller single-output circuit.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g m : ℕ} {U : Type*}

/-- Distinct gates compute distinct scalar functions. Gates may still duplicate input
functions or be unused by the outputs. -/
def Program.Irredundant (p : Program σ n g) (i : Interpretation σ U) : Prop :=
  Function.Injective (p.gateFunction i)

/-- A circuit is irredundant when its internal gates compute pairwise distinct functions. -/
def Circuit.Irredundant (c : Circuit σ n m) (i : Interpretation σ U) : Prop :=
  c.program.Irredundant i

/-- A program can be rebuilt with distinct gate functions, preserving every wire's value. -/
theorem Program.exists_irredundant (p : Program σ n g) (i : Interpretation σ U) :
    ∃ k ≤ g, ∃ q : Program σ n k, ∃ ρ : Wire.Renaming n g k,
      (∀ x w, q.trace i x (ρ w) = p.trace i x w) ∧
        q.Irredundant i := by
  classical
  induction p with
  | empty =>
      exact ⟨0, le_rfl, .empty, .id, by simp, fun w => Fin.elim0 w⟩
  | @gate g p line ih =>
      obtain ⟨k, hk, q, ρ, hρ, hq⟩ := ih
      let l := line.mapWires ρ
      have hl (x) : l.eval i x (q.eval i x) = line.eval i x (p.eval i x) :=
        line.eval_mapWires ρ i x x (p.eval i x) (q.eval i x) (hρ x)
      by_cases h : ∃ w, q.gateFunction i w = fun x => l.eval i x (q.eval i x)
      · obtain ⟨w, hw⟩ := h
        refine ⟨k, by omega, q, ρ.skipLast (Wire.gate w), ?_, hq⟩
        intro x v
        refine Wire.lastCases ?_ (fun v => ?_) v
        · simpa using (congrFun hw x).trans (hl x)
        · simpa using hρ x v
      · refine ⟨k + 1, by omega, q.gate l, ρ.appendLast, ?_, ?_⟩
        · intro x v
          refine Wire.lastCases ?_ (fun v => ?_) v
          · simpa using hl x
          · simpa using hρ x v
        · change Function.Injective ((q.gate l).gateFunction i)
          convert Fin.snoc_injective_of_injective hq h using 1
          ext gate x
          refine Fin.lastCases ?_ (fun gate => ?_) gate <;> simp

/-- Every circuit has an equivalent circuit with distinct gate functions and no more gates. -/
theorem Circuit.exists_irredundant (c : Circuit σ n m) (i : Interpretation σ U) :
    ∃ d : Circuit σ n m, d.eval i = c.eval i ∧ d.Irredundant i ∧ d.size ≤ c.size := by
  obtain ⟨k, hk, q, ρ, hρ, hq⟩ := c.program.exists_irredundant i
  exact ⟨⟨q, ρ ∘ c.outputs⟩, funext fun x => funext fun o => hρ x (c.outputs o), hq, hk⟩

/-- A gate duplicating an earlier wire can be removed without changing the output. -/
theorem Circuit.exists_smaller_of_equal {I : Interpretation σ U} (c : Circuit σ n 1)
    (gate : Fin c.size) (wire : Wire n c.size)
    (hbefore : wire.val < n + gate.val)
    (heq : c.program.gateFunction I gate = c.program.wireFunction I wire) :
    ∃ d : Circuit σ n 1, d.eval I = c.eval I ∧ d.size < c.size := by
  classical
  let cost (j : Fin c.size) : ℕ := if j = gate then 0 else 1
  have hcost : (∑ j, cost j) + 1 = c.size := by
    simp [cost, Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem,
      Nat.sub_add_cancel (show 1 ≤ c.size from by omega)]
  have hs := c.program.synthesis_of_steps (I := I) cost (fun j => by
    by_cases hj : j = gate
    · subst j
      simp only [cost, ite_eq_left rfl]
      apply Synthesis.of_mem
      rw [heq]
      exact c.program.wireFunction_mem_before gate wire hbefore
    · simpa [cost, hj] using c.program.synthesis_step (I := I) j)
  let f := c.program.wireFunction I (c.outputs 0)
  have hf : {f} ⊆ available I c.program := Set.singleton_subset_iff.mpr ⟨_, rfl⟩
  obtain ⟨d, hd, hsize⟩ := (hs.mono Set.Subset.rfl hf le_rfl).exists_circuit
  refine ⟨d, ?_, by omega⟩
  funext x output
  have hzero : output = 0 := Subsingleton.elim _ _
  subst output
  exact congrFun (hd x) 0

/-- A gate read by no gate or designated output can be omitted. The given input supplies
a zero-cost placeholder during reconstruction. -/
theorem Circuit.exists_smaller_of_unused {I : Interpretation σ U}
    (c : Circuit σ n 1) (input : Fin n)
    (gate : Fin c.size) (hread : ∀ j, ¬ c.program.Reads j (Wire.gate gate))
    (houtput : c.outputs 0 ≠ Wire.gate gate) :
    ∃ d : Circuit σ n 1, d.eval I = c.eval I ∧ d.size < c.size := by
  classical
  let f (j : Fin c.size) : (Fin n → U) → U :=
    if j = gate then fun x => x input else c.program.gateFunction I j
  let cost (j : Fin c.size) : ℕ := if j = gate then 0 else 1
  have hcost : (∑ j, cost j) + 1 = c.size := by
    simp [cost, Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem,
      Nat.sub_add_cancel (show 1 ≤ c.size from by have := gate.isLt; omega)]
  have hs : Synthesis I (inputs n) (inputs n ∪ Set.range f) (∑ j, cost j) := by
    apply Synthesis.with_sources
    apply Synthesis.ordered_family f cost
    intro j
    by_cases hj : j = gate
    · subst j
      simp only [f, cost, ite_eq_left rfl]
      exact Synthesis.of_mem (Or.inl ⟨input, rfl⟩)
    · simp only [cost, hj, ite_false, f]
      have hargs (a : Fin (σ.Arity (c.program.lines j).op)) :
          c.program.wireFunction I ((c.program.lines j).wires a) ∈
            inputs n ∪ f '' {i | i < j} := by
        have hlt := c.program.lines_wires_lt j a
        generalize hw : (c.program.lines j).wires a = wire at hlt ⊢
        induction wire using Fin.addCases with
        | left i => exact Or.inl ⟨i, (c.program.wireFunction_input I i).symm⟩
        | right i =>
          have hne : i ≠ gate := by
            intro h
            subst i
            exact hread j ⟨a, hw⟩
          refine Or.inr ⟨i, by simpa using hlt, ?_⟩
          simp [f, hne]
      have h := Synthesis.gate (I := I) (c.program.lines j).op
        (fun a => c.program.wireFunction I ((c.program.lines j).wires a)) hargs
      have heq : (fun x => I (c.program.lines j).op
          (fun a => c.program.wireFunction I ((c.program.lines j).wires a) x)) =
          c.program.gateFunction I j := by
        funext x
        exact c.program.lines_eval I x j
      simpa only [heq, hj, ite_false] using h
  have hout : c.program.wireFunction I (c.outputs 0) ∈ inputs n ∪ Set.range f := by
    generalize hw : c.outputs 0 = wire at houtput ⊢
    induction wire using Fin.addCases with
    | left i => exact Or.inl ⟨i, (c.program.wireFunction_input I i).symm⟩
    | right j =>
      have hne : j ≠ gate := fun h => houtput (congrArg (Fin.natAdd n) h)
      exact Or.inr ⟨j, by simp [f, hne]⟩
  obtain ⟨d, hd, hsize⟩ :=
    (hs.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr hout) le_rfl).exists_circuit
  refine ⟨d, ?_, by omega⟩
  funext x output
  have hzero : output = 0 := Subsingleton.elim _ _
  subst output
  exact congrFun (hd x) 0

end Cslib.Circuits
