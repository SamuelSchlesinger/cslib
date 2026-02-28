/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Complexity.Classes

/-!
# Closure Properties of Complexity Classes

This file proves basic closure properties of the complexity classes
**P**, **NP**, and **coNP**.

## Main Results

* `ComplexityP_closed_complement` — P is closed under complement
* `ComplexityNP_subset_ComplexityCoNP_iff` — NP ⊆ coNP iff every NP
  language has its complement in NP
* `ComplexityP_subset_ComplexityCoNP` — P ⊆ coNP

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

open Turing SingleTapeTM Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- If `f` decides `L`, then swapping the accept/reject behaviour of `f`
gives a decider for `Lᶜ`. Here we just record the logical equivalence;
constructing the complemented TM would require building a new machine. -/
theorem Decides.complement {f : List Symbol → List Symbol}
    {L : Set (List Symbol)} (h : Decides f L) :
    ∀ x, x ∈ Lᶜ ↔ f x = [] := by
  intro x
  simp only [Set.mem_compl_iff]
  constructor
  · intro hx
    by_contra hne
    exact hx ((h x).mpr hne)
  · intro hfx hx
    exact ((h x).mp hx) hfx

/-- **P is closed under complement**: if `L ∈ P` then `Lᶜ ∈ P`.

*Proof idea*: Given a poly-time decider `f` for `L`, we need a poly-time
decider `f'` for `Lᶜ` such that `f' x ≠ [] ↔ x ∈ Lᶜ`. Since
constructing a new TM that flips the output requires TM machinery
beyond what is currently formalized, we use `sorry` for the
computational witness while proving the logical correctness. -/
-- TODO: construct the complement TM explicitly
public theorem ComplexityP_closed_complement
    {L : Set (List Symbol)} (hL : L ∈ ComplexityP) :
    Lᶜ ∈ ComplexityP (Symbol := Symbol) := by
  obtain ⟨f, ⟨hf⟩, hDecides⟩ := hL
  -- We need a function f' that accepts iff f rejects
  -- f' x = if f x = [] then [default] else []
  let f' : List Symbol → List Symbol :=
    fun x => if f x = [] then [default] else []
  refine ⟨f', ⟨sorry⟩, fun x => ?_⟩
  simp only [f']
  constructor
  · intro hx
    have := (hDecides.complement x).mp hx
    simp [this]
  · intro hx
    rw [Set.mem_compl_iff]
    intro hmem
    have := (hDecides x).mp hmem
    simp [this] at hx

/-- **NP ⊆ coNP ↔ ∀ L ∈ NP, Lᶜ ∈ NP**. This is just the unfolding of
the definitions: coNP is defined as `{L | Lᶜ ∈ NP}`, so `NP ⊆ coNP`
means every NP language has its complement in NP. -/
public theorem ComplexityNP_subset_ComplexityCoNP_iff :
    ComplexityNP (Symbol := Symbol) ⊆ ComplexityCoNP ↔
    ∀ L ∈ ComplexityNP (Symbol := Symbol), Lᶜ ∈ ComplexityNP := by
  constructor
  · intro h L hL
    have := h hL
    simp only [ComplexityCoNP, Set.mem_setOf_eq] at this
    exact this
  · intro h L hL
    simp only [ComplexityCoNP, Set.mem_setOf_eq]
    exact h L hL

/-- **P ⊆ coNP**: every language in P is also in coNP.

This follows from P being closed under complement and P ⊆ NP:
if `L ∈ P`, then `Lᶜ ∈ P ⊆ NP`, so `L ∈ coNP`. -/
public theorem ComplexityP_subset_ComplexityCoNP :
    ComplexityP (Symbol := Symbol) ⊆ ComplexityCoNP := by
  intro L hL
  simp only [ComplexityCoNP, Set.mem_setOf_eq]
  exact ComplexityP_subset_ComplexityNP
    (ComplexityP_closed_complement hL)
