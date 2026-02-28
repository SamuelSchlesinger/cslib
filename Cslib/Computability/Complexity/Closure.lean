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

* `ComplexityNP_subset_ComplexityCoNP_iff` — NP ⊆ coNP iff every NP
  language has its complement in NP

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

open Turing SingleTapeTM Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

omit [Inhabited Symbol] [Fintype Symbol] in
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

omit [Inhabited Symbol] [Fintype Symbol] in
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
