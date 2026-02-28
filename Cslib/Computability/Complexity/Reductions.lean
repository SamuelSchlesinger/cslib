/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Complexity.Classes

@[expose] public section

/-!
# Polynomial-Time Reductions and NP-Completeness

This file defines polynomial-time many-one reductions between languages,
and uses them to define NP-hardness and NP-completeness.

## Main Definitions

* `PolyTimeReduces L₁ L₂` — `L₁` poly-time reduces to `L₂`
* `NPHard L` — every NP language poly-time reduces to `L`
* `NPComplete L` — `L` is NP-hard and in NP

## Main Results

* `PolyTimeReduces.refl` — reflexivity
* `PolyTimeReduces.trans` — transitivity
* `PolyTimeReduces.mem_ComplexityP` — downward closure under P
* `NPComplete.p_eq_np` — if any NP-complete language is in P then P = NP

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

open Turing SingleTapeTM Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
A language `L₁` **polynomial-time reduces** to `L₂` if there exists a
polynomial-time computable function `f` such that
for all `x`, `x ∈ L₁ ↔ f x ∈ L₂`.

This is also called a **many-one** or **Karp** reduction.
-/
def PolyTimeReduces (L₁ L₂ : Set (List Symbol)) : Prop :=
  ∃ f, Nonempty (PolyTimeComputable f) ∧ ∀ x, x ∈ L₁ ↔ f x ∈ L₂

/--
A language `L` is **NP-hard** if every language in NP polynomial-time
reduces to `L`.
-/
def NPHard (L : Set (List Symbol)) : Prop :=
  ∀ L' ∈ ComplexityNP (Symbol := Symbol), PolyTimeReduces L' L

/--
A language `L` is **NP-complete** if it is NP-hard and in NP.
-/
def NPComplete (L : Set (List Symbol)) : Prop :=
  NPHard L ∧ L ∈ ComplexityNP

end

open Turing SingleTapeTM Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

set_option linter.unusedFintypeInType false in
/-- `≤ₚ` is reflexive: every language reduces to itself via the identity. -/
theorem PolyTimeReduces.refl
    (L : Set (List Symbol)) : PolyTimeReduces L L :=
  ⟨id, ⟨PolyTimeComputable.id⟩, fun _ => Iff.rfl⟩

set_option linter.unusedFintypeInType false in
/-- `≤ₚ` is transitive: if `L₁ ≤ₚ L₂` and `L₂ ≤ₚ L₃` then `L₁ ≤ₚ L₃`. -/
theorem PolyTimeReduces.trans
    {L₁ L₂ L₃ : Set (List Symbol)}
    (h₁₂ : PolyTimeReduces L₁ L₂)
    (h₂₃ : PolyTimeReduces L₂ L₃) :
    PolyTimeReduces L₁ L₃ := by
  obtain ⟨f, ⟨hf⟩, hf_mem⟩ := h₁₂
  obtain ⟨g, ⟨hg⟩, hg_mem⟩ := h₂₃
  exact ⟨g ∘ f, ⟨hf.comp hg⟩,
    fun x => (hf_mem x).trans (hg_mem (f x))⟩

set_option linter.unusedFintypeInType false in
/-- If `L₁ ≤ₚ L₂` and `L₂ ∈ P` then `L₁ ∈ P`. -/
theorem PolyTimeReduces.mem_ComplexityP
    {L₁ L₂ : Set (List Symbol)}
    (hred : PolyTimeReduces L₁ L₂)
    (hL₂ : L₂ ∈ ComplexityP (Symbol := Symbol)) :
    L₁ ∈ ComplexityP := by
  obtain ⟨f, ⟨hf⟩, hf_mem⟩ := hred
  obtain ⟨g, ⟨hg⟩, hg_dec⟩ := hL₂
  refine ⟨g ∘ f, ⟨hf.comp hg⟩, fun x => ?_⟩
  simp only [Function.comp]
  exact (hf_mem x).trans (hg_dec (f x))

set_option linter.unusedFintypeInType false in
/-- If any NP-complete language is in P, then P = NP.

This is the fundamental theorem connecting NP-completeness to the
P vs NP question. -/
theorem NPComplete.p_eq_np
    {L : Set (List Symbol)}
    (hL : NPComplete L)
    (hP : L ∈ ComplexityP (Symbol := Symbol)) :
    ComplexityP (Symbol := Symbol) = ComplexityNP := by
  apply Set.eq_of_subset_of_subset
  · exact ComplexityP_subset_ComplexityNP
  · intro L' hL'
    exact (hL.1 L' hL').mem_ComplexityP hP
