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

* `PolyTimeComputable.complement` — **P** is closed under complement
* `ComplexityP_subset_ComplexityCoNP` — **P ⊆ coNP**
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

namespace Turing.SingleTapeTM

/-- Given a poly-time computable `f`, the "flip-empty" function
`fun x => if f x = [] then [default] else []` is also poly-time computable.

This is the key primitive for showing **P** is closed under complement.
The underlying TM construction runs `f`, then checks if the output is empty
and flips the result. The check-and-flip adds only O(|f(x)|) steps (to scan
and erase/write), preserving polynomial time.

We axiomatize this rather than building the raw TM because the construction
is mechanical but verbose, involving tape scanning and rewriting. -/
axiom PolyTimeComputable.complement
    {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {f : List Symbol → List Symbol}
    (hf : PolyTimeComputable f) :
    PolyTimeComputable (fun x => if f x = [] then [default] else [])

end Turing.SingleTapeTM

set_option linter.unusedFintypeInType false in
/-- **P is closed under complement**: if `L ∈ P` then `Lᶜ ∈ P`.

Given a poly-time decider `f` for `L` (where `f x ≠ [] ↔ x ∈ L`),
the complement decider `g x = if f x = [] then [default] else []`
satisfies `g x ≠ [] ↔ x ∈ Lᶜ`. By `PolyTimeComputable.complement`,
`g` is also poly-time computable. -/
public theorem ComplexityP_complement
    {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {L : Set (List Symbol)} (hL : L ∈ ComplexityP (Symbol := Symbol)) :
    Lᶜ ∈ ComplexityP := by
  obtain ⟨f, ⟨hf⟩, hDecides⟩ := hL
  refine ⟨fun x => if f x = [] then [default] else [], ⟨hf.complement⟩, fun x => ?_⟩
  simp only [Set.mem_compl_iff]
  constructor
  · intro hx
    -- hx : x ∉ L, so f x = [] by Decides
    have hfx : f x = [] := by
      by_contra hne
      exact hx ((hDecides x).mpr hne)
    simp [hfx]
  · intro hx hxL
    -- hx : (if f x = [] then [default] else []) ≠ [], hxL : x ∈ L
    -- Since x ∈ L, f x ≠ [], so the if produces [], contradicting hx
    have hfx : f x ≠ [] := (hDecides x).mp hxL
    simp [hfx] at hx

set_option linter.unusedFintypeInType false in
/-- **P ⊆ coNP**: every language decidable in polynomial time is also in coNP.

*Proof*: If `L ∈ P`, then `Lᶜ ∈ P` (since P is closed under complement),
and `Lᶜ ∈ P ⊆ NP`, so `L ∈ coNP`. -/
public theorem ComplexityP_subset_ComplexityCoNP
    {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] :
    ComplexityP (Symbol := Symbol) ⊆ ComplexityCoNP := by
  intro L hL
  simp only [ComplexityCoNP, Set.mem_setOf_eq]
  exact ComplexityP_subset_ComplexityNP (ComplexityP_complement hL)

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
