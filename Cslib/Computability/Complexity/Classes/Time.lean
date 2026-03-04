/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Complexity.Classes.Core

@[expose] public section

/-!
# Time Complexity Classes

This file defines the fundamental time complexity classes **P**, **NP**, and **coNP**
using single-tape Turing machines, and states the **P ≠ NP** conjecture.

## Main Definitions

* `ComplexityP` — the class **P** of languages decidable in polynomial time
* `ComplexityNP` — the class **NP** of languages verifiable in polynomial time
* `ComplexityCoNP` — the class **coNP**, complements of **NP** languages
* `PNeNP` — the proposition **P ≠ NP**

## Main Results

* `ComplexityP_subset_ComplexityNP` — **P ⊆ NP**
-/

open Turing SingleTapeTM

variable {Symbol : Type}

/--
**P** is the class of languages decidable by a polynomial-time Turing machine.

We use `Nonempty (PolyTimeComputable f)` because `PolyTimeComputable` is a structure
(carrying computational data), while set membership requires a `Prop`.
-/
def ComplexityP : Set (Set (List Symbol)) :=
  { L | ∃ f, Nonempty (PolyTimeComputable f) ∧ Decides f L }

/--
**NP** is the class of languages for which membership can be verified
in polynomial time given a polynomial-length witness (certificate).
-/
def ComplexityNP : Set (Set (List Symbol)) :=
  { L | ∃ verify p, Nonempty (PolyTimeComputable verify) ∧ Verifies verify L p }

/--
**coNP** is the class of languages whose complements are in **NP**.
-/
def ComplexityCoNP : Set (Set (List Symbol)) :=
  { L | Lᶜ ∈ ComplexityNP }

/--
The **P ≠ NP** conjecture states that the complexity classes P and NP are distinct.
This is stated as a `Prop` definition rather than an axiom.
-/
def PNeNP : Prop := ComplexityP (Symbol := Symbol) ≠ ComplexityNP

end

/--
**P ⊆ NP**: Every language decidable in polynomial time is also verifiable
in polynomial time.

*Proof sketch*: Given a polytime decider `f` for `L`, use `f` as a verifier
that ignores the witness. The witness is taken to be empty (`[]`),
and the polynomial witness bound is `0`.
-/
public theorem ComplexityP_subset_ComplexityNP
    {Symbol : Type} :
    ComplexityP (Symbol := Symbol) ⊆ ComplexityNP := by
  intro L ⟨f, hf, hDecides⟩
  refine ⟨f, 0, hf, fun x => ?_⟩
  simp only [Polynomial.eval_zero]
  constructor
  · intro hx
    exact ⟨[], Nat.le_refl 0, by rwa [List.append_nil, ← hDecides]⟩
  · rintro ⟨w, hw, hverify⟩
    rw [hDecides]
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
    rwa [this, List.append_nil] at hverify

/-- **NP ⊆ coNP ↔ ∀ L ∈ NP, Lᶜ ∈ NP**. This is just the unfolding of
the definitions: coNP is defined as `{L | Lᶜ ∈ NP}`, so `NP ⊆ coNP`
means every NP language has its complement in NP. -/
public theorem ComplexityNP_subset_ComplexityCoNP_iff
    {Symbol : Type} :
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
