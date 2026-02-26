/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.SingleTapeTuring.Basic

@[expose] public section

/-!
# Complexity Classes

This file defines the fundamental complexity classes **P**, **NP**, and **coNP**
using single-tape Turing machines, and states the **P ≠ NP** conjecture.

## Main Definitions

* `Decides f L` — `f` decides language `L` (non-empty output means accept)
* `Verifies verify L p` — `verify` verifies language `L` with polynomial witness bound `p`
* `ComplexityP` — the class **P** of languages decidable in polynomial time
* `ComplexityNP` — the class **NP** of languages verifiable in polynomial time
* `ComplexityCoNP` — the class **coNP**, complements of **NP** languages
* `PNeNP` — the proposition **P ≠ NP**

## Main Results

* `ComplexityP_subset_ComplexityNP` — **P ⊆ NP**
-/

open Turing SingleTapeTM Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
A function `f : List Symbol → List Symbol` **decides** a language `L` when
membership in `L` corresponds to `f` producing non-empty output.
-/
def Decides (f : List Symbol → List Symbol) (L : Set (List Symbol)) : Prop :=
  ∀ x, x ∈ L ↔ f x ≠ []

/--
A verifier `verify` **verifies** a language `L` with polynomial witness bound `p` when
membership in `L` is equivalent to the existence of a short witness `w` such that
`verify (x ++ w)` produces non-empty output.
-/
def Verifies (verify : List Symbol → List Symbol) (L : Set (List Symbol))
    (p : Polynomial ℕ) : Prop :=
  ∀ x, x ∈ L ↔ ∃ w : List Symbol, w.length ≤ p.eval x.length ∧ verify (x ++ w) ≠ []

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
theorem ComplexityP_subset_ComplexityNP {Symbol : Type} :
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
