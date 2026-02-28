/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.Negligible

@[expose] public section

/-!
# Security Games

This file provides the abstract framework for **game-based security
definitions**, the dominant paradigm in modern cryptography.

A security game formalizes the interaction between a **challenger** (the
cryptographic scheme) and an **adversary** (the attacker). The adversary's
goal is to win the game; the scheme is secure if every efficient adversary
wins with probability negligibly close to some baseline (often 1/2).

## Main Definitions

* `SecurityGame` — an abstract security game parameterized by adversary type
* `Secure` — a scheme is secure if every adversary has negligible advantage
* `SecurityReduction` — a reduction from one game to another

## Design Notes

We parametrize games by an abstract adversary type `Adv` and define
the advantage function `ℕ → ℝ` mapping security parameter to winning
probability minus baseline. This allows both:
- **Decision games** (e.g., IND-CPA): adversary tries to distinguish,
  baseline is 1/2
- **Search games** (e.g., OWF inversion): adversary tries to find a
  value, baseline is 0

## References

* [M. Bellare, P. Rogaway, *The Security of Triple Encryption and a
  Framework for Code-Based Game-Playing Proofs*][BellareR2006]
* [V. Shoup, *Sequences of Games: A Tool for Taming Complexity in
  Security Proofs*][Shoup2004]
-/

/-- A **security game** captures the interaction between a cryptographic
scheme and an adversary. The game is parameterized by:
- `Adv` — the type of adversaries
- `advantage` — maps (adversary, security parameter) to the adversary's advantage,
  i.e., `|Pr[adversary wins] - baseline|` -/
structure SecurityGame (Adv : Type*) where
  /-- The advantage of adversary `A` at security parameter `n`. -/
  advantage : Adv → ℕ → ℝ

/-- A security game is **secure** if every adversary has negligible
advantage.

This captures the standard cryptographic notion: no efficient adversary
can win the game with non-negligible probability beyond the baseline. -/
def SecurityGame.Secure (G : SecurityGame Adv) : Prop :=
  ∀ A : Adv, Negligible (G.advantage A)

/-- A **security reduction** from game `G₁` to game `G₂` is a
transformation of adversaries such that any adversary against `G₁`
can be turned into an adversary against `G₂` with comparable advantage.

Specifically, `R A` is the reduction of adversary `A`, and the advantage
of `A` against `G₁` is bounded by a polynomial factor times the
advantage of `R A` against `G₂`. -/
structure SecurityReduction (G₁ : SecurityGame Adv₁)
    (G₂ : SecurityGame Adv₂) where
  /-- The reduction maps adversaries for `G₁` to adversaries for `G₂`. -/
  reduce : Adv₁ → Adv₂
  /-- The advantage of `A` against `G₁` is bounded by the advantage
  of `reduce A` against `G₂` plus a negligible term. -/
  advantage_bound : ∀ A,
    Negligible (fun n => G₁.advantage A n - G₂.advantage (reduce A) n)

end

/-! ### Security reductions transfer security -/

/-- If there is a security reduction from `G₁` to `G₂` and `G₂` is
secure, then `G₁` is secure.

This is the fundamental theorem of game-based cryptography: security
of the target game transfers through the reduction. -/
theorem SecurityReduction.secure_transfer
    {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    (R : SecurityReduction G₁ G₂)
    (h : G₂.Secure) :
    G₁.Secure := by
  intro A
  have hbound := R.advantage_bound A
  have hG₂ := h (R.reduce A)
  -- G₁.advantage A n
  --   = (G₁.adv - G₂.adv) + G₂.adv; both terms are negligible
  have : Negligible (fun n =>
      (G₁.advantage A n - G₂.advantage (R.reduce A) n) +
      G₂.advantage (R.reduce A) n) :=
    Negligible.add hbound hG₂
  intro c hc
  obtain ⟨N, hN⟩ := this c hc
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  simp only [sub_add_cancel] at this
  exact this

/-! ### Game composition -/

/-- The **trivial game** where every adversary has zero advantage. -/
def SecurityGame.trivial : SecurityGame Adv where
  advantage _ _ := 0

/-- The trivial game is secure. -/
theorem SecurityGame.trivial_secure : (SecurityGame.trivial : SecurityGame Adv).Secure := by
  intro A
  exact Negligible.zero
