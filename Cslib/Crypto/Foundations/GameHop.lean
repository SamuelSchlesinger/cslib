/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Foundations.SecurityGame

@[expose] public section

/-!
# Game Hops

This file provides a small DSL for **sequence-of-games** security proofs,
the standard technique (Shoup) for structuring reductions as a chain of
hops between increasingly idealized games, with each hop contributing
a bounded advantage difference ("gap").

## Main Definitions

* `GameHop G₁ G₂` — a one-sided hop `adv_{G₁}(A, n) ≤ adv_{G₂}(R A, n) + gap A n`.
* `GameHop.refl`, `GameHop.trans`, `GameHop.of_sub_le` — combinators.
* `GameHop.secureAgainst_transfer` — security of `G₂` + negligible gap ⟹ security of `G₁`.
* `GameHop.secure_transfer` — the unconditional (`Secure`) variant.

## Why a new structure next to `SecurityReduction`?

`SecurityReduction G₁ G₂` already captures a hop with a *negligible*
advantage difference — the two-sided, zero-additional-assumption case.
But the standard shape that reductions actually prove is

  `adv_{G₁}(A, n) ≤ adv_{G₂}(R A, n) + gap(A, n)`,

where `gap` is non-trivial and is only shown negligible under separate
information-theoretic hypotheses (e.g. "ideal-world gap"). `GameHop`
makes this shape first-class and transitive, so each reduction can
export a single hop and its `_secure` theorem becomes one line.

`SecurityReduction` is the special case `gap = 0`; the other direction,
where any `SecurityReduction` gives a `GameHop`, is provided as
`SecurityReduction.toGameHop`.

## References

* [V. Shoup, *Sequences of Games: A Tool for Taming Complexity in
  Security Proofs*][Shoup2004]
* [M. Bellare, P. Rogaway, *The Security of Triple Encryption and a
  Framework for Code-Based Game-Playing Proofs*][BellareR2006]
-/

universe u v w

/-- A **game hop** from `G₁` to `G₂` with explicit additive gap.

For every `G₁`-adversary `A`, the `G₁`-advantage of `A` is bounded by
the `G₂`-advantage of the transformed adversary `reduce A` plus an
additive correction `gap A n`:

  `G₁.advantage A n ≤ G₂.advantage (reduce A) n + gap A n`.

When `gap A` is negligible and `G₂` is secure against the class into
which `reduce` maps, `G₁` is secure too (see
`GameHop.secureAgainst_transfer`). -/
structure GameHop {Adv₁ : Type u} {Adv₂ : Type v}
    (G₁ : SecurityGame Adv₁) (G₂ : SecurityGame Adv₂) where
  /-- The reduction turning a `G₁`-adversary into a `G₂`-adversary. -/
  reduce : Adv₁ → Adv₂
  /-- The additive gap between the two advantages. -/
  gap : Adv₁ → ℕ → ℝ
  /-- The core one-sided bound. -/
  advantage_le : ∀ A n,
    G₁.advantage A n ≤ G₂.advantage (reduce A) n + gap A n

namespace GameHop

variable {Adv₁ : Type u} {Adv₂ : Type v} {Adv₃ : Type w}

/-- The identity hop: no reduction, zero gap. -/
@[simps]
def refl (G : SecurityGame Adv₁) : GameHop G G where
  reduce := id
  gap _ _ := 0
  advantage_le _ _ := by simp

/-- **Transitivity / sequence-of-games composition.**

Hops compose: given `G₁ ⟹ G₂` (with gap `δ₁`) and `G₂ ⟹ G₃` (with gap
`δ₂`), we get `G₁ ⟹ G₃` whose gap at `A` is `δ₁ A + δ₂ (reduce₁ A)`
and whose reduction is `reduce₂ ∘ reduce₁`.

Chaining is the central operation of a sequence-of-games proof. -/
def trans {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    {G₃ : SecurityGame Adv₃}
    (h₁ : GameHop G₁ G₂) (h₂ : GameHop G₂ G₃) : GameHop G₁ G₃ where
  reduce A := h₂.reduce (h₁.reduce A)
  gap A n := h₁.gap A n + h₂.gap (h₁.reduce A) n
  advantage_le A n := by
    have hA := h₁.advantage_le A n
    have hB := h₂.advantage_le (h₁.reduce A) n
    linarith

/-- Build a hop from the **two-sided triangle-inequality** form

  `|G₁.advantage A n - G₂.advantage (R A) n| ≤ δ A n`.

This is the shape reductions actually prove (via triangle inequality
over some shared ideal-world expectation), and it yields a `GameHop`
with the same gap. -/
def of_abs_le {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    (reduce : Adv₁ → Adv₂) (gap : Adv₁ → ℕ → ℝ)
    (h : ∀ A n,
      |G₁.advantage A n - G₂.advantage (reduce A) n| ≤ gap A n) :
    GameHop G₁ G₂ where
  reduce := reduce
  gap := gap
  advantage_le A n := by
    have := h A n
    have := abs_le.mp this
    linarith [this.2]

/-- Weaken a hop along a pointwise bound on the gap. -/
def mono {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    (H : GameHop G₁ G₂)
    (δ : Adv₁ → ℕ → ℝ)
    (h : ∀ A n, H.gap A n ≤ δ A n) :
    GameHop G₁ G₂ where
  reduce := H.reduce
  gap := δ
  advantage_le A n := by
    have := H.advantage_le A n
    have := h A n
    linarith

/-! ### Security transfer -/

/-- Internal: from `adv₁ ≤ adv₂ + gap` together with
`adv₁ ≥ 0`, `adv₂ ≥ 0`, and `gap ≥ 0`, conclude

  `|adv₁| ≤ |adv₂ + gap|`

so that `Negligible.mono` over `adv₂ + gap` transfers to `adv₁`. -/
private theorem abs_advantage_le_abs_sum
    {a b g : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hbound : a ≤ b + g) : |a| ≤ |b + g| := by
  rw [abs_of_nonneg ha, abs_of_nonneg (by linarith)]
  exact hbound

/-- **Per-adversary transfer.**

If `H : GameHop G₁ G₂` and we know
* the `G₂`-advantage of `H.reduce A` is negligible,
* the gap at `A` is negligible,
* all three quantities are pointwise non-negative,

then the `G₁`-advantage of `A` is negligible.

This is the workhorse: it encapsulates the "`|Adv₁| ≤ |Adv₂ + gap|`
followed by `Negligible.mono (Negligible.add …)`" boilerplate that
every linear-hop reduction repeats. -/
theorem advantage_negligible
    {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    (H : GameHop G₁ G₂) (A : Adv₁)
    (hG₂ : Negligible (fun n => G₂.advantage (H.reduce A) n))
    (hGap : Negligible (H.gap A))
    (hG₁_nn : ∀ n, 0 ≤ G₁.advantage A n)
    (hG₂_nn : ∀ n, 0 ≤ G₂.advantage (H.reduce A) n)
    (hGap_nn : ∀ n, 0 ≤ H.gap A n) :
    Negligible (fun n => G₁.advantage A n) := by
  apply Negligible.mono (Negligible.add hG₂ hGap)
  refine ⟨0, fun n _ => ?_⟩
  exact abs_advantage_le_abs_sum
    (hG₁_nn n) (hG₂_nn n) (hGap_nn n) (H.advantage_le A n)

/-- **Main transfer theorem (admissibility-relative form).**

Security of `G₂` against `P₂` + gap negligibility + admissibility
preservation ⟹ security of `G₁` against `P₁`. -/
theorem secureAgainst_transfer
    {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    (H : GameHop G₁ G₂)
    {P₁ : Adv₁ → Prop} {P₂ : Adv₂ → Prop}
    (hAdm : ∀ A, P₁ A → P₂ (H.reduce A))
    (hGap : ∀ A, P₁ A → Negligible (H.gap A))
    (hG₁_nn : ∀ A n, 0 ≤ G₁.advantage A n)
    (hG₂_nn : ∀ A n, 0 ≤ G₂.advantage A n)
    (hGap_nn : ∀ A n, 0 ≤ H.gap A n)
    (hG₂ : G₂.SecureAgainst P₂) :
    G₁.SecureAgainst P₁ :=
  fun A hA =>
    H.advantage_negligible A (hG₂ _ (hAdm A hA)) (hGap A hA)
      (hG₁_nn A) (hG₂_nn _) (hGap_nn A)

/-- **Main transfer theorem (unconditional form).** -/
theorem secure_transfer
    {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    (H : GameHop G₁ G₂)
    (hGap : ∀ A, Negligible (H.gap A))
    (hG₁_nn : ∀ A n, 0 ≤ G₁.advantage A n)
    (hG₂_nn : ∀ A n, 0 ≤ G₂.advantage A n)
    (hGap_nn : ∀ A n, 0 ≤ H.gap A n)
    (hG₂ : G₂.Secure) :
    G₁.Secure :=
  fun A =>
    H.advantage_negligible A (hG₂ _) (hGap A)
      (hG₁_nn A) (hG₂_nn _) (hGap_nn A)

end GameHop

/-! ### Forking (nonlinear) game hops -/

/-- A **forking-style game hop** bounds the `G₁`-advantage of `A` by

  `√(q(A, n) · adv_{G₂}(reduce A, n) + extra₁(A, n)) + extra₂(A, n)`.

This is the nonlinear shape produced by rewinding / Jensen's-inequality
reductions (the forking lemma, Fiat-Shamir in the ROM, BLS aggregation,
...). The `queries` factor is a polynomial-size rewind count, and the
two `extra` terms collect sub-negligible "slack" coming from
challenge-space collisions and commitment un­predictability.

The transfer theorem `ForkingHop.advantage_negligible` discharges, in
one call, the chain
  `Negl · PolyBounded ⟹ Negl`, `Negl + Negl ⟹ Negl`, `√ Negl ⟹ Negl`
that every such reduction has to write out by hand.

Unlike `GameHop`, forking hops do not currently compose with themselves
(two rewinds in sequence would give a quadratic blow-up); in practice
a forking step is the bottom of a chain, and additional linear hops
before it can be folded into `G₁.advantage` using `GameHop.advantage_le`
and `le_trans`. -/
structure ForkingHop {Adv₁ : Type u} {Adv₂ : Type v}
    (G₁ : SecurityGame Adv₁) (G₂ : SecurityGame Adv₂) where
  /-- The reduction producing a `G₂`-adversary from a `G₁`-adversary. -/
  reduce : Adv₁ → Adv₂
  /-- Polynomially-bounded rewind / query count. -/
  queries : Adv₁ → ℕ → ℝ
  /-- Additive slack under the square root (e.g., `q / |Challenge|`). -/
  extra₁ : Adv₁ → ℕ → ℝ
  /-- Additive slack outside the square root (e.g., `q² · δ`). -/
  extra₂ : Adv₁ → ℕ → ℝ
  /-- The core nonlinear bound. -/
  advantage_le : ∀ A n,
    G₁.advantage A n ≤
      Real.sqrt (queries A n * G₂.advantage (reduce A) n + extra₁ A n) +
      extra₂ A n

namespace ForkingHop

variable {Adv₁ : Type u} {Adv₂ : Type v}

/-- **Per-adversary transfer for forking hops.**

Given `H : ForkingHop G₁ G₂`, if for a specific adversary `A`
* the `G₂`-advantage of `reduce A` is negligible,
* the `queries` factor is polynomially bounded,
* `extra₁` and `extra₂` are negligible,
* all three of `queries`, `extra₁`, and the `G₂`-advantage of `reduce A`
  are pointwise non-negative, as is the `G₁`-advantage of `A`,

then the `G₁`-advantage of `A` is negligible.

This is exactly the Fiat-Shamir / forking-lemma boilerplate:
`q · adv` is `Negl · PolyBd`; adding `extra₁` stays negligible;
`√` preserves negligibility (for non-negatives); adding `extra₂`
stays negligible; `abs_of_nonneg` closes. -/
theorem advantage_negligible
    {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    (H : ForkingHop G₁ G₂) (A : Adv₁)
    (hG₂ : Negligible (fun n => G₂.advantage (H.reduce A) n))
    (hQ : PolynomiallyBounded (H.queries A))
    (hExtra₁ : Negligible (H.extra₁ A))
    (hExtra₂ : Negligible (H.extra₂ A))
    (hG₁_nn : ∀ n, 0 ≤ G₁.advantage A n)
    (hG₂_nn : ∀ n, 0 ≤ G₂.advantage (H.reduce A) n)
    (hQ_nn : ∀ n, 0 ≤ H.queries A n)
    (hExtra₁_nn : ∀ n, 0 ≤ H.extra₁ A n) :
    Negligible (fun n => G₁.advantage A n) := by
  have h_qAdv : Negligible (fun n =>
      H.queries A n * G₂.advantage (H.reduce A) n) :=
    hG₂.polyBounded_mul hQ
  have h_sum_nn : ∀ n, 0 ≤
      H.queries A n * G₂.advantage (H.reduce A) n + H.extra₁ A n :=
    fun n => add_nonneg (mul_nonneg (hQ_nn n) (hG₂_nn n)) (hExtra₁_nn n)
  have h_sqrt := (h_qAdv.add hExtra₁).sqrt_nonneg h_sum_nn
  have h_bound := h_sqrt.add hExtra₂
  exact h_bound.mono ⟨0, fun n _ => by
    rw [abs_of_nonneg (hG₁_nn n)]
    exact le_trans (H.advantage_le A n) (le_abs_self _)⟩

end ForkingHop

/-! ### Bridge to `SecurityReduction` -/

namespace SecurityReduction

variable {Adv₁ : Type u} {Adv₂ : Type v}

/-- Every `SecurityReduction` is a `GameHop` whose gap is
`G₁.advantage A n - G₂.advantage (reduce A) n` (itself negligible).

This exhibits `SecurityReduction` as the zero-extra-assumption case of
`GameHop` and lets reductions proven in the old style participate in
sequence-of-games chains. -/
def toGameHop
    {G₁ : SecurityGame Adv₁} {G₂ : SecurityGame Adv₂}
    (R : SecurityReduction G₁ G₂) : GameHop G₁ G₂ where
  reduce := R.reduce
  gap A n := G₁.advantage A n - G₂.advantage (R.reduce A) n
  advantage_le _ _ := by ring_nf; rfl

end SecurityReduction

end
