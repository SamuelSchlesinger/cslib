/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI Codex
-/

module

public import Cslib.Foundations.Probability.Locality
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Data.ENNReal.Real
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Tactic

@[expose] public section

namespace Cslib
namespace Probability

open scoped BigOperators

universe u

/-- Finite Shannon entropy (in nats) of a PMF, represented with `Real.negMulLog`. -/
noncomputable def shannonEntropy {α : Type u} [Fintype α] (p : PMF α) : ℝ :=
  ∑ a, Real.negMulLog (ENNReal.toReal (p a))

theorem shannonEntropy_nonneg {α : Type u} [Fintype α] (p : PMF α) :
    0 ≤ shannonEntropy p := by
  unfold shannonEntropy
  refine Finset.sum_nonneg ?_
  intro a _
  refine Real.negMulLog_nonneg ENNReal.toReal_nonneg ?_
  have hpa : p a ≤ 1 := p.coe_le_one a
  have htoReal : ENNReal.toReal (p a) ≤ ENNReal.toReal (1 : ENNReal) :=
    ENNReal.toReal_mono ENNReal.one_ne_top hpa
  simpa using htoReal

lemma negMulLog_le_one_sub (x : ℝ) (hx : 0 ≤ x) : Real.negMulLog x ≤ 1 - x := by
  have hkl : 0 ≤ InformationTheory.klFun x := InformationTheory.klFun_nonneg hx
  have hkl' : 0 ≤ -Real.negMulLog x + 1 - x := by
    simpa [InformationTheory.klFun, Real.negMulLog_def, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hkl
  linarith

lemma sum_toReal_eq_one_of_support_subset
    {α : Type*}
    (p : PMF α) (s : Finset α)
    (hsub : p.support ⊆ (s : Set α)) :
    Finset.sum s (fun a => ENNReal.toReal (p a)) = 1 := by
  have hsum_s_enn : Finset.sum s (fun a => p a) = (1 : ENNReal) := by
    calc
      Finset.sum s (fun a => p a) = ∑' a, p a := by
        symm
        refine tsum_eq_sum ?_
        intro a ha_not_s
        exact (p.apply_eq_zero_iff a).2 (by
          intro ha_support
          exact ha_not_s (hsub ha_support))
      _ = 1 := p.tsum_coe
  have hsum_s_real : (Finset.sum s (fun a => p a)).toReal =
      Finset.sum s (fun a => ENNReal.toReal (p a)) := by
    simpa using (ENNReal.toReal_sum (s := s) (f := fun a => p a) (fun a ha => p.apply_ne_top a))
  have hreal : (1 : ENNReal).toReal = Finset.sum s (fun a => ENNReal.toReal (p a)) := by
    simpa [hsum_s_enn] using hsum_s_real
  simpa using hreal.symm

lemma shannonEntropy_eq_sum_on_finset_of_support_subset
    {α : Type*} [Fintype α]
    (p : PMF α) (s : Finset α)
    (hsub : p.support ⊆ (s : Set α)) :
    shannonEntropy p = Finset.sum s (fun a => Real.negMulLog (ENNReal.toReal (p a))) := by
  unfold shannonEntropy
  have hsum_eq :
      Finset.sum s (fun a => Real.negMulLog (ENNReal.toReal (p a))) =
      Finset.sum (Finset.univ : Finset α) (fun a => Real.negMulLog (ENNReal.toReal (p a))) := by
    refine Finset.sum_subset (by intro a ha; simp) ?_
    intro a ha_univ ha_not_s
    have hnot_support : a ∉ p.support := by
      intro ha_support
      exact ha_not_s (hsub ha_support)
    have hpzero : p a = 0 := (p.apply_eq_zero_iff a).2 hnot_support
    simp [hpzero]
  exact hsum_eq.symm

theorem shannonEntropy_le_log_card_of_support_subset
    {α : Type*} [Fintype α]
    (p : PMF α) (s : Finset α) (hs : s.Nonempty)
    (hsub : p.support ⊆ (s : Set α)) :
    shannonEntropy p ≤ Real.log (s.card : ℝ) := by
  let m : ℝ := (s.card : ℝ)
  have hm_nat_pos : 0 < s.card := Finset.card_pos.mpr hs
  have hm_pos_card : 0 < (s.card : ℝ) := by
    exact_mod_cast hm_nat_pos
  have hm_pos : 0 < m := by simpa [m] using hm_pos_card
  have hm_nonneg : 0 ≤ m := le_of_lt hm_pos
  let pa : α → ℝ := fun a => ENNReal.toReal (p a)
  have hpa_nonneg : ∀ a, 0 ≤ pa a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hsum_pa : Finset.sum s pa = 1 := by
    simpa [pa] using sum_toReal_eq_one_of_support_subset p s hsub
  have hpoint : ∀ a ∈ s, Real.negMulLog (m * pa a) ≤ 1 - m * pa a := by
    intro a ha
    exact negMulLog_le_one_sub (m * pa a) (mul_nonneg hm_nonneg (hpa_nonneg a))
  have hsum_ineq : Finset.sum s (fun a => Real.negMulLog (m * pa a))
      ≤ Finset.sum s (fun a => (1 - m * pa a)) := by
    exact Finset.sum_le_sum hpoint
  have hsum_right : Finset.sum s (fun a => (1 - m * pa a)) = 0 := by
    calc
      Finset.sum s (fun a => (1 - m * pa a))
          = Finset.sum s (fun _ => (1 : ℝ)) - Finset.sum s (fun a => m * pa a) := by
              simp [Finset.sum_sub_distrib]
      _ = (s.card : ℝ) - m * Finset.sum s pa := by
            rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
            simp
      _ = (s.card : ℝ) - m := by rw [hsum_pa, mul_one]
      _ = 0 := by simp [m]
  have hsum_left : Finset.sum s (fun a => Real.negMulLog (m * pa a))
      = m * Finset.sum s (fun a => Real.negMulLog (pa a))
        + Real.negMulLog m * Finset.sum s pa := by
    calc
      Finset.sum s (fun a => Real.negMulLog (m * pa a))
          = Finset.sum s (fun a => (pa a * Real.negMulLog m + m * Real.negMulLog (pa a))) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.negMulLog_mul m (pa a))
      _ = Finset.sum s (fun a => pa a * Real.negMulLog m)
          + Finset.sum s (fun a => m * Real.negMulLog (pa a)) := by
              exact Finset.sum_add_distrib
      _ = (Finset.sum s pa) * Real.negMulLog m
          + m * Finset.sum s (fun a => Real.negMulLog (pa a)) := by
              rw [Finset.sum_mul, Finset.mul_sum]
      _ = m * Finset.sum s (fun a => Real.negMulLog (pa a))
          + Real.negMulLog m * Finset.sum s pa := by ring
  have hmain : m * Finset.sum s (fun a => Real.negMulLog (pa a))
      + Real.negMulLog m * Finset.sum s pa ≤ 0 := by
    calc
      m * Finset.sum s (fun a => Real.negMulLog (pa a)) + Real.negMulLog m * Finset.sum s pa
          = Finset.sum s (fun a => Real.negMulLog (m * pa a)) := by
              simp [hsum_left]
      _ ≤ Finset.sum s (fun a => (1 - m * pa a)) := hsum_ineq
      _ = 0 := hsum_right
  have hmain' : m * Finset.sum s (fun a => Real.negMulLog (pa a)) + Real.negMulLog m ≤ 0 := by
    simpa [hsum_pa] using hmain
  have hmain'' : m * (Finset.sum s (fun a => Real.negMulLog (pa a)) - Real.log m) ≤ 0 := by
    have : m * Finset.sum s (fun a => Real.negMulLog (pa a)) - m * Real.log m ≤ 0 := by
      simpa [Real.negMulLog_def, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using hmain'
    simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using this
  have hbound_sum : Finset.sum s (fun a => Real.negMulLog (pa a)) ≤ Real.log m := by
    have hsub : Finset.sum s (fun a => Real.negMulLog (pa a)) - Real.log m ≤ 0 := by
      by_contra hnot
      have hgt : 0 < Finset.sum s (fun a => Real.negMulLog (pa a)) - Real.log m :=
        lt_of_not_ge hnot
      have hmul_pos : 0 < m * (Finset.sum s (fun a => Real.negMulLog (pa a)) - Real.log m) :=
        mul_pos hm_pos hgt
      exact not_lt_of_ge hmain'' hmul_pos
    exact sub_nonpos.mp hsub
  have hentropy_s : shannonEntropy p = Finset.sum s (fun a => Real.negMulLog (pa a)) := by
    simpa [pa] using shannonEntropy_eq_sum_on_finset_of_support_subset p s hsub
  calc
    shannonEntropy p = Finset.sum s (fun a => Real.negMulLog (pa a)) := hentropy_s
    _ ≤ Real.log m := hbound_sum
    _ = Real.log (s.card : ℝ) := by simp [m]

theorem shannonEntropy_uniformOn
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) :
    shannonEntropy (uniformOn s hs) = Real.log (s.card : ℝ) := by
  have hsub : (uniformOn s hs).support ⊆ (s : Set α) := by
    simp [support_uniformOn s hs]
  calc
    shannonEntropy (uniformOn s hs)
        = Finset.sum s
            (fun a => Real.negMulLog (ENNReal.toReal ((uniformOn s hs) a))) :=
          shannonEntropy_eq_sum_on_finset_of_support_subset (uniformOn s hs) s hsub
    _ = Finset.sum s (fun _ => Real.negMulLog (ENNReal.toReal ((s.card : ENNReal)⁻¹))) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp [uniformOn_apply_of_mem hs ha]
    _ = (s.card : ℝ) * Real.negMulLog (ENNReal.toReal ((s.card : ENNReal)⁻¹)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ℝ) * ((s.card : ℝ)⁻¹ * Real.log (s.card : ℝ)) := by
          congr 1
          calc
            Real.negMulLog (ENNReal.toReal ((s.card : ENNReal)⁻¹))
                = Real.negMulLog ((s.card : ℝ)⁻¹) := by
                    simp [ENNReal.toReal_inv, ENNReal.toReal_natCast]
            _ = -((s.card : ℝ)⁻¹ * Real.log ((s.card : ℝ)⁻¹)) := by
                    simp [Real.negMulLog_def]
            _ = -((s.card : ℝ)⁻¹ * (-Real.log (s.card : ℝ))) := by
                    rw [Real.log_inv]
            _ = (s.card : ℝ)⁻¹ * Real.log (s.card : ℝ) := by ring
    _ = Real.log (s.card : ℝ) := by
          have hcard_ne_zero : (s.card : ℝ) ≠ 0 := by
            exact_mod_cast hs.card_ne_zero
          calc
            (s.card : ℝ) * ((s.card : ℝ)⁻¹ * Real.log (s.card : ℝ))
                = ((s.card : ℝ) * (s.card : ℝ)⁻¹) * Real.log (s.card : ℝ) := by ring
            _ = Real.log (s.card : ℝ) := by simp [hcard_ne_zero]

/-- Distribution-level feasibility for hard local constraints: positive mass
only on globally feasible assignments. -/
def FeasibleDistribution {α : Type*}
    (constraints : List (LocalConstraint α)) (p : PMF α) : Prop :=
  p.support ⊆ {x | Feasible constraints x}

/-- `p` is maximum-entropy among all distributions satisfying a predicate `P`. -/
def IsMaxEntropyAmong {α : Type*} [Fintype α] (P : PMF α → Prop) (p : PMF α) : Prop :=
  P p ∧ ∀ q, P q → shannonEntropy q ≤ shannonEntropy p

theorem localVerificationMaximumEntropyOnFinset
    {α : Type*} [Fintype α] [DecidableEq α]
    (target : Finset α) (hTarget : target.Nonempty)
    (constraints : List (LocalConstraint α))
    (hComplete : LocallyComplete constraints (target : Set α))
    (hTargetFeasible : ∀ x, x ∈ (target : Set α) → Feasible constraints x) :
    IsMaxEntropyAmong (FeasibleDistribution constraints) (uniformOn target hTarget) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxTarget : x ∈ (target : Set α) := by
      simpa [support_uniformOn target hTarget] using hx
    exact hTargetFeasible x hxTarget
  · intro q hq
    have hqSupportTarget : q.support ⊆ (target : Set α) := by
      intro x hx
      exact mem_target_of_feasible hComplete (hq hx)
    have hbound := shannonEntropy_le_log_card_of_support_subset q target hTarget hqSupportTarget
    have huniform : shannonEntropy (uniformOn target hTarget) = Real.log (target.card : ℝ) :=
      shannonEntropy_uniformOn target hTarget
    simpa [huniform] using hbound

noncomputable def localVerificationCertificateOnFinset
    {α : Type*} [Fintype α] [DecidableEq α]
    (k : Nat) (target : Finset α) (hTarget : target.Nonempty)
    (constraints : List (LocalConstraint α))
    (hBound : ConstraintsRespectK k constraints)
    (hComplete : LocallyComplete constraints (target : Set α))
    (hTargetFeasible : ∀ x, x ∈ (target : Set α) → Feasible constraints x) :
    PProd (IsKLocal k (uniformOn target hTarget))
      (IsMaxEntropyAmong (FeasibleDistribution constraints) (uniformOn target hTarget)) := by
  refine ⟨?_, ?_⟩
  · exact localVerificationOnFinset k target hTarget constraints hBound hComplete hTargetFeasible
  · exact localVerificationMaximumEntropyOnFinset target hTarget constraints hComplete
      hTargetFeasible

end Probability
end Cslib
