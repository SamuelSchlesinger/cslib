/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI Codex
-/

module

public import Cslib.Init
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

namespace Cslib
namespace Probability

universe u v

/-- A local constraint on assignments of type `α` with an explicit arity bound. -/
structure LocalConstraint (α : Type u) where
  arity : Nat
  accepts : α → Prop

/-- An assignment is feasible when it satisfies all constraints. -/
def Feasible {α : Type u} (constraints : List (LocalConstraint α)) (x : α) : Prop :=
  ∀ c ∈ constraints, c.accepts x

/-- All constraints have arity at most `k`. -/
def ConstraintsRespectK {α : Type u} (k : Nat) (constraints : List (LocalConstraint α)) : Prop :=
  ∀ c ∈ constraints, c.arity ≤ k

/-- Every point outside `target` violates at least one local constraint. -/
def LocallyComplete {α : Type u} (constraints : List (LocalConstraint α)) (target : Set α) : Prop :=
  ∀ x, x ∉ target → ∃ c ∈ constraints, ¬c.accepts x

theorem mem_target_of_feasible
    {α : Type u} {constraints : List (LocalConstraint α)} {target : Set α} {x : α}
    (hComplete : LocallyComplete constraints target) (hx : Feasible constraints x) :
    x ∈ target := by
  by_contra hNotTarget
  rcases hComplete x hNotTarget with ⟨c, hcIn, hcFails⟩
  exact hcFails (hx c hcIn)

theorem feasible_subset_target
    {α : Type u} {constraints : List (LocalConstraint α)} {target : Set α}
    (hComplete : LocallyComplete constraints target) :
    {x | Feasible constraints x} ⊆ target := by
  intro x hx
  exact mem_target_of_feasible hComplete hx

theorem feasible_eq_target
    {α : Type u} {constraints : List (LocalConstraint α)} {target : Set α}
    (hComplete : LocallyComplete constraints target)
    (hTargetFeasible : ∀ x, x ∈ target → Feasible constraints x) :
    {x | Feasible constraints x} = target := by
  ext x
  constructor
  · intro hx
    exact mem_target_of_feasible hComplete hx
  · intro hx
    exact hTargetFeasible x hx

/-- Support-level definition of `k`-locality for a `PMF`. -/
structure IsKLocal {α : Type u} (k : Nat) (p : PMF α) where
  constraints : List (LocalConstraint α)
  kBound : ConstraintsRespectK k constraints
  exactSupport : p.support = {x | Feasible constraints x}

theorem constraintsRespectK_mono
    {α : Type u} {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    {constraints : List (LocalConstraint α)} :
    ConstraintsRespectK kSmall constraints → ConstraintsRespectK kLarge constraints := by
  intro h c hc
  exact Nat.le_trans (h c hc) hkl

def isKLocal_mono
    {α : Type u} {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    {p : PMF α} :
    IsKLocal kSmall p → IsKLocal kLarge p := by
  intro h
  rcases h with ⟨constraints, hBound, hExact⟩
  exact ⟨constraints, constraintsRespectK_mono hkl hBound, hExact⟩

/-- `pJoint` is a marginal model of `pObs` when projecting out latent
coordinates recovers `pObs`. -/
def IsMarginalModel
    {Obs : Type u} {Lat : Type v}
    (pObs : PMF Obs)
    (pJoint : PMF (Obs × Lat)) : Prop :=
  pJoint.map Prod.fst = pObs

/-- A `k`-localization of `pObs` with latent domain `Lat`. -/
structure KLocalization (k : Nat) (Obs : Type u) (Lat : Type v) (pObs : PMF Obs) where
  lifted : PMF (Obs × Lat)
  marginal : IsMarginalModel pObs lifted
  kLocal : IsKLocal k lifted

/-- Existence of a `k`-localization using `latentVars` many Boolean-like latent states. -/
def HasKLocalization (k : Nat) (latentVars : Nat) (Obs : Type u) (pObs : PMF Obs) : Prop :=
  Nonempty (KLocalization k Obs (Fin latentVars) pObs)

theorem hasKLocalization_mono
    {Obs : Type u} {pObs : PMF Obs} {latentVars : Nat}
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge) :
    HasKLocalization kSmall latentVars Obs pObs → HasKLocalization kLarge latentVars Obs pObs := by
  intro h
  rcases h with ⟨w⟩
  refine ⟨{ lifted := w.lifted, marginal := w.marginal, kLocal := ?_ }⟩
  exact isKLocal_mono hkl w.kLocal

/-- Uniform PMF on a nonempty finite set. -/
noncomputable abbrev uniformOn
    {α : Type u} [DecidableEq α] (s : Finset α) (hs : s.Nonempty) : PMF α :=
  PMF.uniformOfFinset s hs

theorem uniformOn_apply_of_mem
    {α : Type u} [DecidableEq α] {s : Finset α} (hs : s.Nonempty)
    {a : α} (ha : a ∈ s) :
    uniformOn s hs a = (s.card : ENNReal)⁻¹ := by
  simpa [uniformOn] using PMF.uniformOfFinset_apply_of_mem (s := s) (hs := hs) ha

theorem uniformOn_apply_of_notMem
    {α : Type u} [DecidableEq α] {s : Finset α} (hs : s.Nonempty)
    {a : α} (ha : a ∉ s) :
    uniformOn s hs a = 0 := by
  simpa [uniformOn] using PMF.uniformOfFinset_apply_of_notMem (s := s) (hs := hs) ha

@[simp]
theorem support_uniformOn
    {α : Type u} [DecidableEq α] (s : Finset α) (hs : s.Nonempty) :
    (uniformOn s hs).support = (s : Set α) := by
  simp [uniformOn]

/-- Local verification at the support level yields `k`-locality for any PMF
with exactly the target support. -/
def localVerificationSupportLevel
    {α : Type u} (k : Nat) (target : Set α) (constraints : List (LocalConstraint α))
    (hBound : ConstraintsRespectK k constraints)
    (hComplete : LocallyComplete constraints target)
    (hTargetFeasible : ∀ x, x ∈ target → Feasible constraints x)
    (p : PMF α) (hSupport : p.support = target) :
    IsKLocal k p := by
  refine ⟨constraints, hBound, ?_⟩
  calc
    p.support = target := hSupport
    _ = {x | Feasible constraints x} := (feasible_eq_target hComplete hTargetFeasible).symm

/-- Local verification instantiated with the canonical uniform distribution on a finite target. -/
noncomputable def localVerificationOnFinset
    {α : Type u} [DecidableEq α]
    (k : Nat) (target : Finset α) (hTarget : target.Nonempty)
    (constraints : List (LocalConstraint α))
    (hBound : ConstraintsRespectK k constraints)
    (hComplete : LocallyComplete constraints (target : Set α))
    (hTargetFeasible : ∀ x, x ∈ (target : Set α) → Feasible constraints x) :
    IsKLocal k (uniformOn target hTarget) :=
  localVerificationSupportLevel k (target : Set α) constraints hBound hComplete hTargetFeasible
    (uniformOn target hTarget) (support_uniformOn target hTarget)

end Probability
end Cslib
