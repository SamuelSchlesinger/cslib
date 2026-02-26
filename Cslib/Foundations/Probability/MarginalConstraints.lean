/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI Codex
-/

module

public import Cslib.Foundations.Probability.Entropy

@[expose] public section

namespace Cslib
namespace Probability

universe u v

abbrev Assignment (Var : Type u) (Val : Type v) : Type (max u v) := Var → Val

/-- Restrict a global assignment to a finite scope. -/
def scopeProjection {Var : Type u} {Val : Type v} [DecidableEq Var]
    (scope : Finset Var) : Assignment Var Val → (↑scope → Val) :=
  fun x i => x i.1

@[simp]
theorem scopeProjection_apply
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    (scope : Finset Var) (x : Assignment Var Val) (i : ↑scope) :
    scopeProjection scope x i = x i.1 := rfl

/-- Marginal of a global PMF on a finite scope. -/
noncomputable def marginal {Var : Type u} {Val : Type v} [DecidableEq Var]
    (scope : Finset Var) (p : PMF (Assignment Var Val)) : PMF (↑scope → Val) :=
  PMF.map (scopeProjection scope) p

/-- A finite-scope marginal constraint. -/
structure MarginalConstraint (Var : Type u) (Val : Type v) [DecidableEq Var] where
  scope : Finset Var
  target : PMF (↑scope → Val)

/-- A global distribution satisfies a marginal constraint if the corresponding marginal is exact. -/
def SatisfiesMarginal
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    (p : PMF (Assignment Var Val)) (c : MarginalConstraint Var Val) : Prop :=
  marginal c.scope p = c.target

/-- Feasibility wrt a finite list of marginal constraints. -/
def FeasibleMarginals
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    (constraints : List (MarginalConstraint Var Val))
    (p : PMF (Assignment Var Val)) : Prop :=
  ∀ c ∈ constraints, SatisfiesMarginal p c

/-- Arity bound for marginal constraints. -/
def MarginalConstraintsRespectK
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    (k : Nat) (constraints : List (MarginalConstraint Var Val)) : Prop :=
  ∀ c ∈ constraints, c.scope.card ≤ k

theorem marginalConstraintsRespectK_mono
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    {constraints : List (MarginalConstraint Var Val)} :
    MarginalConstraintsRespectK kSmall constraints →
      MarginalConstraintsRespectK kLarge constraints := by
  intro h c hc
  exact Nat.le_trans (h c hc) hkl

/-- Pointwise local-support set induced by constrained marginals:
an assignment is admissible if every constrained local pattern has positive target mass. -/
def LocalSupportSet
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    (constraints : List (MarginalConstraint Var Val)) :
    Set (Assignment Var Val) :=
  { x | ∀ c ∈ constraints, c.target (scopeProjection c.scope x) ≠ 0 }

/-- Maximal-support property for a candidate max-entropy solution:
its support equals the intersection of local marginal supports. -/
def MaximalSupport
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    (constraints : List (MarginalConstraint Var Val))
    (p : PMF (Assignment Var Val)) : Prop :=
  p.support = LocalSupportSet constraints

/-- Local completeness at the level of marginal constraints: every point outside
`target` violates at least one constrained local pattern by having zero target mass. -/
def MarginalLocalCompleteness
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    (target : Set (Assignment Var Val))
    (constraints : List (MarginalConstraint Var Val)) : Prop :=
  ∀ x, x ∉ target →
    ∃ c ∈ constraints, c.target (scopeProjection c.scope x) = 0

lemma marginal_at_projection_nonzero_of_mem_support
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    (q : PMF (Assignment Var Val)) (scope : Finset Var)
    {x : Assignment Var Val} (hx : x ∈ q.support) :
    marginal scope q (scopeProjection scope x) ≠ 0 := by
  have hxImage : scopeProjection scope x ∈ (marginal scope q).support := by
    rw [marginal, PMF.support_map]
    exact ⟨x, hx, rfl⟩
  exact (PMF.mem_support_iff (marginal scope q) (scopeProjection scope x)).1 hxImage

theorem support_subset_of_marginalLocalCompleteness
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    {constraints : List (MarginalConstraint Var Val)}
    {target : Set (Assignment Var Val)}
    {q : PMF (Assignment Var Val)}
    (hFeasible : FeasibleMarginals constraints q)
    (hComplete : MarginalLocalCompleteness target constraints) :
    q.support ⊆ target := by
  intro x hx
  by_contra hxNot
  rcases hComplete x hxNot with ⟨c, hcIn, hcZero⟩
  have hMargNonzero : marginal c.scope q (scopeProjection c.scope x) ≠ 0 :=
    marginal_at_projection_nonzero_of_mem_support q c.scope hx
  have hEq : marginal c.scope q = c.target := hFeasible c hcIn
  have hTargetNonzero : c.target (scopeProjection c.scope x) ≠ 0 := by
    simpa [hEq] using hMargNonzero
  exact hTargetNonzero hcZero

theorem support_subset_localSupportSet_of_feasibleMarginals
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    {constraints : List (MarginalConstraint Var Val)}
    {q : PMF (Assignment Var Val)}
    (hFeasible : FeasibleMarginals constraints q) :
    q.support ⊆ LocalSupportSet constraints := by
  intro x hx c hcIn
  have hMargNonzero : marginal c.scope q (scopeProjection c.scope x) ≠ 0 :=
    marginal_at_projection_nonzero_of_mem_support q c.scope hx
  have hEq : marginal c.scope q = c.target := hFeasible c hcIn
  simpa [hEq] using hMargNonzero

/-- Marginal-constraint version of `k`-locality: exact feasibility and entropy optimality. -/
def IsKLocalMarginal
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    [Fintype (Assignment Var Val)]
    (k : Nat) (p : PMF (Assignment Var Val)) : Prop :=
  ∃ constraints : List (MarginalConstraint Var Val),
    MarginalConstraintsRespectK k constraints ∧ IsMaxEntropyAmong (FeasibleMarginals constraints) p

theorem isKLocalMarginal_mono
    {Var : Type u} {Val : Type v} [DecidableEq Var]
    [Fintype (Assignment Var Val)]
    {kSmall kLarge : Nat} (hkl : kSmall ≤ kLarge)
    {p : PMF (Assignment Var Val)} :
    IsKLocalMarginal kSmall p → IsKLocalMarginal kLarge p := by
  intro h
  rcases h with ⟨constraints, hBound, hMax⟩
  exact ⟨constraints, marginalConstraintsRespectK_mono hkl hBound, hMax⟩

end Probability
end Cslib
