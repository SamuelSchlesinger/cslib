/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI Codex
-/

module

public import Cslib.Foundations.Probability.MarginalConstraints

@[expose] public section

namespace Cslib
namespace Probability

universe u v

/-- Local verification in the marginal-constraint setting:
if all feasible distributions are forced into a finite target support, then
uniform-on-target is max entropy among feasible distributions. -/
theorem localVerificationMaximumEntropyMarginalsOnFinset
    {Var : Type u} {Val : Type v}
    [Fintype Var] [DecidableEq Var] [Fintype Val] [DecidableEq Val]
    (target : Finset (Assignment Var Val)) (hTarget : target.Nonempty)
    (constraints : List (MarginalConstraint Var Val))
    (hComplete : MarginalLocalCompleteness (target : Set (Assignment Var Val)) constraints)
    (hUniformFeasible : FeasibleMarginals constraints (uniformOn target hTarget)) :
    IsMaxEntropyAmong (FeasibleMarginals constraints) (uniformOn target hTarget) := by
  refine ⟨hUniformFeasible, ?_⟩
  intro q hq
  have hqSupportTarget : q.support ⊆ (target : Set (Assignment Var Val)) :=
    support_subset_of_marginalLocalCompleteness hq hComplete
  have hbound :=
    shannonEntropy_le_log_card_of_support_subset q target hTarget hqSupportTarget
  have huniform : shannonEntropy (uniformOn target hTarget) = Real.log (target.card : ℝ) :=
    shannonEntropy_uniformOn target hTarget
  simpa [huniform] using hbound

/-- `k`-locality certificate in the marginal-constraint style. -/
theorem localVerificationIsKLocalMarginalOnFinset
    {Var : Type u} {Val : Type v}
    [Fintype Var] [DecidableEq Var] [Fintype Val] [DecidableEq Val]
    (k : Nat)
    (target : Finset (Assignment Var Val)) (hTarget : target.Nonempty)
    (constraints : List (MarginalConstraint Var Val))
    (hBound : MarginalConstraintsRespectK k constraints)
    (hComplete : MarginalLocalCompleteness (target : Set (Assignment Var Val)) constraints)
    (hUniformFeasible : FeasibleMarginals constraints (uniformOn target hTarget)) :
    IsKLocalMarginal k (uniformOn target hTarget) := by
  refine ⟨constraints, hBound, ?_⟩
  exact localVerificationMaximumEntropyMarginalsOnFinset target hTarget constraints hComplete
    hUniformFeasible

end Probability
end Cslib
