/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Complexity.Classes
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# Space Complexity Classes

This file defines space-bounded computation and the complexity classes
**PSPACE** and **L** (logarithmic space).

## Main Definitions

* `OutputsWithinSpace` — TM outputs on input using at most `s` cells
* `SpaceBoundedComputable f s` — `f` is computable within space `s`
* `ComplexityPSPACE` — languages decidable in polynomial space
* `ComplexityL` — languages decidable in logarithmic space

## Main Results

* `ComplexityP_subset_ComplexityPSPACE` — P ⊆ PSPACE
* `ComplexityL_subset_ComplexityP` — L ⊆ P (stated, proof deferred)

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

open Turing SingleTapeTM Polynomial Relation

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A TM `tm` **outputs** `l'` on input `l` using at most `s` tape cells
throughout the computation. This combines the time-based reachability
with a space bound: every configuration along the computation path
uses at most `s` cells. -/
def OutputsWithinSpace (tm : SingleTapeTM Symbol)
    (l l' : List Symbol) (s : ℕ) : Prop :=
  ∃ t : ℕ, tm.OutputsWithinTime l l' t ∧
    ∀ cfg : tm.Cfg,
      ReflTransGen tm.TransitionRelation (tm.initCfg l) cfg →
      Cfg.space_used tm cfg ≤ s

/-- A function `f` is **space-bounded computable** with space bound `s`
if there exists a TM computing `f` that uses at most `s(|x|)` tape
cells on input `x`. -/
structure SpaceBoundedComputable
    (f : List Symbol → List Symbol) (s : ℕ → ℕ) where
  /-- The underlying Turing machine -/
  tm : SingleTapeTM Symbol
  /-- Proof that the machine computes `f` within space `s` -/
  outputsInSpace : ∀ a,
    OutputsWithinSpace tm a (f a) (s a.length)

/-- **PSPACE** is the class of languages decidable by a Turing machine
using polynomial space. -/
def ComplexityPSPACE : Set (Set (List Symbol)) :=
  { L | ∃ f : List Symbol → List Symbol,
    ∃ p : Polynomial ℕ,
    Nonempty (SpaceBoundedComputable f (fun n => p.eval n)) ∧
    Decides f L }

/-- **L** (LOGSPACE) is the class of languages decidable by a Turing
machine using O(log n) space. -/
def ComplexityL : Set (Set (List Symbol)) :=
  { L | ∃ f : List Symbol → List Symbol,
    ∃ c : ℕ,
    Nonempty (SpaceBoundedComputable f
      (fun n => c * Nat.log 2 n)) ∧
    Decides f L }

end

open Turing SingleTapeTM Polynomial Relation

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Any configuration reachable during a halting computation has its space
bounded by the initial space plus the halting time. -/
private lemma space_bounded_of_time_bounded (tm : SingleTapeTM Symbol)
    (l l' : List Symbol) (t : ℕ)
    (htime : tm.OutputsWithinTime l l' t)
    (cfg : tm.Cfg)
    (hreach : ReflTransGen tm.TransitionRelation (tm.initCfg l) cfg) :
    Cfg.space_used tm cfg ≤ max 1 l.length + t := by
  -- Convert ReflTransGen to RelatesInSteps
  obtain ⟨m, hm⟩ := ReflTransGen.relatesInSteps hreach
  -- Extract the halting computation
  obtain ⟨t', ht'_le, ht'⟩ := htime
  -- haltCfg has no successors
  have hhalt : ∀ cfg', ¬tm.TransitionRelation (tm.haltCfg l') cfg' :=
    fun cfg' => no_step_from_halt tm _ cfg' rfl
  -- By determinism, m ≤ t' ≤ t
  have hm_le := reachable_steps_le_halting_steps tm ht' hhalt hm
  -- Space grows by at most 1 per step
  have hspace := RelatesInSteps.apply_le_apply_add hm (Cfg.space_used tm)
    fun a b hstep => Cfg.space_used_step a b (Option.mem_def.mp hstep)
  rw [Cfg.space_used_initCfg] at hspace
  omega

/-- **P ⊆ PSPACE**: every language decidable in polynomial time is also
decidable in polynomial space.

A TM running in time `t` can use at most `max 1 |input| + t` tape cells
(one new cell per step, plus the initial input). So a polynomial time
bound gives a polynomial space bound. -/
public theorem ComplexityP_subset_ComplexityPSPACE :
    ComplexityP (Symbol := Symbol) ⊆ ComplexityPSPACE := by
  intro L ⟨f, ⟨hf⟩, hDecides⟩
  refine ⟨f, hf.poly + X + 1, ⟨{
    tm := hf.tm
    outputsInSpace := fun a =>
      ⟨hf.time_bound a.length, hf.outputsFunInTime a, fun cfg hreach =>
        le_trans
          (space_bounded_of_time_bounded hf.tm a (f a) (hf.time_bound a.length)
            (hf.outputsFunInTime a) cfg hreach)
          (by simp only [eval_add, eval_X, eval_one]
              have := hf.bounds a.length
              omega)⟩
  }⟩, hDecides⟩

/-- **L ⊆ P**: every language decidable in logarithmic space is also
decidable in polynomial time.

*Proof sketch*: A TM using space `s(n)` has at most
`|Q| · |Σ|^s(n) · s(n)` possible configurations. If `s(n) = O(log n)`,
this is polynomial in `n`, so the TM halts in polynomial time (otherwise
it would loop through a configuration twice). This is a deep result
that requires a configuration-counting argument. -/
-- TODO: complete the proof via configuration counting
public theorem ComplexityL_subset_ComplexityP :
    ComplexityL (Symbol := Symbol) ⊆ ComplexityP := by
  intro L ⟨f, c, ⟨hf⟩, hDecides⟩
  exact ⟨f, ⟨sorry⟩, hDecides⟩
