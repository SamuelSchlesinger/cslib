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

* `ComplexityL_subset_ComplexityP` — L ⊆ P
* `ComplexityP_subset_ComplexityPSPACE` — P ⊆ PSPACE
* `ComplexityNP_subset_ComplexityPSPACE` — NP ⊆ PSPACE

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

omit [Inhabited Symbol] [Fintype Symbol] in
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

omit [Inhabited Symbol] [Fintype Symbol] in
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

*Proof sketch*: A TM using space `s` on input of length `n` has at most
`|Q| · (s+1) · |Σ|^s` distinct configurations (state × head position × tape
contents). If the machine halts, it must do so within this many steps. For
`s = c · log₂ n`, this bound is `|Q| · (c · log n + 1) · |Σ|^(c · log n)`.
Since `|Σ|^(c · log₂ n) = n^(c · log₂ |Σ|)`, the total time is polynomial.

We axiomatize this because the configuration-counting argument requires
establishing that the number of configurations is polynomially bounded
when the space is logarithmic, which involves a detailed TM simulation
argument. -/
axiom ComplexityL_subset_ComplexityP
    {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] :
    ComplexityL (Symbol := Symbol) ⊆ ComplexityP

/-- **NP ⊆ PSPACE**: every language in NP is also in PSPACE.

*Proof sketch*: Given an NP verifier that runs in poly-time with poly-length
witnesses, enumerate all possible witnesses `w` of length ≤ `p(|x|)`,
run the verifier on `x ++ w` for each one, and accept if any verification
succeeds. The enumeration reuses the same space for each witness, so the
total space is polynomial (the space for the verifier plus `O(p(|x|))` for
the current witness and the counter).

We axiomatize this because the construction requires building a TM that
enumerates binary strings of bounded length and composes them with the
verifier, which is a substantial TM construction. -/
axiom ComplexityNP_subset_ComplexityPSPACE
    {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] :
    ComplexityNP (Symbol := Symbol) ⊆ ComplexityPSPACE
