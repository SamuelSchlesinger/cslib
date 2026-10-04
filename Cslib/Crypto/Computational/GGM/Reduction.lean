/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GGM.Expansion
public import Cslib.Crypto.Computational.Hybrid.Sequence
public import Cslib.Computability.Probabilistic.Presample

/-!
# The GGM reduction to one generator challenge

The expansion game consumes at most one fresh draw per adversary call. Pre-sampling a sufficient
list exposes it as a test of independent samples, so the shared sequence hybrid supplies a single
challenge reduction. Cached replies ignore the extra draw, preserving repeated-query consistency.

## References

O. Goldreich, S. Goldwasser, S. Micali,
[*How to Construct Random Functions*](https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf),
Section 3.3, the simulation used in the proof of Theorem 3.
-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Probability

/-- Run the expansion game using a saved list, consuming one entry at each adversary call.
Truncation and the empty fallback make the test total on every challenge list. -/
noncomputable def sampleGame (generator : Word → Word) (adversary : OracleDistinguisher)
    (n depth : ℕ) (values : List Word) : ProbComp Bool :=
  Prod.fst <$> OracleComp.simulateWithSamples []
    (fun expansion => expansionOracle generator (pure expansion) n depth)
    (adversary n []) [] values

private theorem expansionOracle_sample (generator : Word → Word) (sample : ProbComp Word)
    (n depth : ℕ) (query : Word) (cache : Cache) :
    (ProbComp.eval sample).bind (fun expansion =>
      ProbComp.eval (expansionOracle generator (pure expansion) n depth query cache)) =
        ProbComp.eval (expansionOracle generator sample n depth query cache) := by
  by_cases hquery : query.length = n
  · cases hlookup : cache.lookup (query.take depth) <;>
      simp [expansionOracle, hquery, memoize, hlookup, PMF.map, Function.comp_def]
  · simp [expansionOracle, hquery]

/-- A list with one independent expansion per possible query gives exactly the online game. -/
theorem sampleGame_replicate (generator : Word → Word) (sample : ProbComp Word)
    (adversary : OracleDistinguisher) (n depth count maxSize : ℕ)
    (hqueries : (adversary n []).HasQueryBounds List.length count maxSize) :
    ProbComp.eval (OracleComp.replicate count sample >>= sampleGame generator adversary n depth) =
      ProbComp.eval (expansionGame generator sample adversary n depth) := by
  have h := hqueries.eval_presample sample []
    (fun expansion => expansionOracle generator (pure expansion) n depth) []
  have hout := congrArg (PMF.map Prod.fst) h
  have hstep := fun query cache => expansionOracle_sample generator sample n depth query cache
  simp only [ProbComp.eval] at hstep
  simpa only [sampleGame, expansionGame, ProbComp.eval, OracleComp.eval_bind,
    OracleComp.eval_map, OracleComp.eval_simulateState, PMF.map_bind, hstep] using hout

/-- The saved-sample game is uniformly PPT, including arbitrary and short challenge lists.
The shared interpreter accounts for list consumption, cache lookup and tree evaluation. -/
theorem isPPTOn_sampleGame {Caller : Type} {input : Caller ↪ Word}
    {generator : Word → Word} (hgenerator : IsPolyTime wordEncoding generator)
    {width depth : Caller → ℕ} {values : Caller → List Word}
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (hdepth : IsPolyTime input (fun a => unaryEncoding (depth a)))
    (hvalues : IsPolyTime input (fun a => listEncoding wordEncoding (values a)))
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT boolEncoding adversary) :
    IsPPTOn input boolEncoding
      (fun a => sampleGame generator adversary (width a) (depth a) (values a)) := by
  have hexpansion := isPPTOn_expansionOracle (input := pairEncoding input wordEncoding) hgenerator
      (sample := fun pair => pure pair.2) (width := fun pair => width pair.1)
      (depth := fun pair => depth pair.1) (by ppt) (by polytime) (by polytime)
  have hrun : IsPPTOn input (pairEncoding boolEncoding cacheEncoding) (fun a =>
      OracleComp.simulateWithSamples []
        (fun expansion => expansionOracle generator (pure expansion) (width a) (depth a))
        (adversary (width a) []) [] (values a)) := by
    refine hadversary.simulateWithSamples [] (prepare := fun a => (width a, []))
      (by polytime) hexpansion (isPolyTime_const _ []) hvalues
      (fun a cache => ∀ entry ∈ cache, entry.2.length ≤ 2 * width a) (by simp)
      (resources := fun a query => 4 * query.length + 4 * width a + 3) (by polytime) ?_
    intro a expansion query cache hcache result hresult
    obtain ⟨hcache', hreply, hgrowth⟩ := expansionOracle_bounds generator
      (pure expansion) (width a) (depth a) query cache hcache result hresult
    exact ⟨hcache', by lia, by lia⟩
  exact hrun.map (isPolyTime_fst boolEncoding cacheEncoding)

/-- Insert one challenge among simulated uniform and generated expansions at a chosen level. -/
noncomputable def levelTest (generator : Word → Word) (adversary : OracleDistinguisher)
    (n depth count : ℕ) (challenge : Word) : ProbComp Bool :=
  sequenceTest (OracleComp.sampleBits (2 * n)) (generator <$> OracleComp.sampleBits n) count
    (sampleGame generator adversary n depth) challenge

/-- The single-challenge reduction is PPT whenever its level and query budget are efficiently
computed. No semantic query-bound hypothesis is needed for this efficiency certificate. -/
theorem isPPTOn_levelTest {Caller : Type} {input : Caller ↪ Word}
    {generator : Word → Word} (hgenerator : IsPolyTime wordEncoding generator)
    {width depth count : Caller → ℕ} {challenge : Caller → Word}
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (hdepth : IsPolyTime input (fun a => unaryEncoding (depth a)))
    (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hchallenge : IsPolyTime input challenge)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT boolEncoding adversary) :
    IsPPTOn input boolEncoding (fun a =>
      levelTest generator adversary (width a) (depth a) (count a) (challenge a)) := by
  have htest : IsPPTOn (pairEncoding input (listEncoding wordEncoding)) boolEncoding
      (fun pair => sampleGame generator adversary (width pair.1) (depth pair.1) pair.2) :=
    isPPTOn_sampleGame hgenerator (by polytime) (by polytime) (by polytime) hadversary
  unfold levelTest
  ppt

/-- The single-challenge test captures the signed gap of adjacent GGM levels. Its loss is the
dyadic sampling range for the query budget, including padding coordinates. -/
theorem levelTest_gap (generator : Word → Word) (adversary : OracleDistinguisher)
    (n depth count maxSize : ℕ) (hdepth : depth < n)
    (hqueries : (adversary n []).HasQueryBounds List.length count maxSize) :
    winProbability (hybridGame generator adversary n depth) -
        winProbability (hybridGame generator adversary n (depth + 1)) =
      (dyadicSize count : ℝ) *
        (winProbability ((generator <$> OracleComp.sampleBits n) >>=
          levelTest generator adversary n depth count) -
        winProbability (OracleComp.sampleBits (2 * n) >>=
          levelTest generator adversary n depth count)) := by
  unfold levelTest
  have h := sequenceTest_gap (OracleComp.sampleBits (2 * n))
    (generator <$> OracleComp.sampleBits n) count (sampleGame generator adversary n depth)
  simpa only [winProbability, sampleGame_replicate generator _ adversary n depth count
    maxSize hqueries, expansionGame_generated generator adversary n depth hdepth,
    expansionGame_uniform generator adversary n depth hdepth] using h

/-- Choose a level uniformly and run its single-challenge reduction. Both random choices use
dyadic ranges, and unused indices reject. The query budget is a fixed function of the parameter. -/
noncomputable def reduction (generator : Word → Word) (adversary : OracleDistinguisher)
    (count : ℕ → ℕ) : Distinguisher := fun n challenge => do
  let depth ← sampleDyadicIndex n
  if depth < n then levelTest generator adversary n depth (count n) challenge else pure false

/-- Efficient generation and an efficient query budget give one uniform PPT reduction. -/
theorem isPPT_reduction {generator : Word → Word}
    (hgenerator : IsPolyTime wordEncoding generator) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT boolEncoding adversary) {count : ℕ → ℕ}
    (hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n))) :
    IsPPT boolEncoding (reduction generator adversary count) := by
  have hlevel : IsPPTOn (pairEncoding parameterEncoding unaryEncoding) boolEncoding
      (fun pair => levelTest generator adversary pair.1.1 pair.2 (count pair.1.1) pair.1.2) :=
    isPPTOn_levelTest hgenerator (by polytime) (by polytime) (by polytime) (by polytime) hadversary
  unfold reduction
  ppt

/-- The GGM reduction preserves the full real/ideal signed gap up to the product of the two
dyadic sampling ranges. This statement is exact, including the zero-width game. -/
theorem reduction_gap (generator : Word → Word) (adversary : OracleDistinguisher)
    (count : ℕ → ℕ) (n maxSize : ℕ)
    (hqueries : (adversary n []).HasQueryBounds List.length (count n) maxSize) :
    winProbability (prfRealGame (eval generator) adversary n) -
        winProbability (prfIdealGame adversary n) =
      (dyadicSize n : ℝ) * dyadicSize (count n) *
        (winProbability ((generator <$> OracleComp.sampleBits n) >>=
          reduction generator adversary count n) -
        winProbability (OracleComp.sampleBits (2 * n) >>=
          reduction generator adversary count n)) := by
  unfold reduction
  have h := Game.winProbability_hybrid_reduction
    (fun depth => ProbComp.eval (hybridGame generator adversary n depth))
    (fun depth => ProbComp.eval ((generator <$> OracleComp.sampleBits n) >>=
      levelTest generator adversary n depth (count n)))
    (fun depth => ProbComp.eval (OracleComp.sampleBits (2 * n) >>=
      levelTest generator adversary n depth (count n))) n (dyadicSize n)
    (lt_dyadicSize n).le (dyadicSize (count n))
    (fun depth hdepth =>
      levelTest_gap generator adversary n depth (count n) maxSize hdepth hqueries)
  simpa only [winProbability, eval_bind_sampleDyadicIndex_guard,
    hybridGame_zero, hybridGame_self] using h

/-- The real/ideal PRF advantage is the reduction's generator advantage times the two sampling
ranges. The loss is polynomial whenever the query budget is polynomial. -/
theorem reduction_advantage (generator : Word → Word) (adversary : OracleDistinguisher)
    (count : ℕ → ℕ) (n maxSize : ℕ)
    (hqueries : (adversary n []).HasQueryBounds List.length (count n) maxSize) :
    advantage (prfRealGame (eval generator) adversary n) (prfIdealGame adversary n) =
      (dyadicSize n : ℝ) * dyadicSize (count n) *
        advantage
          ((generator <$> OracleComp.sampleBits n) >>= reduction generator adversary count n)
          (OracleComp.sampleBits (2 * n) >>= reduction generator adversary count n) := by
  change |winProbability _ - winProbability _| = _ * |winProbability _ - winProbability _|
  rw [reduction_gap generator adversary count n maxSize hqueries, abs_mul, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (dyadicSize n) : (0 : ℝ) ≤ _),
    abs_of_nonneg (Nat.cast_nonneg (dyadicSize (count n)))]

end Cslib.Crypto.GGM
