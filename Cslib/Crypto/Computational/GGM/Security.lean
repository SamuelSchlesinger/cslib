/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GGM.Reduction
public import Cslib.Crypto.Computational.Stretch
public import Cslib.Computability.Probabilistic.QueryBounds

/-!
# GGM pseudorandom functions from pseudorandom generators

The tree evaluator is a pseudorandom function whenever its two-child expansion is efficient and
pseudorandom. For each oracle PPT adversary, the query-bound theorem supplies a polynomial budget.
The single uniform reduction loses only the product of the level and sample-selection ranges.

The PRG wrapper permits surplus expansion bits. Truncating to two labels preserves security and
does not change tree evaluation. In particular, the strict PRG convention at seed length zero is
compatible with the GGM construction.

## References

O. Goldreich, S. Goldwasser, S. Micali,
[*How to Construct Random Functions*](https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf),
Sections 3.2–3.3, construction and Theorem 3.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- The GGM tree of an efficient pseudorandom two-child expansion is a pseudorandom function
against every uniform, strict polynomial-time adaptive oracle adversary. -/
theorem GGM.pseudorandomFunction_of_indistinguishable {generator : Word → Word}
    (hgenerator : IsPolyTime wordEncoding generator)
    (hlength : ∀ seed, (generator seed).length = 2 * seed.length)
    (hsecure : ComputationallyIndistinguishable (generatorEnsemble generator)
      (fun n => uniformBits (2 * n))) : PseudorandomFunction (GGM.eval generator) := by
  refine ⟨isPolyTime_eval hgenerator, fun key query _ =>
    length_eval (fun seed => by rw [hlength]) key query, ?_⟩
  intro adversary hadversary
  obtain ⟨c, d, hqueries⟩ := hadversary.query_bounds
  let count := fun n => c * (n + 2) ^ d
  have hcount : IsPolyTime unaryEncoding (fun n => unaryEncoding (count n)) := by
    unfold count
    polytime
  have hreduce := hsecure (reduction generator adversary count)
    (isPPT_reduction hgenerator hadversary hcount)
  have hloss : PolynomiallyBounded (fun n => dyadicSize n * dyadicSize (count n)) := by
    have := hcount.polynomiallyBounded
    fun_prop
  have hsmall := hreduce.polynomiallyBounded_mul hloss
  apply negligible_of_le hsmall (fun n => Game.advantage_nonneg _ _) ?_
  intro n
  have hquery : (adversary n []).HasQueryBounds List.length (count n) (count n) := by
    simpa [count] using hqueries n []
  have h := reduction_advantage generator adversary count n (count n) hquery
  simpa only [advantage, distinguishingGame, ProbComp.eval_bind, ProbComp.eval_sample,
    ProbComp.eval_map, ProbComp.eval_sampleBits, generatorEnsemble, PRG.Generator.outputDist,
    PRG.Generator.coe_mk, Nat.cast_mul] using h.le

/-- A secure generator providing at least two full labels gives the GGM pseudorandom function.
Surplus bits are ignored by the evaluator; the hypothesis also accommodates seed length zero. -/
theorem PseudorandomGenerator.ggm {generator : Word → Word} {length : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator length) (hdouble : ∀ n, 2 * n ≤ length n) :
    PseudorandomFunction (GGM.eval generator) := by
  have hpoly := hgenerator.polyTime
  have hsecure := hgenerator.indistinguishable.map (fun n word => word.take (2 * n)) (by polytime)
  have htruncated : ComputationallyIndistinguishable
      (generatorEnsemble (fun seed => (generator seed).take (2 * seed.length)))
      (fun n => uniformBits (2 * n)) := by
    simpa only [← generatorEnsemble_postprocess generator (fun n word => word.take (2 * n)),
      uniformBits_take (hdouble _)] using hsecure
  have h := GGM.pseudorandomFunction_of_indistinguishable
    (generator := fun seed => (generator seed).take (2 * seed.length)) (by polytime)
    (fun seed => by simp [hgenerator.length_eq, Nat.min_eq_left (hdouble _)]) htruncated
  simpa only [GGM.eval_truncate] using h

/-- Every uniform pseudorandom generator yields a uniform pseudorandom function. Truncate to one
extra bit, amplify to two labels plus one bit, and apply the GGM tree construction. -/
theorem PseudorandomGenerator.exists_pseudorandomFunction {generator : Word → Word}
    {length : ℕ → ℕ} (hgenerator : PseudorandomGenerator generator length) :
    ∃ family : Word → Word → Word, PseudorandomFunction family := by
  have hone := hgenerator.truncate (fun n => n + 1) (by polytime)
    (fun n => hgenerator.stretch n) (by intro n; lia)
  have htwo := hone.amplify (fun n => 2 * n + 1) (by polytime) (by intro n; lia)
  exact ⟨_, htwo.ggm (by intro n; lia)⟩

end Cslib.Crypto
