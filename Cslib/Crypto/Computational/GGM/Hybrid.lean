/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GGM.Evaluation
public import Cslib.Crypto.Computational.PseudorandomFunction.RandomOracle
public import Cslib.Computability.Probabilistic.OracleSimulation
public import Cslib.Computability.Probabilistic.Memoize

/-!
# The GGM prefix hybrids

At level `depth`, sample an independent label for each newly queried prefix of that length.
Remember it for later queries with the same prefix, and evaluate the remaining suffix using the
generator. Malformed queries receive the empty word, as in the PRF games.

The cache is an ordinary list. One call preserves a label-width invariant and adds at most one
entry. The stateful interpreter then certifies the entire adaptive game without exposing machines.
The endpoint games agree with the real and ideal PRF experiments. `GGM.Reduction` supplies the
adjacent-hybrid reduction and its uniform advantage bound; `GGM.Security` assembles the theorem.

## References

O. Goldreich, S. Goldwasser, S. Micali,
[*How to Construct Random Functions*](https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf),
Section 3.3, the algorithms `A_i` in the proof of Theorem 3.
-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Probability

/-- A finite collection of queried prefixes and their sampled labels. -/
abbrev Cache := List (Word × Word)

/-- Charge for every stored prefix and label, including list and pair delimiters. -/
def cacheEncoding : Cache ↪ Word := listEncoding (pairEncoding wordEncoding wordEncoding)

/-- Answer from a cached random label at the chosen level, followed by ordinary tree evaluation. -/
noncomputable def frontierOracle (generator : Word → Word) (n depth : ℕ) (query : Word) :
    StateT Cache ProbComp Word := fun cache =>
  if query.length = n then do
    let (seed, cache') ← memoize (fun _ : Word => OracleComp.sampleBits n) (query.take depth) cache
    return (eval generator seed (query.drop depth), cache')
  else pure ([], cache)

/-- The adaptive hybrid game starts with an empty prefix cache. -/
noncomputable def hybridGame (generator : Word → Word) (adversary : OracleDistinguisher)
    (n depth : ℕ) : ProbComp Bool :=
  Prod.fst <$> OracleComp.simulateState (frontierOracle generator n depth) (adversary n []) []

/-- At level zero, all valid queries share one root label. Sampling that label on demand agrees
with choosing the key at the start of the real PRF game, even if there are no valid queries. -/
theorem hybridGame_zero (generator : Word → Word) (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (hybridGame generator adversary n 0) =
      ProbComp.eval (prfRealGame (eval generator) adversary n) := by
  let root := fun cache : Cache => (cache.lookup []).elim (uniformBits n) PMF.pure
  have hstep : ∀ query cache,
      (ProbComp.eval (frontierOracle generator n 0 query cache)).bind
        (fun (answer, cache') => (root cache').map (answer, ·)) =
      (root cache).bind (fun seed =>
        (PMF.pure (prfOracle (eval generator) n seed query)).map (·, seed)) := by
    intro query cache
    by_cases hquery : query.length = n <;> cases hcache : cache.lookup [] <;>
      simp [frontierOracle, memoize, root, hquery, hcache, ProbComp.eval,
        prfOracle, PMF.map, Function.comp_def]
  have h := OracleComp.runState_simulation
    (fun query cache => ProbComp.eval (frontierOracle generator n 0 query cache))
    (fun query seed => (PMF.pure (prfOracle (eval generator) n seed query)).map (·, seed))
    root hstep (adversary n []) []
  simp only [OracleComp.runState_readOnly] at h
  have houtput := congrArg (PMF.map Prod.fst) h
  simpa [hybridGame, prfRealGame, ProbComp.eval, OracleComp.eval_simulateState,
    OracleComp.eval_simulate, root, PMF.map, Function.comp_def] using houtput

/-- The final level caches full query answers directly. There is no suffix left to evaluate. -/
theorem frontierOracle_self (generator : Word → Word) (n : ℕ) (query : Word) (cache : Cache) :
    frontierOracle generator n n query cache =
      if query.length = n then memoize (fun _ : Word => OracleComp.sampleBits n) query cache
      else pure ([], cache) := by
  by_cases h : query.length = n
  · simp [frontierOracle, ← h]
  · simp [frontierOracle, h]

/-- At the final level, the prefix hybrid is exactly the ideal PRF game. -/
theorem hybridGame_self (generator : Word → Word) (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (hybridGame generator adversary n n) =
      ProbComp.eval (prfIdealGame adversary n) := by
  have horacle : frontierOracle generator n n = cachedRandomFunctionOracle n := by
    funext query cache
    exact frontierOracle_self generator n query cache
  simp only [hybridGame, horacle, prfIdealGame_eq_cached]

/-- A local invariant and exact storage-growth bound for each prefix-oracle call.
Only cached label widths are constrained; key lengths and duplicate cache keys are unrestricted. -/
theorem frontierOracle_bounds (generator : Word → Word) (n depth : ℕ) (query : Word)
    (cache : Cache) (hcache : ∀ entry ∈ cache, entry.2.length ≤ n) (result : Word × Cache)
    (hresult : result ∈ (ProbComp.eval (frontierOracle generator n depth query cache)).support) :
    (∀ entry ∈ result.2, entry.2.length ≤ n) ∧ result.1.length ≤ n ∧
      (cacheEncoding result.2).length ≤
        (cacheEncoding cache).length + 4 * query.length + 2 * n + 3 := by
  by_cases hquery : query.length = n
  · simp only [frontierOracle, hquery, ite_true, ProbComp.eval_bind,
      PMF.mem_support_bind_iff] at hresult
    obtain ⟨⟨seed, cache'⟩, hseed, hresult⟩ := hresult
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    have hsample : (seed, cache') ∈
        (memoize (fun _ : Word => uniformBits n) (query.take depth) cache).support := by
      simpa only [ProbComp.eval, OracleComp.eval_memoize, OracleComp.eval_sampleBits] using hseed
    obtain ⟨hwidth, hcache', hsize⟩ := memoize_call_size_le wordEncoding wordEncoding
      (fun _ : Word => uniformBits n) (query.take depth) cache n hcache
      (fun _ hvalue => (length_of_mem_support_uniformBits hvalue).le) (seed, cache') hsample
    refine ⟨hcache', (length_eval_le _ _ _).trans hwidth, ?_⟩
    change (cacheEncoding cache').length ≤ (cacheEncoding cache).length +
      4 * (query.take depth).length + 2 * n + 3 at hsize
    simp only [List.length_take] at hsize
    dsimp
    lia
  · simp only [frontierOracle, hquery, ite_false, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨hcache, by simp, by dsimp; lia⟩

/-- One prefix-oracle call is ordinary certified probabilistic code, with all inputs captured. -/
theorem isPPTOn_frontierOracle {generator : Word → Word}
    (hgenerator : IsPolyTime wordEncoding generator) :
    IsPPTOn (pairEncoding (pairEncoding unaryEncoding unaryEncoding)
      (pairEncoding wordEncoding cacheEncoding)) (pairEncoding wordEncoding cacheEncoding)
      (fun pair => frontierOracle generator pair.1.1 pair.1.2 pair.2.1 pair.2.2) := by
  have heval := isPolyTime_eval hgenerator
  unfold frontierOracle cacheEncoding
  ppt

/-- A uniform adversary's complete adaptive prefix game is PPT, uniformly over the chosen level.
The proof combines the one-call program certificate with its local storage invariant. -/
theorem isPPTOn_hybridGame {generator : Word → Word}
    (hgenerator : IsPolyTime wordEncoding generator) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT boolEncoding adversary) :
    IsPPTOn (pairEncoding unaryEncoding unaryEncoding) boolEncoding
      (fun pair => hybridGame generator adversary pair.1 pair.2) := by
  have hhandler := isPPTOn_frontierOracle hgenerator
  have hrun : IsPPTOn (pairEncoding unaryEncoding unaryEncoding)
      (pairEncoding boolEncoding cacheEncoding) (fun pair =>
        OracleComp.simulateState (frontierOracle generator pair.1 pair.2)
          (adversary pair.1 []) []) := by
    refine hadversary.simulateState_preprocess
      (input := pairEncoding unaryEncoding unaryEncoding) (prepare := fun pair => (pair.1, []))
      (by polytime) hhandler (isPolyTime_const _ [])
      (fun pair cache => ∀ entry ∈ cache, entry.2.length ≤ pair.1) (by simp)
      (resources := fun pair query => 4 * query.length + 2 * pair.1 + 3) (by polytime) ?_
    intro pair query cache hcache result hresult
    obtain ⟨hcache', hreply, hgrowth⟩ :=
      frontierOracle_bounds generator pair.1 pair.2 query cache hcache result hresult
    exact ⟨hcache', by lia, by lia⟩
  exact hrun.map (isPolyTime_fst boolEncoding cacheEncoding)

end Cslib.Crypto.GGM
