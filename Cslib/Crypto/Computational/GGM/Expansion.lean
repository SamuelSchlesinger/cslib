/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.GGM.Hybrid

/-!
# Cached expansions between adjacent GGM levels

The oracle caches one expansion per queried parent prefix. Its sampler is a parameter: generator
outputs reproduce the earlier prefix hybrid, while independent random child labels give the
next hybrid. Only the first two labels of an expansion are retained.

The generated case is a change of cache representation, from root labels to their expansions.
The proof uses the shared invariant-based stateful simulation rule. The uniform case uses the
eager/lazy law and a bijective regrouping of random tree labels. Both identities hold for arbitrary
adaptive adversaries. The complete expansion game has a uniform PPT certificate when its sampler
does. `GGM.Reduction` converts these repeated sampler calls into a single-challenge PRG reduction.

## References

O. Goldreich, S. Goldwasser, S. Micali,
[*How to Construct Random Functions*](https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf),
Section 3.3, the simulation used in the proof of Theorem 3.
-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Probability

/-- Cache a sampled expansion at each parent prefix and follow its selected child. -/
noncomputable def expansionOracle (generator : Word → Word) (sample : ProbComp Word)
    (n depth : ℕ) (query : Word) : StateT Cache ProbComp Word := fun cache =>
  if query.length = n then do
    let (expansion, cache') ← memoize (fun _ : Word => List.take (2 * n) <$> sample)
      (query.take depth) cache
    return (eval generator (selectChild n expansion (query[depth]?.getD false))
      (query.drop (depth + 1)), cache')
  else pure ([], cache)

/-- Run the adversary using sampled, cached expansions at the selected level. -/
noncomputable def expansionGame (generator : Word → Word) (sample : ProbComp Word)
    (adversary : OracleDistinguisher) (n depth : ℕ) : ProbComp Bool :=
  Prod.fst <$> OracleComp.simulateState (expansionOracle generator sample n depth)
    (adversary n []) []

private def expandCache (generator : Word → Word) (n : ℕ) (cache : Cache) : Cache :=
  cache.map (fun entry => (entry.1, (generator entry.2).take (2 * n)))

private theorem frontierOracle_preserves_labels (generator : Word → Word) (n depth : ℕ)
    (query : Word) (cache : Cache) (hcache : ∀ entry ∈ cache, entry.2.length = n)
    (answer : Word) (cache' : Cache)
    (hresult : (answer, cache') ∈
      (ProbComp.eval (frontierOracle generator n depth query cache)).support) :
    ∀ entry ∈ cache', entry.2.length = n := by
  by_cases hquery : query.length = n
  · simp only [frontierOracle, hquery, ite_true, ProbComp.eval_bind,
      PMF.mem_support_bind_iff] at hresult
    obtain ⟨⟨seed, next⟩, hseed, hresult⟩ := hresult
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hresult
    rw [hresult.2]
    have hsample : (seed, next) ∈
        (memoize (fun _ : Word => uniformBits n) (query.take depth) cache).support := by
      simpa only [ProbComp.eval, OracleComp.eval_memoize, OracleComp.eval_sampleBits] using hseed
    exact (RandomOracle.memoize_invariant (fun _ : Word => uniformBits n)
      (fun _ seed => seed.length = n) (query.take depth) cache hcache
      (fun _ h => length_of_mem_support_uniformBits h) (seed, next) hsample).2
  · simp only [frontierOracle, hquery, ite_false, ProbComp.eval_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hresult
    simpa only [hresult.2] using hcache

private theorem expansionOracle_generated_step (generator : Word → Word) (n depth : ℕ)
    (hdepth : depth < n) (query : Word) (cache : Cache)
    (hcache : ∀ entry ∈ cache, entry.2.length = n) :
    (ProbComp.eval (frontierOracle generator n depth query cache)).map
      (fun result => (result.1, expandCache generator n result.2)) =
      ProbComp.eval (expansionOracle generator (generator <$> OracleComp.sampleBits n) n depth
        query (expandCache generator n cache)) := by
  by_cases hquery : query.length = n
  · have hmap := memoize_map (m := PMF) (Function.Embedding.refl Word)
      (fun seed => (generator seed).take (2 * n)) (fun _ : Word => uniformBits n)
      (fun _ : Word => (uniformBits n).map (fun seed => (generator seed).take (2 * n)))
      (fun _ => rfl) (query.take depth) cache
    simp only [PMF.monad_map_eq_map, Function.Embedding.refl_apply] at hmap
    simp only [frontierOracle, expansionOracle, hquery, ite_true, ProbComp.eval,
      OracleComp.eval_bind, OracleComp.eval_pure, OracleComp.eval_memoize, OracleComp.eval_map,
      OracleComp.eval_sampleBits, PMF.map_comp, Function.comp_def]
    rw [show expandCache generator n cache =
      cache.map (fun entry => (entry.1, (generator entry.2).take (2 * n))) from rfl, ← hmap]
    simp only [PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def]
    apply Probability.PMF.bind_congr_on_support
    rintro ⟨seed, next⟩ hseed
    have hlength := (RandomOracle.memoize_invariant (fun _ : Word => uniformBits n)
      (fun _ seed => seed.length = n) (query.take depth) cache hcache
      (fun _ h => length_of_mem_support_uniformBits h) (seed, next) hseed).1
    simp only [selectChild_take, ← hlength,
      eval_drop_succ generator seed query depth (by lia), child, expandCache]
  · simp [frontierOracle, expansionOracle, hquery, PMF.pure_map]

/-- Sampling generator expansions reproduces the earlier prefix hybrid for every adaptive
adversary. No security assumption on the generator is needed for this exact identity. -/
theorem expansionGame_generated (generator : Word → Word) (adversary : OracleDistinguisher)
    (n depth : ℕ) (hdepth : depth < n) :
    ProbComp.eval (expansionGame generator (generator <$> OracleComp.sampleBits n)
      adversary n depth) = ProbComp.eval (hybridGame generator adversary n depth) := by
  have h := OracleComp.runState_map_state_of_invariant
    (fun query cache => ProbComp.eval (frontierOracle generator n depth query cache))
    (fun query cache => ProbComp.eval
      (expansionOracle generator (generator <$> OracleComp.sampleBits n) n depth query cache))
    (expandCache generator n) (fun cache => ∀ entry ∈ cache, entry.2.length = n)
    (frontierOracle_preserves_labels generator n depth)
    (expansionOracle_generated_step generator n depth hdepth) (adversary n []) [] (by simp)
  have houtput := congrArg (PMF.map Prod.fst) h
  simpa [expansionGame, hybridGame, ProbComp.eval, OracleComp.eval_simulateState,
    expandCache, PMF.map_comp, Function.comp_def] using houtput.symm

private theorem prefix_eager (n depth width : ℕ) (hdepth : depth ≤ n)
    (respond : Word → Word → Word) (program : OracleComp Word (fun _ => Word) Bool) :
    (PMF.uniformOfFintype (BitString depth → BitString width)).bind (fun table =>
      OracleComp.eval (fun query => PMF.pure (if query.length = n then
        respond query (List.ofFn (table (wordBits depth (query.take depth)))) else [])) program) =
      (OracleComp.runState (fun query cache => if query.length = n then
        (memoize (fun _ : Word => uniformBits width) (query.take depth) cache).map
          (fun (value, next) => (respond query value, next))
        else PMF.pure ([], cache)) program []).map Prod.fst := by
  let adapter := fun query : Word =>
    if query.length = n then
      (respond query) <$> (OracleComp.query (wordBits depth (query.take depth)) :
        OracleComp (BitString depth) (fun _ => Word) Word)
    else pure []
  have h := RandomOracle.eval_eq_memoize_map
    (⟨List.ofFn, List.ofFn_injective⟩ : BitString depth ↪ Word) List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString width)) (fun _ => uniformBits width)
    (fun _ => rfl) (OracleComp.simulate adapter program)
  have hstep (query : Word) :
      OracleComp.runState (fun key => memoize (fun _ : Word => uniformBits width) (List.ofFn key))
        (adapter query) = fun cache => if query.length = n then
          (memoize (fun _ : Word => uniformBits width) (query.take depth) cache).map
            (fun (value, next) => (respond query value, next)) else PMF.pure ([], cache) := by
    funext cache
    by_cases hquery : query.length = n
    · have hprefix : List.ofFn (wordBits depth (query.take depth)) = query.take depth :=
        ofFn_wordBits (by simp [List.length_take, hquery, Nat.min_eq_left hdepth])
      simp only [adapter, hquery, ite_true, OracleComp.runState_map,
        OracleComp.runState_query, hprefix]
    · simp [adapter, hquery]
  have heval (table : BitString depth → BitString width) (query : Word) :
      OracleComp.eval (fun key => PMF.pure (List.ofFn (table key))) (adapter query) =
        PMF.pure (if query.length = n then
          respond query (List.ofFn (table (wordBits depth (query.take depth)))) else []) := by
    by_cases hquery : query.length = n <;> simp [adapter, hquery, PMF.pure_map]
  simpa only [PMF.pi_uniformOfFintype, OracleComp.eval_simulate,
    OracleComp.runState_simulate, Function.Embedding.coeFn_mk, hstep, heval] using h

private def childrenEquiv (n : ℕ) : BitString (2 * n) ≃ (Bool → BitString n) :=
  (maskEquiv 2 n).trans (Equiv.arrowCongr finTwoEquiv (Equiv.refl (BitString n)))

private theorem selectChild_ofFn (n : ℕ) (expansion : BitString (2 * n)) (bit : Bool) :
    selectChild n (List.ofFn expansion) bit = List.ofFn (childrenEquiv n expansion bit) := by
  have h := ofFn_maskEquiv_symm (maskEquiv 2 n expansion)
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  cases bit <;>
    simp [childrenEquiv, selectChild, List.ofFn_succ, finTwoEquiv]

private def childIndexEquiv (depth : ℕ) : BitString (depth + 1) ≃ (BitString depth × Bool) :=
  (Fin.snocEquiv (fun _ : Fin (depth + 1) => Bool)).symm.trans (Equiv.prodComm _ _)

private def childTableEquiv (n depth : ℕ) :
    (BitString depth → BitString (2 * n)) ≃ (BitString (depth + 1) → BitString n) :=
  ((Equiv.piCongrRight (fun _ : BitString depth => childrenEquiv n)).trans
    (Equiv.curry (BitString depth) Bool (BitString n)).symm).trans
      (Equiv.arrowCongr (childIndexEquiv depth).symm (Equiv.refl (BitString n)))

private theorem childTableEquiv_apply (n depth : ℕ) (table : BitString depth → BitString (2 * n))
    (query : BitString (depth + 1)) :
    childTableEquiv n depth table query =
      childrenEquiv n (table (Fin.init query)) (query (Fin.last depth)) := rfl

private theorem ofFn_childTable (n depth : ℕ) (table : BitString depth → BitString (2 * n))
    (query : Word) :
    List.ofFn (childTableEquiv n depth table (wordBits (depth + 1) (query.take (depth + 1)))) =
      selectChild n (List.ofFn (table (wordBits depth (query.take depth))))
        (query[depth]?.getD false) := by
  rw [childTableEquiv_apply, selectChild_ofFn]
  have hprefix : Fin.init (wordBits (depth + 1) (query.take (depth + 1))) =
      wordBits depth (query.take depth) := by
    funext i
    simp [Fin.init, wordBits, i.isLt, show i.val < depth + 1 by lia]
  simp [hprefix, wordBits]

/-- Uniform expansions give the next prefix hybrid: the two independent children of each
parent are exactly the independent labels at the next level. Lazy sampling preserves this law
under repeated and adaptive queries. -/
theorem expansionGame_uniform (generator : Word → Word) (adversary : OracleDistinguisher)
    (n depth : ℕ) (hdepth : depth < n) :
    ProbComp.eval (expansionGame generator (OracleComp.sampleBits (2 * n)) adversary n depth) =
      ProbComp.eval (hybridGame generator adversary n (depth + 1)) := by
  let earlier := fun table : BitString depth → BitString (2 * n) =>
    OracleComp.eval (fun query => PMF.pure (if query.length = n then
      eval generator (selectChild n (List.ofFn (table (wordBits depth (query.take depth))))
        (query[depth]?.getD false)) (query.drop (depth + 1)) else [])) (adversary n [])
  let later := fun table : BitString (depth + 1) → BitString n =>
    OracleComp.eval (fun query => PMF.pure (if query.length = n then
      eval generator (List.ofFn (table (wordBits (depth + 1) (query.take (depth + 1)))))
        (query.drop (depth + 1)) else [])) (adversary n [])
  have hearlier := prefix_eager n depth (2 * n) hdepth.le
    (fun query expansion => eval generator (selectChild n expansion (query[depth]?.getD false))
      (query.drop (depth + 1))) (adversary n [])
  have hlater := prefix_eager n (depth + 1) n (by lia)
    (fun query seed => eval generator seed (query.drop (depth + 1))) (adversary n [])
  calc
    _ = (PMF.uniformOfFintype (BitString depth → BitString (2 * n))).bind earlier := by
      dsimp only [earlier]
      rw [hearlier]
      simp only [expansionGame, ProbComp.eval, OracleComp.eval_map,
        OracleComp.eval_simulateState]
      congr 2
      funext query cache
      by_cases hquery : query.length = n
      · simp only [expansionOracle, hquery, ite_true, OracleComp.eval_bind,
          OracleComp.eval_memoize, OracleComp.eval_map, OracleComp.eval_sampleBits,
          uniformBits_take (Nat.le_refl (2 * n)), OracleComp.eval_pure]
        rfl
      · simp [expansionOracle, hquery]
    _ = (PMF.uniformOfFintype (BitString (depth + 1) → BitString n)).bind later := by
      rw [← PMF.uniformOfFintype_map_equiv (childTableEquiv n depth), PMF.bind_map]
      simp only [earlier, later, Function.comp_def, ofFn_childTable]
    _ = _ := by
      dsimp only [later]
      rw [hlater]
      simp only [hybridGame, ProbComp.eval, OracleComp.eval_map,
        OracleComp.eval_simulateState]
      congr 2
      funext query cache
      by_cases hquery : query.length = n <;>
        simp [frontierOracle, hquery, OracleComp.eval_memoize, PMF.map, Function.comp_def]

/-- Expansion handlers compose an arbitrary certified sampler with ordinary cache and tree code.
The width, level, and sampler can all depend on the caller's captured input. -/
theorem isPPTOn_expansionOracle {Caller : Type} {input : Caller ↪ Word}
    {generator : Word → Word} (hgenerator : IsPolyTime wordEncoding generator)
    {sample : Caller → ProbComp Word} {width depth : Caller → ℕ}
    (hsample : IsPPTOn input wordEncoding sample)
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (hdepth : IsPolyTime input (fun a => unaryEncoding (depth a))) :
    IsPPTOn (pairEncoding input (pairEncoding wordEncoding cacheEncoding))
      (pairEncoding wordEncoding cacheEncoding) (fun pair =>
        expansionOracle generator (sample pair.1) (width pair.1) (depth pair.1)
          pair.2.1 pair.2.2) := by
  have heval := isPolyTime_eval hgenerator
  unfold expansionOracle cacheEncoding
  ppt

/-- A cached expansion uses at most two labels of storage. The sampled word may have any length;
truncation bounds the stored value and selected child even on malformed challenges. -/
theorem expansionOracle_bounds (generator : Word → Word) (sample : ProbComp Word)
    (n depth : ℕ) (query : Word) (cache : Cache)
    (hcache : ∀ entry ∈ cache, entry.2.length ≤ 2 * n) (result : Word × Cache)
    (hresult : result ∈ (ProbComp.eval
      (expansionOracle generator sample n depth query cache)).support) :
    (∀ entry ∈ result.2, entry.2.length ≤ 2 * n) ∧ result.1.length ≤ n ∧
      (cacheEncoding result.2).length ≤
        (cacheEncoding cache).length + 4 * query.length + 4 * n + 3 := by
  by_cases hquery : query.length = n
  · simp only [expansionOracle, hquery, ite_true, ProbComp.eval_bind,
      PMF.mem_support_bind_iff] at hresult
    obtain ⟨⟨expansion, next⟩, hsample, hresult⟩ := hresult
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    have hvalues : ∀ value ∈ ((ProbComp.eval sample).map (List.take (2 * n))).support,
        value.length ≤ 2 * n := by
      intro value hvalue
      obtain ⟨word, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hvalue
      simp
    have hsample' : (expansion, next) ∈ (memoize
        (fun _ : Word => (ProbComp.eval sample).map (List.take (2 * n)))
        (query.take depth) cache).support := by
      simpa only [ProbComp.eval, OracleComp.eval_memoize, OracleComp.eval_map] using hsample
    obtain ⟨_, hcache', hgrowth⟩ := memoize_call_size_le wordEncoding wordEncoding
      (fun _ : Word => (ProbComp.eval sample).map (List.take (2 * n)))
      (query.take depth) cache (2 * n) hcache hvalues (expansion, next) hsample'
    refine ⟨hcache', (length_eval_le ..).trans (length_selectChild_le ..), ?_⟩
    change (cacheEncoding next).length ≤ (cacheEncoding cache).length +
      4 * (query.take depth).length + 2 * (2 * n) + 3 at hgrowth
    simp only [List.length_take] at hgrowth
    dsimp
    lia
  · simp only [expansionOracle, hquery, ite_false, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨hcache, by simp, by dsimp; lia⟩

/-- A complete adaptive expansion game is PPT, uniformly in its captured parameters and sampler.
The machine clock and all cache-growth accounting follow from the public local contracts. -/
theorem isPPTOn_expansionGame {Caller : Type} {input : Caller ↪ Word}
    {generator : Word → Word} (hgenerator : IsPolyTime wordEncoding generator)
    {sample : Caller → ProbComp Word} {width depth : Caller → ℕ}
    (hsample : IsPPTOn input wordEncoding sample)
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (hdepth : IsPolyTime input (fun a => unaryEncoding (depth a)))
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT boolEncoding adversary) :
    IsPPTOn input boolEncoding
      (fun a => expansionGame generator (sample a) adversary (width a) (depth a)) := by
  have hhandler := isPPTOn_expansionOracle hgenerator hsample hwidth hdepth
  have hrun : IsPPTOn input (pairEncoding boolEncoding cacheEncoding) (fun a =>
      OracleComp.simulateState (expansionOracle generator (sample a) (width a) (depth a))
        (adversary (width a) []) []) := by
    refine hadversary.simulateState_preprocess
      (input := input) (prepare := fun a => (width a, [])) (by polytime) hhandler
      (isPolyTime_const _ []) (fun a cache => ∀ entry ∈ cache, entry.2.length ≤ 2 * width a)
      (by simp) (resources := fun a query => 4 * query.length + 4 * width a + 3)
      (by polytime) ?_
    intro a query cache hcache result hresult
    obtain ⟨hcache', hreply, hgrowth⟩ :=
      expansionOracle_bounds generator (sample a) (width a) (depth a) query cache hcache
        result hresult
    exact ⟨hcache', by lia, by lia⟩
  exact hrun.map (isPolyTime_fst boolEncoding cacheEncoding)

end Cslib.Crypto.GGM
