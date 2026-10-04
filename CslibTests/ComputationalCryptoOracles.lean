/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

-- The simulation, query-bound and tree-evaluation checks are anonymous examples.
import Cslib.Computability.Probabilistic.OracleSimulation -- shake: keep
import Cslib.Computability.Probabilistic.QueryBounds -- shake: keep
import Cslib.Crypto.Computational.GGM.Reduction -- shake: keep
import Cslib.Tactic.PPT -- shake: keep
public import Cslib.Foundations.Control.Monad.Memoize
public import Cslib.Tactic.PolyTime
public import Cslib.Languages.Probabilistic.BitString

/-!
# Programming cached probabilistic reductions

These examples exercise captured sampling parameters, two successive calls, and the returned
cache. Their PPT proofs contain no machine representation. Eager/lazy equivalence applies to
the same memoization combinator used by the programs. The final examples certify complete
adaptive interactions with arbitrary PPT oracle adversaries.
-/

@[expose] public section

namespace CslibTests.ComputationalCryptoOracles

open Cslib Cslib.Probability

abbrev Cache := List (Word × Word)

def cacheEncoding : Cache ↪ Word := listEncoding (pairEncoding wordEncoding wordEncoding)

def inputEncoding : (ℕ × Word × Cache) ↪ Word :=
  pairEncoding unaryEncoding (pairEncoding wordEncoding cacheEncoding)

/-- The width, query, and existing cache are ordinary runtime inputs. -/
noncomputable def cachedWord (input : ℕ × Word × Cache) : ProbComp (Word × Cache) :=
  memoize (fun _ => OracleComp.sampleBits input.1) input.2.1 input.2.2

example : IsPPTOn inputEncoding (pairEncoding wordEncoding cacheEncoding) cachedWord := by
  unfold cachedWord inputEncoding cacheEncoding
  ppt

/-- A reduction can keep its inputs while passing the updated cache to its next call. -/
noncomputable def twoCalls (input : ℕ × Word × Cache) : ProbComp ((Word × Word) × Cache) := do
  let (first, cache) ← cachedWord input
  let (second, cache') ← memoize (fun _ => OracleComp.sampleBits input.1) input.2.1 cache
  pure ((first, second), cache')

example : IsPPTOn inputEncoding
    (pairEncoding (pairEncoding wordEncoding wordEncoding) cacheEncoding) twoCalls := by
  unfold twoCalls cachedWord inputEncoding cacheEncoding
  ppt

/-- Repeated calls consume the sampling computation once and return identical answers. -/
example (input : ℕ × Word × Cache) :
    twoCalls input = (do
      let (value, cache) ← cachedWord input
      pure ((value, value), cache)) :=
  memoize_repeat _ _ _

/-- The second query depends on the first answer; the last query repeats the first. -/
def adaptiveBits : OracleComp Bool (fun _ => Bool) (Bool × Bool × Bool) := do
  let first ← OracleComp.query false
  let second ← OracleComp.query first
  let repeated ← OracleComp.query false
  pure (first, second, repeated)

/-- Saved samples follow the adaptive calls in order. The repeated query ignores its fresh
sample, preserving both the original answer and the final cache. -/
example :
    ProbComp.eval (OracleComp.simulateWithSamples false
      (fun value => memoize (fun _ : Bool => (pure value : ProbComp Bool)))
      adaptiveBits [] [true, false, false]) =
      PMF.pure ((true, false, true), [(true, false), (false, true)]) := by
  norm_num [OracleComp.simulateWithSamples, OracleComp.withSampleList, adaptiveBits,
    ProbComp.eval, memoize, List.lookup_cons]

/-- A cache hit still counts as a query. This interaction makes three calls but stores one entry. -/
example :
    OracleComp.runState (OracleComp.withTranscript
      (memoize (fun _ : Bool => PMF.pure false))) adaptiveBits ([], []) =
        PMF.pure ((false, false, false), [(false, false)],
          [⟨false, false⟩, ⟨false, false⟩, ⟨false, false⟩]) := by
  simp only [adaptiveBits, OracleComp.runState_bind, OracleComp.runState_query,
    OracleComp.runState_pure, OracleComp.withTranscript]
  simp [memoize, Bind.bind, Pure.pure, PMF.pure_map, Function.comp_def]

/-- The list cache and the eager table give the same complete observation. -/
example :
    ProbComp.eval (Prod.fst <$> OracleComp.simulateState
      (memoize (fun _ : Bool => (OracleComp.uniform Bool : ProbComp Bool))) adaptiveBits []) =
      (PMF.uniformOfFintype (Bool → Bool)).map
        (fun table => (table false, table (table false), table false)) := by
  rw [RandomOracle.eval_simulateState_memoize_eq_eager]
  simp [ProbComp.eval, OracleComp.uniform, PMF.pi_uniformOfFintype, adaptiveBits,
    PMF.map, Function.comp_def]

/-- A generator that copies its seed labels both children by that seed. This independently checks
the branch order and repeated tree traversal, without making a security claim. -/
example (seed query : Word) : Crypto.GGM.eval (fun seed => seed ++ seed) seed query = seed := by
  induction query with
  | nil => rfl
  | cons bit query ih =>
    cases bit <;> simpa [Crypto.GGM.eval_cons, Crypto.GGM.child, Crypto.GGM.selectChild] using ih

/-- Different leaves below the same cached prefix share its label. For the copying generator,
both replies are exactly that one uniform label, regardless of their different suffixes. -/
example :
    ProbComp.eval (Prod.fst <$> OracleComp.simulateState
      (Crypto.GGM.frontierOracle (fun seed => seed ++ seed) 2 1)
      (do
        let first ← OracleComp.query [false, false]
        let second ← OracleComp.query [false, true]
        pure (first, second)) []) =
      (uniformBits 2).map (fun seed => (seed, seed)) := by
  simp [ProbComp.eval, Crypto.GGM.frontierOracle, Crypto.GGM.child, Crypto.GGM.selectChild,
    memoize, PMF.map, Function.comp_def]

/-- The empty-width endpoint needs no expansion or security assumption on the generator. -/
example (generator : Word → Word) (adversary : Crypto.OracleDistinguisher) :
    ProbComp.eval (Crypto.prfRealGame (Crypto.GGM.eval generator) adversary 0) =
      ProbComp.eval (Crypto.prfIdealGame adversary 0) :=
  (Crypto.GGM.hybridGame_zero generator adversary 0).symm.trans
    (Crypto.GGM.hybridGame_self generator adversary 0)

/-- Two children drawn from one uniform expansion are independent. Revisiting the first child
returns its original label, even after observing its sibling. -/
example :
    ProbComp.eval (Prod.fst <$> OracleComp.simulateState
      (Crypto.GGM.expansionOracle (fun seed => seed ++ seed) (OracleComp.sampleBits 4) 2 1)
      (do
        let first ← OracleComp.query [false, false]
        let second ← OracleComp.query [false, true]
        let repeated ← OracleComp.query [false, false]
        pure (first, second, repeated)) []) =
      (uniformBits 2).bind (fun first => (uniformBits 2).map
        (fun second => (first, second, first))) := by
  calc
    _ = (uniformBits 4).bind (fun expansion =>
        PMF.pure (expansion.take 2, (expansion.drop 2).take 2, expansion.take 2)) := by
      norm_num [ProbComp.eval, Crypto.GGM.expansionOracle, Crypto.GGM.selectChild,
        memoize, PMF.map, Function.comp_def, List.take_take, List.drop_take]
    _ = _ := by
      rw [uniformBits_bind_split 2 2 (fun first second => PMF.pure (first, second.take 2, first))]
      apply PMF.bind_congr_on_support
      intro first _
      apply PMF.bind_congr_on_support
      intro second hsecond
      simp [← length_of_mem_support_uniformBits hsecond]

/-- A certified adversary interacting with an `n`-bit random oracle leaves a polynomial-size
encoded cache. The proof uses the public resource interfaces and exposes no machine witness.
This is a cache-size guarantee; efficient execution of the full simulation is a separate theorem. -/
example (adversary : ℕ → Word → OracleComp Word (fun _ => Word) Bool)
    (h : IsOraclePPT boolEncoding adversary) :
    ∃ bound : ℕ → ℕ, PolynomiallyBounded bound ∧ ∀ n result cache,
      (result, cache) ∈ (OracleComp.runState (memoize (fun _ : Word => uniformBits n))
        (adversary n []) []).support →
      (cacheEncoding cache).length ≤ bound n := by
  obtain ⟨c, d, hqueries⟩ := h.query_bounds
  refine ⟨fun n => c * (n + 2) ^ d * (4 * (c * (n + 2) ^ d) + 2 * n + 3),
    by fun_prop, ?_⟩
  intro n result cache hcache
  simpa [cacheEncoding] using memoize_cache_size_le wordEncoding wordEncoding
    (fun _ : Word => uniformBits n) (adversary n []) (c * (n + 2) ^ d) (c * (n + 2) ^ d) n
    (by simpa [wordEncoding] using hqueries n [])
    (fun _ _ _ hvalue => (length_of_mem_support_uniformBits hvalue).le)
      [] cache (by simp) result hcache

/-- An arbitrary PPT oracle adversary can be executed against a memoized `n`-bit random oracle.
The complete simulation, including lookup and the returned cache, is PPT. -/
example (adversary : ℕ → WordOracleComp Unit Bool)
    (h : IsOraclePPTOn unaryEncoding boolEncoding adversary) :
    IsPPTOn unaryEncoding (pairEncoding boolEncoding cacheEncoding) (fun n =>
      OracleComp.simulateState
        (fun request => memoize (fun _ : Word => OracleComp.sampleBits n) request.2)
        (adversary n) []) := by
  refine h.simulateState_preprocess (stateEncoding := cacheEncoding) (prepare := id) (by polytime)
    (by unfold cacheEncoding; ppt) (isPolyTime_const unaryEncoding [])
    (fun n cache => ∀ entry ∈ cache, entry.2.length ≤ n) (by simp)
    (resources := fun n query => 4 * query.length + 2 * n + 3) (by polytime) ?_
  intro n request cache hcache result hresult
  have hresult' : result ∈ (memoize (fun _ : Word => uniformBits n) request.2 cache).support := by
    simpa only [ProbComp.eval, OracleComp.eval_memoize, OracleComp.eval_sampleBits] using hresult
  obtain ⟨hvalue, hcache', hsize⟩ := memoize_call_size_le wordEncoding wordEncoding
    (fun _ : Word => uniformBits n) request.2 cache n hcache
    (fun _ hvalue => (length_of_mem_support_uniformBits hvalue).le) result hresult'
  change result.1.length ≤ n at hvalue
  change (cacheEncoding result.2).length ≤ (cacheEncoding cache).length +
    4 * request.2.length + 2 * n + 3 at hsize
  exact ⟨hcache', by lia, by lia⟩

/-- The standard adversary interface also supports a stateful handler directly. This one echoes
requests and counts every call, including repetitions. The unary counter's growth is charged. -/
example (adversary : ℕ → Word → OracleComp Word (fun _ => Word) Bool)
    (h : IsOraclePPT boolEncoding adversary) :
    IsPPT (pairEncoding boolEncoding unaryEncoding) (fun n auxiliary =>
      OracleComp.simulateState (fun query calls => pure (query, calls + 1))
        (adversary n auxiliary) 0) := by
  apply IsPPTOn.isPPT
  refine h.simulateState_preprocess (prepare := id) (by polytime)
    (by ppt) (isPolyTime_const parameterEncoding []) (fun _ _ => True) (by simp)
    (resources := fun _ query => query.length + 1) (by polytime) ?_
  intro pair query calls _ result hresult
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
  subst result
  simp only [unaryEncoding_apply, List.length_replicate, true_and]
  constructor <;> lia

/-- A reduction can capture its challenge in the handler while giving the adversary an empty
auxiliary input. Input preparation and all repeated challenge replies are charged. -/
example (adversary : ℕ → Word → OracleComp Word (fun _ => Word) Bool)
    (h : IsOraclePPT boolEncoding adversary) :
    IsPPT (pairEncoding boolEncoding unaryEncoding) (fun n challenge =>
      OracleComp.simulateState (fun _ calls => pure (challenge, calls + 1))
        (adversary n []) 0) := by
  have hrun : IsPPTOn parameterEncoding (pairEncoding boolEncoding unaryEncoding) (fun pair =>
      OracleComp.simulateState (fun _ calls => pure (pair.2, calls + 1))
        (adversary pair.1 []) 0) := by
    refine h.simulateState_preprocess
      (input := parameterEncoding) (prepare := fun pair => (pair.1, [])) (by polytime) (by ppt)
      (isPolyTime_const parameterEncoding []) (fun _ _ => True) (by simp)
      (resources := fun pair _ => pair.2.length + 1) (by polytime) ?_
    intro pair query calls _ result hresult
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    simp only [unaryEncoding_apply, List.length_replicate, true_and]
    constructor <;> lia
  exact hrun.isPPT

/-- Saved samples may use a typed encoding. The simulation handles an arbitrary supplied list,
including exhaustion, and retains the handler's call counter. -/
example (adversary : ℕ → Word → OracleComp Word (fun _ => Word) Bool)
    (h : IsOraclePPT boolEncoding adversary) :
    IsPPTOn (pairEncoding parameterEncoding (listEncoding boolEncoding))
      (pairEncoding boolEncoding unaryEncoding) (fun pair =>
        OracleComp.simulateWithSamples false (fun bit _ calls => pure ([bit], calls + 1))
          (adversary pair.1.1 pair.1.2) 0 pair.2) := by
  refine h.simulateWithSamples false (valueEncoding := boolEncoding) (prepare := Prod.fst)
    (by polytime) (by ppt) (isPolyTime_const _ []) (by polytime)
    (fun _ _ => True) (by simp) (resources := fun _ _ => 1) (by polytime) ?_
  intro pair bit query calls _ result hresult
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
  subst result
  simp [unaryEncoding_apply]

end CslibTests.ComputationalCryptoOracles
