/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.PseudorandomFunction
public import Cslib.Computability.Probabilistic.BitString
public import Cslib.Languages.Probabilistic.BitString

/-!
# A finite-list implementation of the PRF ideal oracle

Valid queries are memoized as ordinary words. Malformed queries receive the empty word and leave
the cache unchanged. Injective cache re-encoding and the generic eager/lazy theorem identify this
implementation with the ideal PRF game, for arbitrary adaptive adversaries.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- A word-valued random-function oracle, implemented by a finite association-list cache. -/
noncomputable def cachedRandomFunctionOracle (n : ℕ) (query : Word) :
    StateT (List (Word × Word)) ProbComp Word := fun cache =>
  if query.length = n then memoize (fun _ : Word => OracleComp.sampleBits n) query cache
  else pure ([], cache)

/-- The finite-list program gives exactly the ideal PRF experiment. It preserves consistency
under repeated adaptive queries and uses the same rejection rule for malformed inputs. -/
theorem prfIdealGame_eq_cached (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfIdealGame adversary n) =
      ProbComp.eval (Prod.fst <$> OracleComp.simulateState
        (cachedRandomFunctionOracle n) (adversary n []) []) := by
  let adapter := fun query : Word => if query.length = n then
    (OracleComp.query (wordBits n query) : OracleComp (BitString n) (fun _ => Word) Word)
    else pure []
  have h := RandomOracle.eval_eq_memoize_map
    (⟨List.ofFn, List.ofFn_injective⟩ : BitString n ↪ Word) List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString n)) (fun _ => uniformBits n)
    (fun _ => rfl) (OracleComp.simulate adapter (adversary n []))
  have hstep (query : Word) :
      OracleComp.runState (fun key => memoize (fun _ : Word => uniformBits n) (List.ofFn key))
        (adapter query) =
          fun cache => ProbComp.eval (cachedRandomFunctionOracle n query cache) := by
    funext cache
    by_cases hquery : query.length = n
    · simp [adapter, cachedRandomFunctionOracle, hquery, ofFn_wordBits hquery,
        ProbComp.eval, OracleComp.eval_memoize]
    · simp [adapter, cachedRandomFunctionOracle, hquery]
  have heval (table : BitString n → BitString n) (query : Word) :
      OracleComp.eval (fun key => PMF.pure (List.ofFn (table key))) (adapter query) =
        PMF.pure (randomFunctionOracle n table query) := by
    by_cases hquery : query.length = n
    · simp only [adapter, randomFunctionOracle, hquery, ite_true, OracleComp.eval_query]
      rfl
    · simp [adapter, randomFunctionOracle, hquery]
  simpa only [prfIdealGame, ProbComp.eval, OracleComp.eval_bind, OracleComp.uniform,
    OracleComp.eval_sample, OracleComp.eval_pure, OracleComp.eval_simulate, PMF.pi_uniformOfFintype,
    OracleComp.runState_simulate, OracleComp.eval_map, OracleComp.eval_simulateState,
    Function.Embedding.coeFn_mk, hstep, heval] using h

end Cslib.Crypto
