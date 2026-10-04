/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Oracle
public import Cslib.Computability.Probabilistic.Realization.OracleSimulation

/-!
# Efficient stateful interpretation of oracle programs

A certified oracle adversary can be run against an ordinary stateful PPT handler. A local
invariant bounds the reply length and the amount of private storage added by each call. The
result is a closed PPT program returning both the adversary's result and the final handler state.

The adversary's machine, clock, configurations and query bounds are internal to the proof.
Polynomially many individually efficient calls are insufficient without a storage bound: a
handler that doubles its state on every call would violate the bounded-growth hypothesis.
-/

@[expose] public section

namespace Cslib.Probability

/-- Run an oracle program with a stateful handler whose local resource allowance is efficiently
computed from the caller and request. The allowance bounds both reply length and added storage;
the polynomial clock is derived internally. -/
theorem IsOraclePPTOn.simulateState_preprocess {Operation α β Caller State : Type}
    [DecidableEq Operation] [Finite Operation]
    {source : α → Word} {input : Caller ↪ Word} {output : β ↪ Word} {stateEncoding : State ↪ Word}
    {program : α → WordOracleComp Operation β}
    {handler : Caller → Operation × Word → State → ProbComp (Word × State)}
    {prepare : Caller → α} {initial : Caller → State} {resources : Caller → Word → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : IsPolyTime input (fun a => source (prepare a)))
    (hhandler : IsPPTOn
      (pairEncoding input (pairEncoding (pairEncoding (finiteEncoding Operation) wordEncoding)
        stateEncoding)) (pairEncoding wordEncoding stateEncoding)
      (fun pair => handler pair.1 pair.2.1 pair.2.2))
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : IsPolyTime (pairEncoding input wordEncoding)
      (fun pair => unaryEncoding (resources pair.1 pair.2)))
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ (ProbComp.eval (handler a request state)).support,
        invariant a result.2 ∧ result.1.length ≤ resources a request.2 ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a request.2) :
    IsPPTOn input (pairEncoding output stateEncoding) (fun a =>
      OracleComp.simulateState (handler a) (program (prepare a)) (initial a)) := by
  obtain ⟨resourceCoeff, resourceDegree, hbound⟩ := hresources.length_le
  let allowance := fun size => resourceCoeff * (2 * size + 2) ^ resourceDegree
  have hallowance : PolynomiallyBounded allowance := by unfold allowance; fun_prop
  have hbound' (a : Caller) (query : Word) :
      resources a query ≤ allowance ((input a).length + query.length) := by
    have h := hbound (a, query)
    simp only [unaryEncoding_apply, List.length_replicate, length_pairEncoding,
      wordEncoding, Function.Embedding.refl_apply] at h
    exact h.trans (by dsimp [allowance]; gcongr resourceCoeff * ?_ ^ resourceDegree; lia)
  obtain ⟨_, k, Control, hfinite, machine, c, d, hrealize⟩ := hprogram
  let _ := hfinite
  have hcount : IsPolyTime input
      (fun a => unaryEncoding (c * ((source (prepare a)).length + 1) ^ d)) := by
    polytime
  have hrun := OracleSimulation.isPPTOn_run machine hprepare hcount hhandler hinitial
    invariant hinit hallowance (fun a request state hstate result hresult => by
      obtain ⟨hstate', hreply, hgrowth⟩ := hpreserve a request state hstate result hresult
      exact ⟨hstate', hreply.trans (hbound' a request.2),
        hgrowth.trans (Nat.add_le_add_left (hbound' a request.2) _)⟩)
  apply IsPPTOn.of_encoded
  refine hrun.encoded.congr ?_
  intro a
  have h := hrealize (prepare a) State
    (fun request state => ProbComp.eval (handler a request state)) (initial a)
  rw [OracleComp.runState_map] at h
  simpa only [ProbComp.eval, OracleComp.eval_map, OracleComp.eval_simulateState, PMF.map_comp,
    Function.comp_def, pairEncoding, wordEncoding, Function.Embedding.coeFn_mk,
    Function.Embedding.refl_apply] using
      congrArg (PMF.map (pairEncoding wordEncoding stateEncoding)) h.symm

/-- Prepare a cryptographic adversary's input and supply a closed stateful handler. The handler
may capture the caller's challenge. Its invariant and efficiently computed resource allowance
certify the full interaction, including the returned private state. -/
theorem IsOraclePPT.simulateState_preprocess {β Caller State : Type}
    {input : Caller ↪ Word} {output : β ↪ Word} {stateEncoding : State ↪ Word}
    {program : ℕ → Word → OracleComp Word (fun _ => Word) β}
    {handler : Caller → Word → State → ProbComp (Word × State)}
    {prepare : Caller → ℕ × Word} {initial : Caller → State} {resources : Caller → Word → ℕ}
    (hprogram : IsOraclePPT output program)
    (hprepare : IsPolyTime input (fun a => parameterEncoding (prepare a)))
    (hhandler : IsPPTOn (pairEncoding input (pairEncoding wordEncoding stateEncoding))
      (pairEncoding wordEncoding stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2))
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : IsPolyTime (pairEncoding input wordEncoding)
      (fun pair => unaryEncoding (resources pair.1 pair.2)))
    (hpreserve : ∀ a query state, invariant a state →
      ∀ result ∈ (ProbComp.eval (handler a query state)).support,
        invariant a result.2 ∧ result.1.length ≤ resources a query ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a query) :
    IsPPTOn input (pairEncoding output stateEncoding) (fun a =>
      OracleComp.simulateState (handler a)
        (program (prepare a).1 (prepare a).2) (initial a)) := by
  have hcaller := isPolyTime_input (pairEncoding input
    (pairEncoding (pairEncoding (finiteEncoding Unit) wordEncoding) stateEncoding))
  have h := hprogram.on.simulateState_preprocess hprepare
    (hhandler.preprocess (hcaller.fst.pair (hcaller.snd.fst.snd.pair hcaller.snd.snd)))
    hinitial invariant hinit hresources (fun a request => hpreserve a request.2)
  refine h.congr ?_
  intro a
  simp only [ProbComp.eval, OracleComp.eval_simulateState, runState_singleOperation]

end Cslib.Probability
