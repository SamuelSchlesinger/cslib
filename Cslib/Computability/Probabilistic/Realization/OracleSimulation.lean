/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Configuration
public import Cslib.Computability.Probabilistic.Sampling
public import Cslib.Computability.Probabilistic.Adaptive
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic.Finite
public import Cslib.Languages.Probabilistic.Simulation

/-!
# Implementing stateful oracle simulation

An interpreter step combines the shared native transition table with a certified closed handler.
All configuration operations use finite data and the ordinary programming certificates. This
module is internal to the efficiency proof; the handler is written as an ordinary stateful
probabilistic program.
-/

@[expose] public section

namespace Cslib.Probability.OracleSimulation

open _root_.Turing _root_.Turing.MultiTapeMachine

variable {k : ℕ} {Control Operation α State : Type} [DecidableEq Operation]

/-- Execute one native step while retaining the handler's private state. -/
noncomputable def step (machine : MultiTapePTM k Bool Control Operation)
    (handler : α → Operation × Word → State → ProbComp (Word × State)) (a : α)
    (pair : FiniteConfig k Bool Control Operation × State) :
    ProbComp (FiniteConfig k Bool Control Operation × State) :=
  match pair.1.tapes.state with
  | none => pure pair
  | some control => do
    let coin ← OracleComp.uniform Bool
    match machine.tr control pair.1.tapes.inputSymbol pair.1.tapes.workTapeSymbols
        pair.1.answerSymbols coin with
    | .step action symbol move => pure (pair.1.step action symbol move, pair.2)
    | .query channel next => do
      let (answer, state) ← handler a (channel, (pair.1.channels channel).1) pair.2
      return (pair.1.receive channel next answer, state)

/-- One interpreted step preserves the full finite configuration and the handler's local state. -/
theorem step_eq_simulateState (machine : MultiTapePTM k Bool Control Operation)
    (handler : α → Operation × Word → State → ProbComp (Word × State)) (a : α)
    (pair : FiniteConfig k Bool Control Operation × State) :
    step machine handler a pair = OracleComp.simulateState (handler a)
      (machine.finiteStep (fun op word => OracleComp.query (op, word)) pair.1) pair.2 := by
  cases hstate : pair.1.tapes.state with
  | none => simp [step, MultiTapePTM.finiteStep, hstate]
  | some control =>
    simp only [step, MultiTapePTM.finiteStep, hstate, OracleComp.simulateState_bind,
      OracleComp.uniform, OracleComp.simulateState_sample, bind_map_left]
    congr 1
    funext coin
    cases machine.tr control pair.1.tapes.inputSymbol pair.1.tapes.workTapeSymbols
        pair.1.answerSymbols coin <;> simp

variable [Finite Control]

/-- A single interpreter step is PPT whenever its complete stateful handler is PPT.
Captured input, requests, replies and private state are all charged by their encodings. -/
theorem isPPTOn_step [Fintype Operation] {input : α ↪ Word} {stateEncoding : State ↪ Word}
    (machine : MultiTapePTM k Bool Control Operation)
    {handler : α → Operation × Word → State → ProbComp (Word × State)}
    (hhandler : IsPPTOn
      (pairEncoding input (pairEncoding (pairEncoding (finiteEncoding Operation) wordEncoding)
        stateEncoding)) (pairEncoding wordEncoding stateEncoding)
      (fun pair => handler pair.1 pair.2.1 pair.2.2)) :
    IsPPTOn (pairEncoding input (pairEncoding finiteConfigEncoding stateEncoding))
      (pairEncoding finiteConfigEncoding stateEncoding)
      (fun pair => step machine handler pair.1 pair.2) := by
  let configuration : FiniteConfig k Bool Control Operation ↪ Word := finiteConfigEncoding
  let localState := pairEncoding configuration stateEncoding
  let caller := pairEncoding input localState
  have hcaller := isPolyTime_input caller
  have hcfg := hcaller.snd.fst
  unfold step
  apply IsPPTOn.finite_cases (branch := fun control pair => match control with
    | none => pure pair.2
    | some control => do
      let coin ← OracleComp.uniform Bool
      match machine.tr control pair.2.1.tapes.inputSymbol pair.2.1.tapes.workTapeSymbols
          pair.2.1.answerSymbols coin with
      | .step action symbol move => pure (pair.2.1.step action symbol move, pair.2.2)
      | .query channel next => do
        let (answer, state) ← handler pair.1 (channel, (pair.2.1.channels channel).1) pair.2.2
        return (pair.2.1.receive channel next answer, state))
    hcfg.finiteConfig_tapes.finiteCfg_state
  intro control
  cases control with
  | none => exact hcaller.snd.isPPTOn
  | some control =>
    apply (isPPTOn_uniformBool caller).bind_with
    let sampled := pairEncoding caller boolEncoding
    have hsampled := isPolyTime_input sampled
    have hc := hsampled.fst.snd.fst
    have htag := hc.finiteConfig_tapes.finiteCfg_inputSymbol.pair
      (hc.finiteConfig_tapes.finiteCfg_workTapeSymbols.pair
        (hc.finiteConfig_answerSymbols.pair hsampled.snd))
    apply IsPPTOn.finite_cases (branch := fun symbols pair =>
      match machine.tr control symbols.1 symbols.2.1 symbols.2.2.1 symbols.2.2.2 with
      | .step action symbol move => pure (pair.1.2.1.step action symbol move, pair.1.2.2)
      | .query channel next => do
        let (answer, state) ← handler pair.1.1 (channel, (pair.1.2.1.channels channel).1) pair.1.2.2
        return (pair.1.2.1.receive channel next answer, state)) htag
    rintro ⟨inputSymbol, workSymbols, answerSymbols, coin⟩
    cases machine.tr control inputSymbol workSymbols answerSymbols coin with
    | step action symbol move =>
      exact ((hc.finiteConfig_step action symbol move).pair hsampled.fst.snd.snd).isPPTOn
    | query channel next =>
      have hcall := hhandler.preprocess (hsampled.fst.fst.pair
        (((isPolyTime_const sampled (finiteEncoding Operation channel)).pair
          (hc.finiteConfig_channels.pi_apply channel).fst).pair hsampled.fst.snd.snd))
      apply hcall.bind_with
      have hresult := isPolyTime_input (pairEncoding sampled
        (pairEncoding wordEncoding stateEncoding))
      exact ((hresult.fst.fst.snd.fst.finiteConfig_receive hresult.snd.fst channel next).pair
        hresult.snd.snd).isPPTOn

/-- Interpret a bounded native run with a stateful PPT handler. A local invariant controls reply
sizes and the amount of private storage added per query; the loop compiler supplies the complete
PPT certificate, including the finite interpreter's storage. -/
theorem isPPTOn_run [Finite Operation] {input : α ↪ Word} {stateEncoding : State ↪ Word}
    (machine : MultiTapePTM k Bool Control Operation) {word : α → Word} {count : α → ℕ}
    {handler : α → Operation × Word → State → ProbComp (Word × State)} {initial : α → State}
    (hword : IsPolyTime input word) (hcount : IsPolyTime input (fun a => unaryEncoding (count a)))
    (hhandler : IsPPTOn
      (pairEncoding input (pairEncoding (pairEncoding (finiteEncoding Operation) wordEncoding)
        stateEncoding)) (pairEncoding wordEncoding stateEncoding)
      (fun pair => handler pair.1 pair.2.1 pair.2.2))
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (invariant : α → State → Prop) (hinit : ∀ a, invariant a (initial a))
    {resources : ℕ → ℕ} (hresources : PolynomiallyBounded resources)
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ (ProbComp.eval (handler a request state)).support,
        invariant a result.2 ∧
        result.1.length ≤ resources ((input a).length + request.2.length) ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length +
          resources ((input a).length + request.2.length)) :
    IsPPTOn input (pairEncoding wordEncoding stateEncoding) (fun a =>
      OracleComp.simulateState (handler a)
        (machine.run (fun op word => OracleComp.query (op, word)) (count a) (word a))
        (initial a)) := by
  let _ := Fintype.ofFinite Operation
  obtain ⟨cw, dw, hwordSize⟩ := hword.length_le
  obtain ⟨ct, dt, htime⟩ := hcount.length_le
  simp only [unaryEncoding_apply, List.length_replicate] at htime
  obtain ⟨ci, di, hinitialSize⟩ := hinitial.length_le
  obtain ⟨cr, dr, hresourceSize⟩ := hresources
  obtain ⟨cf, hconfigurationSize⟩ :=
    length_finiteConfigEncoding_le (k := k) (State := Control) (Oracle := Operation)
  let time (n : ℕ) := ct * (n + 1) ^ dt
  let budget (n : ℕ) := cr * (n + time n + 1) ^ dr
  let start (a : α) := (FiniteConfig.init (k := k) (Oracle := Operation)
    machine.initial (word a), initial a)
  let loopInvariant (a : α) (i : ℕ) (pair : FiniteConfig k Bool Control Operation × State) :=
    FiniteConfig.SpaceBound (word a).length i (budget (input a).length) pair.1 ∧
      invariant a pair.2 ∧ (stateEncoding pair.2).length ≤
        (stateEncoding (initial a)).length + i * budget (input a).length
  have hbudget (a : α) (word : Word) (hword : word.length ≤ count a) :
      resources ((input a).length + word.length) ≤ budget (input a).length :=
    (hresourceSize _).trans (Nat.mul_le_mul_left cr (Nat.pow_le_pow_left
      (by have := htime a; dsimp [time]; lia) dr))
  have hstart : IsPolyTime input (fun a => pairEncoding finiteConfigEncoding stateEncoding
      (start a)) := (hword.finiteConfig_init machine.initial).pair hinitial
  have hloop := (IsPPTOn.iterate_with_spec hstart hcount (isPPTOn_step machine hhandler)
    loopInvariant (fun a => ⟨FiniteConfig.spaceBound_init _ _ _, hinit a, by simp [start]⟩)
    (by
      rintro a i hi ⟨cfg, state⟩ ⟨hcfg, hs, hsize⟩ next hnext
      cases hcontrol : cfg.tapes.state with
      | none =>
        simp only [step, hcontrol, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
        subst next
        exact ⟨hcfg.mono le_rfl (Nat.le_succ i) le_rfl, hs, by
          dsimp at hsize ⊢
          nlinarith⟩
      | some control =>
        simp only [step, hcontrol, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hnext
        obtain ⟨coin, _, hnext⟩ := hnext
        cases haction : machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols coin with
        | step action symbol move =>
          simp only [haction, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
          subst next
          exact ⟨hcfg.step action symbol move, hs, by dsimp at hsize ⊢; nlinarith⟩
        | query channel control =>
          simp only [haction, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hnext
          obtain ⟨⟨answer, state'⟩, hanswer, hnext⟩ := hnext
          simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
          subst next
          obtain ⟨hs', hreply, hgrowth⟩ := hpreserve a _ state hs (answer, state') hanswer
          have hb := hbudget a (cfg.channels channel).1 ((hcfg.query channel).trans hi.le)
          exact ⟨hcfg.receive channel control answer (hreply.trans hb), hs', by
            dsimp at hsize hgrowth ⊢
            nlinarith⟩)
    (size := fun n => 2 * cf * (cw * (n + 1) ^ dw + time n + budget n + 1) + ci * (n + 1) ^ di +
      time n * budget n + 1) (by dsimp [time, budget]; fun_prop)
    (by
      rintro a i ⟨cfg, state⟩ hi ⟨hcfg, _, hstate⟩
      have ht : i ≤ time (input a).length := hi.trans (htime a)
      have hf := hconfigurationSize _ _ _ cfg hcfg
      have hs := hinitialSize a
      have hw := hwordSize a
      simp only [length_pairEncoding]
      dsimp at hstate ⊢
      nlinarith)).1
  have hproject := isPolyTime_input
    (pairEncoding (finiteConfigEncoding (k := k) (State := Control) (Oracle := Operation))
      stateEncoding)
  refine (hloop.map (hproject.fst.finiteConfig_tapes.finiteCfg_output.pair hproject.snd)).congr ?_
  intro a
  rw [← MultiTapePTM.finiteRunFrom_init, MultiTapePTM.finiteRunFrom,
    OracleComp.simulateState_map, OracleComp.simulateState_iterate]
  simp only [← step_eq_simulateState, start]

end Cslib.Probability.OracleSimulation
