/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.FiniteConfiguration
public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Languages.Probabilistic.Iteration

/-!
# Interpreting the shared machine using finite data

`finiteStep` executes the unchanged shared transition table on finite tape representations.
`finiteRunFrom` is an ordinary bounded probabilistic loop. Its output program agrees exactly with
the native evaluator whenever the initial configurations correspond, so every interaction with
an external stateful oracle is preserved.

The semantic equivalence is independent of finite control or an efficient oracle handler.
Computational certificates are supplied separately by the programming layer.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query : Type} {Response : Query → Type}
  [DecidableEq Oracle]

/-- One native machine transition, operating on finite storage. A halted state remains unchanged. -/
noncomputable def finiteStep (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (cfg : FiniteConfig k Symbol State Oracle) :
    OracleComp Query Response (FiniteConfig k Symbol State Oracle) :=
  match cfg.tapes.state with
  | none => pure cfg
  | some state => do
    let coin ← OracleComp.uniform Bool
    match machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols coin with
    | .step action symbol move => pure (cfg.step action symbol move)
    | .query oracle next =>
      let answer ← query oracle (cfg.channels oracle).1
      pure (cfg.receive oracle next answer)

/-- Execute a bounded loop of finite-state updates and observe the accumulated output. -/
noncomputable def finiteRunFrom (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (fuel : ℕ) (cfg : FiniteConfig k Symbol State Oracle) :
    OracleComp Query Response (List Symbol) :=
  (fun final => final.tapes.output) <$> OracleComp.iterate fuel (machine.finiteStep query) cfg

/-- The finite-data interpreter and native evaluator produce the very same oracle program.
This preserves sampling and the complete interaction, not only the returned output distribution. -/
theorem finiteRunFrom_eq (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol)) (fuel : ℕ)
    (finite : FiniteConfig k Symbol State Oracle)
    (cfg : Config k Symbol State Oracle finite.tapes.input) (h : finite.Represents cfg) :
    machine.finiteRunFrom query fuel finite = machine.runFrom query fuel cfg := by
  induction fuel generalizing finite with
  | zero => simp [finiteRunFrom, h.tapes.output]
  | succ fuel ih =>
    rw [finiteRunFrom, OracleComp.iterate_succ_bind, map_bind, runFrom_succ]
    cases hs : cfg.tapes.state with
    | none =>
      simp only [finiteStep, h.tapes.state, hs, pure_bind]
      change machine.finiteRunFrom query fuel finite = pure cfg.tapes.output
      rw [ih finite cfg h]
      simp [runFrom, runConfigFrom_halted _ _ _ _ hs]
    | some state =>
      simp only [finiteStep, h.tapes.state, hs, h.tapes.inputSymbol,
        h.tapes.workTapeSymbols, h.answerSymbols, bind_assoc]
      congr 1
      funext coin
      cases ha : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | step action symbol move =>
        simp only [pure_bind]
        exact ih _ _ (h.step action symbol move)
      | query oracle next =>
        simp only [h.queries, bind_assoc, pure_bind]
        congr 1
        funext answer
        exact ih _ _ (h.receive oracle next answer)

/-- Starting with finite blank storage realizes the standard machine run. -/
theorem finiteRunFrom_init (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp Query Response (List Symbol))
    (fuel : ℕ) (input : List Symbol) :
    machine.finiteRunFrom query fuel (FiniteConfig.init machine.initial input) =
      machine.run query fuel input :=
  finiteRunFrom_eq machine query fuel _ _ (FiniteConfig.represents_init _ _)

end Turing.MultiTapePTM
