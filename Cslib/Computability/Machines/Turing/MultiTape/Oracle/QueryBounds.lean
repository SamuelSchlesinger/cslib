/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Probabilistic
public import Cslib.Languages.Probabilistic.Transcript

/-!
# Oracle query bounds from the machine clock

Each machine transition submits at most one request and writes at most one symbol to each query
buffer. Consequently a run of `fuel` transitions makes at most `fuel` calls, each of length at
most `fuel` when starting with empty communication channels. These are support bounds for every
shared stateful oracle, including oracles with arbitrarily long replies.

The proof uses the common multi-tape evaluator. It does not assume separate query bounds or
change the cost of the oracle's external computation.

The request-label function lets the same proof handle named channels and the single-operation
interface. Its measured request size must be bounded by the actual buffer length.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol Control Operation Query State : Type} [DecidableEq Operation]
  {input : List Symbol}

/-- A partial run adds at most one call per transition. Every recorded request fits within the
initial buffer bound plus elapsed time, independently of all oracle replies. -/
theorem query_bounds_runFrom (machine : MultiTapePTM k Symbol Control Operation)
    (request : Operation → List Symbol → Query) (size : Query → ℕ)
    (hrequest : ∀ op word, size (request op word) ≤ word.length)
    (oracle : Query → StateT State PMF (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol Control Operation input) (bound : ℕ)
    (hbuffers : ∀ op, (cfg.channels op).queryBuffer.length ≤ bound)
    (s s' : State) (transcript transcript' : OracleComp.Transcript
      (fun _ : Query => List Symbol)) (output : List Symbol)
    (htranscript : ∀ entry ∈ transcript, size entry.1 ≤ bound)
    (h : (output, s', transcript') ∈ (OracleComp.runState (OracleComp.withTranscript oracle)
      (machine.runFrom (fun op word => OracleComp.query (request op word)) fuel cfg)
      (s, transcript)).support) :
    transcript'.length ≤ transcript.length + fuel ∧
      ∀ entry ∈ transcript', size entry.1 ≤ bound + fuel := by
  induction fuel generalizing cfg bound s transcript with
  | zero =>
    simp only [runFrom_zero, OracleComp.runState_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at h
    rw [h.2.2]
    exact ⟨by simp, by simpa using htranscript⟩
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      simp only [runFrom_succ, hs, OracleComp.runState_pure, PMF.mem_support_pure_iff,
        Prod.mk.injEq] at h
      rw [h.2.2]
      exact ⟨by simp, fun entry hentry => (htranscript entry hentry).trans (Nat.le_add_right ..)⟩
    | some control =>
      simp only [runFrom_succ, hs, OracleComp.uniform, OracleComp.runState_sample_bind,
        PMF.mem_support_bind_iff] at h
      obtain ⟨coin, _, h⟩ := h
      cases ha : machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | step action symbol move =>
        rw [ha] at h
        have hnext : ∀ op, ((cfg.step action symbol move).channels op).queryBuffer.length ≤
            bound + 1 := by
          intro op
          simp only [Config.step, List.length_append]
          exact Nat.add_le_add (hbuffers op) (symbol op).length_toList_le
        obtain ⟨hcount, hsize⟩ := ih _ (bound + 1) hnext _ _
          (fun entry hentry => (htranscript entry hentry).trans (Nat.le_add_right ..)) h
        exact ⟨by lia, fun entry hentry => by have := hsize entry hentry; lia⟩
      | query op next =>
        simp only [ha, OracleComp.runState_bind, OracleComp.runState_query,
          OracleComp.withTranscript, PMF.bind_map, Function.comp_def,
          PMF.mem_support_bind_iff] at h
        obtain ⟨⟨answer, nextState⟩, _, h⟩ := h
        have hnext : ∀ operation,
            ((cfg.receive op next answer).channels operation).queryBuffer.length ≤ bound := by
          intro operation
          by_cases heq : operation = op
          · subst operation
            simp [Config.receive]
          · simpa [Config.receive, heq] using hbuffers operation
        obtain ⟨hcount, hsize⟩ := ih _ bound hnext _ _ (by
          intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact (hrequest op _).trans (hbuffers op)
          · exact htranscript entry hentry) h
        exact ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount,
          fun entry hentry => (hsize entry hentry).trans (by lia)⟩

/-- The clock bounds both the number of calls and the length of each request from an initial
configuration. The same bound works for every stateful oracle and every initial private state. -/
theorem query_bounds_run (machine : MultiTapePTM k Symbol Control Operation)
    (request : Operation → List Symbol → Query) (size : Query → ℕ)
    (hrequest : ∀ op word, size (request op word) ≤ word.length)
    (oracle : Query → StateT State PMF (List Symbol)) (fuel : ℕ)
    (input : List Symbol) (s s' : State) (output : List Symbol)
    (transcript : OracleComp.Transcript (fun _ : Query => List Symbol))
    (h : (output, s', transcript) ∈ (OracleComp.runState (OracleComp.withTranscript oracle)
      (machine.run (fun op word => OracleComp.query (request op word)) fuel input)
      (s, [])).support) :
    transcript.length ≤ fuel ∧ ∀ entry ∈ transcript, size entry.1 ≤ fuel := by
  simpa using query_bounds_runFrom machine request size hrequest oracle fuel
    (machine.initialConfig input) 0
    (by simp [MultiTapeMachine.initialConfig]) s s' [] transcript output (by simp) h

end Turing.MultiTapePTM
