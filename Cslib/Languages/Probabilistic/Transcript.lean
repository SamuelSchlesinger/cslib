/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.Simulation

/-!
# Observing oracle transcripts

`withTranscript` records each query and its answer while preserving the oracle's private state.
Entries are stored newest first. Forgetting the transcript recovers the original execution,
including its final private state.

`HasQueryBounds` expresses uniform bounds on the number and size of queries, independently of
the machine model. The computational layer derives these bounds from an oracle PPT certificate.

This is semantic instrumentation, not a claim that recording arbitrary replies is efficient.
In particular, a machine's clock bounds its requests but need not bound the oracle's replies.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u

variable {Query : Type u} {Response : Query → Type u} {State α : Type u}

/-- Queries and their typed replies, stored in reverse chronological order. -/
abbrev Transcript (Response : Query → Type u) := List ((q : Query) × Response q)

/-- Observe calls without changing the underlying oracle's replies or private state. -/
noncomputable def withTranscript (oracle : (q : Query) → StateT State PMF (Response q))
    (q : Query) : StateT (State × Transcript Response) PMF (Response q) :=
  fun (s, transcript) => (oracle q s).map
    (fun (answer, s') => (answer, (s', ⟨q, answer⟩ :: transcript)))

/-- Forgetting the transcript preserves the result and the oracle's complete final state. -/
theorem runState_withTranscript (oracle : (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Query Response α) (s : State) (transcript : Transcript Response) :
    (runState (withTranscript oracle) program (s, transcript)).map
        (fun (result, state) => (result, state.1)) = runState oracle program s := by
  apply runState_map_state (withTranscript oracle) oracle Prod.fst
  intro q state
  simp only [withTranscript, PMF.map_comp, Function.comp_def, Prod.mk.eta]
  exact PMF.map_id _

/-- An existing transcript is an untouched suffix of the newly recorded interaction. -/
theorem runState_withTranscript_append (oracle : (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Query Response α) (s : State) (transcript : Transcript Response) :
    runState (withTranscript oracle) program (s, transcript) =
      (runState (withTranscript oracle) program (s, [])).map
        (fun (result, state, fresh) => (result, state, fresh ++ transcript)) := by
  symm
  apply runState_map_state (withTranscript oracle) (withTranscript oracle)
    (fun state => (state.1, state.2 ++ transcript))
  intro q state
  simp [withTranscript, PMF.map_comp, Function.comp_def]

/-- Every possible interaction makes at most `calls` queries, each of size at most `maxSize`.
The bound is uniform in the oracle and its initial private state; it asserts no runtime bound. -/
def HasQueryBounds (program : OracleComp Query Response α) (size : Query → ℕ)
    (calls maxSize : ℕ) : Prop :=
  ∀ (State : Type u) (oracle : (q : Query) → StateT State PMF (Response q))
    (s s' : State) (result : α) (transcript : Transcript Response),
    (result, s', transcript) ∈ (runState (withTranscript oracle) program (s, [])).support →
      transcript.length ≤ calls ∧ ∀ entry ∈ transcript, size entry.1 ≤ maxSize

/-- Increasing either query bound preserves its validity. -/
theorem HasQueryBounds.mono {program : OracleComp Query Response α} {size : Query → ℕ}
    {calls maxSize calls' maxSize' : ℕ} (h : program.HasQueryBounds size calls maxSize)
    (hcalls : calls ≤ calls') (hsize : maxSize ≤ maxSize') :
    program.HasQueryBounds size calls' maxSize' := by
  intro State oracle s s' result transcript hresult
  obtain ⟨hcount, hlength⟩ := h State oracle s s' result transcript hresult
  exact ⟨hcount.trans hcalls, fun entry hentry => (hlength entry hentry).trans hsize⟩

/-- Postprocessing the returned value leaves the oracle transcript unchanged. -/
@[simp] theorem hasQueryBounds_map_iff {β : Type u} (f : α → β)
    (program : OracleComp Query Response α) (size : Query → ℕ) (calls maxSize : ℕ) :
    (f <$> program).HasQueryBounds size calls maxSize ↔
      program.HasQueryBounds size calls maxSize := by
  constructor
  · intro h State oracle s s' result transcript hresult
    apply h State oracle s s' (f result) transcript
    rw [runState_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(result, s', transcript), hresult, rfl⟩
  · intro h State oracle s s' result transcript hresult
    rw [runState_map, PMF.mem_support_map_iff] at hresult
    obtain ⟨⟨value, state⟩, hvalue, heq⟩ := hresult
    cases heq
    exact h State oracle s s' value transcript hvalue

end Cslib.OracleComp
