/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.Repeat
public import Cslib.Languages.Probabilistic.Transcript

/-!
# Pre-sampling an adaptive interaction

A bounded adaptive interaction can draw its independent oracle samples before execution. The
oracle consumes one saved sample per call, retaining its ordinary private state. Unused samples
are discarded. The law preserves the joint output and private state, and needs a query bound only
for the original interaction.

The handler may ignore a sample, for example when answering a repeated query from its cache.
This allows the adversary's query bound to serve directly as a sampling budget.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u v

variable {Query : Type u} {Response : Query → Type u} {State Value α : Type u}

/-- Supply the next saved sample to a stateful handler. The fallback makes the program total on
short lists; a sufficient sampling budget makes its value irrelevant to the distribution. -/
def withSampleList {m : Type u → Type v} [Functor m] (fallback : Value)
    (handler : Value → (q : Query) → StateT State m (Response q))
    (q : Query) : StateT (State × List Value) m (Response q) := fun (state, values) =>
  (fun (answer, next) => (answer, next, values.tail)) <$> handler (values.headD fallback) q state

/-- Run a stateful simulation with a saved list of samples, forgetting the unused suffix. -/
def simulateWithSamples {Query' : Type u} {Response' : Query' → Type u} (fallback : Value)
    (handler : Value → (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    (program : OracleComp Query Response α) (s : State) (values : List Value) :
    OracleComp Query' Response' (α × State) :=
  (fun (result, next, _) => (result, next)) <$>
    simulateState (withSampleList fallback handler) program (s, values)

/-- Interpreting a handler commutes with supplying its saved samples. -/
theorem eval_withSampleList {Query' : Type u} {Response' : Query' → Type u}
    (oracle : (q : Query') → PMF (Response' q)) (fallback : Value)
    (handler : Value → (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    (q : Query) (s : State × List Value) :
    eval oracle (withSampleList fallback handler q s) =
      withSampleList fallback (fun value q s => eval oracle (handler value q s)) q s := by
  simp [withSampleList, PMF.monad_map_eq_map]

private theorem query_bound_cont
    (oracle : (q : Query) → StateT State PMF (Response q))
    (q : Query) (cont : Response q → OracleComp Query Response α) (s : State) (count : ℕ)
    (hbound : ∀ result next transcript,
      (result, next, transcript) ∈
        (runState (withTranscript oracle) (query q >>= cont) (s, [])).support →
        transcript.length ≤ count)
    (answer : Response q) (next : State) (hanswer : (answer, next) ∈ (oracle q s).support)
    (result : α) (final : State) (transcript : Transcript Response)
    (hresult : (result, final, transcript) ∈
      (runState (withTranscript oracle) (cont answer) (next, [])).support) :
    transcript.length + 1 ≤ count := by
  have htrace : (result, final, transcript ++ [⟨q, answer⟩]) ∈
      (runState (withTranscript oracle) (cont answer) (next, [⟨q, answer⟩])).support := by
    rw [runState_withTranscript_append]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(result, final, transcript), hresult, rfl⟩
  have hwhole : (result, final, transcript ++ [⟨q, answer⟩]) ∈
      (runState (withTranscript oracle) (query q >>= cont) (s, [])).support := by
    rw [runState_bind, runState_query, PMF.mem_support_bind_iff]
    refine ⟨(answer, next, [⟨q, answer⟩]), ?_, htrace⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(answer, next), hanswer, rfl⟩
  have hlength : (transcript ++ ([⟨q, answer⟩] : Transcript Response)).length =
      transcript.length + 1 := List.length_append
  exact hlength ▸ hbound result final (transcript ++ [⟨q, answer⟩]) hwhole

/-- Drawing enough independent samples in advance preserves an adaptive interaction's output
and private state. The bound is needed only for the original, online interaction. -/
theorem runState_presample (source : ProbComp Value) (fallback : Value)
    (handler : Value → (q : Query) → StateT State PMF (Response q))
    (program : OracleComp Query Response α) (s : State) (count : ℕ)
    (hbound : ∀ result next transcript,
      (result, next, transcript) ∈ (runState (withTranscript
        (fun q s => (ProbComp.eval source).bind (fun value => handler value q s)))
        program (s, [])).support → transcript.length ≤ count) :
    (ProbComp.eval (replicate count source)).bind (fun values =>
      (runState (withSampleList fallback handler) program (s, values)).map
        (fun (result, next, _) => (result, next))) =
      runState (fun q s => (ProbComp.eval source).bind (fun value => handler value q s))
        program s := by
  induction program using FreeM.induction generalizing s count with
  | pure a => simp [PMF.pure_map]
  | lift_bind op cont ih =>
    simp only [FreeM.bind_eq_bind] at hbound ⊢
    cases op with
    | sample p =>
      simp only [show (FreeM.lift (.sample p) : OracleComp Query Response _) = sample p from rfl]
        at hbound ⊢
      have hnext value (hvalue : value ∈ p.support) : ∀ result next transcript,
          (result, next, transcript) ∈ (runState (withTranscript
            (fun q s => (ProbComp.eval source).bind (fun value => handler value q s)))
            (cont value) (s, [])).support → transcript.length ≤ count := by
        intro result next transcript hresult
        apply hbound result next transcript
        rw [runState_sample_bind, PMF.mem_support_bind_iff]
        exact ⟨value, hvalue, hresult⟩
      simp only [runState_sample_bind, PMF.map_bind]
      rw [PMF.bind_comm]
      apply Probability.PMF.bind_congr_on_support
      intro value hvalue
      exact ih value s count (hnext value hvalue)
    | query q =>
      simp only [show (FreeM.lift (.query q) : OracleComp Query Response _) = query q from rfl]
        at hbound ⊢
      have hnext := query_bound_cont
        (fun q s => (ProbComp.eval source).bind (fun value => handler value q s))
        q cont s count hbound
      obtain ⟨⟨answer, next⟩, hanswer⟩ :=
        ((ProbComp.eval source).bind (fun value => handler value q s)).support_nonempty
      obtain ⟨⟨result, final, transcript⟩, hresult⟩ :=
        (runState (withTranscript
          (fun q s => (ProbComp.eval source).bind (fun value => handler value q s)))
          (cont answer) (next, [])).support_nonempty
      have hpositive : 0 < count := by
        have := hnext answer next hanswer result final transcript hresult
        lia
      cases count with
      | zero => lia
      | succ count =>
        simp only [replicate_succ, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_bind,
          PMF.bind_map, Function.comp_def, runState_bind, runState_query,
          withSampleList, List.headD_cons, List.tail_cons, PMF.map_bind, PMF.monad_map_eq_map]
        apply Probability.PMF.bind_congr_on_support
        intro value hvalue
        rw [PMF.bind_comm]
        apply Probability.PMF.bind_congr_on_support
        rintro ⟨answer, next⟩ hanswer
        apply ih answer next count
        intro result final transcript hresult
        have h := hnext answer next
          ((PMF.mem_support_bind_iff _ _ _).mpr ⟨value, hvalue, hanswer⟩)
          result final transcript hresult
        lia

/-- A uniform semantic query bound supplies a sufficient pre-sampling budget for every handler. -/
theorem HasQueryBounds.runState_presample {program : OracleComp Query Response α}
    {size : Query → ℕ} {count maxSize : ℕ} (h : program.HasQueryBounds size count maxSize)
    (source : ProbComp Value) (fallback : Value)
    (handler : Value → (q : Query) → StateT State PMF (Response q)) (s : State) :
    (ProbComp.eval (replicate count source)).bind (fun values =>
      (runState (withSampleList fallback handler) program (s, values)).map
        (fun (result, next, _) => (result, next))) =
      runState (fun q s => (ProbComp.eval source).bind (fun value => handler value q s))
        program s :=
  OracleComp.runState_presample source fallback handler program s count
    (fun result next transcript hresult =>
      (h _ _ s next result transcript hresult).1)

/-- Sampling a sufficient list and then using it in an adaptive simulation is equivalent to
sampling freshly at each call. The adversary may stop early, repeat queries, and sample privately.
-/
theorem HasQueryBounds.eval_presample {program : OracleComp Query Response α}
    {size : Query → ℕ} {count maxSize : ℕ} (h : program.HasQueryBounds size count maxSize)
    (source : ProbComp Value) (fallback : Value)
    (handler : Value → (q : Query) → StateT State ProbComp (Response q)) (s : State) :
    ProbComp.eval (replicate count source >>= simulateWithSamples fallback handler program s) =
      ProbComp.eval (simulateState
        (fun q s => source >>= fun value => handler value q s) program s) := by
  simpa only [simulateWithSamples, ProbComp.eval, eval_bind, eval_map, eval_simulateState,
    eval_withSampleList] using
      h.runState_presample source fallback (fun value q s => ProbComp.eval (handler value q s)) s

end Cslib.OracleComp
