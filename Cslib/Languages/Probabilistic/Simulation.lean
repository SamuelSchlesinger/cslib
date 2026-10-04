/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.Iteration
public import Cslib.Foundations.Control.Monad.Memoize

/-!
# Stateful oracle simulation

`OracleComp.simulateState` replaces calls by ordinary stateful programs. Its interpretation laws
preserve both the handler's local state and any external oracle state.

To compare two stateful oracles, it suffices to relate their individual calls. The relation may
sample additional hidden state: for example, completing a partially sampled random function.
`OracleComp.runState_simulation` lifts this local identity to an arbitrary adaptive program,
preserving its joint result and the related final state. Its invariant-based variant needs the
local identity only at states satisfying a preserved invariant.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u

variable {Query : Type u} {Response : Query → Type u} {α State State' : Type u}

/-- A private-state invariant preserved by each call holds after every adaptive execution.
The program's own random sampling does not change the oracle's private state. -/
theorem runState_invariant
    (oracle : (q : Query) → StateT State PMF (Response q)) (invariant : State → Prop)
    (step : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (program : OracleComp Query Response α) (s : State) (hs : invariant s)
    (result : α) (s' : State) (h : (result, s') ∈ (runState oracle program s).support) :
    invariant s' := by
  induction program using FreeM.induction generalizing s with
  | pure a =>
    simp only [runState_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    rwa [h.2]
  | lift_bind op cont ih =>
    cases op with
    | sample p =>
      change (result, s') ∈ (runState oracle (sample p >>= cont) s).support at h
      rw [runState_sample_bind, PMF.mem_support_bind_iff] at h
      obtain ⟨a, _, h⟩ := h
      exact ih a s hs h
    | query q =>
      change (result, s') ∈ (runState oracle (query q >>= cont) s).support at h
      rw [runState_bind, runState_query, PMF.mem_support_bind_iff] at h
      obtain ⟨⟨a, next⟩, ha, h⟩ := h
      exact ih a next (step q s hs a next ha) h

/-- Interpreting a memoized program preserves its cache and the effects of its first call. -/
theorem eval_memoize {Key Value : Type u} [BEq Key]
    (compute : Key → OracleComp Query Response Value)
    (oracle : (q : Query) → PMF (Response q)) (key : Key) (cache : List (Key × Value)) :
    eval oracle (memoize compute key cache) =
      memoize (fun key => eval oracle (compute key)) key cache := by
  cases h : cache.lookup key <;> simp [memoize, h] <;> rfl

/-- Replace oracle calls by stateful programs. The handler's state persists between calls, while
the resulting program may still use a separate external oracle interface. -/
def simulateState {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    (program : OracleComp Query Response α) : StateT State (OracleComp Query' Response') α :=
  program.liftM (fun op => match op with
    | .sample p => fun s => (fun a => (a, s)) <$> sample p
    | .query q => handler q)

@[simp] theorem simulateState_pure {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    (a : α) (s : State) : simulateState handler (pure a) s = pure (a, s) := rfl

@[simp] theorem simulateState_bind {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    (program : OracleComp Query Response α) {β : Type u}
    (next : α → OracleComp Query Response β) (s : State) :
    simulateState handler (program >>= next) s =
      (simulateState handler program s >>= fun (a, s') => simulateState handler (next a) s') := by
  unfold simulateState
  rw [FreeM.liftM_bind]
  rfl

@[simp] theorem simulateState_sample {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    (p : PMF α) (s : State) :
    simulateState handler (sample p) s = (fun a => (a, s)) <$> sample p := by
  simp [simulateState, sample]

@[simp] theorem simulateState_query {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    (q : Query) (s : State) : simulateState handler (query q) s = handler q s := by
  simp [simulateState, query]

@[simp] theorem simulateState_map {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    {β : Type u} (f : α → β) (program : OracleComp Query Response α) (s : State) :
    simulateState handler (f <$> program) s =
      (fun (a, s') => (f a, s')) <$> simulateState handler program s := by
  simp only [← bind_pure_comp, simulateState_bind, simulateState_pure]

/-- Stateful interpretation of a bounded loop is an ordinary loop over the program state and
the handler's local state. Both are carried through every iteration. -/
theorem simulateState_iterate {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    (count : ℕ) (step : α → OracleComp Query Response α) (initial : α) (s : State) :
    simulateState handler (iterate count step initial) s =
      iterate count (fun pair => simulateState handler (step pair.1) pair.2) (initial, s) := by
  induction count with
  | zero => simp
  | succ count ih => simp only [iterate_succ, simulateState_bind, ih]

/-- Stateful program substitution denotes the corresponding stateful oracle interpretation. -/
theorem eval_simulateState {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    (oracle : (q : Query') → PMF (Response' q)) (program : OracleComp Query Response α)
    (s : State) :
    eval oracle (simulateState handler program s) =
      runState (fun q s => eval oracle (handler q s)) program s := by
  induction program using FreeM.induction generalizing s with
  | pure a => simp
  | lift_bind op cont ih =>
    cases op with
    | sample p =>
      change eval oracle (simulateState handler (sample p >>= cont) s) =
        runState _ (sample p >>= cont) s
      simp only [simulateState_bind, simulateState_sample, eval_bind, eval_map, eval_sample,
        runState_sample_bind, PMF.bind_map, Function.comp_def, ih]
    | query q =>
      change eval oracle (simulateState handler (query q >>= cont) s) =
        runState _ (query q >>= cont) s
      simp only [simulateState_bind, simulateState_query, eval_bind, runState_bind,
        runState_query, ih]

/-- Interpreting a stateful simulation against another stateful oracle preserves both states.
The handler's local state and the external oracle's private state remain shared across calls. -/
theorem runState_simulateState {Query' : Type u} {Response' : Query' → Type u}
    (handler : (q : Query) → StateT State (OracleComp Query' Response') (Response q))
    (oracle : (q : Query') → StateT State' PMF (Response' q))
    (program : OracleComp Query Response α) (s : State) (t : State') :
    (runState oracle (simulateState handler program s) t).map
        (fun ((a, s'), t') => (a, (s', t'))) =
      runState (fun q state => (runState oracle (handler q state.1) state.2).map
        (fun ((a, s'), t') => (a, (s', t')))) program (s, t) := by
  induction program using FreeM.induction generalizing s t with
  | pure a => simp [PMF.pure_map]
  | lift_bind op cont ih =>
    cases op with
    | sample p =>
      change (runState oracle (simulateState handler (sample p >>= cont) s) t).map _ =
        runState _ (sample p >>= cont) (s, t)
      simp only [simulateState_bind, simulateState_sample, runState_bind, runState_map,
        runState_sample, PMF.map_bind, PMF.bind_map, Function.comp_def, ih]
    | query q =>
      change (runState oracle (simulateState handler (query q >>= cont) s) t).map _ =
        runState _ (query q >>= cont) (s, t)
      simp only [simulateState_bind, simulateState_query, runState_bind, runState_query,
        PMF.map_bind, PMF.bind_map, Function.comp_def, ih]

/-- A probabilistic change of private state commutes with an adaptive computation when it
commutes with each call on invariant states. Only supported transitions must preserve the invariant.
The program may sample privately and repeat queries. -/
theorem runState_simulation_of_invariant
    (oracle : (q : Query) → StateT State PMF (Response q))
    (oracle' : (q : Query) → StateT State' PMF (Response q))
    (relate : State → PMF State')
    (invariant : State → Prop)
    (preserve : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (step : ∀ q s, invariant s →
      (oracle q s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (oracle' q))
    (program : OracleComp Query Response α) (s : State) (hs : invariant s) :
    (runState oracle program s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (fun t => runState oracle' program t) := by
  induction program using FreeM.induction generalizing s with
  | pure a => simp [PMF.map, Function.comp_def]
  | lift_bind op cont ih =>
    cases op with
    | sample p =>
      change (runState oracle (sample p >>= cont) s).bind _ =
        (relate s).bind (fun t => runState oracle' (sample p >>= cont) t)
      simp only [runState_sample_bind, PMF.bind_bind]
      simp_rw [ih _ s hs]
      exact PMF.bind_comm _ _ _
    | query q =>
      change (runState oracle (query q >>= cont) s).bind _ =
        (relate s).bind (fun t => runState oracle' (query q >>= cont) t)
      simp only [runState_bind, runState_query, PMF.bind_bind]
      calc
        _ = (oracle q s).bind (fun (a, s') =>
            (relate s').bind (fun t => runState oracle' (cont a) t)) := by
          apply Probability.PMF.bind_congr_on_support
          rintro ⟨a, s'⟩ hnext
          exact ih a s' (preserve q s hs a s' hnext)
        _ = ((oracle q s).bind (fun (a, s') => (relate s').map (a, ·))).bind
            (fun (a, t) => runState oracle' (cont a) t) := by
          simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
        _ = _ := by rw [step q s hs, PMF.bind_bind]

/-- A probabilistic change of private state that commutes with every oracle call also commutes
with an entire adaptive computation. The program may sample privately and repeat queries. -/
theorem runState_simulation
    (oracle : (q : Query) → StateT State PMF (Response q))
    (oracle' : (q : Query) → StateT State' PMF (Response q))
    (relate : State → PMF State')
    (step : ∀ q s, (oracle q s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (oracle' q))
    (program : OracleComp Query Response α) (s : State) :
    (runState oracle program s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (fun t => runState oracle' program t) :=
  runState_simulation_of_invariant oracle oracle' relate (fun _ => True)
    (by simp) (fun q s _ => step q s) program s trivial

/-- Re-encoding private state preserves adaptive execution when calls agree on invariant states. -/
theorem runState_map_state_of_invariant
    (oracle : (q : Query) → StateT State PMF (Response q))
    (oracle' : (q : Query) → StateT State' PMF (Response q))
    (represent : State → State') (invariant : State → Prop)
    (preserve : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (step : ∀ q s, invariant s →
      (oracle q s).map (fun (a, s') => (a, represent s')) = oracle' q (represent s))
    (program : OracleComp Query Response α) (s : State) (hs : invariant s) :
    (runState oracle program s).map (fun (a, s') => (a, represent s')) =
      runState oracle' program (represent s) := by
  simpa only [PMF.pure_map, PMF.pure_bind, PMF.map, Function.comp_def] using
    runState_simulation_of_invariant oracle oracle' (fun s => PMF.pure (represent s))
      invariant preserve
      (by simpa only [PMF.pure_map, PMF.pure_bind, PMF.map, Function.comp_def] using step)
      program s hs

/-- A deterministic representation change is a special case of stateful oracle simulation. -/
theorem runState_map_state
    (oracle : (q : Query) → StateT State PMF (Response q))
    (oracle' : (q : Query) → StateT State' PMF (Response q))
    (represent : State → State')
    (step : ∀ q s, (oracle q s).map (fun (a, s') => (a, represent s')) =
      oracle' q (represent s))
    (program : OracleComp Query Response α) (s : State) :
    (runState oracle program s).map (fun (a, s') => (a, represent s')) =
      runState oracle' program (represent s) :=
  runState_map_state_of_invariant oracle oracle' represent (fun _ => True)
    (by simp) (fun q s _ => step q s) program s trivial

end Cslib.OracleComp
