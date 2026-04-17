/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.Discrete

@[expose] public section

/-!
# Oracle Interactions

An **oracle interaction** models an adversary that adaptively queries
an oracle, choosing each query based on the responses to all previous
queries. This is the standard model for security games where the
adversary has oracle access (e.g., signing oracles in EUF-CMA).

## Main Definitions

* `OracleInteraction Q R A` — an inductive type representing an
  adaptive sequence of queries of type `Q` receiving responses of
  type `R`, eventually producing a result of type `A`
* `OracleInteraction.run` — execute an interaction against a concrete
  oracle with a fuel budget, returning the query log and result

## Design Notes

The interaction is modeled as a free monad over the query/response
interface. The `run` function uses fuel-based recursion to ensure
termination: each query consumes one unit of fuel, and the oracle
at step `i` is indexed by `Fin fuel` to enable structural recursion
on the fuel parameter.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

/-- An **oracle interaction** where the adversary adaptively queries
an oracle of type `Q → R` and eventually produces a value of type `A`.

- `done a` — the adversary is finished and returns `a`
- `query q k` — the adversary asks query `q` and continues with
  the continuation `k` applied to the oracle's response -/
inductive OracleInteraction (Q : Type) (R : Type) (A : Type) where
  /-- The adversary is done and returns a result -/
  | done : A → OracleInteraction Q R A
  /-- The adversary makes a query and continues based on the response -/
  | query : Q → (R → OracleInteraction Q R A) → OracleInteraction Q R A

/-- Execute an oracle interaction against a concrete oracle, with a
fuel budget limiting the number of queries.

The oracle is `Fin fuel → Q → R`, where the `Fin fuel` index
represents which query step we are at (enabling the game to use
independent randomness for each query). Returns `none` if the
fuel is exhausted before the interaction completes, or
`some (queries, result)` with the list of queries made and the
final result.

Uses structural recursion on `fuel`. -/
def OracleInteraction.run {Q R A : Type}
    : (interaction : OracleInteraction Q R A) →
      (fuel : Nat) →
      (oracle : Fin fuel → Q → R) →
      Option (List Q × A)
  | .done a, _, _ => some ([], a)
  | .query _ _, 0, _ => none
  | .query q k, fuel + 1, oracle =>
    let response := oracle ⟨0, Nat.zero_lt_succ fuel⟩ q
    let shiftedOracle : Fin fuel → Q → R :=
      fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    match (k response).run fuel shiftedOracle with
    | none => none
    | some (qs, a) => some (q :: qs, a)

/-- The query log produced by `run` has length at most `fuel`. -/
theorem OracleInteraction.run_length_le {Q R A : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle : Fin fuel → Q → R)
    {queries : List Q} {a : A}
    (h : interaction.run fuel oracle = some (queries, a)) :
    queries.length ≤ fuel := by
  induction fuel generalizing interaction queries a with
  | zero =>
    cases interaction with
    | done _ =>
      change some ([], _) = some (queries, a) at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact Nat.le.refl
    | query _ _ =>
      change (none : Option _) = some (queries, a) at h
      exact absurd h nofun
  | succ n ih =>
    cases interaction with
    | done _ =>
      change some ([], _) = some (queries, a) at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact Nat.zero_le _
    | query q k =>
      have h_red : OracleInteraction.run (.query q k) (n + 1) oracle =
          match (k (oracle ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none
          | some (qs, a') => some (q :: qs, a') := rfl
      rw [h_red] at h
      rcases h_rec : (k (oracle ⟨0, Nat.zero_lt_succ n⟩ q)).run n
        (fun i : Fin n => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        with _ | ⟨qs, a'⟩
      · rw [h_rec] at h; exact absurd h nofun
      · rw [h_rec] at h
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
        exact Nat.succ_le_succ (ih _ _ h_rec)

/-- **Deterministic prefix**: if two oracles agree on the first `k`
indices, both runs complete, and both query logs have an entry at
position `k`, then the `k`-th query is the same.

This captures the fact that adaptive oracle interactions are
deterministic given the oracle responses: if two oracles agree
on the first `k` steps, the interaction reaches the same state
at step `k`, and hence issues the same query. -/
theorem OracleInteraction.run_prefix_query_eq {Q R A : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → Q → R)
    (k : Nat)
    (h_agree : ∀ (i : Fin fuel), i.val < k → oracle₁ i = oracle₂ i)
    {queries₁ queries₂ : List Q} {a₁ a₂ : A}
    (h₁ : interaction.run fuel oracle₁ = some (queries₁, a₁))
    (h₂ : interaction.run fuel oracle₂ = some (queries₂, a₂))
    (hk₁ : k < queries₁.length) (hk₂ : k < queries₂.length) :
    queries₁[k] = queries₂[k] := by
  induction fuel generalizing interaction k queries₁ queries₂ a₁ a₂ with
  | zero =>
    cases interaction with
    | done _ =>
      change some ([], _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done _ =>
      change some ([], _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query q cont =>
      -- Reduce run in both hypotheses
      have red₁ : OracleInteraction.run (.query q cont) (n + 1) oracle₁ =
          match (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none | some (qs, a') => some (q :: qs, a') := rfl
      have red₂ : OracleInteraction.run (.query q cont) (n + 1) oracle₂ =
          match (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none | some (qs, a') => some (q :: qs, a') := rfl
      rw [red₁] at h₁; rw [red₂] at h₂
      -- Extract recursive results
      rcases h_rec₁ : (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        with _ | ⟨qs₁, a₁'⟩
      · rw [h_rec₁] at h₁; exact absurd h₁ nofun
      · rw [h_rec₁] at h₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
        rcases h_rec₂ : (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          with _ | ⟨qs₂, a₂'⟩
        · rw [h_rec₂] at h₂; exact absurd h₂ nofun
        · rw [h_rec₂] at h₂
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₂)
          -- queries₁ = q :: qs₁, queries₂ = q :: qs₂
          cases k with
          | zero => rfl
          | succ k' =>
            simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk₁ hk₂
            change qs₁[k'] = qs₂[k']
            -- Oracle responses at step 0 agree (0 < k'+1)
            have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q =
                oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q :=
              congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩ (Nat.zero_lt_succ k')) q
            -- So the continuations are the same
            rw [h_r] at h_rec₁
            exact ih (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q))
              (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              k'
              (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                (Nat.succ_lt_succ hi))
              h_rec₁ h_rec₂ hk₁ hk₂

/-- **Prefix length preservation**: if two oracles agree on the first
`k` indices, both runs complete, and the first run has `k < queries₁.length`,
then the second run also has `k < queries₂.length`.

This captures the fact that the interaction's decision to continue or
terminate at step `k` depends only on oracle responses at steps `< k`. -/
theorem OracleInteraction.run_prefix_implies_length {Q R A : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → Q → R)
    (k : Nat)
    (h_agree : ∀ (i : Fin fuel), i.val < k → oracle₁ i = oracle₂ i)
    {queries₁ queries₂ : List Q} {a₁ a₂ : A}
    (h₁ : interaction.run fuel oracle₁ = some (queries₁, a₁))
    (h₂ : interaction.run fuel oracle₂ = some (queries₂, a₂))
    (hk₁ : k < queries₁.length) :
    k < queries₂.length := by
  induction fuel generalizing interaction k queries₁ queries₂ a₁ a₂ with
  | zero =>
    cases interaction with
    | done _ =>
      change some ([], _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done _ =>
      change some ([], _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query q cont =>
      have red₁ : OracleInteraction.run (.query q cont) (n + 1) oracle₁ =
          match (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none | some (qs, a') => some (q :: qs, a') := rfl
      have red₂ : OracleInteraction.run (.query q cont) (n + 1) oracle₂ =
          match (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none | some (qs, a') => some (q :: qs, a') := rfl
      rw [red₁] at h₁; rw [red₂] at h₂
      rcases h_rec₁ : (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        with _ | ⟨qs₁, a₁'⟩
      · rw [h_rec₁] at h₁; exact absurd h₁ nofun
      · rw [h_rec₁] at h₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
        rcases h_rec₂ : (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          with _ | ⟨qs₂, a₂'⟩
        · rw [h_rec₂] at h₂; exact absurd h₂ nofun
        · rw [h_rec₂] at h₂
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₂)
          cases k with
          | zero => simp [List.length_cons]
          | succ k' =>
            simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk₁ ⊢
            have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q =
                oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q :=
              congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩ (Nat.zero_lt_succ k')) q
            rw [h_r] at h_rec₁
            exact ih (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q))
              (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              k'
              (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                (Nat.succ_lt_succ hi))
              h_rec₁ h_rec₂ hk₁

/-- **Deterministic prefix (full)**: if two oracles agree on all indices
`< queries.length`, and the first run succeeds producing `(queries, a)`,
then the second run produces the same `(queries, a)`.

This strengthens `run_prefix_query_eq` from agreement at a single position
to identical outputs: if the oracles agree on all steps the interaction
actually used, the interaction is fully deterministic. -/
theorem OracleInteraction.run_det_prefix {Q R A : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → Q → R)
    {queries : List Q} {a : A}
    (h₁ : interaction.run fuel oracle₁ = some (queries, a))
    (h_agree : ∀ (i : Fin fuel), i.val < queries.length →
               oracle₁ i = oracle₂ i) :
    interaction.run fuel oracle₂ = some (queries, a) := by
  induction fuel generalizing interaction queries a with
  | zero =>
    cases interaction with
    | done a' =>
      change some ([], a') = some (queries, a) at h₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
      rfl
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done a' =>
      change some ([], a') = some (queries, a) at h₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
      rfl
    | query q k =>
      have red₁ : OracleInteraction.run (.query q k) (n + 1) oracle₁ =
          match (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
          | none => none | some (qs, a') => some (q :: qs, a') := rfl
      rw [red₁] at h₁
      rcases h_rec : (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        with _ | ⟨qs, a'⟩
      · rw [h_rec] at h₁; exact absurd h₁ nofun
      · rw [h_rec] at h₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
        -- queries = q :: qs, so queries.length = qs.length + 1
        -- Oracle responses at step 0 agree (0 < (q :: qs).length)
        have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q =
            oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q :=
          congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩
            (by simp [List.length_cons])) q
        -- Apply IH with shifted oracles
        have h_ih := ih (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ q))
          (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          h_rec
          (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
            (by simp [List.length_cons]; omega))
        -- Now show run oracle₂ = some (q :: qs, a)
        have red₂ : OracleInteraction.run (.query q k) (n + 1) oracle₂ =
            match (k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ q)).run n
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) with
            | none => none | some (qs, a') => some (q :: qs, a') := rfl
        rw [red₂, ← h_r, h_ih]

/-- Execute an oracle interaction against a **stateful** oracle, with a
fuel budget. The oracle at each step receives the current state `S` and
returns a response along with an updated state.

Returns `none` if fuel is exhausted, otherwise
`some (queries, result, finalState)`.
Uses structural recursion on `fuel`. -/
def OracleInteraction.runWithState {Q R A S : Type}
    : (interaction : OracleInteraction Q R A) →
      (fuel : Nat) →
      (oracle : Fin fuel → S → Q → R × S) →
      (initState : S) →
      Option (List Q × A × S)
  | .done a, _, _, s => some ([], a, s)
  | .query _ _, 0, _, _ => none
  | .query q k, fuel + 1, oracle, s =>
    let (response, s') := oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q
    let shiftedOracle : Fin fuel → S → Q → R × S :=
      fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    match (k response).runWithState fuel shiftedOracle s' with
    | none => none
    | some (qs, a, sf) => some (q :: qs, a, sf)

/-- **Deterministic prefix (stateful)**: if two stateful oracles agree on
the first `k` indices, both runs complete from the same initial state,
and both query logs have an entry at position `k`, then the `k`-th query
is the same. -/
theorem OracleInteraction.runWithState_prefix_query_eq {Q R A S : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → S → Q → R × S)
    (s : S) (k : Nat)
    (h_agree : ∀ (i : Fin fuel), i.val < k → oracle₁ i = oracle₂ i)
    {queries₁ queries₂ : List Q} {a₁ a₂ : A} {sf₁ sf₂ : S}
    (h₁ : interaction.runWithState fuel oracle₁ s = some (queries₁, a₁, sf₁))
    (h₂ : interaction.runWithState fuel oracle₂ s = some (queries₂, a₂, sf₂))
    (hk₁ : k < queries₁.length) (hk₂ : k < queries₂.length) :
    queries₁[k] = queries₂[k] := by
  induction fuel generalizing interaction k queries₁ queries₂ a₁ a₂ sf₁ sf₂ s with
  | zero =>
    cases interaction with
    | done _ =>
      change some ([], _, _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done _ =>
      change some ([], _, _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query q cont =>
      have red₁ : OracleInteraction.runWithState (.query q cont) (n + 1) oracle₁ s =
          match (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
          | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
      have red₂ : OracleInteraction.runWithState (.query q cont) (n + 1) oracle₂ s =
          match (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
            (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
          | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
      rw [red₁] at h₁; rw [red₂] at h₂
      rcases h_rec₁ : (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2
        with _ | ⟨qs₁, a₁', sf₁'⟩
      · rw [h_rec₁] at h₁; exact absurd h₁ nofun
      · rw [h_rec₁] at h₁
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
        rcases h_rec₂ : (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2
          with _ | ⟨qs₂, a₂', sf₂'⟩
        · rw [h_rec₂] at h₂; exact absurd h₂ nofun
        · rw [h_rec₂] at h₂
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₂)
          cases k with
          | zero => rfl
          | succ k' =>
            simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk₁ hk₂
            change qs₁[k'] = qs₂[k']
            have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q =
                oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q :=
              congrFun (congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩
                (Nat.zero_lt_succ k')) s) q
            rw [h_r] at h_rec₁
            exact ih (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1)
              (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2
              k'
              (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                (Nat.succ_lt_succ hi))
              h_rec₁ h_rec₂ hk₁ hk₂

/-- **Prefix length preservation (stateful)**: if two stateful oracles
agree on the first `k` indices, both runs complete from the same initial
state, and the first run has `k < queries₁.length`, then the second run
also has `k < queries₂.length`. -/
theorem OracleInteraction.runWithState_prefix_implies_length {Q R A S : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → S → Q → R × S)
    (s : S) (k : Nat)
    (h_agree : ∀ (i : Fin fuel), i.val < k → oracle₁ i = oracle₂ i)
    {queries₁ queries₂ : List Q} {a₁ a₂ : A} {sf₁ sf₂ : S}
    (h₁ : interaction.runWithState fuel oracle₁ s = some (queries₁, a₁, sf₁))
    (h₂ : interaction.runWithState fuel oracle₂ s = some (queries₂, a₂, sf₂))
    (hk₁ : k < queries₁.length) :
    k < queries₂.length := by
  induction fuel generalizing interaction k queries₁ queries₂ a₁ a₂ sf₁ sf₂ s with
  | zero =>
    cases interaction with
    | done _ =>
      change some ([], _, _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done _ =>
      change some ([], _, _) = _ at h₁
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
      exact absurd hk₁ (by simp)
    | query q cont =>
      have red₁ : OracleInteraction.runWithState (.query q cont) (n + 1) oracle₁ s =
          match (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
          | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
      have red₂ : OracleInteraction.runWithState (.query q cont) (n + 1) oracle₂ s =
          match (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
            (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
          | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
      rw [red₁] at h₁; rw [red₂] at h₂
      rcases h_rec₁ : (cont (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2
        with _ | ⟨qs₁, a₁', sf₁'⟩
      · rw [h_rec₁] at h₁; exact absurd h₁ nofun
      · rw [h_rec₁] at h₁
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₁)
        rcases h_rec₂ : (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2
          with _ | ⟨qs₂, a₂', sf₂'⟩
        · rw [h_rec₂] at h₂; exact absurd h₂ nofun
        · rw [h_rec₂] at h₂
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h₂)
          cases k with
          | zero => simp [List.length_cons]
          | succ k' =>
            simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk₁ ⊢
            have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q =
                oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q :=
              congrFun (congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩
                (Nat.zero_lt_succ k')) s) q
            rw [h_r] at h_rec₁
            exact ih (cont (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1)
              (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2
              k'
              (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                (Nat.succ_lt_succ hi))
              h_rec₁ h_rec₂ hk₁

/-- **Deterministic prefix (stateful, full)**: if two stateful oracles
agree on all indices `< queries.length`, both start from the same state,
and the first run succeeds producing `(queries, a, sf)`, then the second
run produces the same result. -/
theorem OracleInteraction.runWithState_det_prefix {Q R A S : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → S → Q → R × S)
    (s : S)
    {queries : List Q} {a : A} {sf : S}
    (h₁ : interaction.runWithState fuel oracle₁ s = some (queries, a, sf))
    (h_agree : ∀ (i : Fin fuel), i.val < queries.length →
               oracle₁ i = oracle₂ i) :
    interaction.runWithState fuel oracle₂ s = some (queries, a, sf) := by
  induction fuel generalizing interaction queries a sf s with
  | zero =>
    cases interaction with
    | done a' =>
      change some ([], a', s) = some (queries, a, sf) at h₁
      obtain ⟨rfl, hrest⟩ := Prod.mk.inj (Option.some.inj h₁)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
      rfl
    | query _ _ =>
      exact absurd (show (none : Option _) = _ from h₁) nofun
  | succ n ih =>
    cases interaction with
    | done a' =>
      change some ([], a', s) = some (queries, a, sf) at h₁
      obtain ⟨rfl, hrest⟩ := Prod.mk.inj (Option.some.inj h₁)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
      rfl
    | query q k =>
      have red₁ : OracleInteraction.runWithState (.query q k) (n + 1) oracle₁ s =
          match (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
            (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
          | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
      rw [red₁] at h₁
      rcases h_rec : (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
        (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2
        with _ | ⟨qs, a', sf'⟩
      · rw [h_rec] at h₁; exact absurd h₁ nofun
      · rw [h_rec] at h₁
        obtain ⟨rfl, hrest⟩ := Prod.mk.inj (Option.some.inj h₁)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
        have h_r : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q =
            oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q :=
          congrFun (congrFun (h_agree ⟨0, Nat.zero_lt_succ n⟩
            (by simp [List.length_cons])) s) q
        have h_ih := ih (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).1)
          (fun i : Fin n => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q).2
          h_rec
          (fun i hi => h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
            (by simp [List.length_cons]; omega))
        have red₂ : OracleInteraction.runWithState (.query q k) (n + 1) oracle₂ s =
            match (k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1).runWithState n
              (fun i : Fin n => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
              (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2 with
            | none => none | some (qs, a', sf') => some (q :: qs, a', sf') := rfl
        rw [red₂, ← h_r, h_ih]

/-! ### Per-step access: `queryAtWithState` and `stateBeforeWithState`

These project the query made at step `idx` and the state just before it,
without needing the overall `runWithState` to terminate. They enable
prefix-independence arguments (see `queryAtWithState_eq_of_prefix`) and
are the scaffolding behind `runWithState_eq_of_oracle_agree_on_trace`. -/

/-- Return the `idx`-th query issued by a stateful interaction, if it exists,
without requiring the whole `runWithState` call to terminate successfully.

This is useful for prefix-dependence arguments: `queryAtWithState ... idx`
only depends on oracle indices `< idx + 1`. -/
def queryAtWithState {Q R A S : Type}
    : (interaction : OracleInteraction Q R A) →
      (fuel : Nat) →
      (oracle : Fin fuel → S → Q → R × S) →
      (initState : S) →
      (idx : Nat) →
      Option Q
  | .done _, _, _, _, _ => none
  | .query _ _, 0, _, _, _ => none
  | .query q k, fuel + 1, oracle, s, idx =>
    match idx with
    | 0 => some q
    | idx + 1 =>
      let (response, s') := oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q
      let shiftedOracle : Fin fuel → S → Q → R × S :=
        fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      queryAtWithState (k response) fuel shiftedOracle s' idx

/-- State just before processing query `idx` (if that query exists), for a
stateful interaction run with fixed fuel and oracle. -/
def stateBeforeWithState {Q R A S : Type}
    : (interaction : OracleInteraction Q R A) →
      (fuel : Nat) →
      (oracle : Fin fuel → S → Q → R × S) →
      (initState : S) →
      (idx : Nat) →
      Option S
  | .done _, _, _, s, 0 => some s
  | .done _, _, _, _, _ + 1 => none
  | .query _ _, 0, _, s, 0 => some s
  | .query _ _, 0, _, _, _ + 1 => none
  | .query _ _, _fuel + 1, _, s, 0 => some s
  | .query q k, fuel + 1, oracle, s, idx + 1 =>
    let (response, s') := oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q
    let shiftedOracle : Fin fuel → S → Q → R × S :=
      fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    stateBeforeWithState (k response) fuel shiftedOracle s' idx

/-- `queryAtWithState` depends only on the oracle prefix `≤ idx`. -/
theorem queryAtWithState_eq_of_prefix
    {Q R A S : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat)
    (oracle₁ oracle₂ : Fin fuel → S → Q → R × S)
    (s : S)
    (idx : Nat)
    (h_agree : ∀ (i : Fin fuel), i.val < idx → oracle₁ i = oracle₂ i) :
    queryAtWithState interaction fuel oracle₁ s idx =
    queryAtWithState interaction fuel oracle₂ s idx := by
  induction idx generalizing interaction fuel oracle₁ oracle₂ s with
  | zero =>
    cases interaction with
    | done a =>
      cases fuel <;> rfl
    | query q k =>
      cases fuel <;> rfl
  | succ idx ih =>
    cases interaction with
    | done a =>
      cases fuel <;> rfl
    | query q k =>
      cases fuel with
      | zero =>
        rfl
      | succ fuel =>
        simp only [queryAtWithState]
        have h0 : oracle₁ ⟨0, Nat.zero_lt_succ fuel⟩ s q =
            oracle₂ ⟨0, Nat.zero_lt_succ fuel⟩ s q := by
          exact congrFun (congrFun
            (h_agree ⟨0, Nat.zero_lt_succ fuel⟩ (Nat.zero_lt_succ _)) s) q
        let shifted₁ : Fin fuel → S → Q → R × S :=
          fun i => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        let shifted₂ : Fin fuel → S → Q → R × S :=
          fun i => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        have h_shift : ∀ (i : Fin fuel), i.val < idx → shifted₁ i = shifted₂ i := by
          intro i hi
          exact h_agree ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_lt_succ hi)
        have h_tail := ih
          (k (oracle₁ ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
          fuel shifted₁ shifted₂
          (oracle₁ ⟨0, Nat.zero_lt_succ fuel⟩ s q).2
          h_shift
        have h_rhs :
            queryAtWithState
              (k (oracle₁ ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
              fuel shifted₂
              (oracle₁ ⟨0, Nat.zero_lt_succ fuel⟩ s q).2 idx =
            queryAtWithState
              (k (oracle₂ ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
              fuel shifted₂
              (oracle₂ ⟨0, Nat.zero_lt_succ fuel⟩ s q).2 idx :=
          congrArg
            (fun p : R × S => queryAtWithState (k p.1) fuel shifted₂ p.2 idx) h0
        exact (by
          simpa [shifted₁, shifted₂] using h_tail.trans h_rhs)

/-- The query log produced by `runWithState` has length at most `fuel`. -/
theorem runWithState_length_le {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (queries : List Q) (a : A) (sf : S),
      interaction.runWithState fuel oracle s = some (queries, a, sf) →
      queries.length ≤ fuel := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero =>
    intro oracle s queries a sf h
    cases interaction with
    | done _ =>
      change some ([], _, _) = some (queries, a, sf) at h
      obtain ⟨rfl, _, _⟩ := Prod.mk.inj (Option.some.inj h)
      simp
    | query _ _ => exact absurd h nofun
  | succ n ih =>
    intro oracle s queries a sf h
    cases interaction with
    | done _ =>
      change some ([], _, _) = some (queries, a, sf) at h
      obtain ⟨rfl, _, _⟩ := Prod.mk.inj (Option.some.inj h)
      simp
    | query q k =>
      simp only [OracleInteraction.runWithState] at h
      split at h
      · exact absurd h nofun
      · have hinj := Option.some.inj h
        obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj hinj
        simp only [List.length_cons]
        exact Nat.succ_le_succ (ih _ _ _ _ _ _ (by assumption))

/-- `runWithState` final state equals `stateBeforeWithState` at `queries.length`. -/
theorem runWithState_finalState_eq_stateBeforeWithState {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (queries : List Q) (a : A) (sf : S),
      interaction.runWithState fuel oracle s = some (queries, a, sf) →
      stateBeforeWithState interaction fuel oracle s queries.length = some sf := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero =>
    intro oracle s queries a sf h
    cases interaction with
    | done a' =>
      simp only [OracleInteraction.runWithState, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, rfl⟩ := h; simp [stateBeforeWithState]
    | query _ _ =>
      simp only [OracleInteraction.runWithState] at h; contradiction
  | succ fuel ih =>
    intro oracle s queries a sf h
    cases interaction with
    | done a' =>
      simp only [OracleInteraction.runWithState, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, rfl⟩ := h; simp [stateBeforeWithState]
    | query q k =>
      simp only [OracleInteraction.runWithState] at h
      split at h
      · simp at h
      · next qs' a' hrec =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [stateBeforeWithState]
        exact ih _ _ _ _ _ _ hrec

/-- `runWithState` query list entries match `queryAtWithState`. -/
theorem runWithState_query_eq_queryAtWithState {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (queries : List Q) (a : A) (sf : S),
      interaction.runWithState fuel oracle s = some (queries, a, sf) →
      ∀ (idx : Nat) (hlt : idx < queries.length),
        queryAtWithState interaction fuel oracle s idx = some (queries.get ⟨idx, hlt⟩) := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero =>
    intro oracle s queries a sf h
    cases interaction with
    | done a' =>
      simp only [OracleInteraction.runWithState, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      intro idx hlt; simp at hlt
    | query _ _ =>
      simp only [OracleInteraction.runWithState] at h; contradiction
  | succ fuel ih =>
    intro oracle s queries a sf h
    cases interaction with
    | done a' =>
      simp only [OracleInteraction.runWithState, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      intro idx hlt; simp at hlt
    | query q k =>
      simp only [OracleInteraction.runWithState] at h
      split at h
      · simp at h
      · next qs' a' hrec =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        intro idx hlt
        cases idx with
        | zero => simp [queryAtWithState]
        | succ idx' =>
          simp only [queryAtWithState, List.get_cons_succ]
          exact ih _ _ _ _ _ _ hrec idx' (by simpa [List.length_cons] using hlt)

/-- At index 0, `stateBeforeWithState` always returns the initial state. -/
theorem stateBeforeWithState_at_zero {Q R A S : Type}
    (interaction : OracleInteraction Q R A)
    (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
    (s : S) :
    stateBeforeWithState interaction fuel oracle s 0 = some s := by
  cases interaction with
  | done _ => rfl
  | query _ _ => cases fuel <;> rfl

/-- If `stateBeforeWithState` at `idx+1` is `some`, then so are the state and
query at `idx`, and they compose via the oracle. -/
theorem stateBeforeWithState_pred {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (idx : Nat) (hidx : idx < fuel) (st' : S),
      stateBeforeWithState interaction fuel oracle s (idx + 1) = some st' →
      ∃ (st : S) (qry : Q),
        stateBeforeWithState interaction fuel oracle s idx = some st ∧
        queryAtWithState interaction fuel oracle s idx = some qry ∧
        st' = (oracle ⟨idx, hidx⟩ st qry).2 := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero => intro _ _ _ _ hidx; omega
  | succ fuel ih =>
    intro oracle s idx hidx st' h_step
    cases interaction with
    | done a =>
      cases idx with
      | zero => simp [stateBeforeWithState] at h_step
      | succ _ => simp [stateBeforeWithState] at h_step
    | query q k =>
      cases idx with
      | zero =>
        simp only [stateBeforeWithState] at h_step
        have h0 := stateBeforeWithState_at_zero
          (k (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).1) fuel
          (fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).2
        rw [h0] at h_step
        exact ⟨s, q, rfl, rfl, (Option.some.inj h_step).symm⟩
      | succ idx' =>
        simp only [stateBeforeWithState] at h_step
        have ih_result := ih (k (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
          (fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).2
          idx' (by omega) st' h_step
        obtain ⟨st, qry, h_st, h_qry, h_eq⟩ := ih_result
        simp only [stateBeforeWithState, queryAtWithState]
        exact ⟨st, qry, h_st, h_qry, h_eq⟩

/-- The state at step `idx + 1` is obtained by applying the oracle at step `idx`
to the state and query at step `idx`. -/
theorem stateBeforeWithState_step {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle : Fin fuel → S → Q → R × S)
        (s : S) (idx : Nat) (hidx : idx < fuel) (st : S) (qry : Q),
      stateBeforeWithState interaction fuel oracle s idx = some st →
      queryAtWithState interaction fuel oracle s idx = some qry →
      stateBeforeWithState interaction fuel oracle s (idx + 1) =
        some (oracle ⟨idx, hidx⟩ st qry).2 := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero => intro _ _ _ _ hidx; omega
  | succ fuel ih =>
    intro oracle s idx hidx st qry h_st h_qry
    cases interaction with
    | done a =>
      cases idx with
      | zero => simp [queryAtWithState] at h_qry
      | succ _ => simp [stateBeforeWithState] at h_st
    | query q k =>
      cases idx with
      | zero =>
        simp only [stateBeforeWithState, Option.some.injEq] at h_st
        simp only [queryAtWithState, Option.some.injEq] at h_qry
        subst h_st; subst h_qry
        simp only [stateBeforeWithState]
        cases (k (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).1) with
        | done a => cases fuel <;> simp [stateBeforeWithState]
        | query _ _ => cases fuel <;> simp [stateBeforeWithState]
      | succ idx' =>
        simp only [stateBeforeWithState] at h_st ⊢
        simp only [queryAtWithState] at h_qry
        exact ih (k (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).1)
          (fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (oracle ⟨0, Nat.zero_lt_succ fuel⟩ s q).2
          idx' (by omega) st qry h_st h_qry

/-- If two oracles agree at every step on the `(state, query)` encountered
during execution with `oracle₁`, then `runWithState` produces the same result. -/
theorem runWithState_eq_of_oracle_agree_on_trace {Q R A S : Type}
    : ∀ (interaction : OracleInteraction Q R A)
        (fuel : Nat) (oracle₁ oracle₂ : Fin fuel → S → Q → R × S)
        (s : S),
        (∀ (k : Nat) (hk : k < fuel) (st : S) (q : Q),
          stateBeforeWithState interaction fuel oracle₁ s k = some st →
          queryAtWithState interaction fuel oracle₁ s k = some q →
          oracle₁ ⟨k, hk⟩ st q = oracle₂ ⟨k, hk⟩ st q) →
        interaction.runWithState fuel oracle₁ s =
        interaction.runWithState fuel oracle₂ s := by
  intro interaction fuel
  induction fuel generalizing interaction with
  | zero => intro _ _ _ _; cases interaction <;> rfl
  | succ n ih =>
    intro oracle₁ oracle₂ s h
    cases interaction with
    | done => rfl
    | query q k =>
      simp only [OracleInteraction.runWithState]
      have h0 : oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s q =
          oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q :=
        h 0 (Nat.zero_lt_succ n) s q rfl rfl
      rw [h0]
      have h_ih := ih (k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).1)
        (fun (i : Fin n) => oracle₁ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (fun (i : Fin n) => oracle₂ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s q).2
        (fun k' hk' st' q' h_state h_query => by
          have := h (k' + 1) (by omega) st' q'
            (by simp only [stateBeforeWithState]; rw [h0]; exact h_state)
            (by simp only [queryAtWithState]; rw [h0]; exact h_query)
          exact this)
      rw [h_ih]

open Cslib.Probability in
/-- If two oracle families, parameterized by per-step randomness types
`S₁` and `S₂`, produce the same marginal distribution at each step
(for all queries and all test functions), then the expected value of
any function of the `run` result is the same.

This is the key tool for proving that swapping per-step randomness
(e.g., real prover randomness ↔ simulator randomness in HVZK)
preserves the interaction's expected outcome. The proof is by
induction on `fuel`: at each step, we factor the expectation into
the head component (which we swap using `h_marginal`) and the tail
(which we swap using the inductive hypothesis). -/
theorem run_uniformExpect_oracle_eq
    {Q R A : Type} {S₁ S₂ : Type}
    [Fintype S₁] [Nonempty S₁] [Fintype S₂] [Nonempty S₂]
    (fuel : ℕ)
    (interaction : OracleInteraction Q R A)
    (oracle₁ : Fin fuel → S₁ → Q → R)
    (oracle₂ : Fin fuel → S₂ → Q → R)
    (h_marginal : ∀ (i : Fin fuel) (q : Q) (g : R → ℝ),
      uniformExpect S₁ (fun s => g (oracle₁ i s q)) =
      uniformExpect S₂ (fun s => g (oracle₂ i s q)))
    (f : Option (List Q × A) → ℝ) :
    uniformExpect (Fin fuel → S₁)
      (fun ss => f (interaction.run fuel (fun i => oracle₁ i (ss i)))) =
    uniformExpect (Fin fuel → S₂)
      (fun ss => f (interaction.run fuel (fun i => oracle₂ i (ss i)))) := by
  induction fuel generalizing interaction f with
  | zero =>
    cases interaction with
    | done a =>
      change uniformExpect _ (fun _ => f (some ([], a))) =
             uniformExpect _ (fun _ => f (some ([], a)))
      rw [uniformExpect_const, uniformExpect_const]
    | query q k =>
      change uniformExpect _ (fun _ => f none) =
             uniformExpect _ (fun _ => f none)
      rw [uniformExpect_const, uniformExpect_const]
  | succ n ih =>
    cases interaction with
    | done a =>
      change uniformExpect _ (fun _ => f (some ([], a))) =
             uniformExpect _ (fun _ => f (some ([], a)))
      rw [uniformExpect_const, uniformExpect_const]
    | query q k =>
      let shifted₁ : Fin n → S₁ → Q → R :=
        fun j => oracle₁ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      let shifted₂ : Fin n → S₂ → Q → R :=
        fun j => oracle₂ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      have h_shifted : ∀ (j : Fin n) (q' : Q) (g : R → ℝ),
          uniformExpect S₁ (fun s => g (shifted₁ j s q')) =
          uniformExpect S₂ (fun s => g (shifted₂ j s q')) :=
        fun j => h_marginal ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      let postF : Option (List Q × A) → ℝ := fun result =>
        f (match result with | none => none | some (qs, a) => some (q :: qs, a))
      have lhs_conv :
          uniformExpect (Fin (n + 1) → S₁)
            (fun ss => f (OracleInteraction.run (.query q k) (n + 1)
              (fun i => oracle₁ i (ss i)))) =
          uniformExpect S₁ (fun s₀ =>
            uniformExpect (Fin n → S₁) (fun ss' =>
              postF ((k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ q)).run n
                (fun j => shifted₁ j (ss' j))))) := by
        rw [show (fun ss : Fin (n + 1) → S₁ =>
                f (OracleInteraction.run (.query q k) (n + 1)
                  (fun i => oracle₁ i (ss i)))) =
              ((fun p : S₁ × (Fin n → S₁) =>
                postF ((k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ p.1 q)).run n
                  (fun j => shifted₁ j (p.2 j)))) ∘
              (Fin.consEquiv (fun _ : Fin (n + 1) => S₁)).symm) from by
            funext ss; rfl
          , uniformExpect_congr, uniformExpect_prod]
      have rhs_conv :
          uniformExpect (Fin (n + 1) → S₂)
            (fun ss => f (OracleInteraction.run (.query q k) (n + 1)
              (fun i => oracle₂ i (ss i)))) =
          uniformExpect S₂ (fun s₀ =>
            uniformExpect (Fin n → S₂) (fun ss' =>
              postF ((k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s₀ q)).run n
                (fun j => shifted₂ j (ss' j))))) := by
        rw [show (fun ss : Fin (n + 1) → S₂ =>
                f (OracleInteraction.run (.query q k) (n + 1)
                  (fun i => oracle₂ i (ss i)))) =
              ((fun p : S₂ × (Fin n → S₂) =>
                postF ((k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ p.1 q)).run n
                  (fun j => shifted₂ j (p.2 j)))) ∘
              (Fin.consEquiv (fun _ : Fin (n + 1) => S₂)).symm) from by
            funext ss; rfl
          , uniformExpect_congr, uniformExpect_prod]
      rw [lhs_conv, rhs_conv]
      conv_lhs =>
        arg 2; ext s₀
        rw [ih (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ q)) shifted₁ shifted₂
          h_shifted postF]
      exact h_marginal ⟨0, Nat.zero_lt_succ n⟩ q
        (fun r => uniformExpect (Fin n → S₂) (fun ss' =>
          postF ((k r).run n (fun j => shifted₂ j (ss' j)))))

open Cslib.Probability in
/-- Stateful version of `run_uniformExpect_oracle_eq`. If two oracle
families, parameterized by per-step randomness types `S₁` and `S₂` and
threading state of type `State`, produce the same marginal distribution
at each step (for all states, queries, and test functions), then the
expected value of any function of the `runWithState` result is the same.

The proof mirrors `run_uniformExpect_oracle_eq` by induction on `fuel`. -/
theorem runWithState_uniformExpect_oracle_eq
    {Q R A State : Type} {S₁ S₂ : Type}
    [Fintype S₁] [Nonempty S₁] [Fintype S₂] [Nonempty S₂]
    (fuel : ℕ)
    (interaction : OracleInteraction Q R A)
    (oracle₁ : Fin fuel → S₁ → State → Q → (R × State))
    (oracle₂ : Fin fuel → S₂ → State → Q → (R × State))
    (h_marginal : ∀ (i : Fin fuel) (st : State) (q : Q)
      (g : R × State → ℝ),
      uniformExpect S₁ (fun s => g (oracle₁ i s st q)) =
      uniformExpect S₂ (fun s => g (oracle₂ i s st q)))
    (initState : State)
    (f : Option (List Q × A × State) → ℝ) :
    uniformExpect (Fin fuel → S₁)
      (fun ss => f (interaction.runWithState fuel
        (fun i st q => oracle₁ i (ss i) st q) initState)) =
    uniformExpect (Fin fuel → S₂)
      (fun ss => f (interaction.runWithState fuel
        (fun i st q => oracle₂ i (ss i) st q) initState)) := by
  induction fuel generalizing interaction initState f with
  | zero =>
    cases interaction with
    | done a =>
      change uniformExpect _ (fun _ => f (some ([], a, initState))) =
             uniformExpect _ (fun _ => f (some ([], a, initState)))
      rw [uniformExpect_const, uniformExpect_const]
    | query q k =>
      change uniformExpect _ (fun _ => f none) =
             uniformExpect _ (fun _ => f none)
      rw [uniformExpect_const, uniformExpect_const]
  | succ n ih =>
    cases interaction with
    | done a =>
      change uniformExpect _ (fun _ => f (some ([], a, initState))) =
             uniformExpect _ (fun _ => f (some ([], a, initState)))
      rw [uniformExpect_const, uniformExpect_const]
    | query q k =>
      let shifted₁ : Fin n → S₁ → State → Q → (R × State) :=
        fun j => oracle₁ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      let shifted₂ : Fin n → S₂ → State → Q → (R × State) :=
        fun j => oracle₂ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      have h_shifted : ∀ (j : Fin n) (st : State) (q' : Q)
          (g : R × State → ℝ),
          uniformExpect S₁ (fun s => g (shifted₁ j s st q')) =
          uniformExpect S₂ (fun s => g (shifted₂ j s st q')) :=
        fun j => h_marginal ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      let postF : Option (List Q × A × State) → ℝ := fun result =>
        f (match result with
           | none => none
           | some (qs, a, sf) => some (q :: qs, a, sf))
      have lhs_conv :
          uniformExpect (Fin (n + 1) → S₁)
            (fun ss => f (OracleInteraction.runWithState (.query q k) (n + 1)
              (fun i st q' => oracle₁ i (ss i) st q') initState)) =
          uniformExpect S₁ (fun s₀ =>
            uniformExpect (Fin n → S₁) (fun ss' =>
              postF ((k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).1).runWithState n
                (fun j st q' => shifted₁ j (ss' j) st q')
                (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).2))) := by
        rw [show (fun ss : Fin (n + 1) → S₁ =>
                f (OracleInteraction.runWithState (.query q k) (n + 1)
                  (fun i st q' => oracle₁ i (ss i) st q') initState)) =
              ((fun p : S₁ × (Fin n → S₁) =>
                postF ((k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ p.1 initState q).1).runWithState n
                  (fun j st q' => shifted₁ j (p.2 j) st q')
                  (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ p.1 initState q).2)) ∘
              (Fin.consEquiv (fun _ : Fin (n + 1) => S₁)).symm) from by
            funext ss; rfl
          , uniformExpect_congr, uniformExpect_prod]
      have rhs_conv :
          uniformExpect (Fin (n + 1) → S₂)
            (fun ss => f (OracleInteraction.runWithState (.query q k) (n + 1)
              (fun i st q' => oracle₂ i (ss i) st q') initState)) =
          uniformExpect S₂ (fun s₀ =>
            uniformExpect (Fin n → S₂) (fun ss' =>
              postF ((k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).1).runWithState n
                (fun j st q' => shifted₂ j (ss' j) st q')
                (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).2))) := by
        rw [show (fun ss : Fin (n + 1) → S₂ =>
                f (OracleInteraction.runWithState (.query q k) (n + 1)
                  (fun i st q' => oracle₂ i (ss i) st q') initState)) =
              ((fun p : S₂ × (Fin n → S₂) =>
                postF ((k (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ p.1 initState q).1).runWithState n
                  (fun j st q' => shifted₂ j (p.2 j) st q')
                  (oracle₂ ⟨0, Nat.zero_lt_succ n⟩ p.1 initState q).2)) ∘
              (Fin.consEquiv (fun _ : Fin (n + 1) => S₂)).symm) from by
            funext ss; rfl
          , uniformExpect_congr, uniformExpect_prod]
      rw [lhs_conv, rhs_conv]
      conv_lhs =>
        arg 2; ext s₀
        rw [ih (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).1)
          shifted₁ shifted₂ h_shifted
          (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ initState q).2
          postF]
      exact h_marginal ⟨0, Nat.zero_lt_succ n⟩ initState q
        (fun p => uniformExpect (Fin n → S₂) (fun ss' =>
          postF ((k p.1).runWithState n
            (fun j st q' => shifted₂ j (ss' j) st q') p.2)))

end
