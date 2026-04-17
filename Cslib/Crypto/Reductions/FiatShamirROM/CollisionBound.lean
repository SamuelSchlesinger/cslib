/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Reductions.FiatShamirROM.Games

@[expose] public section

/-!
# Commitment Reuse Bound for the Fiat-Shamir ROM Reduction

Between `LazyROM` and `MapGame_Real`, the oracles differ only at signing
steps where the adversary's running map already binds the key
`(m, commit(w, y, rs_i))`. This file bounds the probability of such a
**commitment reuse** by `q² · δ`, where `δ` is the unpredictability
parameter of the underlying Sigma protocol.

## Main results

* `uniformExpect_commit_collision_pair` — pairwise bound on prover-
  randomness commitment collisions
* `lazyPairCommitReuse_pair_bound` — per-pair bound on reuse at `(i, j)`
* `lazyCommitReuse_bound` — union bound: any reuse event has probability
  `≤ q² · δ`
* `mapGameRealOracle_finalMap_lookup` — traces the forgery key through
  the Map-game association list to establish which challenge is bound
* `lazy_run_stmt_eq_mapGame_real_run_stmt_of_no_reuse` — conditioned on
  no commitment reuse, the lazy and MapGame_Real runs are identical
-/

open Cslib.Probability

/-- For a single pair `(i, j)` of distinct indices, the probability (over
uniform prover randomness) that the signing commitments collide is `≤ δ`.
This adapts `uniformExpect_collision_pair` to the `UnpredictableCommitments`
setting: we split `rs` at coordinate `j` via `Equiv.funSplitAt`, fix the
remaining coordinates (which determines the target `t₀ = commit(w, y, rs i)`),
and apply the unpredictability bound. -/
theorem uniformExpect_commit_collision_pair {R : EffectiveRelation}
    (P : SigmaProtocol R)
    (kg : R.WithKeyGen)
    (n : ℕ) (q : ℕ) (w : R.Witness n)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ)
    [inst_ft : Fintype (P.ProverRandomness n)]
    [inst_ne : Nonempty (P.ProverRandomness n)]
    (i j : Fin q) (hij : i ≠ j) :
    uniformExpect (Fin q → P.ProverRandomness n)
      (fun rs => if P.commit n w (kg.keyOf n w) (rs i) =
        P.commit n w (kg.keyOf n w) (rs j) then (1 : ℝ) else 0) ≤ δ n := by
  -- Align instances with the protocol's canonical instances so h_unpred applies
  have h_ft : inst_ft = P.proverRandomnessFintype n := Subsingleton.elim _ _
  have h_ne : inst_ne = P.proverRandomnessNonempty n := Subsingleton.elim _ _
  subst h_ft; subst h_ne
  -- Split at coordinate j: (Fin q → PR) ≃ PR × ({k // k ≠ j} → PR)
  -- Flip equality direction so it matches UnpredictableCommitments (commit(rj) = t₀)
  have h_comp : (fun rs : Fin q → P.ProverRandomness n =>
      if P.commit n w (kg.keyOf n w) (rs i) =
        P.commit n w (kg.keyOf n w) (rs j) then (1 : ℝ) else 0) =
    (fun p : P.ProverRandomness n × ({k : Fin q // k ≠ j} → P.ProverRandomness n) =>
      if P.commit n w (kg.keyOf n w) p.1 =
        P.commit n w (kg.keyOf n w) (p.2 ⟨i, hij⟩) then 1 else 0) ∘
    Equiv.funSplitAt j (P.ProverRandomness n) := by
    ext rs; simp [Equiv.funSplitAt, Equiv.piSplitAt, eq_comm]
  rw [h_comp, uniformExpect_congr]
  haveI : Nonempty ({k : Fin q // k ≠ j} → P.ProverRandomness n) :=
    ⟨fun _ => (P.proverRandomnessNonempty n).some⟩
  rw [uniformExpect_prod, uniformExpect_comm]
  -- E_{rest}[E_{rj}[1{commit(rj) = commit(rest[i])}]] ≤ δ
  have h_bound : ∀ rest : {k : Fin q // k ≠ j} → P.ProverRandomness n,
      uniformExpect (P.ProverRandomness n) (fun rj =>
        if P.commit n w (kg.keyOf n w) rj =
          P.commit n w (kg.keyOf n w) (rest ⟨i, hij⟩) then 1 else 0) ≤ δ n :=
    fun rest => h_unpred n w (kg.keyOf n w)
      (P.commit n w (kg.keyOf n w) (rest ⟨i, hij⟩)) (kg.keyOf_valid n w)
  exact le_trans (uniformExpect_mono _ h_bound) (le_of_eq (uniformExpect_const _ _))

/-- If `assocLookup key map = some v`, then the pair `(key, v)` occurs in
the association list. -/
lemma assocLookup_some_mem {α β : Type} [DecidableEq α]
    (key : α) (map : List (α × β)) (v : β)
    (h : assocLookup key map = some v) :
    (key, v) ∈ map := by
  induction map with
  | nil =>
    simp [assocLookup] at h
  | cons kv rest ih =>
    rcases kv with ⟨k, v'⟩
    by_cases hk : k = key
    · subst hk
      have hv : v' = v := by
        simpa [assocLookup] using h
      subst hv
      exact List.mem_cons.mpr (Or.inl rfl)
    · have hrest : assocLookup key rest = some v := by
        simpa [assocLookup, hk] using h
      exact List.mem_cons.mpr (Or.inr (ih hrest))

/-- The `idx`-th query in the LazyROM interaction. -/
noncomputable def lazyQueryAt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (idx : Nat) :
    Option (Msg n ⊕ (Msg n × P.Commitment n)) :=
  queryAtWithState (A.interact n y) (A.numQueries n)
    (lazyRomOracle P Msg n (A.numQueries n) w y rs ch) [] idx

/-- LazyROM map state just before query index `idx` (if that query exists). -/
noncomputable def lazyMapBefore {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (idx : Nat) :
    Option (MapState P Msg n) :=
  stateBeforeWithState (A.interact n y) (A.numQueries n)
    (lazyRomOracle P Msg n (A.numQueries n) w y rs ch) [] idx

/-- Prefix-independence for `lazyQueryAt`: changing prover randomness at
indices `≥ idx` does not change the `idx`-th query. -/
theorem lazyQueryAt_eq_of_rs_prefix {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs₁ rs₂ : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (idx : Nat)
    (h_prefix : ∀ i : Fin (A.numQueries n), i.val < idx → rs₁ i = rs₂ i) :
    lazyQueryAt P Msg A n w y rs₁ ch idx =
    lazyQueryAt P Msg A n w y rs₂ ch idx := by
  apply queryAtWithState_eq_of_prefix (interaction := A.interact n y)
  intro i hi
  funext st qry
  cases qry with
  | inr mt =>
    simp [lazyRomOracle]
  | inl m =>
    simp [lazyRomOracle, h_prefix i hi]

/-- Commitment inserted into the LazyROM map at query index `i`, if any.

At a signing query this is `commit(w, y, rs i)`, while at a hash query it is
the queried commitment. -/
noncomputable def lazyInsertedCommitAt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (i : Fin (A.numQueries n)) :
    Option (P.Commitment n) :=
  match lazyQueryAt P Msg A n w y rs ch i.val with
  | some (.inl _) => some (P.commit n w y (rs i))
  | some (.inr (_, t)) => some t
  | none => none

/-- Pair event at `(i,j)`: the `j`-th query is a signing query and its
commitment matches a commitment already inserted at index `i < j`. -/
noncomputable def lazyPairCommitReuse {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (i j : Fin (A.numQueries n)) : Bool :=
  match lazyInsertedCommitAt P Msg A n w y rs ch i,
      lazyQueryAt P Msg A n w y rs ch j.val with
  | some ti, some (.inl _) =>
      decide (ti = P.commit n w y (rs j))
  | _, _ => false

/-- If two prover-randomness vectors agree on indices `< j`, then for any
`i < j` they induce the same inserted commitment at index `i`. -/
theorem lazyInsertedCommitAt_eq_of_rs_prefix_lt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs₁ rs₂ : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (i j : Fin (A.numQueries n))
    (hij : i.val < j.val)
    (h_prefix : ∀ k : Fin (A.numQueries n), k.val < j.val → rs₁ k = rs₂ k) :
    lazyInsertedCommitAt P Msg A n w y rs₁ ch i =
    lazyInsertedCommitAt P Msg A n w y rs₂ ch i := by
  unfold lazyInsertedCommitAt
  have hq : lazyQueryAt P Msg A n w y rs₁ ch i.val =
      lazyQueryAt P Msg A n w y rs₂ ch i.val := by
    apply lazyQueryAt_eq_of_rs_prefix
    intro k hk
    exact h_prefix k (lt_trans hk hij)
  rw [hq]
  simp [h_prefix i hij]

/-- Per-pair bound: for `i < j`, the probability that LazyROM has a
commitment reuse at `(i,j)` is at most `δ`. -/
theorem lazyPairCommitReuse_pair_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ)
    (i j : Fin (A.numQueries n))
    (hij : i.val < j.val) :
    uniformExpect
      ((R.Witness n × (Fin (A.numQueries n) → P.ProverRandomness n)) ×
        (Fin (A.numQueries n) → P.Challenge n))
  (fun ⟨⟨w, rs⟩, ch⟩ =>
    if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j then (1 : ℝ) else 0)
  ≤ δ n := by
  classical
  let q := A.numQueries n
  -- Reorder expectations as E_w E_ch E_rs
  have h_reorder :
      uniformExpect ((R.Witness n × (Fin q → P.ProverRandomness n)) ×
        (Fin q → P.Challenge n))
        (fun ⟨⟨w, rs⟩, ch⟩ =>
          if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j then (1 : ℝ) else 0) =
      uniformExpect (R.Witness n) (fun w =>
        uniformExpect (Fin q → P.Challenge n) (fun ch =>
          uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
            if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
              then (1 : ℝ) else 0))) := by
    rw [uniformExpect_prod, uniformExpect_prod]
    congr 1
    ext w
    exact uniformExpect_comm
      (Fin q → P.ProverRandomness n) (Fin q → P.Challenge n)
      (fun rs ch =>
        if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j then (1 : ℝ) else 0)
  rw [h_reorder]
  -- Inner bound for fixed (w, ch)
  have h_inner : ∀ (w : R.Witness n) (ch : Fin q → P.Challenge n),
      uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
        if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j then (1 : ℝ) else 0)
      ≤ δ n := by
    intro w ch
    let y := kg.keyOf n w
    let e := Equiv.funSplitAt j (P.ProverRandomness n)
    let g : (Fin (A.numQueries n) → P.ProverRandomness n) → ℝ := fun rs =>
      if lazyPairCommitReuse P Msg A n w y rs ch i j then (1 : ℝ) else 0
    have h_split :
        uniformExpect (Fin (A.numQueries n) → P.ProverRandomness n) g =
        uniformExpect
          (P.ProverRandomness n × ({k : Fin (A.numQueries n) // k ≠ j} → P.ProverRandomness n))
          (fun p => g (e.symm p)) := by
      have h_tmp := uniformExpect_congr e
        (fun p : P.ProverRandomness n ×
            ({k : Fin (A.numQueries n) // k ≠ j} → P.ProverRandomness n) =>
          g (e.symm p))
      have h_left : ((fun p : P.ProverRandomness n ×
          ({k : Fin (A.numQueries n) // k ≠ j} → P.ProverRandomness n) =>
          g (e.symm p)) ∘ e) = g := by
        funext rs
        exact congrArg g (e.left_inv rs)
      simpa [h_left] using h_tmp
    rw [h_split, uniformExpect_prod]
    rw [uniformExpect_comm]
    -- For each fixed `rest`, the only remaining randomness is `rj`
    have h_rest :
        ∀ rest : {k : Fin (A.numQueries n) // k ≠ j} → P.ProverRandomness n,
        uniformExpect (P.ProverRandomness n) (fun rj =>
          g (e.symm (rj, rest))) ≤ δ n := by
      intro rest
      let r0 : P.ProverRandomness n := (P.proverRandomnessNonempty n).some
      let rs0 : Fin (A.numQueries n) → P.ProverRandomness n := e.symm (r0, rest)
      have h_prefix_of_rj :
          ∀ (rj : P.ProverRandomness n) (k : Fin (A.numQueries n)), k.val < j.val →
            (e.symm (rj, rest)) k = rs0 k := by
        intro rj k hk
        have hk_ne : k ≠ j := Fin.ne_of_lt hk
        have h_left : (e.symm (rj, rest)) k = rest ⟨k, hk_ne⟩ := by
          simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hk_ne]
        have h_right : rs0 k = rest ⟨k, hk_ne⟩ := by
          simp [rs0, e, Equiv.funSplitAt, Equiv.piSplitAt, hk_ne]
        exact h_left.trans h_right.symm
      have hδ_nonneg : 0 ≤ δ n := by
        have htmp := h_unpred n w y (P.commit n w y r0) (kg.keyOf_valid n w)
        exact le_trans (uniformExpect_nonneg _ (fun _ => by split <;> norm_num)) htmp
      cases h_ins0 : lazyInsertedCommitAt P Msg A n w y rs0 ch i with
      | none =>
        have h_point : ∀ rj : P.ProverRandomness n, g (e.symm (rj, rest)) = 0 := by
          intro rj
          have h_ins_rj :
              lazyInsertedCommitAt P Msg A n w y (e.symm (rj, rest)) ch i =
              lazyInsertedCommitAt P Msg A n w y rs0 ch i := by
            apply lazyInsertedCommitAt_eq_of_rs_prefix_lt P Msg A n w y
              (e.symm (rj, rest)) rs0 ch i j hij
            intro k hk
            exact h_prefix_of_rj rj k hk
          unfold g lazyPairCommitReuse
          rw [h_ins_rj, h_ins0]
          simp
        rw [show (fun rj => g (e.symm (rj, rest))) = fun _ => (0 : ℝ) from by
              funext rj; exact h_point rj,
            uniformExpect_const]
        exact hδ_nonneg
      | some ti =>
        cases h_qj0 : lazyQueryAt P Msg A n w y rs0 ch j.val with
        | none =>
          have h_point : ∀ rj : P.ProverRandomness n, g (e.symm (rj, rest)) = 0 := by
            intro rj
            have h_ins_rj :
                lazyInsertedCommitAt P Msg A n w y (e.symm (rj, rest)) ch i =
                lazyInsertedCommitAt P Msg A n w y rs0 ch i := by
              apply lazyInsertedCommitAt_eq_of_rs_prefix_lt P Msg A n w y
                (e.symm (rj, rest)) rs0 ch i j hij
              intro k hk
              exact h_prefix_of_rj rj k hk
            have h_qj_rj :
                lazyQueryAt P Msg A n w y (e.symm (rj, rest)) ch j.val =
                lazyQueryAt P Msg A n w y rs0 ch j.val := by
              apply lazyQueryAt_eq_of_rs_prefix P Msg A n w y
                (e.symm (rj, rest)) rs0 ch j.val
              intro k hk
              exact h_prefix_of_rj rj k hk
            unfold g lazyPairCommitReuse
            rw [h_ins_rj, h_qj_rj, h_qj0]
            simp
          rw [show (fun rj => g (e.symm (rj, rest))) = fun _ => (0 : ℝ) from by
                funext rj; exact h_point rj,
              uniformExpect_const]
          exact hδ_nonneg
        | some qj =>
          cases qj with
          | inr mt =>
            have h_point : ∀ rj : P.ProverRandomness n, g (e.symm (rj, rest)) = 0 := by
              intro rj
              have h_ins_rj :
                  lazyInsertedCommitAt P Msg A n w y (e.symm (rj, rest)) ch i =
                  lazyInsertedCommitAt P Msg A n w y rs0 ch i := by
                apply lazyInsertedCommitAt_eq_of_rs_prefix_lt P Msg A n w y
                  (e.symm (rj, rest)) rs0 ch i j hij
                intro k hk
                exact h_prefix_of_rj rj k hk
              have h_qj_rj :
                  lazyQueryAt P Msg A n w y (e.symm (rj, rest)) ch j.val =
                  lazyQueryAt P Msg A n w y rs0 ch j.val := by
                apply lazyQueryAt_eq_of_rs_prefix P Msg A n w y
                  (e.symm (rj, rest)) rs0 ch j.val
                intro k hk
                exact h_prefix_of_rj rj k hk
              unfold g lazyPairCommitReuse
              rw [h_ins_rj, h_qj_rj, h_ins0, h_qj0]
              simp
            rw [show (fun rj => g (e.symm (rj, rest))) = fun _ => (0 : ℝ) from by
                  funext rj; exact h_point rj,
                uniformExpect_const]
            exact hδ_nonneg
          | inl mj =>
            have h_point : ∀ rj : P.ProverRandomness n,
                g (e.symm (rj, rest)) =
                  (if ti = P.commit n w y rj then (1 : ℝ) else 0) := by
              intro rj
              have h_ins_rj :
                  lazyInsertedCommitAt P Msg A n w y (e.symm (rj, rest)) ch i =
                  lazyInsertedCommitAt P Msg A n w y rs0 ch i := by
                apply lazyInsertedCommitAt_eq_of_rs_prefix_lt P Msg A n w y
                  (e.symm (rj, rest)) rs0 ch i j hij
                intro k hk
                exact h_prefix_of_rj rj k hk
              have h_qj_rj :
                  lazyQueryAt P Msg A n w y (e.symm (rj, rest)) ch j.val =
                  lazyQueryAt P Msg A n w y rs0 ch j.val := by
                apply lazyQueryAt_eq_of_rs_prefix P Msg A n w y
                  (e.symm (rj, rest)) rs0 ch j.val
                intro k hk
                exact h_prefix_of_rj rj k hk
              unfold g lazyPairCommitReuse
              rw [h_ins_rj, h_qj_rj, h_ins0, h_qj0]
              have h_jcoord : (e.symm (rj, rest)) j = rj := by
                simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
              rw [h_jcoord]
              simp [decide_eq_true_eq]
            rw [show (fun rj => g (e.symm (rj, rest))) =
                (fun rj => if ti = P.commit n w y rj then (1 : ℝ) else 0) from by
                  funext rj; exact h_point rj]
            simpa [eq_comm] using h_unpred n w y ti (kg.keyOf_valid n w)
    exact le_trans (uniformExpect_mono _ h_rest) (le_of_eq (uniformExpect_const _ _))
  have h_inner_w : ∀ w : R.Witness n,
      uniformExpect (Fin q → P.Challenge n) (fun ch =>
        uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
          if lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j then (1 : ℝ) else 0))
      ≤ δ n := by
    intro w
    exact le_trans (uniformExpect_mono _ (h_inner w)) (le_of_eq (uniformExpect_const _ _))
  exact le_trans (uniformExpect_mono _ h_inner_w) (le_of_eq (uniformExpect_const _ _))

/-- Union bound over all pairs `(i,j)`: probability of any LazyROM commitment
reuse event is at most `q² · δ`. -/
theorem lazyCommitReuse_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    uniformExpect
      ((R.Witness n × (Fin (A.numQueries n) → P.ProverRandomness n)) ×
        (Fin (A.numQueries n) → P.Challenge n))
      (fun ⟨⟨w, rs⟩, ch⟩ =>
        if ∃ (i j : Fin (A.numQueries n)), i.val < j.val ∧
            lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
        then (1 : ℝ) else 0)
      ≤ (A.numQueries n : ℝ) ^ 2 * δ n := by
  classical
  let q := A.numQueries n
  have h_union : ∀ (w : R.Witness n) (rs : Fin q → P.ProverRandomness n)
      (ch : Fin q → P.Challenge n),
      (if ∃ (i j : Fin q), i.val < j.val ∧
          lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
        then (1 : ℝ) else 0) ≤
      ∑ p : Fin q × Fin q,
        if p.1.val < p.2.val ∧
            lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch p.1 p.2
        then 1 else 0 := by
    intro w rs ch
    split
    · rename_i h
      obtain ⟨i, j, hij, hpair⟩ := h
      have h_nonneg : ∀ p ∈ (Finset.univ : Finset (Fin q × Fin q)),
          (0 : ℝ) ≤
            (if p.1.val < p.2.val ∧
                lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch p.1 p.2
              then 1 else 0) :=
        fun p _ => ite_nonneg zero_le_one (le_refl 0)
      have h_single := Finset.single_le_sum h_nonneg (Finset.mem_univ (i, j))
      have h_ij :
          (if (i : Fin q).val < j.val ∧
              lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
            then (1 : ℝ) else 0) = 1 := if_pos ⟨hij, hpair⟩
      linarith
    · rename_i hfalse
      exact Finset.sum_nonneg fun p _ => ite_nonneg zero_le_one (le_refl 0)
  have h_pair : ∀ (p : Fin q × Fin q),
      uniformExpect
        ((R.Witness n × (Fin q → P.ProverRandomness n)) × (Fin q → P.Challenge n))
        (fun ⟨⟨w, rs⟩, ch⟩ =>
          if p.1.val < p.2.val ∧
              lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch p.1 p.2
          then (1 : ℝ) else 0) ≤ δ n := by
    intro p
    rcases p with ⟨i, j⟩
    by_cases hij : i.val < j.val
    · have := lazyPairCommitReuse_pair_bound P Msg kg A n δ h_unpred i j hij
      exact le_trans
        (uniformExpect_mono _ (fun ⟨⟨w, rs⟩, ch⟩ => by
          by_cases hpair : lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
          · simp [hij, hpair]
          · simp [hij, hpair]))
        this
    · have h_zero :
          (fun x :
            (R.Witness n × (Fin q → P.ProverRandomness n)) × (Fin q → P.Challenge n) =>
              if i.val < j.val ∧
                  lazyPairCommitReuse P Msg A n x.1.1 (kg.keyOf n x.1.1) x.1.2 x.2 i j
              then (1 : ℝ) else 0) = fun _ => 0 := by
        funext x
        simp [hij]
      rw [h_zero, uniformExpect_const]
      let r0 : P.ProverRandomness n := (P.proverRandomnessNonempty n).some
      let w0 : R.Witness n := (show Nonempty (R.Witness n) from inferInstance).some
      exact le_trans (uniformExpect_nonneg _ (fun _ => by split <;> norm_num))
        (h_unpred n w0 (kg.keyOf n w0) (P.commit n w0 (kg.keyOf n w0) r0)
          (kg.keyOf_valid n w0))
  calc uniformExpect
        ((R.Witness n × (Fin q → P.ProverRandomness n)) × (Fin q → P.Challenge n))
        (fun ⟨⟨w, rs⟩, ch⟩ =>
          if ∃ (i j : Fin q), i.val < j.val ∧
              lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j
          then (1 : ℝ) else 0)
      ≤ uniformExpect
          ((R.Witness n × (Fin q → P.ProverRandomness n)) × (Fin q → P.Challenge n))
          (fun ⟨⟨w, rs⟩, ch⟩ =>
            ∑ p : Fin q × Fin q,
              if p.1.val < p.2.val ∧
                  lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch p.1 p.2
              then 1 else 0) :=
        uniformExpect_mono _ (fun ⟨⟨w, rs⟩, ch⟩ => h_union w rs ch)
    _ = ∑ p : Fin q × Fin q,
          uniformExpect
            ((R.Witness n × (Fin q → P.ProverRandomness n)) × (Fin q → P.Challenge n))
            (fun ⟨⟨w, rs⟩, ch⟩ =>
              if p.1.val < p.2.val ∧
                  lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch p.1 p.2
              then 1 else 0) :=
        uniformExpect_finset_sum _
    _ ≤ ∑ _p : Fin q × Fin q, δ n :=
        Finset.sum_le_sum (fun p _ => h_pair p)
    _ = (Fintype.card (Fin q × Fin q) : ℝ) * δ n := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (q : ℝ) ^ 2 * δ n := by
        simp [Fintype.card_prod, Fintype.card_fin]; ring_nf; exact le_refl _

/-- Single-step lookup persistence for `mapGameRealOracle`: if `(mf, tf)` is
already in the map and the query is not a signing query for `mf`, the lookup
is preserved. -/
theorem mapGameRealOracle_lookup_persist {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (ch : Fin q → P.Challenge n)
    (i : Fin q) (map : MapState P Msg n)
    (mf : Msg n) (tf : P.Commitment n) (v : P.Challenge n)
    (qry : Msg n ⊕ (Msg n × P.Commitment n))
    (h_lookup : assocLookup (mf, tf) map = some v)
    (h_not_sign_mf : ∀ m, qry = .inl m → m ≠ mf) :
    assocLookup (mf, tf) (mapGameRealOracle P Msg n q w y rs ch i map qry).2 = some v := by
  letI := P.commitmentDecEq n
  cases qry with
  | inl m =>
    simp only [mapGameRealOracle]
    have hne : m ≠ mf := h_not_sign_mf m rfl
    simp only [assocLookup]
    rw [if_neg (fun h => hne (Prod.mk.inj h).1)]
    exact h_lookup
  | inr mt =>
    simp only [mapGameRealOracle]
    cases hlk : assocLookup (mt.1, mt.2) map with
    | some c => exact h_lookup
    | none =>
      simp only [assocLookup]
      have hne : ¬ ((mt.1, mt.2) = (mf, tf)) := by
        intro heq; rw [Prod.mk.injEq] at heq; rw [heq.1, heq.2] at hlk
        simp [hlk] at h_lookup
      rw [if_neg hne]
      exact h_lookup

/-- Single-step preservation: `mapGameRealOracle` preserves
`assocLookup key st = none` when the query doesn't insert `key`. -/
theorem mapGameReal_step_preserves_none {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (ch : Fin q → P.Challenge n)
    (i : Fin q) (st : MapState P Msg n)
    (qry : Msg n ⊕ (Msg n × P.Commitment n))
    (key : Msg n × P.Commitment n)
    (h_none : assocLookup key st = none)
    (h_not_hash : qry ≠ Sum.inr key)
    (h_not_sign : ∀ m, qry = Sum.inl m → m ≠ key.1) :
    assocLookup key (mapGameRealOracle P Msg n q w y rs ch i st qry).2 = none := by
  letI := P.commitmentDecEq n
  cases qry with
  | inl m =>
    simp only [mapGameRealOracle, assocLookup]
    have hne : m ≠ key.1 := h_not_sign m rfl
    rw [if_neg (fun h => hne (Prod.mk.inj h).1)]
    exact h_none
  | inr mt =>
    simp only [mapGameRealOracle]
    cases hlk : assocLookup mt st with
    | some c => exact h_none
    | none =>
      simp only [assocLookup]
      have hne : mt ≠ key := fun h => h_not_hash (congrArg Sum.inr h)
      rw [if_neg hne]
      exact h_none

/-- In the mapGameRealOracle execution, if the forged message was never signed
and the first hash query for the forgery key is at index `j`, then the final
map associates the forgery key with `ch j`. -/
theorem mapGameRealOracle_finalMap_lookup {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (queries : List (Msg n ⊕ (Msg n × P.Commitment n)))
    (mf : Msg n) (tf : P.Commitment n) (zf : P.Response n)
    (finalMap : MapState P Msg n)
    (h_result : (A.interact n y).runWithState (A.numQueries n)
        (mapGameRealOracle P Msg n (A.numQueries n) w y rs ch) [] =
      some (queries, (mf, tf, zf), finalMap))
    (hj : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n)
    (hj_in : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < queries.length)
    (h_not_signed : (signMsgsOf queries).contains mf = false) :
    assocLookup (mf, tf) finalMap =
      some (ch ⟨List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries, hj⟩) := by
  set j := List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries with j_def
  set oracle := mapGameRealOracle P Msg n (A.numQueries n) w y rs ch
  have h_final := runWithState_finalState_eq_stateBeforeWithState _ _ _ _ _ _ _ h_result
  have h_query := runWithState_query_eq_queryAtWithState _ _ _ _ _ _ _ h_result
  letI := P.commitmentDecEq n
  have h_len_le := runWithState_length_le _ _ _ _ _ _ _ h_result
  -- Sub-claim: no signing query has message mf
  have h_not_sign_any : ∀ (i : Nat) (hi : i < queries.length) (m : Msg n),
      queries.get ⟨i, hi⟩ = .inl m → m ≠ mf := by
    intro i hi m hqi hmf; rw [hmf] at hqi
    have hmem : Sum.inl mf ∈ queries := by rw [← hqi]; exact List.getElem_mem hi
    have hfm : mf ∈ signMsgsOf queries :=
      List.mem_filterMap.mpr ⟨.inl mf, hmem, rfl⟩
    have h_ct := List.contains_iff_mem.mpr hfm
    rw [h_ct] at h_not_signed
    exact Bool.noConfusion h_not_signed
  -- Sub-claim: before step j, no hash query matches (mf, tf)
  have h_not_hash_before : ∀ (i : Nat), i < j →
      ∀ (hi : i < queries.length), queries.get ⟨i, hi⟩ ≠ .inr (mf, tf) := by
    intro i hi_lt_j hi hqi
    exact absurd hqi (by
      have := List.not_of_lt_findIdx (j_def ▸ hi_lt_j)
      simpa using this)
  -- Main proof by forward induction
  suffices ∀ (k : Nat) (hk : k ≤ queries.length),
      ∃ st, stateBeforeWithState (A.interact n y) (A.numQueries n) oracle [] k = some st ∧
        (k ≤ j → assocLookup (mf, tf) st = none) ∧
        (j < k → assocLookup (mf, tf) st = some (ch ⟨j, hj⟩)) by
    obtain ⟨st, h_st, _, h_after⟩ := this queries.length le_rfl
    rw [h_final] at h_st; cases h_st
    exact h_after (by omega)
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨[], stateBeforeWithState_at_zero _ _ _ _, fun _ => rfl, fun h => absurd h (by omega)⟩
  | succ k' ih =>
    intro hk
    obtain ⟨st_prev, h_prev, h_none_if, h_some_if⟩ := ih (by omega)
    have hk'_fuel : k' < A.numQueries n := by omega
    -- Get query at step k'
    have hk'_len : k' < queries.length := by omega
    have h_qk : queryAtWithState (A.interact n y) (A.numQueries n) oracle [] k' =
        some (queries.get ⟨k', hk'_len⟩) := h_query k' hk'_len
    -- Step forward
    have h_step := stateBeforeWithState_step _ _ _ _ k' hk'_fuel st_prev
      (queries.get ⟨k', hk'_len⟩) h_prev h_qk
    set st_next := (oracle ⟨k', hk'_fuel⟩ st_prev (queries.get ⟨k', hk'_len⟩)).2
    refine ⟨st_next, h_step, fun hle => ?_, fun hlt => ?_⟩
    · -- k'+1 ≤ j, so k' < j: lookup stays none
      have h_prev_none := h_none_if (by omega)
      exact mapGameReal_step_preserves_none P Msg n (A.numQueries n) w y rs ch
        ⟨k', hk'_fuel⟩ st_prev (queries.get ⟨k', hk'_len⟩) (mf, tf) h_prev_none
        (h_not_hash_before k' (by omega) hk'_len)
        (fun m hm => h_not_sign_any k' hk'_len m hm)
    · -- j < k'+1, so j ≤ k'
      by_cases hjk : j = k'
      · -- k' = j: this is the insertion step
        subst hjk
        have h_prev_none := h_none_if le_rfl
        -- Query at step j is .inr (mf, tf)
        have h_qj_eq : queries.get ⟨j, hk'_len⟩ = .inr (mf, tf) := by
          have := List.findIdx_getElem (w := hj_in)
          simp only [decide_eq_true_eq] at this; exact this
        -- Oracle inserts (mf, tf) since assocLookup is none
        change assocLookup (mf, tf) st_next = some (ch ⟨j, hj⟩)
        simp only [st_next, oracle, h_qj_eq, mapGameRealOracle, h_prev_none, assocLookup]
        simp
      · -- k' > j: lookup persists from previous step
        have h_prev_some := h_some_if (by omega)
        change assocLookup (mf, tf) st_next = some (ch ⟨j, hj⟩)
        exact mapGameRealOracle_lookup_persist P Msg n (A.numQueries n) w y rs ch
          ⟨k', hk'_fuel⟩ st_prev mf tf (ch ⟨j, hj⟩) (queries.get ⟨k', hk'_len⟩)
          h_prev_some (fun m hm => h_not_sign_any k' hk'_len m hm)

/-- Every entry in the lazy-oracle map at step `idx` has its commitment
component witnessed by `lazyInsertedCommitAt` at some earlier step. -/
theorem lazyMap_entry_commit_source {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (idx : Nat) (hidx : idx < A.numQueries n)
    (st : MapState P Msg n)
    (key : Msg n × P.Commitment n) (v : P.Challenge n)
    (h_st : lazyMapBefore P Msg A n w y rs ch idx = some st)
    (h_mem : (key, v) ∈ st) :
    ∃ (i : Fin (A.numQueries n)), i.val < idx ∧
      lazyInsertedCommitAt P Msg A n w y rs ch i = some key.2 := by
  induction idx generalizing st key v with
  | zero =>
    unfold lazyMapBefore at h_st
    rw [stateBeforeWithState_at_zero] at h_st
    cases h_st; simp at h_mem
  | succ k ih =>
    have hk : k < A.numQueries n := Nat.lt_of_succ_lt hidx
    unfold lazyMapBefore at h_st
    obtain ⟨map_k, qry_k, h_map_k, h_qry_k, h_eq⟩ :=
      stateBeforeWithState_pred _ _ _ _ k hk st h_st
    rw [h_eq] at h_mem
    letI := P.commitmentDecEq n
    cases qry_k with
    | inl m =>
      simp only [lazyRomOracle] at h_mem
      cases hlookup : assocLookup (m, P.commit n w y (rs ⟨k, hk⟩)) map_k with
      | some c =>
        simp only [hlookup] at h_mem
        obtain ⟨i, hi_lt, hi⟩ :=
          ih hk map_k key v (by unfold lazyMapBefore; exact h_map_k) h_mem
        exact ⟨i, by omega, hi⟩
      | none =>
        simp only [hlookup] at h_mem
        cases h_mem with
        | head =>
          refine ⟨⟨k, hk⟩, by change k < k + 1; omega, ?_⟩
          unfold lazyInsertedCommitAt lazyQueryAt
          rw [h_qry_k]
        | tail _ h_tail =>
          obtain ⟨i, hi_lt, hi⟩ :=
            ih hk map_k key v (by unfold lazyMapBefore; exact h_map_k) h_tail
          exact ⟨i, by omega, hi⟩
    | inr mt =>
      simp only [lazyRomOracle] at h_mem
      cases hlookup : assocLookup (mt.1, mt.2) map_k with
      | some c =>
        simp only [hlookup] at h_mem
        obtain ⟨i, hi_lt, hi⟩ :=
          ih hk map_k key v (by unfold lazyMapBefore; exact h_map_k) h_mem
        exact ⟨i, by omega, hi⟩
      | none =>
        simp only [hlookup] at h_mem
        cases h_mem with
        | head =>
          refine ⟨⟨k, hk⟩, by change k < k + 1; omega, ?_⟩
          unfold lazyInsertedCommitAt lazyQueryAt
          rw [h_qry_k]
        | tail _ h_tail =>
          obtain ⟨i, hi_lt, hi⟩ :=
            ih hk map_k key v (by unfold lazyMapBefore; exact h_map_k) h_tail
          exact ⟨i, by omega, hi⟩

/-- If a signing query at step `k` finds its commitment already in the map,
then a pair-reuse event exists. -/
theorem map_lookup_implies_pairReuse {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    (k : Nat) (hk : k < A.numQueries n)
    (st : MapState P Msg n)
    (m : Msg n) (c : P.Challenge n)
    (h_st : lazyMapBefore P Msg A n w y rs ch k = some st)
    (h_qry : lazyQueryAt P Msg A n w y rs ch k = some (Sum.inl m))
    (h_lookup : assocLookup (m, P.commit n w y (rs ⟨k, hk⟩)) st = some c) :
    ∃ (i j : Fin (A.numQueries n)), i.val < j.val ∧
      lazyPairCommitReuse P Msg A n w y rs ch i j = true := by
  have h_mem := assocLookup_some_mem _ _ _ h_lookup
  obtain ⟨i, hi_lt, hi_commit⟩ := lazyMap_entry_commit_source P Msg A n w y rs ch
    k hk st (m, P.commit n w y (rs ⟨k, hk⟩)) c h_st h_mem
  refine ⟨i, ⟨k, hk⟩, hi_lt, ?_⟩
  unfold lazyPairCommitReuse
  rw [hi_commit, show (⟨k, hk⟩ : Fin (A.numQueries n)).val = k from rfl, h_qry]
  simp

/-- If no pair-reuse event occurs, LazyROM and MapGame_Real produce the same
run statement for fixed coins. -/
theorem lazy_run_stmt_eq_mapGame_real_run_stmt_of_no_reuse {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n) :
    (¬ ∃ (i j : Fin (A.numQueries n)), i.val < j.val ∧
      lazyPairCommitReuse P Msg A n w y rs ch i j = true) →
    lazyRom_run_stmt P Msg A n w y rs ch =
    mapGame_real_run_stmt P Msg A n w y rs ch := by
  intro h_no_reuse
  let q := A.numQueries n
  letI := P.commitmentDecEq n
  -- Step 1: Show the runWithState calls agree
  have h_run_eq : (A.interact n y).runWithState q
      (lazyRomOracle P Msg n q w y rs ch) [] =
    (A.interact n y).runWithState q
      (mapGameRealOracle P Msg n q w y rs ch) [] := by
    apply runWithState_eq_of_oracle_agree_on_trace
    intro k hk st qry h_st h_qry
    cases qry with
    | inr mt =>
      simp [lazyRomOracle, mapGameRealOracle]
    | inl m =>
      unfold lazyRomOracle mapGameRealOracle
      simp only
      cases h_lookup : assocLookup (m, P.commit n w y (rs ⟨k, hk⟩)) st with
      | none => rfl
      | some c =>
        exfalso
        exact h_no_reuse (map_lookup_implies_pairReuse P Msg A n w y rs ch
          k hk st m c h_st h_qry h_lookup)
  -- Step 2: Use the equality to simplify
  simp only [lazyRom_run_stmt, mapGame_real_run_stmt]
  have h_rw : (A.interact n y).runWithState (A.numQueries n)
      (lazyRomOracle P Msg n (A.numQueries n) w y rs ch) [] =
    (A.interact n y).runWithState (A.numQueries n)
      (mapGameRealOracle P Msg n (A.numQueries n) w y rs ch) [] := h_run_eq
  rw [h_rw]
  cases h_result : (A.interact n y).runWithState (A.numQueries n)
      (mapGameRealOracle P Msg n (A.numQueries n) w y rs ch) [] with
  | none => rfl
  | some val =>
    obtain ⟨queries, ⟨mf, tf, zf⟩, finalMap⟩ := val
    simp only
    split
    next hj =>
      -- Split on whether j < queries.length (hash was actually queried)
      by_cases hj_in :
        List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < queries.length
      · -- Hash WAS queried: use mapGameRealOracle_finalMap_lookup
        simp only [hj_in, ↓reduceIte]
        by_cases h_signed : (signMsgsOf queries).contains mf = true
        · -- Contains: both sides' `if` is `if verify && false = true then some else none = none`
          simp only [h_signed, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          cases assocLookup (mf, tf) finalMap <;> rfl
        · -- Not contains: use mapGameRealOracle_finalMap_lookup
          have h_lookup := mapGameRealOracle_finalMap_lookup P Msg A n w y rs ch
            queries mf tf zf finalMap h_result hj hj_in
            (by simpa using h_signed)
          simp only [h_lookup]
      · -- Hash was NOT queried: both sides are none
        simp only [hj_in, ↓reduceIte]
        -- LHS: match assocLookup ... with | some c => ... | none => none = none
        by_cases h_signed : (signMsgsOf queries).contains mf = true
        · simp only [h_signed, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          cases assocLookup (mf, tf) finalMap <;> rfl
        · have h_no_hash : Sum.inr (mf, tf) ∉ queries := by
            intro hmem
            apply hj_in
            rw [List.findIdx_lt_length]
            refine ⟨Sum.inr (mf, tf), hmem, ?_⟩
            dsimp
            exact of_decide_eq_self_eq_true _
          have h_none : assocLookup (mf, tf) finalMap = none := by
            set oracle := mapGameRealOracle P Msg n (A.numQueries n) w y rs ch
            have h_final := runWithState_finalState_eq_stateBeforeWithState _ _ _ _ _ _ _ h_result
            have h_query_at := runWithState_query_eq_queryAtWithState _ _ _ _ _ _ _ h_result
            have h_len_le := runWithState_length_le _ _ _ _ _ _ _ h_result
            -- No signing query has message mf
            have h_not_sign_mf : ∀ (i : Nat) (hi : i < queries.length) (m : Msg n),
                queries.get ⟨i, hi⟩ = .inl m → m ≠ mf := by
              intro i hi m hqi hmf; rw [hmf] at hqi
              have hmem : Sum.inl mf ∈ queries := by rw [← hqi]; exact List.getElem_mem hi
              apply h_signed
              simp only [signMsgsOf, List.contains_eq_mem, decide_eq_true_eq, List.mem_filterMap]
              exact ⟨Sum.inl mf, hmem, rfl⟩
            -- Forward induction: assocLookup stays none at every step
            suffices ∀ k (hk : k ≤ queries.length),
                ∃ st, stateBeforeWithState (A.interact n y) (A.numQueries n)
                    oracle [] k = some st ∧
                  assocLookup (mf, tf) st = none by
              obtain ⟨st, h_st, h_ans⟩ := this queries.length le_rfl
              rw [h_final] at h_st; cases h_st; exact h_ans
            intro k
            induction k with
            | zero =>
              intro _
              exact ⟨[], stateBeforeWithState_at_zero _ _ _ _, rfl⟩
            | succ k' ih =>
              intro hk
              obtain ⟨st_prev, h_prev, h_prev_none⟩ := ih (by omega)
              have hk'_fuel : k' < A.numQueries n := by omega
              have hk'_len : k' < queries.length := by omega
              have h_qk := h_query_at k' hk'_len
              have h_step := stateBeforeWithState_step _ _ _ _ k' hk'_fuel st_prev
                (queries.get ⟨k', hk'_len⟩) h_prev h_qk
              refine ⟨_, h_step, ?_⟩
              exact mapGameReal_step_preserves_none P Msg n (A.numQueries n) w y rs ch
                ⟨k', hk'_fuel⟩ st_prev (queries.get ⟨k', hk'_len⟩) (mf, tf) h_prev_none
                (by intro h_eq; exact h_no_hash (by rw [← h_eq]; exact List.getElem_mem hk'_len))
                (fun m hm => h_not_sign_mf k' hk'_len m hm)
          simp [h_none]
    next hj =>
      rfl

end
