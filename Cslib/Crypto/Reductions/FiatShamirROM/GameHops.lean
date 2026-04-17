/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Reductions.FiatShamirROM.CollisionBound

@[expose] public section

/-!
# Game-Hop Chain for Fiat-Shamir ROM

This file assembles the game-hop chain for the Fiat-Shamir ROM reduction:
`ROM → LazyROM → MapGame_Real → MapGame1_HVZK`.

## Main results

* `rom_eq_lazy_rom` — lazy-sampling step: the ROM advantage equals the
  LazyROM advantage (exact equality, via `lazyRomH_runWithState_uniform_eq`)
* `lazy_le_mapGame_real` — collision step: LazyROM ≤ MapGame_Real + q²δ
  (via `lazy_run_stmt_eq_mapGame_real_run_stmt_of_no_reuse` and the
  collision bound `lazyCommitReuse_bound`)
* `rom_le_mapGame_real` — combines the two preceding hops
* `rom_eq_mapGame1_hvzk_bound` — extends with the HVZK switch
  (`mapGame_real_eq_mapGame1_hvzk` from `Games`)
-/

open Cslib.Probability

/-- **Lazy sampling**: the ROM EUF-CMA advantage equals the LazyROM
advantage. The ROM game samples a full random function
`H : Msg × Comm → Ch` and evaluates it at ≤ q adaptively-chosen points.
By the lazy sampling principle, evaluating a uniform random function at
fresh points yields independent uniform values, which is exactly what
the per-query challenges `ch_i` provide. Cached values in the Map ensure
consistency on repeated queries, faithfully reproducing `H`.

**Proof approach:** Use `uniformExpect_prod` to factor out the witness/
randomness sample, then apply `lazyRomH_runWithState_uniform_eq` to
exchange the full-random-function `H : (Msg × Commitment) → Challenge`
for per-step uniform challenges `ch : Fin q → Challenge` (the lazy
marginal), and finally match the post-processing. -/
theorem rom_eq_lazy_rom {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (ROM_EUF_CMA_Game P Msg kg).advantage A n =
    lazyRom_advantage P Msg kg A n := by
  simp only [ROM_EUF_CMA_Game, romCmaWinCondition,
    List.contains_eq_mem, List.mem_filterMap,
    Sum.exists, Option.some.injEq, exists_eq_right, reduceCtorEq, and_false,
    exists_const, or_false, lazyRom_advantage, forkAcceptProb,
    lazyRom_run, lazyRom_run_stmt, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not]
  conv_lhs => rw [uniformExpect_prod]
  conv_rhs => rw [uniformExpect_prod]
  congr 1
  ext wrs
  rcases wrs with ⟨w, rs⟩
  let runPayoff : Option (List (Msg n ⊕ (Msg n × P.Commitment n)) ×
      (Msg n × P.Commitment n × P.Response n) × MapState P Msg n) → ℝ :=
    fun result =>
      letI := P.commitmentDecEq n
      match result with
      | none => 0
      | some (queries, (mf, tf, zf), finalMap) =>
        let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
        if hj : j < A.numQueries n then
          match assocLookup (mf, tf) finalMap with
          | some c => boolToReal
              (P.verify n (kg.keyOf n w) tf c zf && !decide (mf ∈ signMsgsOf queries))
          | none => 0
        else 0
  have h_swap :=
    lazyRomH_runWithState_uniform_eq (P := P) (Msg := Msg)
      n (A.numQueries n) (A.interact n (kg.keyOf n w)) w (kg.keyOf n w) rs
      runPayoff
  let rhsNested : (Fin (A.numQueries n) → P.Challenge n) → ℝ := fun ch =>
    match
      (match
        (A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
          (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs ch) [] with
      | none => (none : Option (Fin (A.numQueries n) ×
          (Msg n × P.Commitment n × P.Response n)))
      | some (queries, (mf, tf, zf), finalMap) =>
        if hj : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n then
          match assocLookup (mf, tf) finalMap with
          | some c =>
            if P.verify n (kg.keyOf n w) tf c zf &&
                !(signMsgsOf queries).contains mf then
              some
                (⟨List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries, hj⟩,
                  (mf, tf, zf))
            else none
          | none => none
        else (none : Option (Fin (A.numQueries n) ×
            (Msg n × P.Commitment n × P.Response n))))
    with
    | none => 0
    | some _ => 1
  have h_rhs_fun :
      (fun ch =>
        runPayoff ((A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
          (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs ch) [])) =
      rhsNested := by
    funext ch
    let result :=
      (A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
        (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs ch) []
    cases h_result : result with
    | none =>
      simp [rhsNested, runPayoff, boolToReal, result, h_result]
    | some triple =>
      rcases triple with ⟨queries, forg, finalMap⟩
      rcases forg with ⟨mf, tf, zf⟩
      by_cases hj : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n
      · cases h_lookup : assocLookup (mf, tf) finalMap with
        | none =>
          simp [rhsNested, runPayoff, boolToReal, result, h_result, hj, h_lookup]
        | some c =>
          have h_contains :
              (signMsgsOf queries).contains mf =
              decide (mf ∈ signMsgsOf queries) := by
            simp
          by_cases hverify :
              (P.verify n (kg.keyOf n w) tf c zf &&
                !decide (mf ∈ signMsgsOf queries)) = true
          · simp [rhsNested, runPayoff, boolToReal, result, h_result, hj, h_lookup]
            split_ifs <;> rfl
          · simp [rhsNested, runPayoff, boolToReal, result, h_result, hj, h_lookup]
            split_ifs <;> rfl
      · simp [rhsNested, runPayoff, boolToReal, result, h_result, hj]
  have h_main :
      uniformExpect (Fin (A.numQueries n) → (Msg n × P.Commitment n → P.Challenge n))
        (fun Hs =>
          runPayoff
            ((A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
              (fun i st qry =>
                lazyRomHOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs i (Hs i) st qry) [])) =
      uniformExpect (Fin (A.numQueries n) → P.Challenge n) rhsNested := by
    calc
      uniformExpect (Fin (A.numQueries n) → (Msg n × P.Commitment n → P.Challenge n))
          (fun Hs =>
            runPayoff
              ((A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
                (fun i st qry =>
                  lazyRomHOracle P Msg n (A.numQueries n)
                    w (kg.keyOf n w) rs i (Hs i) st qry) [])) =
        uniformExpect (Fin (A.numQueries n) → P.Challenge n)
          (fun ch =>
            runPayoff ((A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
              (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs ch) [])) := by
        simpa [runPayoff, boolToReal, lazyRomHOracle] using h_swap
      _ = uniformExpect (Fin (A.numQueries n) → P.Challenge n) rhsNested := by
        rw [h_rhs_fun]
  let goalRhs : (Fin (A.numQueries n) → P.Challenge n) → ℝ := fun b =>
    match
      match
        (A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
          (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs b) [] with
      | none => (none : Option (Fin (A.numQueries n) ×
          (Msg n × P.Commitment n × P.Response n)))
      | some (queries, (mf, tf, zf), finalMap) =>
        if h : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n then
          match assocLookup (mf, tf) finalMap with
          | some c =>
            if P.verify n (kg.keyOf n w) tf c zf = true ∧
                mf ∉ signMsgsOf queries then
              some
                (⟨List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries, h⟩,
                  (mf, tf, zf))
            else none
          | none => none
        else (none : Option (Fin (A.numQueries n) ×
            (Msg n × P.Commitment n × P.Response n)))
    with
    | none => 0
    | some _ => 1
  have h_rhs_nested_eq_goal : rhsNested = goalRhs := by
    funext b
    simp only [rhsNested, goalRhs, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not]
  conv_lhs =>
    arg 2
    ext Hs
    simp [runPayoff, boolToReal, lazyRomHOracle]
  refine h_main.trans ?_
  rw [h_rhs_nested_eq_goal]
  apply congrArg (uniformExpect (Fin (A.numQueries n) → P.Challenge n))
  funext b
  let result :=
    (A.interact n (kg.keyOf n w)).runWithState (A.numQueries n)
      (lazyRomOracle P Msg n (A.numQueries n) w (kg.keyOf n w) rs b) []
  cases h_result : result with
  | none =>
    simp [goalRhs, result, h_result]
  | some triple =>
    rcases triple with ⟨queries, forg, finalMap⟩
    rcases forg with ⟨mf, tf, zf⟩
    by_cases hj : List.findIdx (fun x => decide (x = Sum.inr (mf, tf))) queries < A.numQueries n
    · cases h_lookup : assocLookup (mf, tf) finalMap with
      | none =>
        simp [goalRhs, result, h_result, hj, h_lookup]
      | some c =>
        simp only [goalRhs, result, h_result, hj, h_lookup]
        split_ifs <;> rfl
    · simp [goalRhs, result, h_result, hj]

/-- **LazyROM ≤ MapGame_Real + q²δ**: the game hop from lazy ROM to
MapGame_Real. The two games use the same coin type
`(W × (Fin q → PR)) × (Fin q → Ch)` and identical post-processing.
Their oracles differ only at signing steps where the key
`(m, commit(w,y,rs_i))` is already in the Map:

- `lazyRomOracle` uses the cached challenge (simulating a consistent
  random function)
- `mapGameRealOracle` always uses the fresh `ch_i`

When no such collision occurs, both oracles are identical at every step,
producing the same interaction and hence the same indicator value.

The collision probability is bounded by `q² · δ`:
- **Signing-signing**: commitment collision between `rs_i` and `rs_j`,
  bounded by `uniformExpect_commit_collision_pair` / `δ` per pair
- **Hash-signing**: adversary predicting `commit(w,y,rs_i)` before step
  `i`, bounded by `UnpredictableCommitments` since `rs_i` is independent
  of the adversary's queries before step `i`

Total: ≤ `q(q-1)/2` pairs × `δ` each ≤ `q² · δ`. -/
theorem lazy_le_mapGame_real {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    lazyRom_advantage P Msg kg A n ≤
    mapGame_real_advantage P Msg kg A n +
    (A.numQueries n : ℝ) ^ 2 * δ n := by
  classical
  let q := A.numQueries n
  letI := P.proverRandomnessFintype n
  letI := P.proverRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  let Ω := (R.Witness n × (Fin q → P.ProverRandomness n)) ×
      (Fin q → P.Challenge n)
  let fL : Ω → ℝ := fun ⟨⟨w, rs⟩, ch⟩ =>
    match lazyRom_run_stmt P Msg A n w (kg.keyOf n w) rs ch with
    | none => 0
    | some _ => 1
  let fM : Ω → ℝ := fun ⟨⟨w, rs⟩, ch⟩ =>
    match mapGame_real_run_stmt P Msg A n w (kg.keyOf n w) rs ch with
    | none => 0
    | some _ => 1
  let bad : Ω → Prop := fun ⟨⟨w, rs⟩, ch⟩ =>
    ∃ (i j : Fin q), i.val < j.val ∧
      lazyPairCommitReuse P Msg A n w (kg.keyOf n w) rs ch i j = true
  have h_agree : ∀ ω : Ω, ¬ bad ω → fL ω = fM ω := by
    intro ⟨⟨w, rs⟩, ch⟩ hnb
    dsimp [fL, fM, bad] at hnb ⊢
    rw [lazy_run_stmt_eq_mapGame_real_run_stmt_of_no_reuse
      P Msg A n w (kg.keyOf n w) rs ch hnb]
  have h_fL_nn : ∀ ω : Ω, 0 ≤ fL ω := by
    intro ⟨⟨w, rs⟩, ch⟩
    dsimp [fL]
    split <;> norm_num
  have h_fL_le : ∀ ω : Ω, fL ω ≤ 1 := by
    intro ⟨⟨w, rs⟩, ch⟩
    dsimp [fL]
    split <;> norm_num
  have h_fM_nn : ∀ ω : Ω, 0 ≤ fM ω := by
    intro ⟨⟨w, rs⟩, ch⟩
    dsimp [fM]
    split <;> norm_num
  have h_fM_le : ∀ ω : Ω, fM ω ≤ 1 := by
    intro ⟨⟨w, rs⟩, ch⟩
    dsimp [fM]
    split <;> norm_num
  have h_hop := uniformExpect_game_hop Ω fL fM bad h_agree
    h_fL_nn h_fL_le h_fM_nn h_fM_le
  have h_bad_bound :
      uniformExpect Ω (fun ω => if bad ω then (1 : ℝ) else 0) ≤
      (q : ℝ) ^ 2 * δ n := by
    simpa [Ω, bad] using
      lazyCommitReuse_bound P Msg kg A n δ h_unpred
  have h_sub :
      uniformExpect Ω fL - uniformExpect Ω fM ≤
        uniformExpect Ω (fun ω => if bad ω then (1 : ℝ) else 0) :=
    le_trans (le_abs_self _) h_hop
  have h_lin :
      uniformExpect Ω fL ≤
        uniformExpect Ω fM +
        uniformExpect Ω (fun ω => if bad ω then (1 : ℝ) else 0) := by
    linarith [h_sub]
  have h_main :
      uniformExpect Ω fL ≤ uniformExpect Ω fM + (q : ℝ) ^ 2 * δ n :=
    le_trans h_lin (by linarith [h_bad_bound])
  have h_advL : lazyRom_advantage P Msg kg A n = uniformExpect Ω fL := by
    unfold lazyRom_advantage forkAcceptProb lazyRom_run
    congr!; rename_i x; obtain ⟨⟨w, rs⟩, ch⟩ := x
    dsimp [fL]; split <;> simp_all
  have h_advM : mapGame_real_advantage P Msg kg A n = uniformExpect Ω fM := by
    unfold mapGame_real_advantage forkAcceptProb mapGame_real_run
    congr!; rename_i x; obtain ⟨⟨w, rs⟩, ch⟩ := x
    dsimp [fM]; split <;> simp_all
  rw [h_advL, h_advM]; exact h_main

/-- **ROM ≤ MapGame_Real + q²δ**: the ROM advantage is at most the
MapGame_Real advantage plus a commitment collision term `q² · δ`.

Proved by combining:
- `rom_eq_lazy_rom`: ROM advantage = LazyROM advantage (lazy sampling)
- `lazy_le_mapGame_real`: LazyROM ≤ MapGame_Real + q²δ (game hop) -/
theorem rom_le_mapGame_real {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    (ROM_EUF_CMA_Game P Msg kg).advantage A n ≤
    mapGame_real_advantage P Msg kg A n +
    (A.numQueries n : ℝ) ^ 2 * δ n := by
  have h1 := rom_eq_lazy_rom P Msg kg A n
  have h2 := lazy_le_mapGame_real P Msg kg A n δ h_unpred
  linarith

/-- **ROM game hop bound**: combines `rom_le_mapGame_real` (lazy sampling +
collision bound) with `mapGame_real_eq_mapGame1_hvzk` (HVZK switch). -/
theorem rom_eq_mapGame1_hvzk_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    (ROM_EUF_CMA_Game P Msg kg).advantage A n ≤
      mapGame1_hvzk_advantage P Msg kg hvzk A n +
      (A.numQueries n : ℝ) ^ 2 * δ n := by
  have h1 := rom_le_mapGame_real P Msg kg A n δ h_unpred
  have h2 := mapGame_real_eq_mapGame1_hvzk P Msg kg hvzk A n
  linarith

end
