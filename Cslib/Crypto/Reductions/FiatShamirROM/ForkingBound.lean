/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Reductions.FiatShamirROM.Games

@[expose] public section

/-!
# Forking Bound for MapGame1_HVZK

In the MapGame1_HVZK game, the signing oracle uses the HVZK simulator
and does **not** use the witness — so the game is parameterised by
`(witness, sim-randomness, challenges)` with the witness appearing only
through `kg.keyOf`. Applying the general forking lemma to this setup and
using special soundness to extract a witness from any two accepting
transcripts that branch at the same query gives the quadratic bound

  `mapGame1_hvzk_advantage ≤ √(q · Adv_R + q / |Ch|)`.

## Main results

* `mapGame1_hvzk_run_stmt_data` — inverts the run statement to recover
  the underlying `runWithState` trace and the query-index invariant
* `mapGame1_hvzk_run_stmt_verify` — verification holds on acceptance
* `mapGame1_hvzk_fork_sound` — two accepting forks with distinct
  challenges at the branch point yield a valid witness via special
  soundness
* `mapGame1_hvzk_relationSolver` — the explicit forking-based relation
  solver
* `forkProb_le_relationGame_advantage_mapGame1_hvzk` — relates `forkProb`
  to the relation-game advantage of the solver
* `mapGame1_hvzk_forking_bound` — the quadratic `√` bound
-/

open Cslib.Probability

/-- When `mapGame1_hvzk_run_stmt` succeeds, extract the underlying
`runWithState` result and key properties. -/
lemma mapGame1_hvzk_run_stmt_data {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK) (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (y : R.Statement n) (sr : Fin (A.numQueries n) → hvzk.SimRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    {j : Fin (A.numQueries n)} {mf : Msg n} {tf : P.Commitment n}
    {zf : P.Response n}
    (h : mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch =
      some (j, (mf, tf, zf))) :
    ∃ queries finalMap,
      (A.interact n y).runWithState (A.numQueries n)
        (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch) [] =
        some (queries, (mf, tf, zf), finalMap) ∧
      j.val ≤ queries.length ∧
      (∀ (hlt : j.val < queries.length), queries[j.val] = .inr (mf, tf)) := by
  letI := P.commitmentDecEq n
  have h_def : mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch =
      match (A.interact n y).runWithState (A.numQueries n)
        (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch) [] with
      | none => none
      | some (queries, (mf', tf', zf'), _) =>
        let jv := queries.findIdx (fun x => decide (x = .inr (mf', tf')))
        if hj : jv < A.numQueries n then
          if jv < queries.length then
            let signMsgs := queries.filterMap (fun q => match q with
              | .inl m => some m | .inr _ => none)
            if P.verify n y tf' (ch ⟨jv, hj⟩) zf' && !(signMsgs.contains mf') then
              some (⟨jv, hj⟩, (mf', tf', zf'))
            else none
          else none
        else none := by rfl
  rw [h_def] at h
  generalize h_run : (A.interact n y).runWithState (A.numQueries n)
    (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch) [] = result at h
  rcases result with _ | ⟨queries, ⟨mf', tf', zf'⟩, finalMap⟩
  · exact absurd h nofun
  · dsimp only [] at h
    split at h
    · split at h
      · split at h
        · have hinj := Option.some.inj h
          have hj_eq := (Prod.mk.inj hinj).1
          have hrest := (Prod.mk.inj hinj).2
          have hmf : mf' = mf := (Prod.mk.inj hrest).1
          have hrest2 := (Prod.mk.inj hrest).2
          have htf_eq : tf' = tf := (Prod.mk.inj hrest2).1
          have hzf : zf' = zf := (Prod.mk.inj hrest2).2
          refine ⟨queries, finalMap, ?_, ?_, ?_⟩
          · rw [← hmf, ← htf_eq, ← hzf]
          · have hj_val : queries.findIdx (fun x => decide (x = .inr (mf', tf'))) = j.val :=
              congrArg Fin.val hj_eq
            rw [← hj_val]; exact List.findIdx_le_length
          · intro hlt
            rw [← hmf, ← htf_eq]
            have hj_val : queries.findIdx (fun x => decide (x = .inr (mf', tf'))) = j.val :=
              congrArg Fin.val hj_eq
            have hlt' : queries.findIdx (fun x => decide (x = .inr (mf', tf'))) < queries.length :=
              hj_val ▸ hlt
            have h_beq := List.findIdx_getElem (w := hlt')
            have h_at := of_decide_eq_true h_beq
            simp only [hj_val] at h_at; exact h_at
        · exact absurd h nofun
      · exact absurd h nofun
    · exact absurd h nofun

/-- When `mapGame1_hvzk_run_stmt` succeeds, verification passed. -/
lemma mapGame1_hvzk_run_stmt_verify {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK) (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (y : R.Statement n) (sr : Fin (A.numQueries n) → hvzk.SimRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    {j : Fin (A.numQueries n)} {mf : Msg n} {tf : P.Commitment n}
    {zf : P.Response n}
    (h : mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch =
      some (j, (mf, tf, zf))) :
    P.verify n y tf (ch j) zf = true := by
  simp only [mapGame1_hvzk_run_stmt] at h
  split at h
  · exact absurd h nofun
  · split at h
    · split at h
      · split at h
        · have hinj := Option.some.inj h
          have hj_eq : _ = j := congrArg Prod.fst hinj
          have hmf := congrArg Prod.fst (congrArg Prod.snd hinj)
          have htf := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd hinj))
          have hzf := congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd hinj))
          subst hmf; subst htf; subst hzf; rw [← hj_eq]
          simp_all
        · exact absurd h nofun
      · exact absurd h nofun
    · exact absurd h nofun

/-- When the two forked runs both succeed at the same index with distinct
challenges, special soundness extracts a valid witness. -/
theorem mapGame1_hvzk_fork_sound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Nonempty (Msg n)]
    [∀ n, Nonempty (R.Witness n)]
    (_kg : R.WithKeyGen)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    [Nonempty (hvzk.SimRandomness n)]
    [Nonempty (P.Challenge n)] :
    ∀ (y : R.Statement n) (sr : Fin (A.numQueries n) → hvzk.SimRandomness n)
      (ch₁ ch₂ : Fin (A.numQueries n) → P.Challenge n)
      {j : Fin (A.numQueries n)} {mf₁ mf₂ : Msg n}
      {tf₁ tf₂ : P.Commitment n} {zf₁ zf₂ : P.Response n},
      mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch₁ = some (j, (mf₁, tf₁, zf₁)) →
      mapGame1_hvzk_run_stmt P Msg hvzk A n y sr
        (fun i => if i.val < j.val then ch₁ i else ch₂ i) =
        some (j, (mf₂, tf₂, zf₂)) →
      ch₁ j ≠ ch₂ j →
      R.relation n (ss.extract n y tf₁ (ch₁ j) zf₁ (ch₂ j) zf₂) y := by
  intro y sr ch₁ ch₂ j mf₁ mf₂ tf₁ tf₂ zf₁ zf₂ h₁ h₂ h_neq
  have hv₁ := mapGame1_hvzk_run_stmt_verify P Msg hvzk A n y sr ch₁ h₁
  have hv₂ := mapGame1_hvzk_run_stmt_verify P Msg hvzk A n y sr
    (fun i => if i.val < j.val then ch₁ i else ch₂ i) h₂
  have h_ch_at_j : (fun i : Fin (A.numQueries n) =>
      if i.val < j.val then ch₁ i else ch₂ i) j = ch₂ j :=
    if_neg (Nat.lt_irrefl _)
  rw [h_ch_at_j] at hv₂
  have htf : tf₁ = tf₂ := by
    obtain ⟨queries₁, _, hrun₁, hle₁, hget₁⟩ :=
      mapGame1_hvzk_run_stmt_data P Msg hvzk A n y sr ch₁ h₁
    set ch_fork : Fin (A.numQueries n) → P.Challenge n :=
      fun i => if i.val < j.val then ch₁ i else ch₂ i
    obtain ⟨queries₂, _, hrun₂, hle₂, hget₂⟩ :=
      mapGame1_hvzk_run_stmt_data P Msg hvzk A n y sr ch_fork h₂
    have h_oracle_agree : ∀ (i : Fin (A.numQueries n)), i.val < j.val →
        mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch₁ i =
        mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch_fork i := by
      intro i hi
      have h_ch_eq : ch_fork i = ch₁ i := if_pos hi
      funext map qry
      unfold mapGame1HvzkOracle
      rw [h_ch_eq]
    by_cases hjlt : j.val < queries₁.length
    · have hjlt₂ : j.val < queries₂.length :=
        OracleInteraction.runWithState_prefix_implies_length
          (A.interact n y) (A.numQueries n)
          (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch₁)
          (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch_fork)
          [] j.val h_oracle_agree hrun₁ hrun₂ hjlt
      have hq_eq : queries₁[j.val] = queries₂[j.val] :=
        OracleInteraction.runWithState_prefix_query_eq
          (A.interact n y) (A.numQueries n)
          (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch₁)
          (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch_fork)
          [] j.val h_oracle_agree hrun₁ hrun₂ hjlt hjlt₂
      have hq₁ : queries₁[j.val] = .inr (mf₁, tf₁) := hget₁ hjlt
      have hq₂ : queries₂[j.val] = .inr (mf₂, tf₂) := hget₂ hjlt₂
      have := hq₁.symm.trans (hq_eq.trans hq₂)
      exact (Prod.mk.inj (Sum.inr.inj this)).2
    · have h_agree_all : ∀ (i : Fin (A.numQueries n)),
          i.val < queries₁.length →
          mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch₁ i =
          mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch_fork i := by
        intro i hi
        exact h_oracle_agree i (lt_of_lt_of_le hi (Nat.le_of_not_lt hjlt))
      have hrun₂' :=
        OracleInteraction.runWithState_det_prefix
          (A.interact n y) (A.numQueries n)
          (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch₁)
          (mapGame1HvzkOracle P Msg hvzk n (A.numQueries n) y sr ch_fork)
          [] hrun₁ h_agree_all
      rw [hrun₂'] at hrun₂
      have hinj := Option.some.inj hrun₂
      have hrest := (Prod.mk.inj hinj).2
      have hforg := (Prod.mk.inj hrest).1
      exact (Prod.mk.inj (Prod.mk.inj hforg).2).1
  rw [← htf] at hv₂
  exact ss.soundness n y tf₁ (ch₁ j) zf₁ (ch₂ j) zf₂ h_neq hv₁ hv₂

/-- The explicit forking-based relation solver used in the Fiat-Shamir
reduction. -/
noncomputable def mapGame1_hvzk_relationSolver {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (_kg : R.WithKeyGen)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) : RelationSolver R where
  Randomness n :=
    (Fin (A.numQueries n) → hvzk.SimRandomness n) ×
      (Fin (A.numQueries n) → P.Challenge n) ×
      (Fin (A.numQueries n) → P.Challenge n)
  randomnessFintype n := by
    letI := hvzk.simRandomnessFintype n
    letI := P.challengeFintype n
    infer_instance
  randomnessNonempty n := by
    letI := hvzk.simRandomnessNonempty n
    letI := P.challengeNonempty n
    infer_instance
  find n y coins :=
    let fallback : R.Witness n := (show Nonempty (R.Witness n) from inferInstance).some
    let sr := coins.1
    let ch₁ := coins.2.1
    let ch₂ := coins.2.2
    match h₁ : mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch₁ with
    | none => fallback
    | some (j, (mf₁, tf₁, zf₁)) =>
      let ch_fork : Fin (A.numQueries n) → P.Challenge n :=
        fun i => if i.val < j.val then ch₁ i else ch₂ i
      match h₂ : mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch_fork with
      | none => fallback
      | some (j', (mf₂, tf₂, zf₂)) =>
        if h : j = j' ∧ ch₁ j ≠ ch₂ j then
          ss.extract n y tf₁ (ch₁ j) zf₁ (ch₂ j) zf₂
        else
          fallback

/-- The explicit relation solver succeeds whenever the forking experiment
produces two accepting transcripts at the same query with distinct
challenges. -/
theorem forkProb_le_relationGame_advantage_mapGame1_hvzk {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (kg : R.WithKeyGen)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    [Fintype (hvzk.SimRandomness n)] [Nonempty (hvzk.SimRandomness n)]
    [Fintype (P.Challenge n)] [Nonempty (P.Challenge n)]
    [DecidableEq (P.Challenge n)] :
    forkProb
      (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
      (P.Challenge n) (A.numQueries n)
      (mapGame1_hvzk_run P Msg kg hvzk A n) ≤
    (RelationGame R kg).advantage
      (mapGame1_hvzk_relationSolver P Msg kg ss hvzk A) n := by
  set q := A.numQueries n
  let B := mapGame1_hvzk_relationSolver P Msg kg ss hvzk A
  let e :
      ((R.Witness n × (Fin q → hvzk.SimRandomness n)) ×
        ((Fin q → P.Challenge n) × (Fin q → P.Challenge n))) ≃
      (R.Witness n × B.Randomness n) :=
    Equiv.prodAssoc (R.Witness n) (Fin q → hvzk.SimRandomness n)
      ((Fin q → P.Challenge n) × (Fin q → P.Challenge n))
  let f : R.Witness n × B.Randomness n → ℝ :=
    fun x => boolToReal (decide (R.relation n
      (B.find n (kg.keyOf n x.1) x.2) (kg.keyOf n x.1)))
  have h_mono :
      forkProb (R.Witness n × (Fin q → hvzk.SimRandomness n))
        (P.Challenge n) q (mapGame1_hvzk_run P Msg kg hvzk A n) ≤
      uniformExpect ((R.Witness n × (Fin q → hvzk.SimRandomness n)) ×
        ((Fin q → P.Challenge n) × (Fin q → P.Challenge n)))
        (f ∘ e) := by
    unfold forkProb uniformExpect
    apply Finset.sum_le_sum
    intro ⟨⟨w, sr⟩, ch₁, ch₂⟩ _
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    dsimp only [mapGame1_hvzk_run]
    rcases h_run₁ : mapGame1_hvzk_run_stmt P Msg hvzk A n (kg.keyOf n w) sr ch₁
      with _ | ⟨j, mf₁, tf₁, zf₁⟩
    · exact boolToReal_nonneg _
    · dsimp only [B, mapGame1_hvzk_relationSolver]
      rcases h_run₂ : mapGame1_hvzk_run_stmt P Msg hvzk A n (kg.keyOf n w) sr
          (fun i => if i.val < j.val then ch₁ i else ch₂ i)
        with _ | ⟨j', mf₂, tf₂, zf₂⟩
      · exact boolToReal_nonneg _
      · dsimp only []
        have h_if : (if (j : ℕ) < (j : ℕ) then ch₁ j else ch₂ j) = ch₂ j :=
          if_neg (Nat.lt_irrefl _)
        simp only [h_if]
        by_cases h_cond : j = j' ∧ ch₁ j ≠ ch₂ j
        · obtain ⟨hjj', h_neq⟩ := h_cond
          subst hjj'
          have h_cond' : j = j ∧ ch₁ j ≠ ch₂ j := ⟨rfl, h_neq⟩
          have h_rel := mapGame1_hvzk_fork_sound P Msg kg ss hvzk A n
            (kg.keyOf n w) sr ch₁ ch₂ h_run₁ h_run₂ h_neq
          have h_left : boolToReal (decide (j = j ∧ ch₁ j ≠ ch₂ j)) = 1 := by
            simp [boolToReal, h_neq]
          rw [h_left]
          have h_find :
              B.find n (kg.keyOf n w) (sr, ch₁, ch₂) =
                ss.extract n (kg.keyOf n w) tf₁ (ch₁ j) zf₁ (ch₂ j) zf₂ := by
            dsimp [B, mapGame1_hvzk_relationSolver]
            rw [h_run₁]
            simp only
            rw [h_run₂]
            simp [h_cond']
          have h_goal :
              1 ≤ boolToReal (decide (R.relation n
                (B.find n (kg.keyOf n w) (sr, ch₁, ch₂))
                (kg.keyOf n w))) := by
            rw [h_find]
            simp [boolToReal, h_rel]
          simpa [Function.comp, e, f] using h_goal
        · have h_left : boolToReal (decide (j = j' ∧ ch₁ j ≠ ch₂ j)) = 0 := by
            simp [boolToReal, h_cond]
          rw [h_left]
          simpa [Function.comp, e, f] using
            (boolToReal_nonneg
              (decide (R.relation n
                (B.find n (kg.keyOf n w) (sr, ch₁, ch₂))
                (kg.keyOf n w))))
  calc
    forkProb (R.Witness n × (Fin q → hvzk.SimRandomness n))
        (P.Challenge n) q (mapGame1_hvzk_run P Msg kg hvzk A n) ≤
      uniformExpect ((R.Witness n × (Fin q → hvzk.SimRandomness n)) ×
        ((Fin q → P.Challenge n) × (Fin q → P.Challenge n)))
        (f ∘ e) := h_mono
    _ = uniformExpect
        (R.Witness n × B.Randomness n)
        f := uniformExpect_congr e f
    _ = (RelationGame R kg).advantage B n := by
        rfl

/-- **Forking reduction for MapGame1_HVZK.** -/
theorem mapGame1_hvzk_forking_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (kg : R.WithKeyGen)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) :
    ∀ n,
      mapGame1_hvzk_advantage P Msg kg hvzk A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          (RelationGame R kg).advantage
            (mapGame1_hvzk_relationSolver P Msg kg ss hvzk A) n +
          (A.numQueries n : ℝ) /
            Fintype.card (P.Challenge n)) := by
  intro n
  letI := hvzk.simRandomnessFintype n
  letI := hvzk.simRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  letI := P.challengeDecEq n
  by_cases hq : A.numQueries n = 0
  · have h_adv_le : mapGame1_hvzk_advantage P Msg kg hvzk A n ≤ 0 := by
      change forkAcceptProb _ _ _ _ ≤ 0
      have h_nn := forkAcceptProb_nonneg
        (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
        (P.Challenge n) (A.numQueries n)
        (mapGame1_hvzk_run P Msg kg hvzk A n)
      suffices h : forkAcceptProb
          (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
          (P.Challenge n) (A.numQueries n)
          (mapGame1_hvzk_run P Msg kg hvzk A n) ≤ 0 from h
      unfold forkAcceptProb
      trans uniformExpect
        ((R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n)) ×
          (Fin (A.numQueries n) → P.Challenge n))
        (fun _ => (0 : ℝ))
      · apply uniformExpect_mono
        intro ⟨⟨w, sr⟩, ch⟩
        dsimp only []
        cases h_run : mapGame1_hvzk_run P Msg kg hvzk A n ⟨w, sr⟩ ch with
        | none => norm_num
        | some p => exact absurd p.1.isLt (by omega)
      · exact le_of_eq (uniformExpect_const _ 0)
    have h_rhs_nonneg : 0 ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          (RelationGame R kg).advantage
            (mapGame1_hvzk_relationSolver P Msg kg ss hvzk A) n +
          (A.numQueries n : ℝ) / Fintype.card (P.Challenge n)) :=
      Real.sqrt_nonneg _
    linarith
  · have hq_pos : 0 < A.numQueries n := by omega
    let Coins := R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n)
    let run := mapGame1_hvzk_run P Msg kg hvzk A n
    have h_fork := forking_lemma Coins (P.Challenge n) (A.numQueries n) run hq_pos
    have h_rel :=
      forkProb_le_relationGame_advantage_mapGame1_hvzk P Msg kg ss hvzk A n
    have h_rearrange :
        forkAcceptProb Coins (P.Challenge n) (A.numQueries n) run ^ 2 /
          (A.numQueries n : ℝ) ≤
        (RelationGame R kg).advantage
          (mapGame1_hvzk_relationSolver P Msg kg ss hvzk A) n +
        forkAcceptProb Coins (P.Challenge n) (A.numQueries n) run /
          Fintype.card (P.Challenge n) := by
      linarith
    have h_acc_nn := forkAcceptProb_nonneg Coins (P.Challenge n) (A.numQueries n) run
    have h_acc_le1 := forkAcceptProb_le_one Coins (P.Challenge n) (A.numQueries n) run
    have h_Ch_pos : (0 : ℝ) < Fintype.card (P.Challenge n) :=
      Nat.cast_pos.mpr Fintype.card_pos
    change forkAcceptProb Coins (P.Challenge n) (A.numQueries n) run ≤ _
    exact quadratic_sqrt_bound h_acc_nn h_acc_le1
      (Nat.cast_pos.mpr hq_pos) h_Ch_pos h_rearrange

end
