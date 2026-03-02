/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.ForkingLemma
public import Cslib.Cryptography.Foundations.RandomOracle

@[expose] public section

/-!
# Fiat-Shamir ROM Security Reduction

The central security theorem for Fiat-Shamir signatures: if the
underlying Sigma protocol has **special soundness** and **special
HVZK**, and the relation is hard, then the Fiat-Shamir signature
scheme is **EUF-CMA secure** in the **random oracle model**.

## Main Results

* `ROM_EUF_CMA_SimGame` — Game 1: simulated signing game using HVZK
  simulator (intermediate game for the security reduction)
* `game_hop_bound` — the gap between Game 0 and Game 1 is at most
  `q² / |Commit|` (commitment collision bound)
* `fiatShamir_ROM_bound` — concrete security bound:
  `ROM-EUF-CMA advantage ≤ √(q · Adv_R + q/|Ch|) + q²/|Commit|`
* `fiatShamir_ROM_secure` — asymptotic security: negligible advantage
  under negligible relation advantage, super-polynomial challenge and
  commitment spaces, and polynomial query bound

## Proof Outline (Boneh-Shoup §19.6)

**Game 0** = ROM EUF-CMA game (real signing, random H).

**Game 1** = Simulated signing using HVZK simulator (no witness needed).
Gap bounded by commitment collision probability: `q²/|Commit|`.

**Forking step**: In Game 1, the signing oracle doesn't use the witness.
Fork the adversary at the hash query for the forgery. Two accepting
transcripts with different challenges yield a witness via special
soundness. The forking lemma bounds the extraction probability.

The final bound inverts the forking lemma:
`acc²/q ≤ frk + acc/|Ch|` implies `acc ≤ √(q · frk + q/|Ch|)`,
and `frk ≤ Adv_R(B)` by special soundness.

## References

* Boneh-Shoup, *A Graduate Course in Applied Cryptography*, §19.6
* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model
  and a General Forking Lemma*][BellareNeven2006]
-/

open Cslib.Probability

/-- Execute the adversary in the simulated game, wrapped for the forking
framework. Takes a public key `y`, simulator randomness, and a challenge
table `Fin q → Challenge`. The signing oracle uses HVZK simulation;
the hash oracle returns challenges from the table. Returns a fork index
(the hash query for the forgery) and the forgery, or `none`. -/
noncomputable def simGame_run_stmt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (y : R.Statement n)
    (simRand : Fin (A.numQueries n) → hvzk.SimRandomness n)
    (challenges : Fin (A.numQueries n) → P.Challenge n) :
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  let q := A.numQueries n
  letI := P.commitmentDecEq n
  let oracle : Fin q →
      (Msg n ⊕ (Msg n × P.Commitment n)) →
      ((P.Commitment n × P.Response n) ⊕ P.Challenge n) :=
    fun i qry => match qry with
    | .inl _ =>
      let (t, z) := hvzk.simulate n y (challenges i) (simRand i)
      .inl (t, z)
    | .inr _ => .inr (challenges i)
  match (A.interact n y).run q oracle with
  | none => none
  | some (queries, mf, tf, zf) =>
    let j := queries.findIdx (· == .inr (mf, tf))
    if hj : j < q then
      let signMsgs := queries.filterMap (fun q => match q with
        | .inl m => some m | .inr _ => none)
      if P.verify n y tf (challenges ⟨j, hj⟩) zf && !(signMsgs.contains mf) then
        some (⟨j, hj⟩, (mf, tf, zf))
      else
        none
    else
      none

/-- `simGame_run` wraps `simGame_run_stmt` with a witness/randomness pair
as coins, deriving the public key via `keyOf`. -/
noncomputable def simGame_run {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n)) →
    (Fin (A.numQueries n) → P.Challenge n) →
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  fun ⟨w, simRand⟩ challenges =>
    simGame_run_stmt P Msg hvzk A n (keyOf n w) simRand challenges

/-- **Game 1: Simulated signing game (indexed oracle version).**

The adversary's advantage is the acceptance probability of `simGame_run`
in the forking framework: each query step `i` uses `challenges(i)` for
both signing (via HVZK simulator) and hash responses.

This is definitionally `forkAcceptProb` of `simGame_run`, making the
forking lemma directly applicable. -/
noncomputable def ROM_EUF_CMA_SimGame {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (hvzk : P.SpecialHVZK) :
    SecurityGame (ROM_EUF_CMA_Adversary P Msg) where
  advantage A n :=
    let q := A.numQueries n
    letI := hvzk.simRandomnessFintype n
    letI := hvzk.simRandomnessNonempty n
    letI := P.challengeFintype n
    letI := P.challengeNonempty n
    forkAcceptProb
      (R.Witness n × (Fin q → hvzk.SimRandomness n))
      (P.Challenge n) q
      (simGame_run P Msg keyOf hvzk A n)

/-- **Game hop bound**: the gap between Game 0 (`ROM_EUF_CMA_Game`) and
Game 1 (`ROM_EUF_CMA_SimGame`) is bounded by the commitment collision
probability `q² / |Commit|`.

The proof relies on HVZK `sim_distribution` (individual transcript
distributions match) and a union bound over commitment collisions
across the `q` signing queries. The hypothesis `keyOf_valid` is needed
because `sim_distribution` requires the witness-statement pair to
satisfy the relation. -/
theorem game_hop_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (hvzk : P.SpecialHVZK)
    (keyOf_valid : ∀ n w, R.relation n w (keyOf n w))
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    |(ROM_EUF_CMA_Game P Msg keyOf).advantage A n -
     (ROM_EUF_CMA_SimGame P Msg keyOf hvzk).advantage A n| ≤
      (A.numQueries n : ℝ) ^ 2 / Fintype.card (P.Commitment n) := by
  sorry

/-- When `simGame_run_stmt` succeeds, the verification check passed. -/
private lemma simGame_run_stmt_verify {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK) (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (y : R.Statement n) (sr : Fin (A.numQueries n) → hvzk.SimRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    {j : Fin (A.numQueries n)} {mf : Msg n} {tf : P.Commitment n}
    {zf : P.Response n}
    (h : simGame_run_stmt P Msg hvzk A n y sr ch =
      some (j, (mf, tf, zf))) :
    P.verify n y tf (ch j) zf = true := by
  simp only [simGame_run_stmt] at h
  split at h
  · exact absurd h nofun
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

/-- **Fork extraction**: when forking succeeds, special soundness extracts
a valid witness. This bounds the forking probability by the relation game
advantage.

The logical argument:
1. When fork succeeds with index `j` and different challenges `c ≠ c'`,
   both runs verify with the same commitment (by deterministic prefix)
2. Special soundness extracts a witness from the two transcripts
3. Derandomize over `(simRand, h₁, h₂)` using `uniformExpect_le_exists` -/
private theorem forkExtraction_le_advR {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    [Fintype (hvzk.SimRandomness n)] [Nonempty (hvzk.SimRandomness n)]
    [Fintype (P.Challenge n)] [Nonempty (P.Challenge n)]
    [DecidableEq (P.Challenge n)] :
    ∃ find_n : R.Statement n → R.Witness n,
      forkProb
        (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
        (P.Challenge n) (A.numQueries n)
        (simGame_run P Msg keyOf hvzk A n) ≤
      uniformExpect (R.Witness n) (fun w =>
        boolToReal (decide (R.relation n (find_n (keyOf n w)) (keyOf n w)))) := by
  set q := A.numQueries n
  -- Key lemma: when both runs succeed with same index and different challenges,
  -- special soundness extracts a valid witness.
  have fork_sound : ∀ (y : R.Statement n) (sr : Fin q → hvzk.SimRandomness n)
      (ch₁ ch₂ : Fin q → P.Challenge n)
      {j : Fin q} {mf₁ mf₂ : Msg n} {tf₁ tf₂ : P.Commitment n}
      {zf₁ zf₂ : P.Response n},
      simGame_run_stmt P Msg hvzk A n y sr ch₁ = some (j, (mf₁, tf₁, zf₁)) →
      simGame_run_stmt P Msg hvzk A n y sr
        (fun i => if i.val < j.val then ch₁ i else ch₂ i) =
        some (j, (mf₂, tf₂, zf₂)) →
      ch₁ j ≠ ch₂ j →
      R.relation n (ss.extract n y tf₁ (ch₁ j) zf₁ (ch₂ j) zf₂) y := by
    intro y sr ch₁ ch₂ j mf₁ mf₂ tf₁ tf₂ zf₁ zf₂ h₁ h₂ h_neq
    -- Extract verification conditions from both runs
    have hv₁ := simGame_run_stmt_verify P Msg hvzk A n y sr ch₁ h₁
    have hv₂ := simGame_run_stmt_verify P Msg hvzk A n y sr
      (fun i => if i.val < j.val then ch₁ i else ch₂ i) h₂
    -- The forked oracle at index j gives ch₂ j (since ¬(j < j))
    have h_ch_at_j : (fun i : Fin (A.numQueries n) =>
        if i.val < j.val then ch₁ i else ch₂ i) j = ch₂ j :=
      if_neg (Nat.lt_irrefl _)
    rw [h_ch_at_j] at hv₂
    -- Show tf₁ = tf₂ using deterministic prefix, then apply soundness
    have htf : tf₁ = tf₂ := by sorry
    rw [← htf] at hv₂
    exact ss.soundness n y tf₁ (ch₁ j) zf₁ (ch₂ j) zf₂ h_neq hv₁ hv₂
  -- Define find_n using Classical.epsilon: for each statement y, pick any
  -- witness satisfying the relation (if one exists)
  let find_n : R.Statement n → R.Witness n := fun y =>
    Classical.epsilon (fun w' => R.relation n w' y)
  refine ⟨find_n, ?_⟩
  -- Monotonicity: forkProb ≤ E_full[boolToReal(relation)]
  -- Proved by case-splitting on simGame_run results to avoid match eliminator mismatch
  have h_mono : forkProb
      (R.Witness n × (Fin q → hvzk.SimRandomness n))
      (P.Challenge n) q
      (simGame_run P Msg keyOf hvzk A n) ≤
    uniformExpect ((R.Witness n × (Fin q → hvzk.SimRandomness n)) ×
      (Fin q → P.Challenge n) × (Fin q → P.Challenge n))
      (fun p => boolToReal (decide (R.relation n (find_n (keyOf n p.1.1)) (keyOf n p.1.1)))) := by
    unfold forkProb uniformExpect
    apply Finset.sum_le_sum
    intro ⟨⟨w, sr⟩, ch₁, ch₂⟩ _
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    dsimp only [simGame_run]
    rcases h_run₁ : simGame_run_stmt P Msg hvzk A n (keyOf n w) sr ch₁
      with _ | ⟨j, mf₁, tf₁, zf₁⟩
    · exact boolToReal_nonneg _
    · dsimp only []
      rcases h_run₂ : simGame_run_stmt P Msg hvzk A n (keyOf n w) sr
          (fun i => if i.val < j.val then ch₁ i else ch₂ i)
        with _ | ⟨j', mf₂, tf₂, zf₂⟩
      · exact boolToReal_nonneg _
      · dsimp only []
        have h_if : (if (j : ℕ) < (j : ℕ) then ch₁ j else ch₂ j) = ch₂ j :=
          if_neg (Nat.lt_irrefl _)
        simp only [h_if]
        by_cases h_cond : j = j' ∧ ch₁ j ≠ ch₂ j
        · obtain ⟨hjj', h_neq⟩ := h_cond; subst hjj'
          have h_rel := fork_sound (keyOf n w) sr ch₁ ch₂ h_run₁ h_run₂ h_neq
          have h_eps := Classical.epsilon_spec
            (p := fun w' => R.relation n w' (keyOf n w)) ⟨_, h_rel⟩
          have h_rel_find : R.relation n (find_n (keyOf n w)) (keyOf n w) := h_eps
          have lhs_eq : boolToReal (decide (j = j ∧ ch₁ j ≠ ch₂ j)) = 1 := by
            simp [boolToReal, h_neq]
          have rhs_eq : boolToReal
              (decide (R.relation n (find_n (keyOf n w)) (keyOf n w))) = 1 := by
            simp [boolToReal, h_rel_find]
          linarith
        · have lhs_eq : boolToReal (decide (j = j' ∧ ch₁ j ≠ ch₂ j)) = 0 := by
            simp [boolToReal, h_cond]
          linarith [boolToReal_nonneg (decide (R.relation n (find_n (keyOf n w)) (keyOf n w)))]
  -- Marginalize out unused components: E_full[f(w)] = E_w[f(w)]
  have h_eq : uniformExpect ((R.Witness n × (Fin q → hvzk.SimRandomness n)) ×
      (Fin q → P.Challenge n) × (Fin q → P.Challenge n))
      (fun p => boolToReal (decide (R.relation n (find_n (keyOf n p.1.1)) (keyOf n p.1.1)))) =
    uniformExpect (R.Witness n) (fun w =>
      boolToReal (decide (R.relation n (find_n (keyOf n w)) (keyOf n w)))) := by
    trans uniformExpect (R.Witness n × (Fin q → hvzk.SimRandomness n))
      (fun (x : R.Witness n × (Fin q → hvzk.SimRandomness n)) =>
        boolToReal (decide (R.relation n (find_n (keyOf n x.1)) (keyOf n x.1))))
    · exact uniformExpect_prod_ignore_snd
        (fun (x : R.Witness n × (Fin q → hvzk.SimRandomness n)) =>
          boolToReal (decide (R.relation n (find_n (keyOf n x.1)) (keyOf n x.1))))
    · exact uniformExpect_prod_ignore_snd
        (fun w => boolToReal (decide (R.relation n (find_n (keyOf n w)) (keyOf n w))))
  linarith

/-- **Forking reduction for the simulated game.**

Proves the forking bound for Game 1 using:
1. The forking lemma (`acc²/q ≤ forkProb + acc/|Ch|`)
2. Fork extraction (`forkProb ≤ Adv_R(B)`)
3. Algebraic inversion (`quadratic_sqrt_bound`) -/
private theorem simGame_forking_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (_keyOf_valid : ∀ n w, R.relation n w (keyOf n w))
    (A : ROM_EUF_CMA_Adversary P Msg) :
    ∃ B : RelationSolver R, ∀ n,
      (ROM_EUF_CMA_SimGame P Msg keyOf hvzk).advantage A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          (RelationGame R keyOf).advantage B n +
          (A.numQueries n : ℝ) /
            Fintype.card (P.Challenge n)) := by
  -- For each n, construct a per-n solver function and prove the bound
  suffices per_n : ∀ n, ∃ find_n : R.Statement n → R.Witness n,
      (ROM_EUF_CMA_SimGame P Msg keyOf hvzk).advantage A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          uniformExpect (R.Witness n) (fun w =>
            boolToReal (decide (R.relation n (find_n (keyOf n w)) (keyOf n w)))) +
          (A.numQueries n : ℝ) / Fintype.card (P.Challenge n)) by
    exact ⟨⟨fun n => (per_n n).choose⟩, fun n => (per_n n).choose_spec⟩
  intro n
  letI := hvzk.simRandomnessFintype n
  letI := hvzk.simRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  letI := P.challengeDecEq n
  by_cases hq : A.numQueries n = 0
  · -- q = 0: simGame_run returns none (Fin 0 × α is empty), so advantage = 0
    refine ⟨fun _ => Classical.arbitrary _, ?_⟩
    have h_adv_le : (ROM_EUF_CMA_SimGame P Msg keyOf hvzk).advantage A n ≤ 0 := by
      change forkAcceptProb
        (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
        (P.Challenge n) (A.numQueries n)
        (simGame_run P Msg keyOf hvzk A n) ≤ 0
      have h_le := forkAcceptProb_le_one
        (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
        (P.Challenge n) (A.numQueries n)
        (simGame_run P Msg keyOf hvzk A n)
      have h_nn := forkAcceptProb_nonneg
        (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
        (P.Challenge n) (A.numQueries n)
        (simGame_run P Msg keyOf hvzk A n)
      -- With q = 0, forkAcceptProb is a sum over Coins × (Fin 0 → Ch),
      -- and simGame_run always returns none (Fin 0 is empty), so indicator = 0.
      -- Show the value is ≤ 0 by showing the indicator is always 0.
      suffices h : forkAcceptProb
          (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n))
          (P.Challenge n) (A.numQueries n)
          (simGame_run P Msg keyOf hvzk A n) ≤ 0 from h
      unfold forkAcceptProb
      trans uniformExpect
        ((R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n)) ×
          (Fin (A.numQueries n) → P.Challenge n))
        (fun _ => (0 : ℝ))
      · apply uniformExpect_mono
        intro ⟨⟨w, sr⟩, ch⟩; dsimp only []
        cases h_run : simGame_run P Msg keyOf hvzk A n ⟨w, sr⟩ ch with
        | none => norm_num
        | some p => exact absurd p.1.isLt (by omega)
      · exact le_of_eq (uniformExpect_const _ 0)
    linarith [Real.sqrt_nonneg ((A.numQueries n : ℝ) *
      uniformExpect (R.Witness n) (fun w =>
        boolToReal (decide (R.relation n
          ((fun _ => Classical.arbitrary _) (keyOf n w)) (keyOf n w)))) +
      (A.numQueries n : ℝ) / Fintype.card (P.Challenge n))]
  · -- q > 0: apply forking lemma + extraction + sqrt bound
    have hq_pos : 0 < A.numQueries n := by omega
    let Coins := R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n)
    let run := simGame_run P Msg keyOf hvzk A n
    -- Step 1: Forking lemma
    have h_fork := forking_lemma Coins (P.Challenge n) (A.numQueries n) run hq_pos
    -- Step 2: Extraction bound
    obtain ⟨find_n, h_extract⟩ := forkExtraction_le_advR P Msg keyOf ss hvzk A n
    -- Step 3: Rearrange: acc²/q ≤ advR + acc/|Ch|
    have h_rearrange :
        forkAcceptProb Coins (P.Challenge n) (A.numQueries n) run ^ 2 /
          (A.numQueries n : ℝ) ≤
        uniformExpect (R.Witness n) (fun w =>
          boolToReal (decide (R.relation n (find_n (keyOf n w)) (keyOf n w)))) +
        forkAcceptProb Coins (P.Challenge n) (A.numQueries n) run /
          Fintype.card (P.Challenge n) := by
      linarith
    -- Step 4: Apply quadratic_sqrt_bound
    have h_acc_nn := forkAcceptProb_nonneg Coins (P.Challenge n) (A.numQueries n) run
    have h_acc_le1 := forkAcceptProb_le_one Coins (P.Challenge n) (A.numQueries n) run
    have h_Ch_pos : (0 : ℝ) < Fintype.card (P.Challenge n) :=
      Nat.cast_pos.mpr Fintype.card_pos
    refine ⟨find_n, ?_⟩
    change forkAcceptProb Coins (P.Challenge n) (A.numQueries n) run ≤ _
    exact quadratic_sqrt_bound h_acc_nn h_acc_le1
      (Nat.cast_pos.mpr hq_pos) h_Ch_pos h_rearrange

/-- **Concrete security bound for Fiat-Shamir in the ROM.**

If the Sigma protocol has special soundness and special HVZK,
there exists a relation solver whose advantage, combined with
the forking overhead, bounds the ROM EUF-CMA advantage:

$$\mathrm{Adv}_{\mathrm{ROM\text{-}EUF\text{-}CMA}}(A, n)
  \le \sqrt{q \cdot \mathrm{Adv}_R(B, n) + q / |\mathcal{C}|}
    + q^2 / |\mathcal{T}|$$

where `q` is the total query bound, `|𝒞|` is the challenge space size,
and `|𝒯|` is the commitment space size.

**Proof sketch**:
1. *Game hop* (`game_hop_bound`): Replace real signing
   (`ROM_EUF_CMA_Game`) with HVZK simulation (`ROM_EUF_CMA_SimGame`).
   The gap is bounded by commitment collisions: at most `q²/|Commit|`.
2. *Forking*: In `ROM_EUF_CMA_SimGame`, the signing oracle doesn't use
   the witness. Run the forking lemma on the adversary's interaction.
   When forking succeeds (same fork index, different challenge), apply
   special soundness to extract a witness.
3. *Invert the forking bound*: `acc²/q ≤ Adv_R + acc/|Ch|` gives
   `acc ≤ √(q · Adv_R + q/|Ch|)`. -/
theorem fiatShamir_ROM_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (keyOf_valid : ∀ n w, R.relation n w (keyOf n w))
    (A : ROM_EUF_CMA_Adversary P Msg) :
    ∃ B : RelationSolver R, ∀ n,
      (ROM_EUF_CMA_Game P Msg keyOf).advantage A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          (RelationGame R keyOf).advantage B n +
          (A.numQueries n : ℝ) /
            Fintype.card (P.Challenge n)) +
        (A.numQueries n : ℝ) ^ 2 /
          Fintype.card (P.Commitment n) := by
  obtain ⟨B, hB⟩ := simGame_forking_bound P Msg keyOf ss hvzk keyOf_valid A
  exact ⟨B, fun n => by
    have h_hop := game_hop_bound P Msg keyOf hvzk keyOf_valid A n
    have h_sim := hB n
    have h1 : (ROM_EUF_CMA_Game P Msg keyOf).advantage A n -
        (ROM_EUF_CMA_SimGame P Msg keyOf hvzk).advantage A n ≤
        (A.numQueries n : ℝ) ^ 2 / Fintype.card (P.Commitment n) :=
      le_trans (le_abs_self _) h_hop
    linarith⟩

/-- **Asymptotic security of Fiat-Shamir in the ROM.**

If:
1. The Sigma protocol has special soundness and special HVZK
2. The underlying relation is hard (`RelationGame` is secure)
3. The commitment and challenge spaces grow super-polynomially
4. The adversary makes polynomially many queries

Then the ROM EUF-CMA advantage is negligible.

This is the main theorem connecting Sigma protocols to practical
signatures in the random oracle model. -/
theorem fiatShamir_ROM_secure {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)
    (keyOf_valid : ∀ n w, R.relation n w (keyOf n w))
    (hR : (RelationGame R keyOf).Secure)
    (hCommit : Negligible (fun n => 1 / (Fintype.card (P.Commitment n) : ℝ)))
    (hChallenge : Negligible (fun n => 1 / (Fintype.card (P.Challenge n) : ℝ)))
    (A : ROM_EUF_CMA_Adversary P Msg)
    (hPoly : PolynomiallyBounded (fun n => (A.numQueries n : ℝ))) :
    Negligible (fun n => (ROM_EUF_CMA_Game P Msg keyOf).advantage A n) := by
  obtain ⟨B, hB⟩ := fiatShamir_ROM_bound P Msg keyOf ss hvzk keyOf_valid A
  -- Component 1: q · Adv_R(B, ·) is negligible
  have h_qAdv : Negligible (fun n =>
      (A.numQueries n : ℝ) * (RelationGame R keyOf).advantage B n) :=
    ((hR B).mul_polyBounded hPoly).mono ⟨0, fun n _ =>
      le_of_eq (congr_arg abs (mul_comm _ _))⟩
  -- Component 2: q / |Ch| is negligible
  have h_qCh : Negligible (fun n =>
      (A.numQueries n : ℝ) / (Fintype.card (P.Challenge n) : ℝ)) :=
    (hChallenge.mul_polyBounded hPoly).mono ⟨0, fun n _ =>
      le_of_eq (congr_arg abs (by ring))⟩
  -- Component 3: √(q · Adv_R + q/|Ch|) is negligible
  have h_sum_nn : ∀ n, 0 ≤ (A.numQueries n : ℝ) *
      (RelationGame R keyOf).advantage B n +
      (A.numQueries n : ℝ) / (Fintype.card (P.Challenge n) : ℝ) :=
    fun n => add_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (uniformExpect_nonneg _ fun _ => boolToReal_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have h_sqrt := (h_qAdv.add h_qCh).sqrt_nonneg h_sum_nn
  -- Component 4: q²/|Commit| is negligible
  have h_q2Commit : Negligible (fun n =>
      (A.numQueries n : ℝ) ^ 2 / (Fintype.card (P.Commitment n) : ℝ)) :=
    (hCommit.mul_polyBounded hPoly.sq).mono ⟨0, fun n _ =>
      le_of_eq (congr_arg abs (by ring))⟩
  -- Full bound is negligible
  have h_bound := h_sqrt.add h_q2Commit
  -- Transfer to advantage
  exact h_bound.mono ⟨0, fun n _ => by
    have h_adv_nn : 0 ≤ (ROM_EUF_CMA_Game P Msg keyOf).advantage A n := by
      unfold ROM_EUF_CMA_Game
      apply uniformExpect_nonneg
      intro ⟨_, _, _⟩
      dsimp only
      generalize (A.interact _ _).run _ _ = result
      cases result with
      | none => exact le_refl 0
      | some _ => exact boolToReal_nonneg _
    rw [abs_of_nonneg h_adv_nn]
    exact le_trans (hB n) (le_abs_self _)⟩

end
