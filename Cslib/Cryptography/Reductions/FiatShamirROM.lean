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
private theorem run_uniformExpect_oracle_eq
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
    -- Fin 0 → S is a singleton; run at fuel 0 doesn't use the oracle.
    cases interaction with
    | done a =>
      -- run (.done a) 0 _ = some ([], a)
      change uniformExpect _ (fun _ => f (some ([], a))) =
             uniformExpect _ (fun _ => f (some ([], a)))
      rw [uniformExpect_const, uniformExpect_const]
    | query q k =>
      -- run (.query q k) 0 _ = none
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
      -- Shifted oracles for the IH
      let shifted₁ : Fin n → S₁ → Q → R :=
        fun j => oracle₁ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      let shifted₂ : Fin n → S₂ → Q → R :=
        fun j => oracle₂ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      have h_shifted : ∀ (j : Fin n) (q' : Q) (g : R → ℝ),
          uniformExpect S₁ (fun s => g (shifted₁ j s q')) =
          uniformExpect S₂ (fun s => g (shifted₂ j s q')) :=
        fun j => h_marginal ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      -- Post-processing: wraps result with q :: prefix
      let postF : Option (List Q × A) → ℝ := fun result =>
        f (match result with | none => none | some (qs, a) => some (q :: qs, a))
      -- Step 1: Convert Fin(n+1) → S to S × (Fin n → S) using Fin.consEquiv,
      -- then factor with uniformExpect_prod.
      -- LHS conversion
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
      -- RHS conversion
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
      -- Step 2: Apply IH to rewrite inner expectation
      -- For each s₀, the inner expectation over Fin n → S₁ equals Fin n → S₂
      conv_lhs =>
        arg 2; ext s₀
        rw [ih (k (oracle₁ ⟨0, Nat.zero_lt_succ n⟩ s₀ q)) shifted₁ shifted₂
          h_shifted postF]
      -- Step 3: Apply h_marginal for the outer expectation
      -- Goal: E_{s₀:S₁}[G(oracle₁ 0 s₀ q)] = E_{s₀:S₂}[G(oracle₂ 0 s₀ q)]
      exact h_marginal ⟨0, Nat.zero_lt_succ n⟩ q
        (fun r => uniformExpect (Fin n → S₂) (fun ss' =>
          postF ((k r).run n (fun j => shifted₂ j (ss' j)))))

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
    let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
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

/-- Execute the adversary in the per-query game. Same as `simGame_run_stmt`
but uses the real prover (commit + respond) instead of the HVZK simulator.
Challenges are drawn from a per-query table rather than a consistent hash. -/
noncomputable def perQueryGame_run_stmt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (challenges : Fin (A.numQueries n) → P.Challenge n) :
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  let q := A.numQueries n
  letI := P.commitmentDecEq n
  let oracle : Fin q →
      (Msg n ⊕ (Msg n × P.Commitment n)) →
      ((P.Commitment n × P.Response n) ⊕ P.Challenge n) :=
    fun i qry => match qry with
    | .inl _ =>
      let t := P.commit n w y (rs i)
      .inl (t, P.respond n w y (rs i) (challenges i))
    | .inr _ => .inr (challenges i)
  match (A.interact n y).run q oracle with
  | none => none
  | some (queries, mf, tf, zf) =>
    let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
    if hj : j < q then
      let signMsgs := queries.filterMap (fun q => match q with
        | .inl m => some m | .inr _ => none)
      if P.verify n y tf (challenges ⟨j, hj⟩) zf && !(signMsgs.contains mf) then
        some (⟨j, hj⟩, (mf, tf, zf))
      else
        none
    else
      none

/-- `perQueryGame_run` wraps `perQueryGame_run_stmt` with a witness/randomness
pair as coins, deriving the public key via `keyOf`. -/
noncomputable def perQueryGame_run {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (R.Witness n × (Fin (A.numQueries n) → P.ProverRandomness n)) →
    (Fin (A.numQueries n) → P.Challenge n) →
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  fun ⟨w, rs⟩ challenges =>
    perQueryGame_run_stmt P Msg A n w (keyOf n w) rs challenges

/-- **Per-query game**: real prover with per-query independent challenges.
This is an intermediate game between Game 0 (consistent hash) and
Game 1 (HVZK simulator). -/
noncomputable def ROM_EUF_CMA_PerQueryGame {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (keyOf : ∀ n, R.Witness n → R.Statement n) :
    SecurityGame (ROM_EUF_CMA_Adversary P Msg) where
  advantage A n :=
    let q := A.numQueries n
    letI := P.challengeFintype n
    letI := P.challengeNonempty n
    forkAcceptProb
      (R.Witness n × (Fin q → P.ProverRandomness n))
      (P.Challenge n) q
      (perQueryGame_run P Msg keyOf A n)

/-- Replacing the consistent hash oracle `H` with per-query independent
challenges changes the game outcome by at most `q² · δ`, where `δ` bounds
the probability of predicting any single commitment value.

**Proof sketch** (Boneh-Shoup §19.6.1): the games differ only when a
signing query's commitment `(m_i, t_i)` was previously queried to the
hash table. Each commitment has probability `≤ δ` of hitting any
specific point, and there are `≤ q` previous queries. Union bound
over `q` signing queries gives `q² · δ`. -/
theorem rom_to_perquery_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (keyOf_valid : ∀ n w, R.relation n w (keyOf n w))
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    |(ROM_EUF_CMA_Game P Msg keyOf).advantage A n -
     (ROM_EUF_CMA_PerQueryGame P Msg keyOf).advantage A n| ≤
      (A.numQueries n : ℝ) ^ 2 * δ n := by
  sorry

/-- Replacing the real prover with the HVZK simulator does not change
the expected game outcome, because `sim_distribution` guarantees that
for each fixed challenge, the real and simulated transcript distributions
are identical. Since challenges are independent across queries, the
joint distribution is preserved.

**Proof sketch**: Hybrid argument, replacing real prover with simulator
one query at a time. At each step, apply `sim_distribution`. -/
theorem perquery_eq_simgame {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (hvzk : P.SpecialHVZK)
    (keyOf_valid : ∀ n w, R.relation n w (keyOf n w))
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (ROM_EUF_CMA_PerQueryGame P Msg keyOf).advantage A n =
    (ROM_EUF_CMA_SimGame P Msg keyOf hvzk).advantage A n := by
  let q := A.numQueries n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  letI := hvzk.simRandomnessFintype n
  letI := hvzk.simRandomnessNonempty n
  letI := P.commitmentDecEq n
  -- Both sides are forkAcceptProb
  change forkAcceptProb _ _ q (perQueryGame_run P Msg keyOf A n) =
       forkAcceptProb _ _ q (simGame_run P Msg keyOf hvzk A n)
  -- Unfold forkAcceptProb to uniformExpect
  unfold forkAcceptProb
  -- Factor: E_{(w,s), ch}[body] = E_w[E_s[E_ch[body]]]
  simp only [uniformExpect_prod]
  -- Go inside E_w
  congr 1; ext w
  -- Swap: E_s[E_ch[...]] → E_ch[E_s[...]] on each side independently
  conv_lhs => rw [uniformExpect_comm]
  conv_rhs => rw [uniformExpect_comm]
  -- E_ch[E_rs[body₁]] = E_ch[E_sr[body₂]]
  congr 1; ext ch
  -- Goal: E_{rs}[indicator(PQ(w,rs,ch))] = E_{sr}[indicator(SG(w,sr,ch))]
  -- Strategy: show both indicators factor as post(interaction.run q oracle_i(s_i)),
  -- then apply run_uniformExpect_oracle_eq.
  -- Define post-processing (let-bound for kernel transparency)
  let post : Option (List (Msg n ⊕ (Msg n × P.Commitment n)) ×
      (Msg n × P.Commitment n × P.Response n)) → ℝ :=
    fun result => match result with
    | none => 0
    | some (queries, mf, tf, zf) =>
      let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
      if hj : j < q then
        let signMsgs := queries.filterMap (fun q => match q with
          | .inl m => some m | .inr _ => none)
        if P.verify n (keyOf n w) tf (ch ⟨j, hj⟩) zf && !(signMsgs.contains mf)
        then 1 else 0
      else 0
  -- Show both sides equal E_s[post(interaction.run q oracle_s)]
  -- NOTE: oracle must match unfolded perQueryGame_run_stmt exactly (with let t := ...)
  have h_pq : ∀ rs,
      (match perQueryGame_run P Msg keyOf A n (w, rs) ch with
        | none => 0 | some _ => 1) =
      post ((A.interact n (keyOf n w)).run q
        (fun i qry => match qry with
          | .inl _ =>
            let t := P.commit n w (keyOf n w) (rs i)
            .inl (t, P.respond n w (keyOf n w) (rs i) (ch i))
          | .inr _ => .inr (ch i))) := by
    intro rs
    have h_eq : perQueryGame_run P Msg keyOf A n (w, rs) ch =
        perQueryGame_run_stmt P Msg A n w (keyOf n w) rs ch := rfl
    rw [h_eq]; unfold perQueryGame_run_stmt; dsimp only []
    generalize (A.interact n (keyOf n w)).run q _ = result
    cases result with
    | none => rfl
    | some p =>
      obtain ⟨queries, mf, tf, zf⟩ := p
      dsimp only []
      have h_post : post (some (queries, mf, tf, zf)) =
        (let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
         if hj : j < q then
           let signMsgs := queries.filterMap (fun q => match q with
             | .inl m => some m | .inr _ => none)
           if P.verify n (keyOf n w) tf (ch ⟨j, hj⟩) zf && !(signMsgs.contains mf)
           then 1 else 0
         else 0) := rfl
      rw [h_post]; dsimp only []
      -- Both sides depend on same conditions; case-split directly
      by_cases h_lt :
          queries.findIdx (fun x => decide (x = .inr (mf, tf))) < q
      · -- j < q on both sides; need proof for both q and A.numQueries n forms
        have h_lt_an :
            queries.findIdx (fun x => decide (x = .inr (mf, tf)))
              < A.numQueries n := h_lt
        simp only [dif_pos h_lt, dif_pos h_lt_an]
        by_cases h_v :
            (P.verify n (keyOf n w) tf (ch ⟨_, h_lt⟩) zf &&
             !(queries.filterMap (fun q => match q with
               | .inl m => some m | .inr _ => none
               )).contains mf) = true
        · simp only [if_pos h_v]
        · simp only [if_neg h_v]
      · -- ¬(j < q) on both sides
        have h_lt_an :
            ¬ queries.findIdx (fun x => decide (x = .inr (mf, tf)))
              < A.numQueries n := h_lt
        simp only [dif_neg h_lt, dif_neg h_lt_an]
  have h_sim : ∀ sr,
      (match simGame_run P Msg keyOf hvzk A n (w, sr) ch with
        | none => 0 | some _ => 1) =
      post ((A.interact n (keyOf n w)).run q
        (fun i qry => match qry with
          | .inl _ =>
            let (t, z) :=
              hvzk.simulate n (keyOf n w) (ch i) (sr i)
            .inl (t, z)
          | .inr _ => .inr (ch i))) := by
    intro sr
    have h_eq : simGame_run P Msg keyOf hvzk A n (w, sr) ch =
        simGame_run_stmt P Msg hvzk A n (keyOf n w) sr ch := rfl
    rw [h_eq]; unfold simGame_run_stmt; dsimp only []
    generalize (A.interact n (keyOf n w)).run q _ = result
    cases result with
    | none => rfl
    | some p =>
      obtain ⟨queries, mf, tf, zf⟩ := p
      dsimp only []
      have h_post : post (some (queries, mf, tf, zf)) =
        (let j :=
           queries.findIdx (fun x => decide (x = .inr (mf, tf)))
         if hj : j < q then
           let signMsgs :=
             queries.filterMap (fun q => match q with
               | .inl m => some m | .inr _ => none)
           if P.verify n (keyOf n w) tf (ch ⟨j, hj⟩) zf
               && !(signMsgs.contains mf)
           then 1 else 0
         else 0) := rfl
      rw [h_post]; dsimp only []
      by_cases h_lt :
          queries.findIdx
            (fun x => decide (x = .inr (mf, tf))) < q
      · have h_lt_an :
            queries.findIdx
              (fun x => decide (x = .inr (mf, tf)))
                < A.numQueries n := h_lt
        simp only [dif_pos h_lt, dif_pos h_lt_an]
        by_cases h_v :
            (P.verify n (keyOf n w) tf (ch ⟨_, h_lt⟩) zf &&
             !(queries.filterMap (fun q => match q with
               | .inl m => some m | .inr _ => none
               )).contains mf) = true
        · simp only [if_pos h_v]
        · simp only [if_neg h_v]
      · have h_lt_an :
            ¬ queries.findIdx
              (fun x => decide (x = .inr (mf, tf)))
                < A.numQueries n := h_lt
        simp only [dif_neg h_lt, dif_neg h_lt_an]
  -- Rewrite both sides using h_pq and h_sim, then apply oracle equivalence
  trans uniformExpect _ (fun (rs : Fin (A.numQueries n) → P.ProverRandomness n) =>
      post ((A.interact n (keyOf n w)).run q
        (fun i qry => match qry with
          | .inl _ =>
            let t := P.commit n w (keyOf n w) (rs i)
            .inl (t, P.respond n w (keyOf n w) (rs i) (ch i))
          | .inr _ => .inr (ch i))))
  · congr 1; ext rs; convert h_pq rs using 1
    · cases perQueryGame_run P Msg keyOf A n (w, rs) ch <;> rfl
  trans uniformExpect _ (fun (sr : Fin (A.numQueries n) → hvzk.SimRandomness n) =>
      post ((A.interact n (keyOf n w)).run q
        (fun i qry => match qry with
          | .inl _ =>
            let (t, z) := hvzk.simulate n (keyOf n w) (ch i) (sr i)
            .inl (t, z)
          | .inr _ => .inr (ch i))))
  · -- E_{rs}[post(run q oracle₁(rs))] = E_{sr}[post(run q oracle₂(sr))]
    exact run_uniformExpect_oracle_eq q (A.interact n (keyOf n w))
      (fun i s qry => match qry with
        | .inl _ =>
          let t := P.commit n w (keyOf n w) s
          .inl (t, P.respond n w (keyOf n w) s (ch i))
        | .inr _ => .inr (ch i))
      (fun i s qry => match qry with
        | .inl _ =>
          let (t, z) := hvzk.simulate n (keyOf n w) (ch i) s
          .inl (t, z)
        | .inr _ => .inr (ch i))
      (fun i qr g => by
        cases qr with
        | inl m =>
          exact hvzk.sim_distribution n w (keyOf n w) (ch i) (keyOf_valid n w)
            (fun pair => g (.inl pair))
        | inr mt =>
          rw [show (fun s => g (.inr (ch i))) = (fun _ : P.ProverRandomness n => g (.inr (ch i)))
            from rfl, uniformExpect_const,
              show (fun s => g (.inr (ch i))) = (fun _ : hvzk.SimRandomness n => g (.inr (ch i)))
            from rfl, uniformExpect_const])
      post
  · -- Rewrite RHS back
    symm; congr 1; ext sr; convert h_sim sr using 1
    · cases simGame_run P Msg keyOf hvzk A n (w, sr) ch <;> rfl

/-- **Game hop bound**: the gap between Game 0 (`ROM_EUF_CMA_Game`) and
Game 1 (`ROM_EUF_CMA_SimGame`) is bounded by `q² · δ`, where `δ` comes
from the unpredictable commitments property.

This follows from the two-step decomposition:
1. `rom_to_perquery_bound`: consistent H → per-query challenges (gap ≤ q²·δ)
2. `perquery_eq_simgame`: real prover → HVZK simulator (gap = 0) -/
theorem game_hop_bound {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    (hvzk : P.SpecialHVZK)
    (keyOf_valid : ∀ n w, R.relation n w (keyOf n w))
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    |(ROM_EUF_CMA_Game P Msg keyOf).advantage A n -
     (ROM_EUF_CMA_SimGame P Msg keyOf hvzk).advantage A n| ≤
      (A.numQueries n : ℝ) ^ 2 * δ n := by
  rw [← perquery_eq_simgame P Msg keyOf hvzk keyOf_valid A n]
  exact rom_to_perquery_bound P Msg keyOf keyOf_valid A n δ h_unpred

/-- The oracle used in `simGame_run_stmt`, extracted for reasoning. -/
private noncomputable def simOracle {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    (hvzk : P.SpecialHVZK) (n : ℕ) (q : ℕ)
    (y : R.Statement n) (sr : Fin q → hvzk.SimRandomness n)
    (ch : Fin q → P.Challenge n) :
    Fin q → (Msg n ⊕ (Msg n × P.Commitment n)) →
      ((P.Commitment n × P.Response n) ⊕ P.Challenge n) :=
  fun i qry => match qry with
  | .inl _ =>
    let (t, z) := hvzk.simulate n y (ch i) (sr i)
    .inl (t, z)
  | .inr _ => .inr (ch i)

/-- When `simGame_run_stmt` succeeds, extract the underlying `run` result
and key properties relating the fork index to the query log. -/
private lemma simGame_run_stmt_data {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK) (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (y : R.Statement n) (sr : Fin (A.numQueries n) → hvzk.SimRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n)
    {j : Fin (A.numQueries n)} {mf : Msg n} {tf : P.Commitment n}
    {zf : P.Response n}
    (h : simGame_run_stmt P Msg hvzk A n y sr ch = some (j, (mf, tf, zf))) :
    ∃ queries,
      (A.interact n y).run (A.numQueries n)
        (simOracle P Msg hvzk n (A.numQueries n) y sr ch) =
        some (queries, (mf, tf, zf)) ∧
      j.val ≤ queries.length ∧
      (∀ (hlt : j.val < queries.length), queries[j.val] = .inr (mf, tf)) := by
  letI := P.commitmentDecEq n
  -- simGame_run_stmt is definitionally a match on run simOracle
  have h_def : simGame_run_stmt P Msg hvzk A n y sr ch =
      match (A.interact n y).run (A.numQueries n)
        (simOracle P Msg hvzk n (A.numQueries n) y sr ch) with
      | none => none
      | some (queries, mf', tf', zf') =>
        let jv := queries.findIdx (fun x => decide (x = .inr (mf', tf')))
        if hj : jv < A.numQueries n then
          let signMsgs := queries.filterMap (fun q => match q with
            | .inl m => some m | .inr _ => none)
          if P.verify n y tf' (ch ⟨jv, hj⟩) zf' && !(signMsgs.contains mf') then
            some (⟨jv, hj⟩, (mf', tf', zf'))
          else none
        else none := by rfl
  rw [h_def] at h
  -- Case split on the run result
  generalize h_run : (A.interact n y).run (A.numQueries n)
    (simOracle P Msg hvzk n (A.numQueries n) y sr ch) = result at h
  rcases result with _ | ⟨queries, mf', tf', zf'⟩
  · exact absurd h nofun
  · -- Reduce the match on the constructor in h
    dsimp only [] at h
    split at h
    · split at h
      · -- Success: extract via injection
        have hinj := Option.some.inj h
        have hj_eq := (Prod.mk.inj hinj).1
        have hrest := (Prod.mk.inj hinj).2
        have hmf : mf' = mf := (Prod.mk.inj hrest).1
        have hrest2 := (Prod.mk.inj hrest).2
        have htf_eq : tf' = tf := (Prod.mk.inj hrest2).1
        have hzf : zf' = zf := (Prod.mk.inj hrest2).2
        refine ⟨queries, ?_, ?_, ?_⟩
        · -- run equation
          rw [← hmf, ← htf_eq, ← hzf]
        · -- j.val ≤ queries.length from findIdx_le_length
          have hj_val : queries.findIdx (fun x => decide (x = .inr (mf', tf'))) = j.val :=
            congrArg Fin.val hj_eq
          rw [← hj_val]; exact List.findIdx_le_length
        · -- queries[j.val] = .inr (mf, tf)
          intro hlt
          rw [← hmf, ← htf_eq]
          have hj_val : queries.findIdx (fun x => decide (x = .inr (mf', tf'))) = j.val :=
            congrArg Fin.val hj_eq
          have hlt' : queries.findIdx (fun x => decide (x = .inr (mf', tf'))) < queries.length :=
            hj_val ▸ hlt
          have h_beq := List.findIdx_getElem (w := hlt')
          -- h_beq : decide (queries[findIdx ...] = .inr (mf', tf')) = true
          -- Use of_decide_eq_true to get propositional equality
          have h_at := of_decide_eq_true h_beq
          -- Transfer from findIdx position to j.val
          simp only [hj_val] at h_at; exact h_at
      · exact absurd h nofun
    · exact absurd h nofun

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
    have htf : tf₁ = tf₂ := by
      -- Extract run results from both successful simGame_run_stmt calls
      obtain ⟨queries₁, hrun₁, hle₁, hget₁⟩ :=
        simGame_run_stmt_data P Msg hvzk A n y sr ch₁ h₁
      set ch_fork : Fin (A.numQueries n) → P.Challenge n :=
        fun i => if i.val < j.val then ch₁ i else ch₂ i
      obtain ⟨queries₂, hrun₂, hle₂, hget₂⟩ :=
        simGame_run_stmt_data P Msg hvzk A n y sr ch_fork h₂
      -- The oracles agree on all indices < j.val
      have h_oracle_agree : ∀ (i : Fin (A.numQueries n)), i.val < j.val →
          simOracle P Msg hvzk n (A.numQueries n) y sr ch₁ i =
          simOracle P Msg hvzk n (A.numQueries n) y sr ch_fork i := by
        intro i hi
        have h_ch_eq : ch_fork i = ch₁ i := if_pos hi
        ext qry; unfold simOracle; rw [h_ch_eq]
      -- Case split: j.val < queries₁.length or j.val ≥ queries₁.length
      by_cases hjlt : j.val < queries₁.length
      · -- Case A: j.val < queries₁.length
        -- By prefix length preservation, j.val < queries₂.length
        have hjlt₂ : j.val < queries₂.length :=
          OracleInteraction.run_prefix_implies_length
            (A.interact n y) (A.numQueries n)
            (simOracle P Msg hvzk n (A.numQueries n) y sr ch₁)
            (simOracle P Msg hvzk n (A.numQueries n) y sr ch_fork)
            j.val h_oracle_agree hrun₁ hrun₂ hjlt
        -- The j-th queries are equal by deterministic prefix
        have hq_eq : queries₁[j.val] = queries₂[j.val] :=
          OracleInteraction.run_prefix_query_eq
            (A.interact n y) (A.numQueries n)
            (simOracle P Msg hvzk n (A.numQueries n) y sr ch₁)
            (simOracle P Msg hvzk n (A.numQueries n) y sr ch_fork)
            j.val h_oracle_agree hrun₁ hrun₂ hjlt hjlt₂
        -- The j-th query in each run is .inr (mf, tf)
        have hq₁ : queries₁[j.val] = .inr (mf₁, tf₁) := hget₁ hjlt
        have hq₂ : queries₂[j.val] = .inr (mf₂, tf₂) := hget₂ hjlt₂
        -- Combine: .inr (mf₁, tf₁) = .inr (mf₂, tf₂)
        have := hq₁.symm.trans (hq_eq.trans hq₂)
        exact (Prod.mk.inj (Sum.inr.inj this)).2
      · -- Case B: j.val ≥ queries₁.length (= queries₁.length by findIdx_le_length)
        -- All oracle indices < queries₁.length are < j.val
        have h_agree_all : ∀ (i : Fin (A.numQueries n)),
            i.val < queries₁.length →
            simOracle P Msg hvzk n (A.numQueries n) y sr ch₁ i =
            simOracle P Msg hvzk n (A.numQueries n) y sr ch_fork i := by
          intro i hi
          exact h_oracle_agree i (lt_of_lt_of_le hi (Nat.le_of_not_lt hjlt))
        -- By run_det_prefix, both runs produce the same result
        have hrun₂' :=
          OracleInteraction.run_det_prefix
            (A.interact n y) (A.numQueries n)
            (simOracle P Msg hvzk n (A.numQueries n) y sr ch₁)
            (simOracle P Msg hvzk n (A.numQueries n) y sr ch_fork)
            hrun₁ h_agree_all
        -- The second run result must match
        rw [hrun₂'] at hrun₂
        exact (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (Option.some.inj hrun₂)).2).2).1
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

If the Sigma protocol has special soundness, special HVZK, and
`δ`-unpredictable commitments (Def 19.7, Boneh-Shoup), there exists
a relation solver whose advantage, combined with the forking overhead,
bounds the ROM EUF-CMA advantage:

$$\mathrm{Adv}_{\mathrm{ROM\text{-}EUF\text{-}CMA}}(A, n)
  \le \sqrt{q \cdot \mathrm{Adv}_R(B, n) + q / |\mathcal{C}|}
    + q^2 \cdot \delta$$

where `q` is the total query bound and `|𝒞|` is the challenge space size.

**Proof sketch** (Boneh-Shoup §19.6.1, Theorem 19.16):
1. *Game hop 1* (`rom_to_perquery_bound`): Replace consistent hash with
   per-query independent challenges. Gap bounded by `q² · δ` via
   unpredictable commitments.
2. *Game hop 2* (`perquery_eq_simgame`): Replace real prover with HVZK
   simulator. Gap = 0 by `sim_distribution`.
3. *Forking*: In `ROM_EUF_CMA_SimGame`, the signing oracle doesn't use
   the witness. Run the forking lemma + special soundness extraction.
4. *Invert the forking bound*: `acc²/q ≤ Adv_R + acc/|Ch|` gives
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
    (A : ROM_EUF_CMA_Adversary P Msg)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    ∃ B : RelationSolver R, ∀ n,
      (ROM_EUF_CMA_Game P Msg keyOf).advantage A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          (RelationGame R keyOf).advantage B n +
          (A.numQueries n : ℝ) /
            Fintype.card (P.Challenge n)) +
        (A.numQueries n : ℝ) ^ 2 * δ n := by
  obtain ⟨B, hB⟩ := simGame_forking_bound P Msg keyOf ss hvzk keyOf_valid A
  exact ⟨B, fun n => by
    have h_hop := game_hop_bound P Msg keyOf hvzk keyOf_valid A n δ h_unpred
    have h_sim := hB n
    have h1 : (ROM_EUF_CMA_Game P Msg keyOf).advantage A n -
        (ROM_EUF_CMA_SimGame P Msg keyOf hvzk).advantage A n ≤
        (A.numQueries n : ℝ) ^ 2 * δ n :=
      le_trans (le_abs_self _) h_hop
    linarith⟩

/-- **Asymptotic security of Fiat-Shamir in the ROM.**

If:
1. The Sigma protocol has special soundness and special HVZK
2. The underlying relation is hard (`RelationGame` is secure)
3. The protocol has `δ`-unpredictable commitments for negligible `δ`
4. The challenge space grows super-polynomially
5. The adversary makes polynomially many queries

Then the ROM EUF-CMA advantage is negligible.

This is the main theorem connecting Sigma protocols to practical
signatures in the random oracle model (Theorem 19.16, Boneh-Shoup). -/
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
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ)
    (hDelta : Negligible δ)
    (hChallenge : Negligible (fun n => 1 / (Fintype.card (P.Challenge n) : ℝ)))
    (A : ROM_EUF_CMA_Adversary P Msg)
    (hPoly : PolynomiallyBounded (fun n => (A.numQueries n : ℝ))) :
    Negligible (fun n => (ROM_EUF_CMA_Game P Msg keyOf).advantage A n) := by
  -- Apply concrete bound with δ_n := δ n for each n
  -- We need a uniform δ for fiatShamir_ROM_bound, but our δ varies with n.
  -- Use the pointwise bound: for each n, apply fiatShamir_ROM_bound with δ(n).
  -- First, get the forking bound (independent of δ)
  obtain ⟨B, hB⟩ := simGame_forking_bound P Msg keyOf ss hvzk keyOf_valid A
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
  -- Component 4: q² · δ is negligible
  have h_q2Delta : Negligible (fun n =>
      (A.numQueries n : ℝ) ^ 2 * δ n) :=
    (hDelta.mul_polyBounded hPoly.sq).mono ⟨0, fun n _ =>
      le_of_eq (congr_arg abs (by ring))⟩
  -- Full bound is negligible
  have h_bound := h_sqrt.add h_q2Delta
  -- Transfer to advantage via pointwise game_hop_bound
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
    -- Use game_hop_bound with δ to bound the gap
    have h_hop := game_hop_bound P Msg keyOf hvzk keyOf_valid A n δ h_unpred
    have h_sim := hB n
    have h1 : (ROM_EUF_CMA_Game P Msg keyOf).advantage A n -
        (ROM_EUF_CMA_SimGame P Msg keyOf hvzk).advantage A n ≤
        (A.numQueries n : ℝ) ^ 2 * δ n :=
      le_trans (le_abs_self _) h_hop
    exact le_trans (by linarith) (le_abs_self _)⟩

end
