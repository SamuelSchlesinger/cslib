/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Foundations.RandomOracle
public import Cslib.Probability.ForkingLemma

@[expose] public section

/-!
# Map-Based Intermediate Games for Fiat-Shamir ROM

The Map-based game-hop chain in the proof of Fiat-Shamir ROM security
(Boneh-Shoup §19.6). The games differ only in how the signing oracle
answers queries:

* **MapGame0** ≡ ROM (via lazy sampling; see `lazyRomOracle`)
* **MapGame_Real** — signing uses the real prover `(commit, respond)`
  and always writes its fresh challenge `ch_i` into the map,
  ignoring any cached entry
* **MapGame1_HVZK** — same as `MapGame_Real` but signing uses the HVZK
  simulator in place of the real prover

This file contains the *definitions* and the **HVZK switch** theorem
(`mapGame_real_eq_mapGame1_hvzk`): the MapGame_Real and MapGame1_HVZK
advantages coincide, by `sim_distribution` lifted through
`runWithState_uniformExpect_oracle_eq`.

The gap between `MapGame0` (= LazyROM) and `MapGame_Real`, and the
forking bound on `MapGame1_HVZK`, are proved in the sibling files.
-/

open Cslib.Probability

/-- Map state type: association list from `(Msg × Commitment)` to `Challenge`. -/
abbrev MapState {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) (n : ℕ) :=
  List ((Msg n × P.Commitment n) × P.Challenge n)

/-- Extract the signed messages from a list of oracle queries.

Named helper used by the Map-game run statements so proofs downstream
can pattern-match against a stable identifier rather than an inline
`fun q => match q with ...` whose match auxiliary would differ across
modules. -/
def signMsgsOf {R : EffectiveRelation} {P : SigmaProtocol R}
    {Msg : ℕ → Type} {n : ℕ}
    (queries : List (Msg n ⊕ (Msg n × P.Commitment n))) : List (Msg n) :=
  queries.filterMap fun q => match q with | .inl m => some m | .inr _ => none

/-- Oracle for MapGame_Real: signing uses the real prover (commit/respond)
with per-query challenge `ch_i`, and inserts into Map. Hash oracle checks
Map for consistency. This is the intermediate game between ROM and
MapGame1_HVZK. -/
noncomputable def mapGameRealOracle {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (ch : Fin q → P.Challenge n) :
    Fin q → MapState P Msg n →
      (Msg n ⊕ (Msg n × P.Commitment n)) →
      (((P.Commitment n × P.Response n) ⊕ P.Challenge n) × MapState P Msg n) :=
  fun i map qry =>
    letI := P.commitmentDecEq n
    match qry with
    | .inl m =>
      let t := P.commit n w y (rs i)
      let z := P.respond n w y (rs i) (ch i)
      (.inl (t, z), ((m, t), ch i) :: map)
    | .inr (m, t) =>
      match assocLookup (m, t) map with
      | some c => (.inr c, map)
      | none => (.inr (ch i), ((m, t), ch i) :: map)

/-- Execute MapGame_Real: run the adversary with the Map-based real oracle,
then post-process to extract forgery and check verification. -/
noncomputable def mapGame_real_run_stmt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n) :
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  let q := A.numQueries n
  letI := P.commitmentDecEq n
  match (A.interact n y).runWithState q
      (mapGameRealOracle P Msg n q w y rs ch) [] with
  | none => none
  | some (queries, (mf, tf, zf), _) =>
    let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
    if hj : j < q then
      if j < queries.length then
        if P.verify n y tf (ch ⟨j, hj⟩) zf && !(signMsgsOf queries).contains mf then
          some (⟨j, hj⟩, (mf, tf, zf))
        else
          none
      else
        none
    else
      none

/-- Wrap `mapGame_real_run_stmt` for the `forkAcceptProb` framework. -/
noncomputable def mapGame_real_run {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (R.Witness n × (Fin (A.numQueries n) → P.ProverRandomness n)) →
    (Fin (A.numQueries n) → P.Challenge n) →
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  fun ⟨w, rs⟩ ch =>
    mapGame_real_run_stmt P Msg A n w (kg.keyOf n w) rs ch

/-- **MapGame_Real advantage**: acceptance probability of the Map-based
real-prover game in the forking framework. -/
noncomputable def mapGame_real_advantage {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) : ℝ :=
  let q := A.numQueries n
  letI := P.proverRandomnessFintype n
  letI := P.proverRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  forkAcceptProb
    (R.Witness n × (Fin q → P.ProverRandomness n))
    (P.Challenge n) q
    (mapGame_real_run P Msg kg A n)

/-- Oracle for LazyROM (= MapGame0 in Boneh-Shoup §19.6): like
`mapGameRealOracle` but checks the Map at signing steps before using
`ch_i`. When the key `(m, commit(w,y,rs_i))` is already cached, uses
the cached challenge for consistency (faithfully simulating a random
function). When the key is fresh, behaves identically to
`mapGameRealOracle`. -/
noncomputable def lazyRomOracle {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (ch : Fin q → P.Challenge n) :
    Fin q → MapState P Msg n →
      (Msg n ⊕ (Msg n × P.Commitment n)) →
      (((P.Commitment n × P.Response n) ⊕ P.Challenge n) × MapState P Msg n) :=
  fun i map qry =>
    letI := P.commitmentDecEq n
    match qry with
    | .inl m =>
      let t := P.commit n w y (rs i)
      match assocLookup (m, t) map with
      | some c => (.inl (t, P.respond n w y (rs i) c), map)
      | none => (.inl (t, P.respond n w y (rs i) (ch i)),
                 ((m, t), ch i) :: map)
    | .inr (m, t) =>
      match assocLookup (m, t) map with
      | some c => (.inr c, map)
      | none => (.inr (ch i), ((m, t), ch i) :: map)

/-- LazyROM oracle variant where each step receives a random function
`Hᵢ : Msg × Comm → Ch` and uses `Hᵢ(key)` when the key is fresh.
Map lookups still enforce consistency on repeated keys. -/
noncomputable def lazyRomHOracle {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n) :
    Fin q → (Msg n × P.Commitment n → P.Challenge n) →
      MapState P Msg n →
      (Msg n ⊕ (Msg n × P.Commitment n)) →
      (((P.Commitment n × P.Response n) ⊕ P.Challenge n) × MapState P Msg n) :=
  fun i H map qry =>
    letI := P.commitmentDecEq n
    match qry with
    | .inl m =>
      let t := P.commit n w y (rs i)
      match assocLookup (m, t) map with
      | some c => (.inl (t, P.respond n w y (rs i) c), map)
      | none =>
        let c := H (m, t)
        (.inl (t, P.respond n w y (rs i) c), ((m, t), c) :: map)
    | .inr (m, t) =>
      match assocLookup (m, t) map with
      | some c => (.inr c, map)
      | none =>
        let c := H (m, t)
        (.inr c, ((m, t), c) :: map)

/-- One-step marginal equivalence:
sampling a fresh value via `Hᵢ(key)` (uniform random function) matches
sampling a fresh uniform challenge directly. -/
theorem lazyRomHOracle_marginal_eq {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (i : Fin q) (map : MapState P Msg n)
    (qry : Msg n ⊕ (Msg n × P.Commitment n))
    (g : (((P.Commitment n × P.Response n) ⊕ P.Challenge n) ×
      MapState P Msg n) → ℝ) :
    uniformExpect (Msg n × P.Commitment n → P.Challenge n)
      (fun H => g (lazyRomHOracle P Msg n q w y rs i H map qry)) =
    uniformExpect (P.Challenge n)
      (fun c => g (lazyRomOracle P Msg n q w y rs (fun _ => c) i map qry)) := by
  letI := P.commitmentDecEq n
  cases qry with
  | inl m =>
    let t := P.commit n w y (rs i)
    cases h_lookup : assocLookup (m, t) map with
    | some c0 =>
      simpa [lazyRomHOracle, lazyRomOracle, t, h_lookup] using
        (show uniformExpect (Msg n × P.Commitment n → P.Challenge n)
            (fun _ => g (.inl (t, P.respond n w y (rs i) c0), map)) =
          uniformExpect (P.Challenge n)
            (fun _ => g (.inl (t, P.respond n w y (rs i) c0), map)) from by
          rw [uniformExpect_const, uniformExpect_const])
    | none =>
      let g' : P.Challenge n → ℝ := fun c =>
        g (.inl (t, P.respond n w y (rs i) c), ((m, t), c) :: map)
      have h_eval :=
        uniformExpect_eval_at_point (x₀ := (m, t)) (g := g')
      simpa [lazyRomHOracle, lazyRomOracle, t, h_lookup, g'] using h_eval
  | inr mt =>
    rcases mt with ⟨m, t⟩
    cases h_lookup : assocLookup (m, t) map with
    | some c0 =>
      simpa [lazyRomHOracle, lazyRomOracle, h_lookup] using
        (show uniformExpect (Msg n × P.Commitment n → P.Challenge n)
            (fun _ => g (.inr c0, map)) =
          uniformExpect (P.Challenge n)
            (fun _ => g (.inr c0, map)) from by
          rw [uniformExpect_const, uniformExpect_const])
    | none =>
      let g' : P.Challenge n → ℝ := fun c => g (.inr c, ((m, t), c) :: map)
      have h_eval :=
        uniformExpect_eval_at_point (x₀ := (m, t)) (g := g')
      simpa [lazyRomHOracle, lazyRomOracle, h_lookup, g'] using h_eval

/-- Run-level oracle swap for LazyROM:
replacing per-step random functions `Hᵢ` with per-step uniform challenges
preserves the expected value of any post-processing of `runWithState`. -/
theorem lazyRomH_runWithState_uniform_eq {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    (n : ℕ) (q : ℕ)
    (interaction : OracleInteraction
      (Msg n ⊕ (Msg n × P.Commitment n))
      ((P.Commitment n × P.Response n) ⊕ P.Challenge n)
      (Msg n × P.Commitment n × P.Response n))
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin q → P.ProverRandomness n)
    (f : Option
      (List (Msg n ⊕ (Msg n × P.Commitment n)) ×
        (Msg n × P.Commitment n × P.Response n) ×
        MapState P Msg n) → ℝ) :
    uniformExpect (Fin q → (Msg n × P.Commitment n → P.Challenge n))
      (fun Hs =>
        f (interaction.runWithState q
          (fun i st qry => lazyRomHOracle P Msg n q w y rs i (Hs i) st qry) [])) =
    uniformExpect (Fin q → P.Challenge n)
      (fun ch =>
        f (interaction.runWithState q
          (lazyRomOracle P Msg n q w y rs ch) [])) := by
  have h_oracle_lazy :
      ∀ (ch : Fin q → P.Challenge n),
        lazyRomOracle P Msg n q w y rs ch =
        fun i st qry => (fun i s st qry =>
          lazyRomOracle P Msg n q w y rs (fun _ => s) i st qry) i (ch i) st qry := by
    intro ch
    funext i st qry
    rfl
  conv_rhs =>
    arg 2
    ext ch
    rw [h_oracle_lazy ch]
    dsimp only []
  exact runWithState_uniformExpect_oracle_eq q interaction
    (fun i s => lazyRomHOracle P Msg n q w y rs i s)
    (fun i s => lazyRomOracle P Msg n q w y rs (fun _ => s) i)
    (by
      intro i st qry g
      exact lazyRomHOracle_marginal_eq P Msg n q w y rs i st qry g)
    [] f

/-- Execute LazyROM: run the adversary with the lazy ROM oracle,
then post-process to extract forgery and check verification.
Mirrors `mapGame_real_run_stmt` exactly, substituting `lazyRomOracle`
for `mapGameRealOracle`. -/
noncomputable def lazyRom_run_stmt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (w : R.Witness n) (y : R.Statement n)
    (rs : Fin (A.numQueries n) → P.ProverRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n) :
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  let q := A.numQueries n
  letI := P.commitmentDecEq n
  match (A.interact n y).runWithState q
      (lazyRomOracle P Msg n q w y rs ch) [] with
  | none => none
  | some (queries, (mf, tf, zf), finalMap) =>
    let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
    if hj : j < q then
      match assocLookup (mf, tf) finalMap with
      | some c =>
        if P.verify n y tf c zf && !(signMsgsOf queries).contains mf then
          some (⟨j, hj⟩, (mf, tf, zf))
        else
          none
      | none => none
    else
      none

/-- Wrap `lazyRom_run_stmt` for the `forkAcceptProb` framework. -/
noncomputable def lazyRom_run {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (R.Witness n × (Fin (A.numQueries n) → P.ProverRandomness n)) →
    (Fin (A.numQueries n) → P.Challenge n) →
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  fun ⟨w, rs⟩ ch =>
    lazyRom_run_stmt P Msg A n w (kg.keyOf n w) rs ch

/-- **LazyROM advantage**: acceptance probability of the lazy ROM game
in the forking framework. -/
noncomputable def lazyRom_advantage {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) : ℝ :=
  let q := A.numQueries n
  letI := P.proverRandomnessFintype n
  letI := P.proverRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  forkAcceptProb
    (R.Witness n × (Fin q → P.ProverRandomness n))
    (P.Challenge n) q
    (lazyRom_run P Msg kg A n)

/-- Oracle for MapGame1_HVZK: signing uses HVZK simulator, always uses
`ch_i`, and inserts into Map. Hash oracle checks Map for consistency. -/
noncomputable def mapGame1HvzkOracle {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK) (n : ℕ) (q : ℕ)
    (y : R.Statement n)
    (sr : Fin q → hvzk.SimRandomness n)
    (ch : Fin q → P.Challenge n) :
    Fin q → MapState P Msg n →
      (Msg n ⊕ (Msg n × P.Commitment n)) →
      (((P.Commitment n × P.Response n) ⊕ P.Challenge n) × MapState P Msg n) :=
  fun i map qry =>
    letI := P.commitmentDecEq n
    match qry with
    | .inl m =>
      let (t, z) := hvzk.simulate n y (ch i) (sr i)
      (.inl (t, z), ((m, t), ch i) :: map)
    | .inr (m, t) =>
      match assocLookup (m, t) map with
      | some c => (.inr c, map)
      | none => (.inr (ch i), ((m, t), ch i) :: map)

/-- Execute MapGame1_HVZK: run the adversary with the Map-based HVZK oracle,
then post-process to extract forgery and check verification. -/
noncomputable def mapGame1_hvzk_run_stmt {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ)
    (y : R.Statement n)
    (sr : Fin (A.numQueries n) → hvzk.SimRandomness n)
    (ch : Fin (A.numQueries n) → P.Challenge n) :
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  let q := A.numQueries n
  letI := P.commitmentDecEq n
  match (A.interact n y).runWithState q
      (mapGame1HvzkOracle P Msg hvzk n q y sr ch) [] with
  | none => none
  | some (queries, (mf, tf, zf), _) =>
    let j := queries.findIdx (fun x => decide (x = .inr (mf, tf)))
    if hj : j < q then
      if j < queries.length then
        if P.verify n y tf (ch ⟨j, hj⟩) zf && !(signMsgsOf queries).contains mf then
          some (⟨j, hj⟩, (mf, tf, zf))
        else
          none
      else
        none
    else
      none

/-- Wrap `mapGame1_hvzk_run_stmt` for the `forkAcceptProb` framework. -/
noncomputable def mapGame1_hvzk_run {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    (kg : R.WithKeyGen)
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    (R.Witness n × (Fin (A.numQueries n) → hvzk.SimRandomness n)) →
    (Fin (A.numQueries n) → P.Challenge n) →
    Option (Fin (A.numQueries n) × (Msg n × P.Commitment n × P.Response n)) :=
  fun ⟨w, sr⟩ ch =>
    mapGame1_hvzk_run_stmt P Msg hvzk A n (kg.keyOf n w) sr ch

/-- **MapGame1_HVZK advantage**: acceptance probability of the Map-based
HVZK game in the forking framework. -/
noncomputable def mapGame1_hvzk_advantage {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) : ℝ :=
  let q := A.numQueries n
  letI := hvzk.simRandomnessFintype n
  letI := hvzk.simRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  forkAcceptProb
    (R.Witness n × (Fin q → hvzk.SimRandomness n))
    (P.Challenge n) q
    (mapGame1_hvzk_run P Msg kg hvzk A n)

/-- **HVZK switch**: the MapGame_Real advantage equals the MapGame1_HVZK
advantage. The real prover `(commit, respond)` produces the same marginal
distribution as the HVZK simulator at each step (by `sim_distribution`),
so the overall interaction's expected payoff is preserved. -/
theorem mapGame_real_eq_mapGame1_hvzk {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (kg : R.WithKeyGen)
    (hvzk : P.SpecialHVZK)
    (A : ROM_EUF_CMA_Adversary P Msg) (n : ℕ) :
    mapGame_real_advantage P Msg kg A n =
    mapGame1_hvzk_advantage P Msg kg hvzk A n := by
  set q := A.numQueries n with hq
  letI := P.proverRandomnessFintype n
  letI := P.proverRandomnessNonempty n
  letI := hvzk.simRandomnessFintype n
  letI := hvzk.simRandomnessNonempty n
  letI := P.challengeFintype n
  letI := P.challengeNonempty n
  simp only [mapGame_real_advantage, mapGame1_hvzk_advantage]
  apply forkAcceptProb_coins_eq
  intro ch f_payoff
  simp only [mapGame_real_run, mapGame1_hvzk_run]
  rw [uniformExpect_prod, uniformExpect_prod]
  congr 1; ext w; dsimp only []
  -- For fixed w and ch, show the inner expectations over per-step randomness are equal
  set y := kg.keyOf n w
  -- Post-processing function applied after runWithState (same in both games)
  let pp : Option (List (Msg n ⊕ (Msg n × P.Commitment n)) ×
      (Msg n × P.Commitment n × P.Response n) × MapState P Msg n) →
      Option (Fin q × (Msg n × P.Commitment n × P.Response n)) :=
    fun result =>
    letI := P.commitmentDecEq n
    match result with
    | none => none
    | some (queries, (mf, tf, zf), _) =>
      let j := queries.findIdx (fun x => decide (x = Sum.inr (mf, tf)))
      if hj : j < q then
        if j < queries.length then
          if P.verify n y tf (ch ⟨j, hj⟩) zf && !(signMsgsOf queries).contains mf then
            some (⟨j, hj⟩, (mf, tf, zf))
          else none
        else none
      else none
  -- Factoring: run_stmt = pp ∘ runWithState ∘ oracle
  have h_run_real : ∀ rs,
      mapGame_real_run_stmt P Msg A n w y rs ch =
      pp ((A.interact n y).runWithState q (mapGameRealOracle P Msg n q w y rs ch) []) := by
    intro rs; rfl
  have h_run_hvzk : ∀ sr,
      mapGame1_hvzk_run_stmt P Msg hvzk A n y sr ch =
      pp ((A.interact n y).runWithState q (mapGame1HvzkOracle P Msg hvzk n q y sr ch) []) := by
    intro sr; rfl
  -- Oracle factoring: oracle(rs)(i) = oracle₁(i)(rs i) where oracle₁ doesn't depend on rs
  have h_oracle_real : ∀ (rs : Fin q → P.ProverRandomness n),
      mapGameRealOracle P Msg n q w y rs ch =
      fun i st qry => (fun i s st qry =>
        mapGameRealOracle P Msg n q w y (fun _ => s) ch i st qry) i (rs i) st qry := by
    intro rs; funext i st qry; rfl
  have h_oracle_hvzk : ∀ (sr : Fin q → hvzk.SimRandomness n),
      mapGame1HvzkOracle P Msg hvzk n q y sr ch =
      fun i st qry => (fun i s st qry =>
        mapGame1HvzkOracle P Msg hvzk n q y (fun _ => s) ch i st qry) i (sr i) st qry := by
    intro sr; funext i st qry; rfl
  conv_lhs => arg 2; ext rs; rw [h_run_real, h_oracle_real]; dsimp only []
  conv_rhs => arg 2; ext sr; rw [h_run_hvzk, h_oracle_hvzk]; dsimp only []
  -- Normalize Fin (A.numQueries n) to Fin q for unification
  change uniformExpect (Fin q → P.ProverRandomness n) (fun rs =>
      f_payoff (pp ((A.interact n y).runWithState q
        (fun i st qry => mapGameRealOracle P Msg n q w y (fun _ => rs i) ch i st qry) []))) =
    uniformExpect (Fin q → hvzk.SimRandomness n) (fun sr =>
      f_payoff (pp ((A.interact n y).runWithState q
        (fun i st qry => mapGame1HvzkOracle P Msg hvzk n q y (fun _ => sr i) ch i st qry) [])))
  -- Apply the stateful oracle swap lemma
  exact runWithState_uniformExpect_oracle_eq q (A.interact n y)
    (fun i s => mapGameRealOracle P Msg n q w y (fun _ => s) ch i)
    (fun i s => mapGame1HvzkOracle P Msg hvzk n q y (fun _ => s) ch i)
    (by
      intro i st qry g
      cases qry with
      | inr mt =>
        -- Hash query: result is independent of per-step randomness s
        simp only [mapGameRealOracle, mapGame1HvzkOracle]
        rw [uniformExpect_const, uniformExpect_const]
      | inl m =>
        -- Sign query: real prover ↔ HVZK simulator by sim_distribution
        simp only [mapGameRealOracle, mapGame1HvzkOracle]
        exact hvzk.sim_distribution n w y (ch i) (kg.keyOf_valid n w)
          (fun ⟨t, z⟩ => g (Sum.inl (t, z), ((m, t), ch i) :: st)))
    [] (fun result => f_payoff (pp result))

end
