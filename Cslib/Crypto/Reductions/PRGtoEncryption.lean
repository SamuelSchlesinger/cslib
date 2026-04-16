/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Primitives.PRG
public import Cslib.Crypto.Primitives.Encryption

@[expose] public section

/-!
# PRG → IND-CPA Encryption Security Reduction

This file constructs an IND-CPA secure stream cipher from any
pseudorandom generator (PRG) and proves that PRG security implies
IND-CPA security of the resulting scheme.

## Construction

Given a PRG `G : Seed n → Output n` with an `AddCommGroup` on
the output type (abstracting XOR), we define:
- `Enc(k, m; ()) = G(k) + m`
- `Dec(k, c) = c - G(k)`

## Main Results

* `PRG.toEncryptionScheme` — the construction
* `PRG.toEncryptionScheme_correct` — correctness
* `PRG.toEncryptionScheme_secure` — PRG security → IND-CPA security

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014], §3.3
-/

open Cslib.Probability

/-- The standard PRG-based stream cipher: `Enc(k, m) = G(k) + m`. -/
@[reducible] noncomputable def PRG.toEncryptionScheme (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    : EncryptionScheme where
  Key := G.Seed
  Plaintext := G.Output
  Ciphertext := G.Output
  Randomness := fun _ => Unit
  keyFintype := G.seedFintype
  keyNonempty := G.seedNonempty
  randomnessFintype := fun _ => inferInstance
  randomnessNonempty := fun _ => inferInstance
  encrypt n k m _ := G.stretch n k + m
  decrypt n k c := some (c - G.stretch n k)

/-- The PRG-based stream cipher is correct. -/
theorem PRG.toEncryptionScheme_correct (G : PRG)
    [∀ n, AddCommGroup (G.Output n)] :
    G.toEncryptionScheme.Correct := by
  intro n k m r
  simp [toEncryptionScheme, add_sub_cancel_left]

/-- The non-key coins used by the PRG reduction.

For the stream cipher, the per-query encryption randomness is trivial,
so these coins consist of the adversary's internal randomness, the
dummy `Unit` randomness slots from the IND-CPA game, and the challenge
bit. -/
abbrev PRGReductionCoins (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme) (n : ℕ) : Type :=
  A.Coins n × (Fin (A.numQueries1 n) → Unit) × Unit ×
    (Fin (A.numQueries2 n) → Unit) × Bool

/-- Simulate the IND-CPA game body with a fixed non-key coin tuple and
candidate keystream `y`.

Since the stream cipher has `Randomness = Unit`, the encryption oracle
is `fun m => y + m` regardless of the per-query randomness. Returns `0`
on fuel exhaustion (adversary defaults to losing). -/
noncomputable def PRG.simulateStreamBody (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (n : ℕ) (coins : PRGReductionCoins G A n) (y : G.Output n) : ℝ :=
  match (A.choose n coins.1).run (A.numQueries1 n) (fun _ m => y + m) with
  | none => 0
  | some (_, m₀, m₁, σ) =>
    match
      (A.guess n coins.1 (y + if coins.2.2.2.2 then m₁ else m₀) σ).run
        (A.numQueries2 n) (fun _ m => y + m) with
    | none => 0
    | some (_, b') => boolToReal (b' == coins.2.2.2.2)

/-- Boolean version of `simulateStreamBody`. -/
def prgSimulateStreamBodyBool (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (n : ℕ) (coins : PRGReductionCoins G A n) (y : G.Output n) : Bool :=
  match (A.choose n coins.1).run (A.numQueries1 n) (fun _ m => y + m) with
  | none => false
  | some (_, m₀, m₁, σ) =>
    match
      (A.guess n coins.1 (y + if coins.2.2.2.2 then m₁ else m₀) σ).run
        (A.numQueries2 n) (fun _ m => y + m) with
    | none => false
    | some (_, b') => b' == coins.2.2.2.2

theorem prgSimulateStreamBody_eq_bool (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (n : ℕ) (coins : PRGReductionCoins G A n) (y : G.Output n) :
    G.simulateStreamBody A n coins y =
      boolToReal (prgSimulateStreamBodyBool G A n coins y) := by
  unfold PRG.simulateStreamBody prgSimulateStreamBodyBool
  rcases hc : (A.choose n coins.1).run (A.numQueries1 n)
      (fun _ m => y + m) with _ | ⟨_, m₀, m₁, σ⟩
  · simp [boolToReal]
  · rcases hg : (A.guess n coins.1 (y + if coins.2.2.2.2 then m₁ else m₀) σ).run
        (A.numQueries2 n) (fun _ m => y + m) with _ | ⟨_, b'⟩
    · simp [hg, boolToReal]
    · simp [hg, boolToReal, beq_iff_eq]

/-- Construct a PRG distinguisher from an IND-CPA adversary. -/
noncomputable def PRG.mkPRGAdversary (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme) :
    PRG.DistinguishingAdversary G where
  Coins := PRGReductionCoins G A
  coinsFintype := by
    intro n
    letI := A.coinsFintype n
    infer_instance
  coinsNonempty := by
    intro n
    letI := A.coinsNonempty n
    infer_instance
  distinguish n coins y := prgSimulateStreamBodyBool G A n coins y

/-- The ideal-world gap for the PRG→IND-CPA reduction. -/
noncomputable def PRG.IND_CPA_idealWorldGap (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (n : ℕ) : ℝ :=
  letI := G.outputFintype n; letI := G.outputNonempty n
  letI := A.coinsFintype n; letI := A.coinsNonempty n
  letI : Fintype (PRGReductionCoins G A n) := inferInstance
  letI : Nonempty (PRGReductionCoins G A n) := inferInstance
  |uniformExpect (G.Output n × PRGReductionCoins G A n) (fun x =>
      G.simulateStreamBody A n x.2 x.1)
   - 1/2|

/-- **PRG → IND-CPA reduction bound.** -/
theorem PRG.toEncryptionScheme_reduction_bound (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (A : IND_CPA_Adversary G.toEncryptionScheme) :
    ∃ (B : PRG.DistinguishingAdversary G),
      ∀ n, (IND_CPA_Game G.toEncryptionScheme).advantage A n ≤
        G.SecurityGame.advantage B n +
        G.IND_CPA_idealWorldGap A n := by
  let B := G.mkPRGAdversary A
  refine ⟨B, fun n => ?_⟩
  letI := G.seedFintype n
  letI := G.seedNonempty n
  letI := G.outputFintype n
  letI := G.outputNonempty n
  letI := A.coinsFintype n
  letI := A.coinsNonempty n
  letI : Fintype (PRGReductionCoins G A n) := inferInstance
  letI : Nonempty (PRGReductionCoins G A n) := inferInstance
  have h_game_bool :
      (IND_CPA_Game G.toEncryptionScheme).advantage A n =
        |uniformExpect (G.Seed n × PRGReductionCoins G A n) (fun x =>
            boolToReal (prgSimulateStreamBodyBool G A n x.2 (G.stretch n x.1))) - 1 / 2| := by
    unfold IND_CPA_Game
    simp only [PRG.toEncryptionScheme]
    congr 1
    congr 1
    rw [uniformExpect_eq, uniformExpect_eq]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro a _
    rcases a with ⟨seed, coins, rs1, r_ch, rs2, b⟩
    change _ =
      boolToReal (prgSimulateStreamBodyBool G A n (coins, rs1, r_ch, rs2, b) (G.stretch n seed))
    unfold prgSimulateStreamBodyBool
    rcases hc : (A.choose n coins).run (A.numQueries1 n)
        (fun _ m => G.stretch n seed + m) with _ | ⟨_, m₀, m₁, σ⟩
    · simp [boolToReal]
    · rcases hg : (A.guess n coins (G.stretch n seed + if b then m₁ else m₀) σ).run
          (A.numQueries2 n) (fun _ m => G.stretch n seed + m) with _ | ⟨_, b'⟩
      · simp [hg, boolToReal]
      · simp [hg, boolToReal, beq_iff_eq]
  have h_gap :
      G.IND_CPA_idealWorldGap A n =
        |uniformExpect (G.Output n × PRGReductionCoins G A n) (fun x =>
            G.simulateStreamBody A n x.2 x.1) - 1 / 2| := by
    rfl
  have h_gap_bool :
      G.IND_CPA_idealWorldGap A n =
        |uniformExpect (G.Output n × PRGReductionCoins G A n) (fun x =>
            boolToReal (prgSimulateStreamBodyBool G A n x.2 x.1)) - 1 / 2| := by
    have h_eq :
        uniformExpect (G.Output n × PRGReductionCoins G A n) (fun x =>
          G.simulateStreamBody A n x.2 x.1) =
          uniformExpect (G.Output n × PRGReductionCoins G A n) (fun x =>
            boolToReal (prgSimulateStreamBodyBool G A n x.2 x.1)) := by
      congr 1
      funext x
      simpa using prgSimulateStreamBody_eq_bool G A n x.2 x.1
    rw [h_gap, h_eq]
  have h_B :
      G.SecurityGame.advantage B n =
        |uniformExpect (G.Seed n × PRGReductionCoins G A n) (fun x =>
            boolToReal (prgSimulateStreamBodyBool G A n x.2 (G.stretch n x.1))) -
          uniformExpect (G.Output n × PRGReductionCoins G A n) (fun x =>
            boolToReal (prgSimulateStreamBodyBool G A n x.2 x.1))| := by
    rfl
  rw [h_game_bool, h_B, h_gap_bool]
  calc
    |uniformExpect (G.Seed n × PRGReductionCoins G A n) (fun x =>
        boolToReal (prgSimulateStreamBodyBool G A n x.2 (G.stretch n x.1))) - 1 / 2| ≤
      |uniformExpect (G.Seed n × PRGReductionCoins G A n) (fun x =>
          boolToReal (prgSimulateStreamBodyBool G A n x.2 (G.stretch n x.1))) -
        uniformExpect (G.Output n × PRGReductionCoins G A n) (fun x =>
          boolToReal (prgSimulateStreamBodyBool G A n x.2 x.1))| +
      |uniformExpect (G.Output n × PRGReductionCoins G A n) (fun x =>
          boolToReal (prgSimulateStreamBodyBool G A n x.2 x.1)) - 1 / 2| := by
      have h_split :
          uniformExpect (G.Seed n × PRGReductionCoins G A n) (fun x =>
              boolToReal (prgSimulateStreamBodyBool G A n x.2 (G.stretch n x.1))) - 1 / 2 =
            (uniformExpect (G.Seed n × PRGReductionCoins G A n) (fun x =>
                boolToReal (prgSimulateStreamBodyBool G A n x.2 (G.stretch n x.1))) -
              uniformExpect (G.Output n × PRGReductionCoins G A n) (fun x =>
                boolToReal (prgSimulateStreamBodyBool G A n x.2 x.1))) +
            (uniformExpect (G.Output n × PRGReductionCoins G A n) (fun x =>
                boolToReal (prgSimulateStreamBodyBool G A n x.2 x.1)) - 1 / 2) := by
        ring
      rw [h_split]
      exact abs_add_le _ _

/-- **PRG security → IND-CPA security** for the stream cipher,
given that the ideal-world gap is negligible. -/
theorem PRG.toEncryptionScheme_secure (G : PRG)
    [∀ n, AddCommGroup (G.Output n)]
    (hG : G.Secure)
    (A : IND_CPA_Adversary G.toEncryptionScheme)
    (hGap : Negligible (G.IND_CPA_idealWorldGap A)) :
    Negligible (fun n =>
      (IND_CPA_Game G.toEncryptionScheme).advantage A n) := by
  obtain ⟨B, hB⟩ := G.toEncryptionScheme_reduction_bound A
  apply Negligible.mono (Negligible.add (hG B) hGap)
  refine ⟨0, fun n _ => ?_⟩
  have h1 : 0 ≤ (IND_CPA_Game G.toEncryptionScheme).advantage A n := by
    simp only [IND_CPA_Game]; exact abs_nonneg _
  have h2 : 0 ≤ G.SecurityGame.advantage B n := abs_nonneg _
  have h3 : 0 ≤ G.IND_CPA_idealWorldGap A n := abs_nonneg _
  rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
  exact hB n

end
