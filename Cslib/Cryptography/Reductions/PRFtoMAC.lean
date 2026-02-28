/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Primitives.PRF
public import Cslib.Cryptography.Primitives.MAC

@[expose] public section

/-!
# PRF → MAC Security Reduction

This file constructs an EUF-CMA secure MAC from any pseudorandom
function (PRF) and proves the security reduction.

## Construction

Given a PRF `F : Key n → Input n → Output n`, we define:
- `tag(k, m) = F(k, m)`
- `verify(k, m, t) = (F(k, m) == t)`

## Main Results

* `PRF.toMACScheme` — the construction
* `PRF.toMACScheme_correct` — correctness
* `PRF.toMACScheme_reduction_bound` — EUF-CMA advantage ≤ PRF advantage + ideal gap
* `PRF.toMACScheme_secure` — PRF security + negligible ideal gap → EUF-CMA security

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014], §4.3
-/

open Cslib.Probability

/-- The standard PRF-based MAC: `tag(k, m) = F(k, m)`. -/
def PRF.toMACScheme (F : PRF) [∀ n, DecidableEq (F.Output n)] :
    MACScheme where
  Key := F.Key
  Message := F.Input
  Tag := F.Output
  keyFintype := F.keyFintype
  keyNonempty := F.keyNonempty
  tag n k m := F.eval n k m
  verify n k m t := decide (F.eval n k m = t)
  efficient := F.efficient

/-- The PRF-based MAC is correct: verification accepts honestly
generated tags. -/
theorem PRF.toMACScheme_correct (F : PRF)
    [∀ n, DecidableEq (F.Output n)] :
    F.toMACScheme.Correct := by
  intro n k m
  simp [toMACScheme]

/-- Simulate the EUF-CMA game body with a given oracle function.

Given `oracle : F.Input n → F.Output n` (either `F(k,·)` or a random
function), compute whether the adversary produces a valid forgery
under this oracle. -/
noncomputable def PRF.simulateMACBody (F : PRF)
    [∀ n, DecidableEq (F.Output n)]
    [∀ n, DecidableEq (F.Input n)]
    (A : MACScheme.EUF_CMA_Adversary F.toMACScheme)
    (n : ℕ) (oracle : F.Input n → F.Output n) : Bool :=
  let m_query : F.Input n := A.query n
  let t_query : F.Output n := oracle m_query
  let result := A.forge n t_query
  let m_forge : F.Input n := result.1
  let t_forge : F.Output n := result.2
  (decide (m_forge ≠ m_query) && decide (oracle m_forge = t_forge))

/-- Construct a PRF adversary from a MAC forger.

The PRF adversary simulates the MAC game using its oracle and outputs
`true` (claiming the oracle is the PRF) iff the forgery verifies. -/
noncomputable def PRF.mkPRFAdversaryFromMAC (F : PRF)
    [∀ n, DecidableEq (F.Output n)]
    [∀ n, DecidableEq (F.Input n)]
    (A : MACScheme.EUF_CMA_Adversary F.toMACScheme) :
    PRF.OracleAdversary F where
  run n oracle := F.simulateMACBody A n oracle

/-- The ideal-world forgery probability: the adversary's success rate
when the tagging oracle is a truly random function. -/
noncomputable def PRF.EUF_CMA_idealWorldGap (F : PRF)
    [∀ n, DecidableEq (F.Output n)]
    [∀ n, DecidableEq (F.Input n)]
    (A : MACScheme.EUF_CMA_Adversary F.toMACScheme) (n : ℕ) : ℝ :=
  letI := F.funFintype n; letI := F.funNonempty n
  uniformExpect (F.Input n → F.Output n) (fun rf =>
    boolToReal (F.simulateMACBody A n rf))

/-- **PRF → EUF-CMA reduction bound.**

For any EUF-CMA adversary `A`, the PRF distinguisher `mkPRFAdversaryFromMAC`
satisfies:
$$\mathrm{EUF\text{-}CMA~advantage}(A, n)
  \le \mathrm{PRF~advantage}(B, n)
    + \mathrm{idealWorldGap}(A, n)$$
-/
theorem PRF.toMACScheme_reduction_bound (F : PRF)
    [∀ n, DecidableEq (F.Output n)]
    [instDI : ∀ n, DecidableEq (F.Input n)]
    (A : MACScheme.EUF_CMA_Adversary F.toMACScheme) :
    ∀ n, (@MACScheme.EUF_CMA_Game F.toMACScheme instDI).advantage A n ≤
      F.SecurityGame.advantage (F.mkPRFAdversaryFromMAC A) n +
      F.EUF_CMA_idealWorldGap A n := by
  intro n
  letI := F.keyFintype n; letI := F.keyNonempty n
  letI := F.funFintype n; letI := F.funNonempty n
  -- Step 1: Express MAC advantage using simulateMACBody
  have h_mac_eq :
      (@MACScheme.EUF_CMA_Game F.toMACScheme instDI).advantage A n =
      uniformExpect (F.Key n) (fun k =>
        boolToReal (F.simulateMACBody A n (F.eval n k))) := by
    simp only [MACScheme.EUF_CMA_Game, toMACScheme, simulateMACBody]; rfl
  -- Step 2: The PRF advantage of our adversary
  have h_prf_eq : F.SecurityGame.advantage (F.mkPRFAdversaryFromMAC A) n =
      |uniformExpect (F.Key n) (fun k =>
          boolToReal (F.simulateMACBody A n (F.eval n k))) -
       uniformExpect (F.Input n → F.Output n) (fun rf =>
          boolToReal (F.simulateMACBody A n rf))| := by
    simp [PRF.SecurityGame, mkPRFAdversaryFromMAC]
  -- Step 3: real = (real - ideal) + ideal ≤ |real - ideal| + ideal
  rw [h_mac_eq, h_prf_eq]
  unfold EUF_CMA_idealWorldGap
  set real := uniformExpect (F.Key n) (fun k =>
    boolToReal (F.simulateMACBody A n (F.eval n k)))
  set ideal := uniformExpect (F.Input n → F.Output n) (fun rf =>
    boolToReal (F.simulateMACBody A n rf))
  linarith [le_abs_self (real - ideal)]

/-- **PRF security + negligible ideal-world gap → EUF-CMA security.** -/
theorem PRF.toMACScheme_secure (F : PRF)
    [∀ n, DecidableEq (F.Output n)]
    [instDI : ∀ n, DecidableEq (F.Input n)]
    (hF : F.Secure)
    (A : MACScheme.EUF_CMA_Adversary F.toMACScheme)
    (hGap : Negligible (F.EUF_CMA_idealWorldGap A)) :
    Negligible (fun n =>
      (@MACScheme.EUF_CMA_Game F.toMACScheme instDI).advantage A n) := by
  let B := F.mkPRFAdversaryFromMAC A
  apply Negligible.mono (Negligible.add (hF B) hGap)
  refine ⟨0, fun n _ => ?_⟩
  letI := F.toMACScheme.keyFintype n; letI := F.toMACScheme.keyNonempty n
  letI := F.funFintype n; letI := F.funNonempty n
  have h1 : 0 ≤ (@MACScheme.EUF_CMA_Game F.toMACScheme instDI).advantage A n :=
    uniformExpect_nonneg _ fun _ => boolToReal_nonneg _
  have h2 : 0 ≤ F.SecurityGame.advantage B n := abs_nonneg _
  have h3 : 0 ≤ F.EUF_CMA_idealWorldGap A n :=
    uniformExpect_nonneg _ fun _ => boolToReal_nonneg _
  rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
  exact F.toMACScheme_reduction_bound A n

end
