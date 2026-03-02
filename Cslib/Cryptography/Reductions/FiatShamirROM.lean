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

/-- **Game 1: Simulated signing game.**

Identical to `ROM_EUF_CMA_Game` (Game 0) except the signing oracle
uses the HVZK simulator instead of real signing. Per-query randomness
is `P.Challenge n × hvzk.SimRandomness n` (a challenge and simulator
randomness) rather than `P.ProverRandomness n`.

The signing oracle ignores the message and witness: it samples `(c, s)`
from the per-query coins and computes `(t, z) = hvzk.simulate n y c s`.
Hash oracle and verification are unchanged.

This is the key intermediate game: because the signing oracle does NOT
use the witness `w`, the forking reduction can be applied. -/
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
    uniformExpect
      (R.Witness n × (Msg n × P.Commitment n → P.Challenge n)
       × (Fin q → P.Challenge n × hvzk.SimRandomness n))
      (fun ⟨w, H, simCoins⟩ =>
        let y := keyOf n w
        let oracle : Fin q →
            (Msg n ⊕ (Msg n × P.Commitment n)) →
            ((P.Commitment n × P.Response n) ⊕ P.Challenge n) :=
          fun i qry => match qry with
          | .inl _m =>
            let (c, s) := simCoins i
            let (t, z) := hvzk.simulate n y c s
            .inl (t, z)
          | .inr mt => .inr (H mt)
        match (A.interact n y).run q oracle with
        | none => 0
        | some (queries, mf, tf, zf) =>
          let signMsgs := queries.filterMap (fun q => match q with
            | .inl m => some m | .inr _ => none)
          boolToReal (P.verify n y tf (H (mf, tf)) zf &&
            !(signMsgs.contains mf)))

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
    (A : ROM_EUF_CMA_Adversary P Msg) :
    ∃ B : RelationSolver R, ∀ n,
      (ROM_EUF_CMA_Game P Msg keyOf).advantage A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          (RelationGame R keyOf).advantage B n +
          (A.numQueries n : ℝ) /
            Fintype.card (P.Challenge n)) +
        (A.numQueries n : ℝ) ^ 2 /
          Fintype.card (P.Commitment n) := by
  sorry

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
    (hR : (RelationGame R keyOf).Secure)
    (hCommit : Negligible (fun n => 1 / (Fintype.card (P.Commitment n) : ℝ)))
    (hChallenge : Negligible (fun n => 1 / (Fintype.card (P.Challenge n) : ℝ)))
    (A : ROM_EUF_CMA_Adversary P Msg)
    (hPoly : PolynomiallyBounded (fun n => (A.numQueries n : ℝ))) :
    Negligible (fun n => (ROM_EUF_CMA_Game P Msg keyOf).advantage A n) := by
  sorry

end
