/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Foundations.GameHop
public import Cslib.Crypto.Reductions.FiatShamirROM.Games
public import Cslib.Crypto.Reductions.FiatShamirROM.CollisionBound
public import Cslib.Crypto.Reductions.FiatShamirROM.GameHops
public import Cslib.Crypto.Reductions.FiatShamirROM.ForkingBound

@[expose] public section

/-!
# Fiat-Shamir ROM Security Reduction

The central security theorem for Fiat-Shamir signatures: if the
underlying Sigma protocol has **special soundness** and **special
HVZK**, and the relation is hard, then the Fiat-Shamir signature
scheme is **EUF-CMA secure** in the **random oracle model**.

## Main Results

* `fiatShamir_ROM_bound` — concrete security bound:
  `ROM-EUF-CMA advantage ≤ √(q · Adv_R + q/|Ch|) + q² · δ`
* `fiatShamirReduction` — the relation solver constructed from the
  EUF-CMA adversary via the forking lemma and special soundness
* `fiatShamirForkingHop` — the concrete bound packaged as a
  `ForkingHop` in the sequence-of-games DSL
* `fiatShamir_ROM_secure` — asymptotic security: negligible advantage
  under computational hardness of the relation (`SecureAgainst`),
  super-polynomial challenge space, negligible `δ`-unpredictable
  commitments, and polynomial query bound. The proof is a one-line
  application of `ForkingHop.advantage_negligible`.

## Proof Architecture (Boneh-Shoup §19.6)

The reduction proceeds through a chain of game hops:

### Game-hop chain: ROM → LazyROM → MapGame_Real → MapGame1_HVZK

1. **ROM → LazyROM** (`rom_eq_lazy_rom`): The real ROM game samples
   `Fin q → (Msg × Commitment → Challenge)` (per-step random functions).
   By `uniformExpect_eval_at_point`, evaluating a random function at a
   point is equivalent to sampling a uniform value directly. This
   gives exact equality with the lazy-sampling game that uses
   `Fin q → Challenge` as its randomness.

2. **LazyROM → MapGame_Real** (`lazy_le_mapGame_real`): The lazy ROM
   oracle checks the association-list map before using its fresh
   challenge `ch_i` at signing steps. MapGame_Real always uses `ch_i`
   and inserts into the map without checking. The two games differ
   only when a signing query hits a key already in the map, which
   requires a commitment collision. By the union bound over
   `≤ q²` pairs, the gap is at most `q² · δ`
   (`lazyCommitReuse_bound`, via `lazyPairCommitReuse_pair_bound`).

3. **MapGame_Real → MapGame1_HVZK** (`mapGame_real_eq_mapGame1_hvzk`):
   The real prover `(commit, respond)` and the HVZK simulator produce
   the same marginal distribution at each step (by `sim_distribution`).
   The `runWithState_uniformExpect_oracle_eq` lemma lifts this per-step
   equivalence to the full interaction, giving exact equality.

### Combining the game hops

`rom_eq_mapGame1_hvzk_bound` assembles the chain:
  `ROM.adv ≤ MapGame1_HVZK.adv + q² · δ`

### Forking step: MapGame1_HVZK → relation advantage

In MapGame1_HVZK, the signing oracle uses the HVZK simulator and
does **not** use the witness. The forking lemma (`forking_lemma`)
applied to the adversary's interaction yields the quadratic bound:
  `acc²/q ≤ frk + acc/|Ch|`

When forking succeeds, two accepting transcripts with different
challenges at the same forgery index yield a witness via special
soundness (`forkExtraction_le_advR_map`). Thus `frk ≤ Adv_R(B)`.

Inverting the quadratic gives:
  `acc ≤ √(q · Adv_R(B) + q/|Ch|)`

This is `mapGame1_hvzk_forking_bound`.

### Infrastructure lemmas

The file also develops infrastructure for reasoning about stateful
oracle interactions:

* `run_uniformExpect_oracle_eq` / `runWithState_uniformExpect_oracle_eq`:
  per-step marginal equivalence lifts to full interaction expected values
* `queryAtWithState` / `stateBeforeWithState`: access the `k`-th query
  and the state just before it, enabling prefix-independence arguments
* `queryAtWithState_eq_of_prefix`: changing the oracle at indices `≥ k`
  does not affect the `k`-th query
* `mapGameRealOracle_finalMap_lookup`: traces the forgery key through
  the association list to establish which challenge the final map binds
* `lazy_run_stmt_eq_mapGame_real_run_stmt_of_no_reuse`: conditioned on
  no commitment reuse, the lazy and MapGame_Real runs are identical
* `runWithState_eq_of_oracle_agree_on_trace`: two oracles that agree
  on the actual trace produce the same `runWithState` result

## References

* Boneh-Shoup, *A Graduate Course in Applied Cryptography*, §19.6
* [M. Bellare, G. Neven, *Multi-Signatures in the Plain Public-Key Model
  and a General Forking Lemma*][BellareNeven2006]
-/

open Cslib.Probability

/- **Concrete security bound for Fiat-Shamir in the ROM.**

If the Sigma protocol has special soundness, special HVZK, and
`δ`-unpredictable commitments (Def 19.7, Boneh-Shoup), the explicit
Fiat-Shamir reduction has advantage which, combined with the forking overhead,
bounds the ROM EUF-CMA advantage:

$$\mathrm{Adv}_{\mathrm{ROM\text{-}EUF\text{-}CMA}}(A, n)
  \le \sqrt{q \cdot \mathrm{Adv}_R(B_A, n) + q / |\mathcal{C}|}
    + q^2 \cdot \delta$$

where `q` is the total query bound and `|𝒞|` is the challenge space size.

**Proof** (Boneh-Shoup §19.6.1, Theorem 19.16):
1. *Game hop* (`rom_eq_mapGame1_hvzk_bound`): ROM → MapGame1_HVZK.
   Gap bounded by `q² · δ` via lazy sampling + collision bound + HVZK.
2. *Forking* (`mapGame1_hvzk_forking_bound`): In MapGame1_HVZK, the
   signing oracle doesn't use the witness. Forking lemma + special
   soundness extraction yields `acc ≤ √(q · Adv_R + q/|Ch|)`. -/
section FiatShamirMain

variable {R : EffectiveRelation}
  (P : SigmaProtocol R) (Msg : ℕ → Type)
  [∀ n, DecidableEq (Msg n)]
  [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
  [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
  [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)]
  (kg : R.WithKeyGen)
  (ss : P.SpecialSoundness) (hvzk : P.SpecialHVZK)

/-- The **Fiat-Shamir reduction**: given a ROM EUF-CMA adversary `A`,
construct the explicit randomized relation solver obtained from the
forking lemma and special soundness extraction. -/
noncomputable def fiatShamirReduction
    (A : ROM_EUF_CMA_Adversary P Msg) : RelationSolver R :=
  mapGame1_hvzk_relationSolver P Msg kg ss hvzk A

theorem fiatShamir_ROM_bound
    (A : ROM_EUF_CMA_Adversary P Msg)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ) :
    ∀ n,
      (ROM_EUF_CMA_Game P Msg kg).advantage A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          (RelationGame R kg).advantage
            (fiatShamirReduction P Msg kg ss hvzk A) n +
          (A.numQueries n : ℝ) /
            Fintype.card (P.Challenge n)) +
        (A.numQueries n : ℝ) ^ 2 * δ n := by
  intro n
  have h_rom_le := rom_eq_mapGame1_hvzk_bound P Msg kg hvzk A n δ h_unpred
  have h_fork :
      mapGame1_hvzk_advantage P Msg kg hvzk A n ≤
        Real.sqrt ((A.numQueries n : ℝ) *
          (RelationGame R kg).advantage
            (fiatShamirReduction P Msg kg ss hvzk A) n +
          (A.numQueries n : ℝ) /
            Fintype.card (P.Challenge n)) := by
    simpa [fiatShamirReduction] using
      (mapGame1_hvzk_forking_bound P Msg kg ss hvzk A n)
  linarith

/-- **Fiat-Shamir as a `ForkingHop`.**

The concrete `fiatShamir_ROM_bound` packaged into the sequence-of-games
DSL: the ROM EUF-CMA game hops to the underlying relation game through
a rewinding / forking step, with `queries = q`, `extra₁ = q/|Ch|`, and
`extra₂ = q² · δ`. Composing this with `ForkingHop.advantage_negligible`
turns the asymptotic security theorem into a one-line invocation. -/
noncomputable def fiatShamirForkingHop
    (δ : ℕ → ℝ) (h_unpred : P.UnpredictableCommitments δ) :
    ForkingHop (ROM_EUF_CMA_Game P Msg kg) (RelationGame R kg) where
  reduce := fiatShamirReduction P Msg kg ss hvzk
  queries A n := (A.numQueries n : ℝ)
  extra₁ A n := (A.numQueries n : ℝ) / Fintype.card (P.Challenge n)
  extra₂ A n := (A.numQueries n : ℝ) ^ 2 * δ n
  advantage_le A := fiatShamir_ROM_bound P Msg kg ss hvzk A δ h_unpred

/-- **Asymptotic security of Fiat-Shamir in the ROM.**

If:
1. The Sigma protocol has special soundness and special HVZK
2. The underlying relation is hard against `Admissible` adversaries
3. The protocol has `δ`-unpredictable commitments for negligible `δ`
4. The challenge space grows super-polynomially
5. The adversary makes polynomially many queries
6. The Fiat-Shamir reduction `fiatShamirReduction P Msg kg ss hvzk A`
   is in the `Admissible` class

Then the ROM EUF-CMA advantage is negligible.

This is the main theorem connecting Sigma protocols to practical
signatures in the random oracle model (Theorem 19.16, Boneh-Shoup).
The proof is a direct application of `ForkingHop.advantage_negligible`
to `fiatShamirForkingHop`. -/
theorem fiatShamir_ROM_secure
    {Admissible : RelationSolver R → Prop}
    (hR : (RelationGame R kg).SecureAgainst Admissible)
    (δ : ℕ → ℝ)
    (h_unpred : P.UnpredictableCommitments δ)
    (hDelta : Negligible δ)
    (hChallenge : Negligible (fun n => 1 / (Fintype.card (P.Challenge n) : ℝ)))
    (A : ROM_EUF_CMA_Adversary P Msg)
    (hPoly : PolynomiallyBounded (fun n => (A.numQueries n : ℝ)))
    (hAdm : Admissible (fiatShamirReduction P Msg kg ss hvzk A)) :
    Negligible (fun n => (ROM_EUF_CMA_Game P Msg kg).advantage A n) :=
  (fiatShamirForkingHop P Msg kg ss hvzk δ h_unpred).advantage_negligible A
    (hR _ hAdm) hPoly (hChallenge.polyBounded_div hPoly)
    (hDelta.polyBounded_mul hPoly.sq)
    (ROM_EUF_CMA_Game_advantage_nonneg P Msg kg A)
    (RelationGame_advantage_nonneg kg _)
    (fun _ => Nat.cast_nonneg _)
    (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end FiatShamirMain

end
