/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Protocols.SigmaProtocol
public import Cslib.Cryptography.Foundations.OracleInteraction

@[expose] public section

/-!
# Random Oracle Model for Fiat-Shamir Signatures

This file defines the **ROM (Random Oracle Model) EUF-CMA** security
game for Fiat-Shamir signature schemes and a generic **relation hardness
game** for the underlying relation.

## Main Definitions

* `ROM_EUF_CMA_Adversary` — an adversary with oracle access to both
  a signing oracle and a hash oracle (modeled via sum-type queries)
* `ROM_EUF_CMA_Game` — the EUF-CMA game in the random oracle model
* `RelationSolver` — an adversary trying to find a witness for a relation
* `RelationGame` — the hardness game for a relation

## Design Notes

The two-oracle adversary model uses sum types for queries:
- `Sum.inl m` — signing query for message `m`
- `Sum.inr (m, t)` — hash query for `(m, t)`

The hash function `H` is sampled uniformly as part of the game coins.
Signing is performed honestly using `H`.

## References

* Boneh-Shoup, *A Graduate Course in Applied Cryptography*, §19.6
* [M. Bellare, P. Rogaway, *Random Oracles are Practical*][BellareR1993]
-/

open Cslib.Probability

/-- A **ROM EUF-CMA adversary** for a Fiat-Shamir signature scheme.

The adversary receives the public key (statement) and adaptively
queries either:
- `Sum.inl m` — request a signature on message `m`
- `Sum.inr (m, t)` — request the hash of `(m, t)`

The responses are:
- `Sum.inl (t, z)` — a signature (commitment, response)
- `Sum.inr c` — a hash value (challenge)

The adversary eventually outputs a forgery `(m★, t★, z★)`. -/
structure ROM_EUF_CMA_Adversary {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type) where
  /-- Upper bound on the total number of queries (hash + sign) -/
  numQueries : ℕ → ℕ
  /-- The adaptive oracle interaction -/
  interact : (n : ℕ) → R.Statement n →
    OracleInteraction
      (Msg n ⊕ (Msg n × P.Commitment n))
      ((P.Commitment n × P.Response n) ⊕ P.Challenge n)
      (Msg n × P.Commitment n × P.Response n)

/-- The **ROM EUF-CMA security game** for a Fiat-Shamir signature scheme.

The game:
1. Samples a witness `w` uniformly
2. Samples a random oracle `H : Msg × Commitment → Challenge` uniformly
3. Samples signing randomness `rs : Fin q → ProverRandomness`
4. Gives the adversary the statement `y = keyOf w`
5. Answers signing queries using honest Fiat-Shamir signing with `H`
6. Answers hash queries by evaluating `H`
7. Checks if the forgery verifies and the message is fresh -/
noncomputable def ROM_EUF_CMA_Game {R : EffectiveRelation}
    (P : SigmaProtocol R) (Msg : ℕ → Type)
    [∀ n, DecidableEq (Msg n)]
    [∀ n, Fintype (Msg n)] [∀ n, Nonempty (Msg n)]
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    (keyOf : ∀ n, R.Witness n → R.Statement n) :
    SecurityGame (ROM_EUF_CMA_Adversary P Msg) where
  advantage A n :=
    let q := A.numQueries n
    uniformExpect
      (R.Witness n × (Msg n × P.Commitment n → P.Challenge n)
       × (Fin q → P.ProverRandomness n))
      (fun ⟨w, H, rs⟩ =>
        let y := keyOf n w
        let oracle : Fin q →
            (Msg n ⊕ (Msg n × P.Commitment n)) →
            ((P.Commitment n × P.Response n) ⊕ P.Challenge n) :=
          fun i qry => match qry with
          | .inl m =>
            let t := P.commit n w y (rs i)
            .inl (t, P.respond n w y (rs i) (H (m, t)))
          | .inr mt => .inr (H mt)
        match (A.interact n y).run q oracle with
        | none => 0
        | some (queries, mf, tf, zf) =>
          let signMsgs := queries.filterMap (fun q => match q with
            | .inl m => some m | .inr _ => none)
          boolToReal (P.verify n y tf (H (mf, tf)) zf &&
            !(signMsgs.contains mf)))

/-- A **relation solver** is an adversary that attempts to find a
witness given a statement. -/
structure RelationSolver (R : EffectiveRelation) where
  /-- Given a statement, attempt to find a witness. -/
  find : (n : ℕ) → R.Statement n → R.Witness n

/-- The **relation hardness game**: the challenger samples a witness `w`
uniformly, computes the statement `y = keyOf w`, and gives `y` to the
solver. The solver wins if it outputs a valid witness for `y`. -/
noncomputable def RelationGame (R : EffectiveRelation)
    (keyOf : ∀ n, R.Witness n → R.Statement n)
    [∀ n, Fintype (R.Witness n)] [∀ n, Nonempty (R.Witness n)]
    [∀ n (w : R.Witness n) (y : R.Statement n), Decidable (R.relation n w y)] :
    SecurityGame (RelationSolver R) where
  advantage B n := uniformExpect (R.Witness n) (fun w =>
    boolToReal (decide (R.relation n (B.find n (keyOf n w)) (keyOf n w))))

end
