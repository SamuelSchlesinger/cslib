/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.SecurityGame

@[expose] public section

/-!
# Sigma Protocols

A **Sigma protocol** (Σ-protocol) is a three-move interactive proof
system between a prover and a verifier. The prover sends a commitment,
the verifier responds with a random challenge, and the prover sends
a response. The verifier then accepts or rejects.

Sigma protocols are the key abstraction for honest-verifier
zero-knowledge proofs and form the basis for Schnorr signatures,
the Fiat-Shamir heuristic, and many advanced protocols.

## Main Definitions

* `EffectiveRelation` — a relation between witnesses and statements
* `SigmaProtocol` — a three-move proof system for an `EffectiveRelation`
* `SigmaProtocol.SpecialSoundness` — from two accepting conversations
  with the same commitment but different challenges, one can extract
  a witness (Def 19.4 in Boneh-Shoup)
* `SigmaProtocol.SpecialHVZK` — a simulator can produce transcripts
  indistinguishable from real conversations (Def 19.5 in Boneh-Shoup)

## References

* Boneh-Shoup, *A Graduate Course in Applied Cryptography*, Ch. 19
* [O. Goldreich, *Foundations of Cryptography, Vol. 1*][Goldreich2001]
-/

/-- An **effective relation** between witnesses and statements, indexed
by the security parameter. This captures the NP relation underlying
a proof system: `relation n w y` means `w` is a valid witness for
statement `y` at security level `n`. -/
structure EffectiveRelation where
  /-- Witness type at security level `n` -/
  Witness : ℕ → Type
  /-- Statement type at security level `n` -/
  Statement : ℕ → Type
  /-- The relation: `relation n w y` holds when `w` is a valid
  witness for statement `y` -/
  relation : ∀ n, Witness n → Statement n → Prop

/-- A **Sigma protocol** for an effective relation `R`. The protocol
is a three-move proof of knowledge:

1. **Commit**: The prover sends a commitment `t`
2. **Challenge**: The verifier sends a random challenge `c`
3. **Respond**: The prover sends a response `z`
4. **Verify**: The verifier accepts or rejects based on `(y, t, c, z)` -/
structure SigmaProtocol (R : EffectiveRelation) where
  /-- Commitment type -/
  Commitment : ℕ → Type
  /-- Challenge type -/
  Challenge : ℕ → Type
  /-- Response type -/
  Response : ℕ → Type
  /-- Prover's randomness type -/
  ProverRandomness : ℕ → Type
  /-- Commitments form a finite type -/
  commitmentFintype : ∀ n, Fintype (Commitment n)
  /-- Commitments are nonempty -/
  commitmentNonempty : ∀ n, Nonempty (Commitment n)
  /-- Commitments have decidable equality -/
  commitmentDecEq : ∀ n, DecidableEq (Commitment n)
  /-- Challenges form a finite type -/
  challengeFintype : ∀ n, Fintype (Challenge n)
  /-- Challenges are nonempty -/
  challengeNonempty : ∀ n, Nonempty (Challenge n)
  /-- Challenges have decidable equality -/
  challengeDecEq : ∀ n, DecidableEq (Challenge n)
  /-- Responses form a finite type -/
  responseFintype : ∀ n, Fintype (Response n)
  /-- Responses are nonempty -/
  responseNonempty : ∀ n, Nonempty (Response n)
  /-- Prover randomness forms a finite type -/
  proverRandomnessFintype : ∀ n, Fintype (ProverRandomness n)
  /-- Prover randomness is nonempty -/
  proverRandomnessNonempty : ∀ n, Nonempty (ProverRandomness n)
  /-- Prover's commitment function: given witness, statement, and
  randomness, produce a commitment -/
  commit : ∀ n, R.Witness n → R.Statement n →
    ProverRandomness n → Commitment n
  /-- Prover's response function: given witness, statement,
  randomness, and challenge, produce a response -/
  respond : ∀ n, R.Witness n → R.Statement n →
    ProverRandomness n → Challenge n → Response n
  /-- Verifier's decision function: given statement, commitment,
  challenge, and response, accept or reject -/
  verify : ∀ n, R.Statement n → Commitment n →
    Challenge n → Response n → Bool
  /-- **Completeness**: an honest prover with a valid witness is
  always accepted. For any `(w, y) ∈ R`, any randomness `r`, and
  any challenge `c`, the honest transcript is accepted. -/
  completeness : ∀ n (w : R.Witness n) (y : R.Statement n)
    (r : ProverRandomness n) (c : Challenge n),
    R.relation n w y →
    verify n y (commit n w y r) c (respond n w y r c) = true
  /-- **Commitment uniformity**: for any valid `(w, y)`, the commitment
  function `commit(w, y, ·)` pushes the uniform distribution on
  `ProverRandomness` to the uniform distribution on `Commitment`.
  Equivalently, `E_r[f(commit(w, y, r))] = E_t[f(t)]` for all `f`.

  This holds for all standard Sigma protocols (e.g., Schnorr, where
  commitments are `g^r` for uniform `r`). -/
  commitmentUniform : ∀ n (w : R.Witness n) (y : R.Statement n),
    R.relation n w y →
    ∀ (f : Commitment n → ℝ),
    Cslib.Probability.uniformExpect (ProverRandomness n)
      (fun r => f (commit n w y r)) =
    Cslib.Probability.uniformExpect (Commitment n) f

attribute [instance] SigmaProtocol.commitmentFintype
  SigmaProtocol.commitmentNonempty SigmaProtocol.commitmentDecEq
  SigmaProtocol.challengeFintype SigmaProtocol.challengeNonempty
  SigmaProtocol.challengeDecEq SigmaProtocol.responseFintype
  SigmaProtocol.responseNonempty
  SigmaProtocol.proverRandomnessFintype
  SigmaProtocol.proverRandomnessNonempty

open Cslib.Probability in
/-- Each commitment value has probability exactly `1/|Commitment|`. -/
theorem SigmaProtocol.commit_prob_eq {R : EffectiveRelation} (P : SigmaProtocol R)
    (n : ℕ) (w : R.Witness n) (y : R.Statement n) (t₀ : P.Commitment n)
    (hw : R.relation n w y) :
    uniformExpect (P.ProverRandomness n)
      (fun r => if P.commit n w y r = t₀ then (1 : ℝ) else 0) =
    1 / Fintype.card (P.Commitment n) := by
  have h := P.commitmentUniform n w y hw (fun t => if t = t₀ then 1 else 0)
  simp only [h, uniformExpect_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- **Product commitment uniformity**: the tuple of commitments
`(commit(w,y,rs₀), ..., commit(w,y,rs_{q-1}))` is uniformly
distributed when `rs : Fin q → ProverRandomness` is uniform.

This extends `commitmentUniform` (single coordinate) to the product
distribution over `q` independent signing queries. -/
theorem SigmaProtocol.commitmentUniform_prod {R : EffectiveRelation}
    (P : SigmaProtocol R) (n : ℕ) (q : ℕ)
    (w : R.Witness n) (y : R.Statement n) (hw : R.relation n w y)
    (f : (Fin q → P.Commitment n) → ℝ) :
    Cslib.Probability.uniformExpect (Fin q → P.ProverRandomness n)
      (fun rs => f (fun i => P.commit n w y (rs i))) =
    Cslib.Probability.uniformExpect (Fin q → P.Commitment n) f := by
  induction q with
  | zero =>
    -- Both Fin 0 → α are singletons; both sides equal f(Fin.elim0)
    have h1 : (fun rs : Fin 0 → P.ProverRandomness n =>
        f (fun i => P.commit n w y (rs i))) = fun _ => f Fin.elim0 :=
      funext fun rs => congr_arg f (funext fun i => i.elim0)
    rw [h1, Cslib.Probability.uniformExpect_const]
    have h2 : f = fun _ => f Fin.elim0 :=
      funext fun ts => congr_arg f (funext fun i => i.elim0)
    rw [h2, Cslib.Probability.uniformExpect_const]
  | succ q ih =>
    open Cslib.Probability in
    haveI : Nonempty (Fin q → P.ProverRandomness n) := inferInstance
    haveI : Nonempty (Fin q → P.Commitment n) := inferInstance
    -- Decompose (Fin (q+1) → α) ≃ α × (Fin q → α) via Fin.consEquiv
    let eR := (Fin.consEquiv (fun _ : Fin (q + 1) => P.ProverRandomness n)).symm
    let eC := (Fin.consEquiv (fun _ : Fin (q + 1) => P.Commitment n)).symm
    -- Decompose LHS via consEquiv
    have h_lhs : (fun rs : Fin (q + 1) → P.ProverRandomness n =>
        f (fun i => P.commit n w y (rs i))) =
      (fun p : P.ProverRandomness n × (Fin q → P.ProverRandomness n) =>
        f (Fin.cons (P.commit n w y p.1)
          (fun j => P.commit n w y (p.2 j)))) ∘ eR := by
      ext rs; simp only [Function.comp_apply, eR]
      congr 1; exact (Fin.cons_self_tail _).symm
    -- Decompose RHS via consEquiv
    have h_rhs : f = (fun p : P.Commitment n × (Fin q → P.Commitment n) =>
        f (Fin.cons p.1 p.2)) ∘ eC := by
      ext ts; simp only [Function.comp_apply, eC]
      congr 1; exact (Fin.cons_self_tail ts).symm
    -- Forward-decompose both sides, then connect in the middle
    rw [h_lhs, uniformExpect_congr, uniformExpect_prod]
    rw [h_rhs, uniformExpect_congr, uniformExpect_prod]
    -- Force goal into beta-reduced form
    change uniformExpect (P.ProverRandomness n) (fun r₀ =>
        uniformExpect (Fin q → P.ProverRandomness n) (fun rs' =>
          f (Fin.cons (P.commit n w y r₀)
            (fun j => P.commit n w y (rs' j))))) =
      uniformExpect (P.Commitment n) (fun t₀ =>
        uniformExpect (Fin q → P.Commitment n) (fun ts' =>
          f (Fin.cons t₀ ts')))
    -- IH rewrites inner, commitmentUniform rewrites outer
    simp_rw [show ∀ r₀ : P.ProverRandomness n,
        uniformExpect (Fin q → P.ProverRandomness n) (fun rs' =>
          f (Fin.cons (P.commit n w y r₀) (fun j => P.commit n w y (rs' j)))) =
        uniformExpect (Fin q → P.Commitment n) (fun ts' =>
          f (Fin.cons (P.commit n w y r₀) ts'))
      from fun r₀ => ih (fun ts' => f (Fin.cons (P.commit n w y r₀) ts'))]
    exact P.commitmentUniform n w y hw
      (fun t₀ => uniformExpect (Fin q → P.Commitment n)
        (fun ts' => f (Fin.cons t₀ ts')))

/-- **Special soundness** (Def 19.4 in Boneh-Shoup): from two
accepting conversations `(t, c, z)` and `(t, c', z')` sharing the
same commitment `t` but with distinct challenges `c ≠ c'`, an
extractor can recover a valid witness. -/
structure SigmaProtocol.SpecialSoundness {R : EffectiveRelation}
    (P : SigmaProtocol R) where
  /-- The witness extractor -/
  extract : ∀ n, R.Statement n → P.Commitment n →
    P.Challenge n → P.Response n →
    P.Challenge n → P.Response n → R.Witness n
  /-- If both conversations accept and challenges differ, the
  extracted witness satisfies the relation -/
  soundness : ∀ n (y : R.Statement n) (t : P.Commitment n)
    (c : P.Challenge n) (z : P.Response n)
    (c' : P.Challenge n) (z' : P.Response n),
    c ≠ c' →
    P.verify n y t c z = true →
    P.verify n y t c' z' = true →
    R.relation n (extract n y t c z c' z') y

/-- **Special honest-verifier zero-knowledge** (Def 19.5 in
Boneh-Shoup): there exists a simulator that, given a statement `y`
and a challenge `c`, produces a commitment-response pair `(t, z)`
such that `(t, c, z)` is accepting and has the same distribution
as a real transcript. -/
structure SigmaProtocol.SpecialHVZK {R : EffectiveRelation}
    (P : SigmaProtocol R) where
  /-- Simulator randomness type -/
  SimRandomness : ℕ → Type
  /-- Simulator randomness is finite -/
  simRandomnessFintype : ∀ n, Fintype (SimRandomness n)
  /-- Simulator randomness is nonempty -/
  simRandomnessNonempty : ∀ n, Nonempty (SimRandomness n)
  /-- The simulator: given statement and challenge, produce
  commitment and response -/
  simulate : ∀ n, R.Statement n → P.Challenge n →
    SimRandomness n → P.Commitment n × P.Response n
  /-- Simulated transcripts are always accepting -/
  sim_accepting : ∀ n (y : R.Statement n) (c : P.Challenge n)
    (s : SimRandomness n),
    let (t, z) := simulate n y c s
    P.verify n y t c z = true
  /-- The simulated distribution equals the real distribution:
  for any `(w, y) ∈ R` and any function `f` on transcripts,
  `E_r[f(commit(w,y,r), respond(w,y,r,c))]
    = E_s[f(simulate(y,c,s))]`.

  This captures that the two distributions are identical. -/
  sim_distribution : ∀ n (w : R.Witness n) (y : R.Statement n)
    (c : P.Challenge n),
    R.relation n w y →
    ∀ (f : P.Commitment n × P.Response n → ℝ),
    Cslib.Probability.uniformExpect (P.ProverRandomness n)
      (fun r => f (P.commit n w y r, P.respond n w y r c)) =
    Cslib.Probability.uniformExpect (SimRandomness n)
      (fun s => f (simulate n y c s))
  /-- The simulator's commitment marginal is uniform: for any statement
  `y` and challenge `c`, the map `s ↦ (simulate y c s).1` pushes the
  uniform distribution on `SimRandomness` to uniform on `Commitment`. -/
  simCommitmentUniform : ∀ n (y : R.Statement n) (c : P.Challenge n)
      (f : P.Commitment n → ℝ),
      Cslib.Probability.uniformExpect (SimRandomness n)
        (fun s => f (simulate n y c s).1) =
      Cslib.Probability.uniformExpect (P.Commitment n) f

end
