/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.SecurityGame

@[expose] public section

/-!
# Message Authentication Codes

A **message authentication code (MAC)** allows a party to produce a
short tag on a message such that anyone sharing the secret key can
verify the tag, but no one without the key can forge a valid tag on
a new message.

## Main Definitions

* `MACScheme` — a MAC scheme (Tag, Verify) with efficiency constraint
* `MACScheme.EUF_CMA_Adversary` — existential unforgeability adversary
  (single-query variant)
* `MACScheme.EUF_CMA_Game` — the EUF-CMA security game
* `MACScheme.EUF_CMA_Secure` — security predicate

## Design Notes

We use a single-query adversary model for simplicity: the adversary
queries the tagging oracle on one chosen message and then must forge
a valid tag on a *different* message. This suffices for the PRF → MAC
reduction and can be extended to multi-query later.

The EUF-CMA game is a **search game** (baseline 0, not 1/2).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014], §4.3
* [M. Bellare, J. Kilian, P. Rogaway, *The Security of the Cipher
  Block Chaining Message Authentication Code*][BKR2000]
-/

/-- A **message authentication code scheme** parameterized by the
security parameter.

- `Key n` — the type of secret keys at security level `n`
- `Message n` — the type of messages
- `Tag n` — the type of authentication tags
-/
structure MACScheme where
  /-- Key type at security level n -/
  Key : ℕ → Type
  /-- Message type -/
  Message : ℕ → Type
  /-- Tag type -/
  Tag : ℕ → Type
  /-- Key type is finite (for sampling) -/
  keyFintype : ∀ n, Fintype (Key n)
  /-- Key type is nonempty -/
  keyNonempty : ∀ n, Nonempty (Key n)
  /-- The tagging function -/
  tag : (n : ℕ) → Key n → Message n → Tag n
  /-- The verification function -/
  verify : (n : ℕ) → Key n → Message n → Tag n → Bool
  /-- The tag and verify algorithms are efficiently (poly-time) computable. -/
  efficient : Prop

/-! ### Correctness -/

/-- A MAC scheme is **correct** if verification always accepts honestly
generated tags. -/
def MACScheme.Correct (M : MACScheme) : Prop :=
  ∀ (n : ℕ) (k : M.Key n) (m : M.Message n),
    M.verify n k m (M.tag n k m) = true

/-! ### EUF-CMA Security -/

/-- An **EUF-CMA adversary** for a MAC scheme (single-query variant).

The adversary operates in two phases:
1. `query` — choose a message to query the tagging oracle on
2. `forge` — given the tag on the queried message, produce a forgery
   `(m*, t*)` where `m*` must differ from the queried message -/
structure MACScheme.EUF_CMA_Adversary (M : MACScheme) where
  /-- Phase 1: choose a message to query -/
  query : (n : ℕ) → M.Message n
  /-- Phase 2: given the tag on `query`, produce a forgery attempt -/
  forge : (n : ℕ) → M.Tag n → M.Message n × M.Tag n

/-- The **EUF-CMA security game** for a MAC scheme.

The advantage is `E_k[1[A forges]]`, where the adversary must produce
a valid tag on a message different from its single oracle query.

This is a **search game** with baseline 0. -/
noncomputable def MACScheme.EUF_CMA_Game (M : MACScheme)
    [∀ n, DecidableEq (M.Message n)] :
    SecurityGame (MACScheme.EUF_CMA_Adversary M) where
  advantage A n :=
    letI := M.keyFintype n; letI := M.keyNonempty n
    Cslib.Probability.uniformExpect (M.Key n) (fun k =>
      let m_query := A.query n
      let t_query := M.tag n k m_query
      let (m_forge, t_forge) := A.forge n t_query
      Cslib.Probability.boolToReal
        (decide (m_forge ≠ m_query) &&
         M.verify n k m_forge t_forge))

/-- A MAC scheme is **EUF-CMA secure** if the EUF-CMA game is secure
against all adversaries. -/
def MACScheme.EUF_CMA_Secure (M : MACScheme)
    [∀ n, DecidableEq (M.Message n)] : Prop :=
  M.EUF_CMA_Game.Secure

/-- A MAC scheme is **EUF-CMA secure against** a class of adversaries. -/
def MACScheme.EUF_CMA_SecureAgainst (M : MACScheme)
    [∀ n, DecidableEq (M.Message n)]
    (Admissible : MACScheme.EUF_CMA_Adversary M → Prop) : Prop :=
  M.EUF_CMA_Game.SecureAgainst Admissible

end
