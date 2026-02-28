/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.SecurityGame

@[expose] public section

/-!
# Digital Signature Schemes

A **digital signature scheme** allows a signer to produce a signature
on a message that can be verified by anyone with the signer's public
key, but cannot be forged without the secret key.

## Main Definitions

* `SignatureScheme` — a digital signature scheme (KeyGen, Sign, Verify)
* `EUF_CMA` — existential unforgeability under chosen-message attack

## Design Notes

We model signature schemes with abstract types for keys, messages,
signatures, and randomness. The security notion EUF-CMA says that
no efficient adversary, even after seeing signatures on chosen messages,
can produce a valid signature on a new message.

## References

* [S. Goldwasser, S. Micali, R. Rivest, *A Digital Signature Scheme
  Secure Against Adaptive Chosen-Message Attacks*][GMR1988]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

/-- A **digital signature scheme** parameterized by the security parameter.

- `PublicKey n` — verification key
- `SecretKey n` — signing key
- `Message n` — message type
- `Signature n` — signature type
-/
structure SignatureScheme where
  /-- Public (verification) key type -/
  PublicKey : ℕ → Type
  /-- Secret (signing) key type -/
  SecretKey : ℕ → Type
  /-- Message type -/
  Message : ℕ → Type
  /-- Signature type -/
  Signature : ℕ → Type
  /-- Randomness for signing -/
  Randomness : ℕ → Type
  /-- Sign a message with the secret key -/
  sign : (n : ℕ) → SecretKey n → Message n → Randomness n →
    Signature n
  /-- Verify a signature with the public key -/
  verify : (n : ℕ) → PublicKey n → Message n → Signature n → Bool

/-! ### Correctness -/

/-- A signature scheme is **correct** if honestly generated signatures
always verify. -/
def SignatureScheme.Correct (S : SignatureScheme)
    (keyPair : (n : ℕ) → S.PublicKey n × S.SecretKey n) : Prop :=
  ∀ (n : ℕ) (m : S.Message n) (r : S.Randomness n),
    let (pk, sk) := keyPair n
    S.verify n pk m (S.sign n sk m r) = true

/-! ### EUF-CMA Security -/

/-- An **EUF-CMA adversary** for a signature scheme has access to a
signing oracle and must produce a valid signature on a message it
never queried the oracle for.

The adversary is modeled as producing a forgery attempt directly;
the oracle interaction is captured by the `queries` field recording
the messages the adversary saw signed. -/
structure EUF_CMA_Adversary (S : SignatureScheme) where
  /-- Queries: the messages the adversary asks the signing oracle
  to sign (modeled as a finite list). -/
  queries : (n : ℕ) → List (S.Message n)
  /-- The forgery attempt: a message and signature. -/
  forge : (n : ℕ) →
    (S.Message n → S.Randomness n → S.Signature n) →
    S.Message n × S.Signature n

/-- The **EUF-CMA security game** for a signature scheme.

The adversary wins if it produces a valid signature on a message
not in its query list. -/
def SignatureScheme.EUF_CMA_Game (S : SignatureScheme)
    [∀ n, DecidableEq (S.Message n)] :
    SecurityGame (EUF_CMA_Adversary S) where
  advantage _A _n := 0  -- Placeholder: Pr[A forges]

/-- A signature scheme is **EUF-CMA secure** if the EUF-CMA game
is secure. -/
def SignatureScheme.EUF_CMA (S : SignatureScheme)
    [∀ n, DecidableEq (S.Message n)] : Prop :=
  S.EUF_CMA_Game.Secure

end
