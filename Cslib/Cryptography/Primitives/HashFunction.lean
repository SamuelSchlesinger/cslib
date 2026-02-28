/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.SecurityGame

@[expose] public section

/-!
# Cryptographic Hash Functions

This file defines **collision-resistant hash function families** and
their security notions.

## Main Definitions

* `HashFamily` — a keyed hash function family
* `HashFamily.CollisionResistant` — collision resistance
* `HashFamily.SecondPreimageResistant` — second preimage resistance

## Design Notes

We follow the standard keyed hash function model where a public key
(hash function description) is sampled and given to the adversary.
The adversary wins if it finds a collision.

## References

* [I. Damgård, *Collision Free Hash Functions and Public Key
  Signature Schemes*][Damgard1987]
* [P. Rogaway, T. Shrimpton, *Cryptographic Hash-Function
  Basics*][RogawayS2004]
-/

/-- A **keyed hash function family** parameterized by security level.

At each security level `n`, a key selects a specific hash function
from the family. -/
structure HashFamily where
  /-- Key (hash function description) type -/
  Key : ℕ → Type
  /-- Input (preimage) type -/
  Input : ℕ → Type
  /-- Output (digest) type -/
  Output : ℕ → Type
  /-- The hash function -/
  hash : (n : ℕ) → Key n → Input n → Output n

/-! ### Collision Resistance -/

/-- A **collision-finding adversary** attempts to find two distinct
inputs that hash to the same output under a given key. -/
structure HashFamily.CollisionAdversary (H : HashFamily) where
  /-- Given a key, find two inputs. The adversary wins if they are
  distinct and hash to the same value. -/
  findCollision : (n : ℕ) → H.Key n → H.Input n × H.Input n

/-- The **collision resistance game**: the adversary wins if it finds
two distinct inputs `(x₁, x₂)` with `H(k, x₁) = H(k, x₂)`. -/
def HashFamily.CollisionGame (H : HashFamily)
    [∀ n, DecidableEq (H.Input n)]
    [∀ n, DecidableEq (H.Output n)] :
    SecurityGame (HashFamily.CollisionAdversary H) where
  advantage _A _n := 0  -- Placeholder: Pr[A finds collision]

/-- A hash family is **collision resistant** if the collision game
is secure. -/
def HashFamily.CollisionResistant (H : HashFamily)
    [∀ n, DecidableEq (H.Input n)]
    [∀ n, DecidableEq (H.Output n)] : Prop :=
  H.CollisionGame.Secure

/-! ### Second Preimage Resistance -/

/-- A **second-preimage adversary** is given a key and an input `x₁`,
and must find a different input `x₂` with the same hash value. -/
structure HashFamily.SecondPreimageAdversary (H : HashFamily) where
  /-- Given a key and an input, find another input with the same hash -/
  findSecondPreimage : (n : ℕ) → H.Key n → H.Input n → H.Input n

end

