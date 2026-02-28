/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.SecurityGame

@[expose] public section

/-!
# Commitment Schemes

A **commitment scheme** allows a party to commit to a value while
keeping it hidden, and later reveal the committed value. It satisfies
two security properties:

- **Hiding**: the commitment reveals nothing about the committed value
- **Binding**: the committer cannot change the committed value

Commitment schemes are fundamental building blocks for zero-knowledge
proofs, secure computation, and many other cryptographic protocols.

## Main Definitions

* `CommitmentScheme` — a commitment scheme (Commit, Open)
* `CommitmentScheme.Hiding` — computational hiding property
* `CommitmentScheme.Binding` — computational binding property

## Design Notes

We model commitment as a two-phase process: `commit` produces a
commitment and an opening (decommitment), and `verify` checks that
a claimed value matches the commitment.

## References

* [O. Goldreich, *Foundations of Cryptography, Vol. 1*][Goldreich2001]
* [M. Blum, *Coin Flipping by Telephone*][Blum1981]
-/

/-- A **commitment scheme** parameterized by the security parameter.

- `Message n` — the type of messages that can be committed
- `Commitment n` — the type of commitments
- `Opening n` — the decommitment information
- `Randomness n` — randomness used in commitment
-/
structure CommitmentScheme where
  /-- Message type at security level n -/
  Message : ℕ → Type
  /-- Commitment type -/
  Commitment : ℕ → Type
  /-- Opening (decommitment) type -/
  Opening : ℕ → Type
  /-- Randomness for commitment -/
  Randomness : ℕ → Type
  /-- Create a commitment: given message and randomness, produce
  commitment and opening -/
  commit : (n : ℕ) → Message n → Randomness n →
    Commitment n × Opening n
  /-- Verify an opening: check that the opening matches the
  commitment for the claimed message -/
  verify : (n : ℕ) → Commitment n → Message n → Opening n → Bool

/-! ### Correctness -/

/-- A commitment scheme is **correct** if verification always accepts
honestly generated commitments. -/
def CommitmentScheme.Correct (C : CommitmentScheme) : Prop :=
  ∀ (n : ℕ) (m : C.Message n) (r : C.Randomness n),
    let (com, opening) := C.commit n m r
    C.verify n com m opening = true

/-! ### Security: Hiding -/

/-- A **hiding adversary** tries to determine which of two messages
was committed. -/
structure CommitmentScheme.HidingAdversary (C : CommitmentScheme) where
  /-- Adversary state -/
  State : ℕ → Type
  /-- Phase 1: choose two messages -/
  choose : (n : ℕ) → C.Message n × C.Message n × State n
  /-- Phase 2: given a commitment, guess which message was committed -/
  guess : (n : ℕ) → C.Commitment n → State n → Bool

/-- The **hiding game**: the advantage of an adversary is
`|Pr[A guesses correctly] - 1/2|`. -/
def CommitmentScheme.HidingGame (C : CommitmentScheme) :
    SecurityGame (CommitmentScheme.HidingAdversary C) where
  advantage _A _n := 0  -- Placeholder

/-- A commitment scheme is **(computationally) hiding** if the hiding
game is secure. -/
def CommitmentScheme.Hiding (C : CommitmentScheme) : Prop :=
  C.HidingGame.Secure

/-! ### Security: Binding -/

/-- A **binding adversary** tries to open a commitment to two different
messages. -/
structure CommitmentScheme.BindingAdversary (C : CommitmentScheme) where
  /-- Given the security parameter, produce a commitment that can be
  opened to two different messages. Returns (commitment, msg1,
  opening1, msg2, opening2). -/
  forge : (n : ℕ) → C.Commitment n × C.Message n × C.Opening n ×
    C.Message n × C.Opening n

/-- The **binding game**: the adversary wins if it opens a commitment
to two different messages. -/
def CommitmentScheme.BindingGame (C : CommitmentScheme)
    [∀ n, DecidableEq (C.Message n)] :
    SecurityGame (CommitmentScheme.BindingAdversary C) where
  advantage A n :=
    let (com, m₁, o₁, m₂, o₂) := A.forge n
    if m₁ ≠ m₂ ∧ C.verify n com m₁ o₁ = true ∧
       C.verify n com m₂ o₂ = true
    then 1 else 0

/-- A commitment scheme is **(computationally) binding** if the binding
game is secure. -/
def CommitmentScheme.Binding (C : CommitmentScheme)
    [∀ n, DecidableEq (C.Message n)] : Prop :=
  (C.BindingGame).Secure

end
