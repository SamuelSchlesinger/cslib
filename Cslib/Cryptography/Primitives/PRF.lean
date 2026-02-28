/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.Foundations.SecurityGame

@[expose] public section

/-!
# Pseudorandom Functions

A **pseudorandom function (PRF)** is a keyed function family that is
computationally indistinguishable from a truly random function when
the key is chosen at random.

PRFs are central to symmetric-key cryptography: they are used to
construct encryption schemes, MACs, and other primitives. The
GGM construction builds a PRF from any pseudorandom generator.

## Main Definitions

* `PRF` — a pseudorandom function family
* `PRF.Secure` — security via oracle indistinguishability

## Design Notes

We model PRFs as keyed function families `f : Key n → Input n → Output n`.
Security says that no efficient oracle adversary can distinguish
`f(k, ·)` (for random `k`) from a truly random function.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random
  Functions*][GGM1986]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

/-- A **pseudorandom function family** indexed by the security parameter.

At each security level `n`, `eval n k x` evaluates the PRF on key `k`
and input `x`. -/
structure PRF where
  /-- Key type at security level n -/
  Key : ℕ → Type
  /-- Input type -/
  Input : ℕ → Type
  /-- Output type -/
  Output : ℕ → Type
  /-- The keyed function -/
  eval : (n : ℕ) → Key n → Input n → Output n

/-- A **PRF adversary** has oracle access to either the PRF (keyed with
a random key) or a truly random function, and must distinguish between
the two cases.

The adversary makes a sequence of queries and then outputs a decision
bit. We model the oracle as a function from inputs to outputs. -/
structure PRF.OracleAdversary (F : PRF) where
  /-- Given oracle access, produce a decision -/
  run : (n : ℕ) → (F.Input n → F.Output n) → Bool

/-- The **PRF security game**: the adversary's advantage is the gap
between its acceptance probability when given the real PRF oracle
versus a random function oracle. -/
def PRF.SecurityGame (F : PRF) :
    SecurityGame (PRF.OracleAdversary F) where
  advantage _A _n := 0  -- Placeholder: |Pr[A^{f_k}=1] - Pr[A^{RF}=1]|

/-- A PRF is **secure** if its security game is secure. -/
def PRF.Secure (F : PRF) : Prop := F.SecurityGame.Secure

/-- A **pseudorandom permutation (PRP)** is a PRF where each keyed
instance is a bijection. PRPs model block ciphers. -/
structure PRP extends PRF where
  /-- Each keyed instance is a bijection -/
  bij : ∀ (n : ℕ) (k : toPRF.Key n),
    Function.Bijective (toPRF.eval n k)

end
