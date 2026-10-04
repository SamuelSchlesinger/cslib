/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.BitString
public import Cslib.Languages.Probabilistic.LinearHash
public import Cslib.Tactic.PPT

/-!
# Polynomial-time binary linear hashing

The hash seed is a flat, row-major Boolean matrix. Hashing reads its rows and folds the
coordinatewise AND with the input using XOR. The certificates for `LinearHash.wordHash` and
`LinearHash.extract` are uniform in the input length and requested output length, and also cover
short seed tapes. The family and its laws are in `Cslib.Probability.LinearHash`.
-/

@[expose] public section

namespace Cslib.Probability.LinearHash

open Cslib.Probability.PMF

/-- Hashing efficiently available words has a uniform polynomial-time certificate. -/
theorem isPolyTime_wordHash {α : Type} {encode : α ↪ Word}
    {count : α → ℕ} {seed input : α → Word}
    (hcount : IsPolyTime encode (fun a => unaryEncoding (count a)))
    (hseed : IsPolyTime encode seed) (hinput : IsPolyTime encode input) :
    IsPolyTime encode (fun a => wordHash (count a) (seed a) (input a)) := by
  unfold wordHash
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] isPolyTime_wordHash

/-- The complete seeded extractor is PPT, including all sampling and the revealed seed. -/
theorem isPPTOn_extract {α : Type} {encode : α ↪ Word} {count : α → ℕ} {input : α → Word}
    (hcount : IsPolyTime encode (fun a => unaryEncoding (count a)))
    (hinput : IsPolyTime encode input) :
    IsPPTOn encode wordEncoding (fun a => extract (count a) (input a)) := by
  unfold extract
  ppt

attribute [program_certificate] isPPTOn_extract

end Cslib.Probability.LinearHash
