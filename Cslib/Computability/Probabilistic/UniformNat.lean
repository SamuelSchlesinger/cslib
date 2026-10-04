/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.UniformNat
public import Cslib.Tactic.PPT

/-!
# Sampling bounded indices in strict polynomial time

The samplers of `Cslib.Languages.Probabilistic.UniformNat` are strict PPT: each uses a fixed
number of fair bits, and both binary decoding and the unary result are charged. The dyadic range is
at most `2 * (bound + 1)`, so the unary result remains polynomially bounded.
-/

@[expose] public section

namespace Cslib.Probability

/-- Saturating binary decoding has a polynomial-time unary implementation on all input words. -/
theorem isPolyTime_boundedBinaryValue : IsPolyTime (pairEncoding unaryEncoding wordEncoding)
    (fun input => unaryEncoding (boundedBinaryValue input.1 input.2)) := by
  let advance (state : ℕ × ℕ) (bit : Bool) :=
    (state.1, min state.1 (2 * state.2 + bit.toNat))
  have hstep : IsPolyTime (pairEncoding (pairEncoding unaryEncoding unaryEncoding) boolEncoding)
      (fun input => pairEncoding unaryEncoding unaryEncoding (advance input.1 input.2)) := by
    have hbit : IsPolyTime boolEncoding (fun bit => unaryEncoding bit.toNat) := by
      convert (isPolyTime_input boolEncoding).filter id using 1
      funext bit
      cases bit <;> rfl
    unfold advance
    polytime
  have hinput : IsPolyTime (pairEncoding unaryEncoding wordEncoding)
      (fun input => input.2) := by polytime
  have hinitial : IsPolyTime (pairEncoding unaryEncoding wordEncoding)
      (fun input => pairEncoding unaryEncoding unaryEncoding (input.1, 0)) := by polytime
  have hfold := hinput.foldl_spec hinitial hstep
    (fun input _ state => state.1 = input.1 ∧ state.2 ≤ input.1)
    (by simp) (by intro input consumed state bit _ h; simp [advance, h.1])
    (size := fun n => 3 * n + 1) (by fun_prop)
    (by
      intro input consumed state _ h
      simp [length_pairEncoding, unaryEncoding, wordEncoding]
      lia)
  have hstate (bound : ℕ) (word : Word) (value : ℕ) :
      word.foldl advance (bound, value) =
        (bound, word.foldl (fun value bit => min bound (2 * value + bit.toNat)) value) := by
    induction word generalizing value with
    | nil => rfl
    | cons bit word ih => simpa only [List.foldl_cons, advance] using ih _
  simpa only [hstate, boundedBinaryValue] using hfold.1.snd

/-- Decode efficiently available binary data under an efficiently available unary cap. -/
theorem IsPolyTime.boundedBinaryValue {α : Type} {input : α ↪ Word}
    {bound : α → ℕ} {word : α → Word}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hword : IsPolyTime input word) :
    IsPolyTime input (fun a => unaryEncoding
      (Cslib.Probability.boundedBinaryValue (bound a) (word a))) :=
  isPolyTime_boundedBinaryValue.comp_encoded (hbound.pair hword)

attribute [aesop safe apply (rule_sets := [PolyTime])] IsPolyTime.boundedBinaryValue

/-- The next power of two has an efficient unary implementation; its exponential expression
does not license an exponentially long output. The proved linear bound supplies the cap. -/
theorem IsPolyTime.dyadicSize {α : Type} {input : α ↪ Word} {bound : α → ℕ}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a))) :
    IsPolyTime input (fun a => unaryEncoding (Cslib.Probability.dyadicSize (bound a))) := by
  simp only [dyadicSize_eq_boundedBinaryValue]
  polytime

attribute [program_certificate] IsPolyTime.dyadicSize

-- Also recognize the expanded power-of-two expression in explicitly unfolded client programs.
attribute [aesop safe apply (rule_sets := [PolyTime])] IsPolyTime.dyadicSize

/-- Decode the first coordinate of a rectangular grid with a dyadic row width. -/
theorem IsPolyTime.div_dyadicSize {α : Type} {input : α ↪ Word} {index bound : α → ℕ}
    (hindex : IsPolyTime input (fun a => unaryEncoding (index a)))
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a))) :
    IsPolyTime input (fun a => unaryEncoding
      (index a / Cslib.Probability.dyadicSize (bound a))) := by
  unfold Cslib.Probability.dyadicSize
  exact hindex.unary_div_pow_two
    (hbound.unary_log2.unary_add (isPolyTime_const input (unaryEncoding 1)))

/-- Decode the second coordinate of a rectangular grid with a dyadic row width. -/
theorem IsPolyTime.mod_dyadicSize {α : Type} {input : α ↪ Word} {index bound : α → ℕ}
    (hindex : IsPolyTime input (fun a => unaryEncoding (index a)))
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a))) :
    IsPolyTime input (fun a => unaryEncoding
      (index a % Cslib.Probability.dyadicSize (bound a))) := by
  simpa only [Nat.mod_eq_sub_mul_div, Nat.mul_comm, unaryEncoding_apply] using
    hindex.unary_sub ((hindex.div_dyadicSize hbound).unary_mul hbound.dyadicSize)

attribute [program_certificate] IsPolyTime.div_dyadicSize IsPolyTime.mod_dyadicSize

/-- An efficiently supplied unary bound gives a strict PPT exact dyadic sampler. -/
theorem IsPolyTime.sampleDyadicIndex {α : Type} {input : α ↪ Word} {bound : α → ℕ}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a))) :
    IsPPTOn input unaryEncoding (fun a => Cslib.Probability.sampleDyadicIndex (bound a)) := by
  unfold Cslib.Probability.sampleDyadicIndex
  ppt

/-- Efficiently supplied unary parameters give a strict PPT dyadic coin. -/
theorem IsPolyTime.sampleDyadicCoin {α : Type} {input : α ↪ Word} {bound numerator : α → ℕ}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a)))
    (hnumerator : IsPolyTime input (fun a => unaryEncoding (numerator a))) :
    IsPPTOn input boolEncoding
      (fun a => Cslib.Probability.sampleDyadicCoin (bound a) (numerator a)) := by
  unfold Cslib.Probability.sampleDyadicCoin
  ppt

/-- An efficiently supplied unary bound gives a uniform PPT index sampler. -/
theorem IsPolyTime.sampleBoundedIndex {α : Type} {input : α ↪ Word} {bound : α → ℕ}
    (hbound : IsPolyTime input (fun a => unaryEncoding (bound a))) :
    IsPPTOn input unaryEncoding (fun a => Cslib.Probability.sampleBoundedIndex (bound a)) := by
  have hdecode := isPolyTime_boundedBinaryValue
  unfold Cslib.Probability.sampleBoundedIndex
  ppt

-- Select the actual sampler before unification. Their implementations are deliberately similar,
-- but unfolding one while trying to certify the other needlessly expands arithmetic and encodings.
attribute [program_certificate]
  IsPolyTime.sampleBoundedIndex IsPolyTime.sampleDyadicIndex IsPolyTime.sampleDyadicCoin

end Cslib.Probability
