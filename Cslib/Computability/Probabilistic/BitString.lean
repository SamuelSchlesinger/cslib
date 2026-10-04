/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.WordBits
public import Cslib.Tactic.PolyTime

/-!
# Polynomial-time word operations

Polynomial-time certificates for the word operations of `Cslib.Probability.WordBits`: fixed-width
views, matrix rows, XOR and Boolean dot products. They use ordinary word and collection
combinators and also cover malformed or short input tapes. Self-delimiting padding gives bounded
words a common length without identifying distinct words.
-/

@[expose] public section

namespace Cslib.Probability

/-- Pad a self-delimiting word to `2 * bound + 1` bits when its length is at most `bound`.
Words outside the bound remain distinguishable, rather than being truncated. -/
def padWord (bound : ℕ) (word : Word) : Word :=
  pairEncoding wordEncoding wordEncoding
    (word, List.replicate (2 * (bound - word.length)) false)

/-- Padding never identifies distinct words, even when their bounds differ. -/
theorem word_eq_of_padWord_eq {bound bound' : ℕ} {word word' : Word}
    (h : padWord bound word = padWord bound' word') : word = word' :=
  congrArg Prod.fst ((pairEncoding wordEncoding wordEncoding).injective h)

/-- Every word within the supplied bound has the same padded length. -/
theorem length_padWord {bound : ℕ} {word : Word} (h : word.length ≤ bound) :
    (padWord bound word).length = 2 * bound + 1 := by
  simp only [padWord, length_pairEncoding, wordEncoding, Function.Embedding.refl_apply,
    List.length_replicate]
  lia

/-- Concatenating bounded, padded words has a length determined solely by their count. -/
theorem length_flatten_padWord (bound : ℕ) (words : List Word)
    (hbound : ∀ word ∈ words, word.length ≤ bound) :
    ((words.map (padWord bound)).flatten).length = words.length * (2 * bound + 1) := by
  induction words with
  | nil => simp
  | cons word rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hbound
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      length_padWord hbound.1, ih hbound.2, List.length_cons]
    lia

/-- Self-delimiting padding uses the shared word encoder and unary arithmetic. -/
theorem isPolyTime_padWord {α : Type} {encode : α ↪ Word}
    {bound : α → ℕ} {word : α → Word}
    (hbound : IsPolyTime encode (fun a => unaryEncoding (bound a)))
    (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => padWord (bound a) (word a)) := by
  unfold padWord
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] isPolyTime_padWord

/-- Padding embeds bounded words into a fixed finite bitstring space. -/
theorem word_eq_of_paddedBits_eq {bound : ℕ} {left right : Word}
    (hleft : left.length ≤ bound) (hright : right.length ≤ bound)
    (h : wordBits (2 * bound + 1) (padWord bound left) =
      wordBits (2 * bound + 1) (padWord bound right)) : left = right := by
  apply word_eq_of_padWord_eq
  simpa only [ofFn_wordBits (length_padWord hleft), ofFn_wordBits (length_padWord hright)] using
    congrArg List.ofFn h

/-- Truncating or padding a word to a supplied unary width is uniformly polynomial time. -/
theorem isPolyTime_wordBits {α : Type} {input : α ↪ Word} {n : α → ℕ} {word : α → Word}
    (hn : IsPolyTime input (fun a => unaryEncoding (n a))) (hword : IsPolyTime input word) :
    IsPolyTime input (fun a => List.ofFn (wordBits (n a) (word a))) := by
  simp_rw [ofFn_wordBits_eq_range]
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] isPolyTime_wordBits

/-- Matrix parsing charges for the dimension, every runtime index, and the complete output. -/
theorem isPolyTime_maskRows {α : Type} {encode : α ↪ Word}
    {count dimension : α → ℕ} {word : α → Word}
    (hcount : IsPolyTime encode (fun a => unaryEncoding (count a)))
    (hdimension : IsPolyTime encode (fun a => unaryEncoding (dimension a)))
    (hword : IsPolyTime encode word) :
    IsPolyTime encode (fun a => listEncoding wordEncoding
      (maskRows (count a) (dimension a) (word a))) := by
  unfold maskRows maskRow
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] isPolyTime_maskRows

/-- Bitstring addition is uniformly efficient, including when the dimension varies
with the input. Its certificate uses the ordinary `zipWith` combinator. -/
theorem isPolyTime_addMasks {α : Type} {encode : α → Word} {n : α → ℕ}
    {left right : (a : α) → BitString (n a)}
    (hleft : IsPolyTime encode (fun a => List.ofFn (left a)))
    (hright : IsPolyTime encode (fun a => List.ofFn (right a))) :
    IsPolyTime encode (fun a => List.ofFn (left a + right a)) := by
  simpa only [ofFn_add] using hleft.zipWith hright Bool.xor

/-- Variable-width XOR uses only ordinary mapping, runtime indexing, and Boolean folds. -/
theorem isPolyTime_xorWords {α : Type} {input : α ↪ Word}
    {width : α → ℕ} {words : α → List Word}
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (hwords : IsPolyTime input (fun a => listEncoding wordEncoding (words a))) :
    IsPolyTime input (fun a => xorWords (width a) (words a)) := by
  unfold xorWords
  polytime

attribute [program_certificate] isPolyTime_xorWords

/-- The dot product is uniformly efficient through word combinators. -/
theorem isPolyTime_dotProduct {α : Type} {encode : α → Word} {n : α → ℕ}
    {left right : (a : α) → BitString (n a)}
    (hleft : IsPolyTime encode (fun a => List.ofFn (left a)))
    (hright : IsPolyTime encode (fun a => List.ofFn (right a))) :
    IsPolyTime encode (fun a => [left a ⬝ᵥ right a]) := by
  simpa only [dotProduct_eq_foldl] using
    (hleft.zipWith hright Bool.and).foldl_bool Bool.xor false

end Cslib.Probability

namespace Cslib.ProbComp

open Probability

end Cslib.ProbComp
