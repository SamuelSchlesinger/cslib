/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Data.BitString
public import Cslib.Probability.BitString
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Matrix.Mul

/-!
# Binary words as bitstrings

`wordBits n` views a word as `n` coordinates, padding missing bits with `false`. A flat word is
read as a row-major matrix of masks, words are combined by coordinatewise XOR, and Boolean dot
products are folds over the coordinates. A uniformly random word of the right length gives a
uniform bitstring, and its rows are independent and uniform.

The Goldreich–Levin decoder and binary linear hashing share these representations.
-/

@[expose] public section

namespace Cslib.Probability

/-- View a word as `n` coordinates, using false for missing bits. Valid lengths lose no data. -/
def wordBits (n : ℕ) (word : Word) : BitString n := fun i => word[i.val]?.getD false

/-- A finite bitstring survives the word representation unchanged. -/
@[simp] theorem wordBits_ofFn {n : ℕ} (bits : BitString n) :
    wordBits n (List.ofFn bits) = bits := by
  funext i
  simp [wordBits]

/-- A correctly sized word survives the finite-coordinate representation unchanged. -/
theorem ofFn_wordBits {n : ℕ} {word : Word} (hlen : word.length = n) :
    List.ofFn (wordBits n word) = word := by
  subst n
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [wordBits, List.getElem?_eq_getElem hi']

/-- The fixed-width representation reads a bounded range of indices, padding missing bits. -/
theorem ofFn_wordBits_eq_range (n : ℕ) (word : Word) :
    List.ofFn (wordBits n word) = (List.range n).map (fun i => word[i]?.getD false) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [wordBits]

/-- The row-major bijection between a flat bitstring and a matrix of masks. -/
def maskEquiv (k n : ℕ) : BitString (k * n) ≃ (Fin k → BitString n) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin k) (Fin n) Bool)

/-- Packing fixed-width rows is ordinary list concatenation. -/
theorem ofFn_maskEquiv_symm {count width : ℕ} (rows : Fin count → BitString width) :
    List.ofFn ((maskEquiv count width).symm rows) =
      (List.ofFn (fun i => List.ofFn (rows i))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h := congrArg (fun values => values i j) ((maskEquiv count width).apply_symm_apply rows)
  change (maskEquiv count width).symm rows (finProdFinEquiv (i, j)) = rows i j at h
  convert h using 1
  apply congrArg ((maskEquiv count width).symm rows)
  apply Fin.ext
  simp only [finProdFinEquiv_apply_val]
  lia

/-- Concatenated fixed-width rows recover the same finite tuple, including empty rows. -/
theorem wordBits_flatten_ofFn {count width : ℕ} (rows : Fin count → BitString width) :
    wordBits (count * width) ((List.ofFn rows).map List.ofFn).flatten =
      (maskEquiv count width).symm rows := by
  simp only [List.map_ofFn, Function.comp_def, ← ofFn_maskEquiv_symm, wordBits_ofFn]

/-- Interpret a flat sampled word as a matrix of masks. -/
def masksFromWord (k n : ℕ) (word : Word) : Fin k → BitString n :=
  maskEquiv k n (wordBits (k * n) word)

/-- Read one row of the sampled mask tape, padding missing bits with false. -/
def maskRow (dimension row : ℕ) (word : Word) : Word :=
  (List.range dimension).map (fun column => word[row * dimension + column]?.getD false)

/-- Parsing a row agrees with the finite matrix representation, even on short tapes. -/
theorem maskRow_eq_ofFn {count : ℕ} (dimension : ℕ) (row : Fin count) (word : Word) :
    maskRow dimension row.val word = List.ofFn (masksFromWord count dimension word row) := by
  apply List.ext_getElem (by simp [maskRow])
  intro column hleft hright
  simp [maskRow, masksFromWord, maskEquiv, wordBits, Nat.mul_comm, Nat.add_comm]

/-- Read the mask tape as an ordinary list of rows, padding missing bits with false. -/
def maskRows (count dimension : ℕ) (word : Word) : List Word :=
  (List.range count).map (fun row => maskRow dimension row word)

/-- Row parsing always returns the requested number of fixed-width words. -/
@[simp] theorem length_maskRows (count dimension : ℕ) (word : Word) :
    (maskRows count dimension word).length = count := by
  simp only [maskRows, List.length_map, List.length_range]

/-- Every parsed row has its declared width, including rows padded from short tapes. -/
theorem length_of_mem_maskRows {count dimension : ℕ} {word row : Word}
    (hrow : row ∈ maskRows count dimension word) : row.length = dimension := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hrow
  simp only [maskRow, List.length_map, List.length_range]

/-- The nested-list program is exactly the finite matrix interpretation, also on short tapes. -/
theorem maskRows_eq_ofFn (count dimension : ℕ) (word : Word) :
    maskRows count dimension word =
      List.ofFn (fun row => List.ofFn (masksFromWord count dimension word row)) := by
  apply List.ext_getElem (by simp [maskRows])
  intro row hleft hright
  simpa only [maskRows, List.getElem_map, List.getElem_range, List.getElem_ofFn] using
    maskRow_eq_ofFn dimension ⟨row, by simpa using hright⟩ word

/-- Reading fewer rows takes a prefix of the same matrix, including on short tapes. -/
theorem masksFromWord_prefix {count rows dimension : ℕ} (h : rows ≤ count) (word : Word) :
    masksFromWord rows dimension word = masksFromWord count dimension word ∘ Fin.castLE h := by
  ext row column
  simp [masksFromWord, maskEquiv, wordBits]

/-- Adding finite masks is exactly coordinatewise XOR of their word representations. -/
theorem ofFn_add {n : ℕ} (left right : BitString n) :
    List.ofFn (left + right) = (List.ofFn left).zipWith Bool.xor (List.ofFn right) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [List.getElem_zipWith, Bool.add_eq_xor]

/-- XOR a collection at the supplied width, treating missing bits as false. -/
def xorWords (width : ℕ) (words : List Word) : Word :=
  (List.range width).map fun bit =>
    (words.map (fun word => word[bit]?.getD false)).foldl Bool.xor false

/-- XOR returns exactly the declared width, even for an empty collection or short words. -/
@[simp] theorem length_xorWords (width : ℕ) (words : List Word) :
    (xorWords width words).length = width := by simp [xorWords]

/-- The word program agrees exactly with the sum of the finite bitstring representations. -/
theorem xorWords_ofFn {count : ℕ} (width : ℕ) (words : Fin count → Word) :
    xorWords width (List.ofFn words) = List.ofFn (∑ i, wordBits width (words i)) := by
  have hparity (word : Word) : word.foldl Bool.xor false = word.sum := by
    simp [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false]
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [xorWords, hparity, wordBits, List.map_ofFn, List.sum_ofFn, Finset.sum_apply]

/-- A Boolean dot product is a pointwise AND followed by a parity fold on words. -/
theorem dotProduct_eq_foldl {n : ℕ} (left right : BitString n) :
    left ⬝ᵥ right = ((List.ofFn left).zipWith Bool.and (List.ofFn right)).foldl Bool.xor false := by
  have hzip : (List.ofFn left).zipWith Bool.and (List.ofFn right) =
      List.ofFn (fun i => left i * right i) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp [List.getElem_zipWith, Bool.mul_eq_and]
  rw [hzip, dotProduct, ← List.sum_ofFn]
  simp [List.sum_eq_foldl, Bool.add_eq_xor, Bool.zero_eq_false]

/-- Uniform words become exactly uniform finite bitstrings. -/
theorem uniformBits_wordBits (n : ℕ) :
    (uniformBits n).map (wordBits n) = PMF.uniformOfFintype (BitString n) := by
  simp only [uniformBits, PMF.map_comp, Function.comp_def, wordBits_ofFn]
  exact PMF.map_id _

/-- A flat tape of `k * n` uniform bits supplies exactly `k` independent uniform masks. -/
theorem uniformBits_masksFromWord (k n : ℕ) :
    (uniformBits (k * n)).map (masksFromWord k n) =
      PMF.uniformOfFintype (Fin k → BitString n) := by
  change (uniformBits (k * n)).map ((maskEquiv k n) ∘ wordBits (k * n)) = _
  rw [← PMF.map_comp, uniformBits_wordBits]
  exact PMF.uniformOfFintype_map_equiv (maskEquiv k n)

end Cslib.Probability
