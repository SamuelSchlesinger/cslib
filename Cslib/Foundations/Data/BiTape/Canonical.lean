/-
Copyright (c) 2026 Christian Reitwiessner, Sam Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Sam Schlesinger
-/

module

public import Cslib.Foundations.Data.BiTape
public import Mathlib.Data.List.TakeDrop

@[expose] public section

/-!
# Canonical input-tape shapes for `BiTape`

The canonical `BiTape` configuration for an input list `s` with the head at integer position
`p` relative to the start of the input. Used by the multi-tape Turing machine head-position
bound to characterise tape `0`'s shape along a trace.

* `canonicalInputTapeNat s n` — the shape when the head sits at natural-number position `n`.
* `canonicalInputTape s p` — the integer-indexed version, with `p = -1` representing "one
  cell left of the input" and `p ≥ 0` delegating to `canonicalInputTapeNat`.

The basic move-right / move-left / head / zero / nil lemmas collected here are what the
Turing-machine invariant uses to step the head back and forth within `[-1, s.length]`.
-/

namespace Turing

open StackTape

variable {Symbol : Type}

/--
The canonical `BiTape` configuration for an input tape containing `s`, with the head at
natural number position `n` (i.e. `0` is the start of the input).

For `n < s.length`, the head reads `some s[n]`; for `n ≥ s.length`, the head reads
`none` and the tape has `s.reverse` on the left.
-/
def canonicalInputTapeNat (s : List Symbol) (n : ℕ) : BiTape Symbol where
  head := s[n]?
  left := StackTape.map_some (s.take n).reverse
  right := StackTape.map_some (s.drop (n + 1))

/--
The canonical `BiTape` shape of the input tape at integer position `p`, with `p = -1`
representing "one cell left of the input" (a blank cell with `s` to the right) and
`p ≥ 0` delegating to `canonicalInputTapeNat`.

The head-position bound theorem shows that traces from `initCfg s` only produce tapes
matching `canonicalInputTape s p` for `-1 ≤ p ≤ s.length`.
-/
def canonicalInputTape (s : List Symbol) (p : ℤ) : BiTape Symbol :=
  if 0 ≤ p then canonicalInputTapeNat s p.toNat
  else ⟨none, ∅, StackTape.map_some s⟩

@[simp]
lemma canonicalInputTape_ofNat (s : List Symbol) (n : ℕ) :
    canonicalInputTape s (n : ℤ) = canonicalInputTapeNat s n := by
  simp [canonicalInputTape]

@[simp]
lemma canonicalInputTape_neg_one (s : List Symbol) :
    canonicalInputTape s (-1) = ⟨none, ∅, StackTape.map_some s⟩ := rfl

@[simp]
lemma canonicalInputTapeNat_zero (s : List Symbol) :
    canonicalInputTapeNat s 0 = BiTape.mk₁ s := by
  cases s <;> simp [canonicalInputTapeNat, BiTape.mk₁, BiTape.nil]

@[simp]
lemma canonicalInputTape_zero (s : List Symbol) :
    canonicalInputTape s 0 = BiTape.mk₁ s :=
  (canonicalInputTape_ofNat s 0).trans (canonicalInputTapeNat_zero s)

/-- One-step move-right on the canonical configuration at natural-number position `n`,
when still within the input region. -/
lemma canonicalInputTapeNat_move_right {s : List Symbol} {n : ℕ} (h : n < s.length) :
    (canonicalInputTapeNat s n).move_right = canonicalInputTapeNat s (n + 1) := by
  simp only [canonicalInputTapeNat, BiTape.move_right]
  have h_take : s.take (n + 1) = s.take n ++ [s[n]] := (List.take_concat_get' s n h).symm
  have h_get : s[n]? = some s[n] := List.getElem?_eq_getElem h
  ext
  · -- head: (map_some (s.drop (n+1))).head = s[n+1]?
    rw [StackTape.head_map_some, List.head?_drop]
  · -- left: cons s[n]? (map_some (s.take n).reverse) = map_some (s.take (n+1)).reverse
    rw [h_get, h_take, List.reverse_append, List.reverse_singleton, List.singleton_append,
      StackTape.map_some_cons]
  · -- right: (map_some (s.drop (n+1))).tail = map_some (s.drop (n+2))
    rw [StackTape.tail_map_some, List.tail_drop]

/-- One-step move-left on the canonical configuration at natural-number position `n + 1`,
when still within the input region. -/
lemma canonicalInputTapeNat_move_left {s : List Symbol} {n : ℕ} (h : n < s.length) :
    (canonicalInputTapeNat s (n + 1)).move_left = canonicalInputTapeNat s n := by
  simp only [canonicalInputTapeNat, BiTape.move_left]
  have h_take : s.take (n + 1) = s.take n ++ [s[n]] := (List.take_concat_get' s n h).symm
  have h_get : s[n]? = some s[n] := List.getElem?_eq_getElem h
  ext
  · -- head: (map_some (s.take (n+1)).reverse).head = s[n]?
    rw [h_take, List.reverse_append, List.reverse_singleton, List.singleton_append,
      StackTape.head_map_some_cons, h_get]
  · -- left: (map_some (s.take (n+1)).reverse).tail = map_some (s.take n).reverse
    rw [StackTape.tail_map_some, h_take, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.tail_cons]
  · -- right: cons s[n+1]? (map_some (s.drop (n+1+1))) = map_some (s.drop (n+1))
    -- `cases h_drop : s.drop (n+1)` rewrites `s.drop (n+1)` on the RHS
    cases h_drop : s.drop (n + 1) with
    | nil =>
      have h1 : s.length ≤ n + 1 := List.drop_eq_nil_iff.mp h_drop
      have h_head : s[n + 1]? = none := List.getElem?_eq_none (by omega)
      have h_drop2 : s.drop (n + 1 + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
      rw [h_head, h_drop2]
      rfl
    | cons a rest =>
      have h_head : s[n + 1]? = some a := by
        rw [← List.head?_drop, h_drop]; rfl
      have h_drop2 : s.drop (n + 1 + 1) = rest := by
        rw [← List.tail_drop, h_drop]; rfl
      rw [h_head, h_drop2]
      exact (StackTape.map_some_cons a rest).symm

/-- One-step move-right on the integer-indexed canonical configuration, staying within
`[-1, s.length]`. -/
lemma canonicalInputTape_move_right {s : List Symbol} {p : ℤ}
    (h_lo : -1 ≤ p) (h_hi : p < (s.length : ℤ)) :
    (canonicalInputTape s p).move_right = canonicalInputTape s (p + 1) := by
  by_cases hp_nn : 0 ≤ p
  · simp only [canonicalInputTape, if_pos hp_nn, if_pos (show (0 : ℤ) ≤ p + 1 by omega),
      show (p + 1).toNat = p.toNat + 1 from by omega]
    exact canonicalInputTapeNat_move_right (by omega)
  · obtain rfl : p = -1 := by omega
    rw [show (-1 : ℤ) + 1 = 0 from rfl, canonicalInputTape_neg_one, canonicalInputTape_zero]
    cases s with
    | nil => rfl
    | cons a t =>
      simp [BiTape.mk₁, BiTape.move_right]

/-- One-step move-left on the integer-indexed canonical configuration, staying within
`[0, s.length]` (with the result going to `[-1, s.length - 1]`). -/
lemma canonicalInputTape_move_left {s : List Symbol} {p : ℤ}
    (h_lo : 0 ≤ p) (h_hi : p ≤ (s.length : ℤ)) :
    (canonicalInputTape s p).move_left = canonicalInputTape s (p - 1) := by
  by_cases hp_pos : 0 < p
  · have hp_pred : (p - 1).toNat + 1 = p.toNat := by omega
    simp only [canonicalInputTape, if_pos hp_pos.le, if_pos (show (0 : ℤ) ≤ p - 1 by omega)]
    rw [← hp_pred]
    exact canonicalInputTapeNat_move_left (by omega)
  · obtain rfl : p = 0 := by omega
    rw [show (0 : ℤ) - 1 = -1 from rfl, canonicalInputTape_zero, canonicalInputTape_neg_one]
    cases s with
    | nil => rfl
    | cons a t =>
      simp [BiTape.mk₁, BiTape.move_left]

/-- Characterization of when the head of a canonical configuration is blank (inside the
valid range `[-1, s.length]`). -/
lemma canonicalInputTape_head_eq_none_iff {s : List Symbol} {p : ℤ}
    (h_lo : -1 ≤ p) (h_hi : p ≤ (s.length : ℤ)) :
    (canonicalInputTape s p).head = none ↔ p = -1 ∨ p = s.length := by
  by_cases hp_nn : 0 ≤ p
  · have hp_cast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp_nn
    simp only [canonicalInputTape, if_pos hp_nn, canonicalInputTapeNat,
      List.getElem?_eq_none_iff]
    omega
  · obtain rfl : p = -1 := by omega
    simp

/-- With empty input, every integer position collapses to the empty bi-tape. This makes the
empty-input branch of `HasInputTape.head_position_bounded` trivial: every reachable tape-`0`
configuration is `BiTape.nil`, which equals `canonicalInputTape [] p` for any `p`. -/
lemma canonicalInputTape_nil (p : ℤ) :
    canonicalInputTape ([] : List Symbol) p = BiTape.nil := by
  unfold canonicalInputTape
  split_ifs <;> simp [canonicalInputTapeNat, BiTape.nil]

end Turing
