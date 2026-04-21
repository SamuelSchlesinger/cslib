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

* `canonicalInputTapeNat s n` — the tape obtained by moving right `n` cells from `mk₁ s`.
* `canonicalInputTape s p` — the tape obtained by moving by integer offset `p` from `mk₁ s`.

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
`none`.
-/
def canonicalInputTapeNat (s : List Symbol) (n : ℕ) : BiTape Symbol :=
  (BiTape.mk₁ s).move_int n

/-- Closed form for canonical natural positions while the head is at most one cell past
the input. This is private because the public API is movement-based. -/
private def canonicalInputTapeNatClosed (s : List Symbol) (n : ℕ) : BiTape Symbol where
  head := s[n]?
  left := StackTape.map_some (s.take n).reverse
  right := StackTape.map_some (s.drop (n + 1))

/--
The canonical `BiTape` shape of the input tape at integer position `p`, obtained by moving
by `p` cells from `BiTape.mk₁ s`.

The head-position bound theorem shows that the input-tape invariant only needs positions
in the range `-1 ≤ p ≤ s.length`.
-/
def canonicalInputTape (s : List Symbol) (p : ℤ) : BiTape Symbol :=
  (BiTape.mk₁ s).move_int p

@[simp]
lemma canonicalInputTape_ofNat (s : List Symbol) (n : ℕ) :
    canonicalInputTape s (n : ℤ) = canonicalInputTapeNat s n := rfl

@[simp]
lemma canonicalInputTape_neg_one (s : List Symbol) :
    canonicalInputTape s (-1) = ⟨none, ∅, StackTape.map_some s⟩ := by
  rw [canonicalInputTape, BiTape.move_int_neg_one_eq_move_left]
  cases s <;> simp [BiTape.mk₁, BiTape.move_left, BiTape.nil]

@[simp]
lemma canonicalInputTapeNat_zero (s : List Symbol) :
    canonicalInputTapeNat s 0 = BiTape.mk₁ s := by
  simp [canonicalInputTapeNat]

@[simp]
lemma canonicalInputTape_zero (s : List Symbol) :
    canonicalInputTape s 0 = BiTape.mk₁ s := by
  simp [canonicalInputTape]

@[simp]
private lemma canonicalInputTapeNatClosed_zero (s : List Symbol) :
    canonicalInputTapeNatClosed s 0 = BiTape.mk₁ s := by
  cases s <;> simp [canonicalInputTapeNatClosed, BiTape.mk₁, BiTape.nil]

/-- One-step move-right on the canonical configuration at natural-number position `n`,
when still within the input region. -/
private lemma canonicalInputTapeNatClosed_move_right {s : List Symbol} {n : ℕ}
    (h : n < s.length) :
    (canonicalInputTapeNatClosed s n).move_right = canonicalInputTapeNatClosed s (n + 1) := by
  simp only [canonicalInputTapeNatClosed, BiTape.move_right]
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

/-- One-step move-right on the canonical configuration at natural-number position `n`. -/
lemma canonicalInputTapeNat_move_right {s : List Symbol} {n : ℕ} :
    (canonicalInputTapeNat s n).move_right = canonicalInputTapeNat s (n + 1) := by
  rw [canonicalInputTapeNat, canonicalInputTapeNat, BiTape.move_int_move_right]
  simp [Int.natCast_succ]

/-- One-step move-left on the canonical configuration at natural-number position `n + 1`. -/
lemma canonicalInputTapeNat_move_left {s : List Symbol} {n : ℕ} :
    (canonicalInputTapeNat s (n + 1)).move_left = canonicalInputTapeNat s n := by
  rw [canonicalInputTapeNat, canonicalInputTapeNat, BiTape.move_int_move_left]
  simp [Int.natCast_succ]

private lemma canonicalInputTapeNat_eq_closed_of_le {s : List Symbol} {n : ℕ}
    (h : n ≤ s.length) :
    canonicalInputTapeNat s n = canonicalInputTapeNatClosed s n := by
  induction n with
  | zero => rw [canonicalInputTapeNat_zero, canonicalInputTapeNatClosed_zero]
  | succ n ih =>
      have hn_le : n ≤ s.length := Nat.le_trans (Nat.le_succ n) h
      have hn_lt : n < s.length := Nat.lt_of_succ_le h
      rw [← canonicalInputTapeNat_move_right, ih hn_le]
      exact canonicalInputTapeNatClosed_move_right hn_lt

/-- One-step move-right on the integer-indexed canonical configuration, staying within
`[-1, s.length]`. -/
lemma canonicalInputTape_move_right {s : List Symbol} {p : ℤ}
    (_h_lo : -1 ≤ p) (_h_hi : p < (s.length : ℤ)) :
    (canonicalInputTape s p).move_right = canonicalInputTape s (p + 1) := by
  simp [canonicalInputTape]

/-- One-step move-left on the integer-indexed canonical configuration, staying within
`[0, s.length]` (with the result going to `[-1, s.length - 1]`). -/
lemma canonicalInputTape_move_left {s : List Symbol} {p : ℤ}
    (_h_lo : 0 ≤ p) (_h_hi : p ≤ (s.length : ℤ)) :
    (canonicalInputTape s p).move_left = canonicalInputTape s (p - 1) := by
  simp [canonicalInputTape]

/-- Characterization of when the head of a canonical configuration is blank (inside the
valid range `[-1, s.length]`). -/
lemma canonicalInputTape_head_eq_none_iff {s : List Symbol} {p : ℤ}
    (h_lo : -1 ≤ p) (h_hi : p ≤ (s.length : ℤ)) :
    (canonicalInputTape s p).head = none ↔ p = -1 ∨ p = s.length := by
  by_cases hp_nn : 0 ≤ p
  · have hp_cast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp_nn
    have hp_le : p.toNat ≤ s.length := by omega
    rw [← hp_cast, canonicalInputTape_ofNat,
      canonicalInputTapeNat_eq_closed_of_le hp_le]
    simp only [canonicalInputTapeNatClosed, List.getElem?_eq_none_iff]
    omega
  · obtain rfl : p = -1 := by omega
    simp

/-- With empty input, every integer position collapses to the empty bi-tape. This makes the
empty-input branch of `HasInputTape.head_position_bounded` trivial: every reachable tape-`0`
configuration is `BiTape.nil`, which equals `canonicalInputTape [] p` for any `p`. -/
lemma canonicalInputTape_nil (p : ℤ) :
    canonicalInputTape ([] : List Symbol) p = BiTape.nil := by
  simp [canonicalInputTape, BiTape.mk₁]

end Turing
