/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Foundations.Data.StackTape
public import Mathlib.Algebra.Group.End
public import Mathlib.Computability.TuringMachine.Tape
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Algebra.Order.Group.Nat

@[expose] public section

/-!
# BiTape: Bidirectionally infinite TM tape representation using StackTape

This file defines `BiTape`, a tape representation for Turing machines
in the form of an `List` of `Option` values,
with the additional property that the list cannot end with `none`.

## Design

Note that Mathlib has a `Tape` type, but it requires the alphabet type to be inhabited,
and considers the ends of the tape to be filled with default values.

This design requires the tape elements to be `Option` values, and ensures that
`List`s of the base alphabet, rendered directly onto the tape by mapping over `some`,
will not collide.

## Main definitions

* `BiTape`: A tape with a head symbol and left/right contents stored as `StackTape`
* `BiTape.move`: Move the tape head left or right
* `BiTape.write`: Write a symbol at the current head position
* `BiTape.space_used`: The space used by the tape
-/

namespace Turing

/--
A structure for bidirectionally-infinite Turing machine tapes
that eventually take on blank `none` values
-/
@[ext]
structure BiTape (Symbol : Type) where
  /-- The symbol currently under the tape head -/
  head : Option Symbol
  /-- The contents to the left of the head -/
  left : StackTape Symbol
  /-- The contents to the right of the head -/
  right : StackTape Symbol

namespace BiTape

variable {Symbol : Type}

/-- The empty `BiTape` -/
def nil : BiTape Symbol := ⟨none, ∅, ∅⟩

instance : Inhabited (BiTape Symbol) where
  default := nil

instance : EmptyCollection (BiTape Symbol) :=
  ⟨nil⟩

@[simp]
lemma empty_eq_nil : (∅ : BiTape Symbol) = nil := rfl

/--
Given a `List` of `Symbol`s, construct a `BiTape` by mapping the list to `some` elements
and laying them out to the right side,
with the head under the first element of the list if it exists.
-/
def mk₁ (l : List Symbol) : BiTape Symbol :=
  match l with
  | [] => ∅
  | h :: t => { head := some h, left := ∅, right := StackTape.map_some t }

section Move

/--
Move the head left by shifting the left StackTape under the head.
-/
def move_left (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

/--
Move the head right by shifting the right StackTape under the head.
-/
def move_right (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

/--
Move the head to the left or right, shifting the tape underneath it.
-/
def move (t : BiTape Symbol) : Dir → BiTape Symbol
  | .left => t.move_left
  | .right => t.move_right

/--
Optionally perform a `move`, or do nothing if `none`.
-/
def optionMove : BiTape Symbol → Option Dir → BiTape Symbol
  | t, none => t
  | t, some d => t.move d

@[simp]
lemma move_left_move_right (t : BiTape Symbol) : t.move_left.move_right = t := by
  simp [move_right, move_left]

@[simp]
lemma move_right_move_left (t : BiTape Symbol) : t.move_right.move_left = t := by
  simp [move_left, move_right]

@[simp]
lemma move_left_nil : (nil : BiTape Symbol).move_left = nil := rfl

@[simp]
lemma move_right_nil : (nil : BiTape Symbol).move_right = nil := rfl

@[simp]
lemma optionMove_nil (m : Option Dir) : (nil : BiTape Symbol).optionMove m = nil := by
  cases m with
  | none => rfl
  | some d => cases d <;> rfl

/-- The right-move equivalence, with inverse `move_left`. -/
def moveEquiv : Equiv.Perm (BiTape Symbol) where
  toFun := move_right
  invFun := move_left
  left_inv := move_right_move_left
  right_inv := move_left_move_right

/-- Move the head by an integer amount of cells: positive values move right, negative
values move left. -/
def move_int (t : BiTape Symbol) (delta : ℤ) : BiTape Symbol :=
  (moveEquiv ^ delta) t

@[simp]
lemma move_int_zero_eq_id (t : BiTape Symbol) :
    t.move_int 0 = t := by
  simp [move_int]

@[simp]
lemma move_int_one_eq_move_right (t : BiTape Symbol) :
    t.move_int 1 = t.move_right := by
  simp [move_int, moveEquiv]

@[simp]
lemma move_int_neg_one_eq_move_left (t : BiTape Symbol) :
    t.move_int (-1) = t.move_left := by
  simp [move_int, moveEquiv]

@[simp]
lemma move_int_move_right (t : BiTape Symbol) (delta : ℤ) :
    (t.move_int delta).move_right = t.move_int (delta + 1) := by
  change moveEquiv ((moveEquiv ^ delta) t) = (moveEquiv ^ (delta + 1)) t
  rw [← Equiv.Perm.mul_apply, ← zpow_one_add, add_comm]

@[simp]
lemma move_int_move_left (t : BiTape Symbol) (delta : ℤ) :
    (t.move_int delta).move_left = t.move_int (delta - 1) := by
  change (moveEquiv (Symbol := Symbol))⁻¹ ((moveEquiv ^ delta) t) =
    (moveEquiv ^ (delta - 1)) t
  rw [← Equiv.Perm.mul_apply, ← zpow_neg_one, ← zpow_add]
  rw [show -1 + delta = delta - 1 by omega]

@[simp]
lemma move_int_move_int (t : BiTape Symbol) (delta₁ delta₂ : ℤ) :
    (t.move_int delta₁).move_int delta₂ = t.move_int (delta₁ + delta₂) := by
  change (moveEquiv ^ delta₂) ((moveEquiv ^ delta₁) t) =
    (moveEquiv ^ (delta₁ + delta₂)) t
  rw [← Equiv.Perm.mul_apply, ← zpow_add, add_comm]

@[simp]
lemma move_int_nil (delta : ℤ) : (nil : BiTape Symbol).move_int delta = nil := by
  cases delta with
  | ofNat n =>
      induction n with
      | zero => simp
      | succ n ih =>
          rw [show Int.ofNat (n + 1) = (Int.ofNat n : ℤ) + 1 by
            simp [Int.natCast_succ]]
          rw [← move_int_move_right, ih, move_right_nil]
  | negSucc n =>
      induction n with
      | zero => simp
      | succ n ih =>
          rw [show Int.negSucc (n + 1) = Int.negSucc n - 1 by
            rw [Int.negSucc_eq, Int.negSucc_eq]
            omega]
          rw [← move_int_move_left, ih, move_left_nil]

end Move

/--
Write a value under the head of the `BiTape`.
-/
def write (t : BiTape Symbol) (a : Option Symbol) : BiTape Symbol := { t with head := a }

@[simp]
lemma write_head (t : BiTape Symbol) : t.write t.head = t := rfl

/--
The space used by a `BiTape` is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the `BiTape`.
-/
@[scoped grind]
def space_used (t : BiTape Symbol) : ℕ := 1 + t.left.length + t.right.length

@[simp, grind =]
lemma space_used_write (t : BiTape Symbol) (a : Option Symbol) :
    (t.write a).space_used = t.space_used := by rfl

lemma space_used_mk₁ (l : List Symbol) :
    (mk₁ l).space_used = max 1 l.length := by
  cases l with
  | nil => simp [mk₁, space_used, nil, StackTape.length_nil]
  | cons h t => simp [mk₁, space_used, StackTape.length_nil, StackTape.length_map_some]; omega

lemma space_used_move (t : BiTape Symbol) (d : Dir) :
    (t.move d).space_used ≤ t.space_used + 1 := by
  cases d <;> grind [move_left, move_right, move,
    space_used, StackTape.length_tail_le, StackTape.length_cons_le]

end BiTape

end Turing
