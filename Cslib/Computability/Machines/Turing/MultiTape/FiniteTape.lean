/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Data.BiTape
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Finite representations of native work tapes

`BiTape` stores the nonblank contents around its current head. `Represents` relates
that finite data to an ordinary `Cfg` tape and its integer head position. The action law uses the
same optional write and signed move as `Action.workTapes`, including writing a blank and moving
through negative positions.
-/

@[expose] public section

namespace Cslib.Turing.BiTape

variable {Symbol : Type*}

/-- Apply the work-tape component of a native multi-tape action. -/
def step (tape : BiTape Symbol) (action : Option (Option Symbol) × SignType) : BiTape Symbol :=
  let written := action.1.elim tape tape.write
  match action.2 with
  | .neg => written.moveLeft
  | .zero => written
  | .pos => written.moveRight

/-- The finite representation agrees with the native tape at every displacement from its head. -/
def Represents (tape : BiTape Symbol) (contents : ℤ → Option Symbol) (head : ℤ) : Prop :=
  ∀ position, tape.read position = contents (head + position)

/-- Blank finite storage represents the native initial work tape. -/
theorem represents_nil (head : ℤ) : (nil : BiTape Symbol).Represents (fun _ => none) head := by
  intro position
  simp

/-- Related tapes present the same symbol to the machine's transition table. -/
theorem Represents.head {tape : BiTape Symbol} {contents : ℤ → Option Symbol} {head : ℤ}
    (h : tape.Represents contents head) : tape.head = contents head := by
  simpa using h 0

/-- Finite tape updates realize precisely the native write and movement, with no restriction
on the head position or on blank gaps within the stored contents. -/
theorem Represents.step {tape : BiTape Symbol} {contents : ℤ → Option Symbol} {head : ℤ}
    (h : tape.Represents contents head) (action : Option (Option Symbol) × SignType) :
    (tape.step action).Represents
      (action.1.elim contents (fun symbol => Function.update contents head symbol))
      (head + action.2) := by
  unfold Represents at h
  intro position
  rcases action with ⟨write, move⟩
  cases write with
  | none =>
    cases move <;> simp [BiTape.step, read_moveLeft, read_moveRight, h,
      sub_eq_add_neg, add_left_comm, add_comm]
  | some symbol =>
    cases move <;>
      simp only [BiTape.step, Option.elim_some, read_moveLeft, read_moveRight, read_write,
        SignType.cast]
    all_goals
      simp only [Function.update_apply]
      split_ifs <;> first | rfl | lia | (rw [h]; congr 1; lia)

/-- A work-tape action increases the finite representation by at most one cell. -/
theorem spaceUsed_step_le (tape : BiTape Symbol) (action : Option (Option Symbol) × SignType) :
    (tape.step action).spaceUsed ≤ tape.spaceUsed + 1 := by
  rcases action with ⟨write, move⟩
  cases write <;> cases move <;>
    simp only [step, Option.elim_none, Option.elim_some]
  all_goals first
    | exact spaceUsed_move _ .left
    | exact spaceUsed_move _ .right
    | simp

end Cslib.Turing.BiTape
