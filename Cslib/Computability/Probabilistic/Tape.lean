/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Finite
public import Cslib.Computability.Machines.Turing.MultiTape.FiniteTape

/-!
# Polynomial-time operations on finite tape representations

The `StackTape` and `BiTape` representations have list and product encodings. Their
operations inherit computational certificates from the collection API. In particular, simulating
a native tape action charges for the entire stored tape, including blanks between occupied cells.
-/

@[expose] public section

namespace Cslib.Probability

open Cslib.Turing

variable {Symbol : Type} [Finite Symbol]

/-- Encode the finite stored portion of an eventually blank tape. -/
noncomputable def stackTapeEncoding : StackTape Symbol ↪ Word where
  toFun tape := listEncoding (finiteEncoding (Option Symbol)) tape.toList
  inj' := fun _ _ h => StackTape.ext ((listEncoding _).injective h)

@[simp] theorem stackTapeEncoding_apply (tape : StackTape Symbol) :
    stackTapeEncoding tape = listEncoding (finiteEncoding (Option Symbol)) tape.toList := rfl

/-- Encode the current cell and both finite sides of a bidirectional tape. -/
noncomputable def biTapeEncoding : BiTape Symbol ↪ Word where
  toFun tape := pairEncoding (finiteEncoding (Option Symbol))
    (pairEncoding stackTapeEncoding stackTapeEncoding) (tape.head, tape.left, tape.right)
  inj' := by
    intro tape other h
    have heq := (pairEncoding _ _).injective h
    exact BiTape.ext (congrArg Prod.fst heq) (congrArg (Prod.fst ∘ Prod.snd) heq)
      (congrArg (Prod.snd ∘ Prod.snd) heq)

/-- The stack encoding charges a fixed number of bits per stored cell. -/
theorem length_stackTapeEncoding_le (tape : StackTape Symbol) :
    (stackTapeEncoding tape).length ≤ tape.length * (2 * Nat.card (Option Symbol) + 1) :=
  length_listEncoding_le _ (fun symbol _ => (length_finiteEncoding_lt symbol).le)

/-- A tape encoding has length linear in the space used by the tape representation. -/
theorem length_biTapeEncoding_le (tape : BiTape Symbol) :
    (biTapeEncoding tape).length ≤ 4 * (Nat.card (Option Symbol) + 1) * tape.spaceUsed := by
  have hhead := (length_finiteEncoding_lt tape.head).le
  have hleft := length_stackTapeEncoding_le tape.left
  have hright := length_stackTapeEncoding_le tape.right
  simp only [biTapeEncoding, Function.Embedding.coeFn_mk,
    length_pairEncoding, BiTape.spaceUsed]
  nlinarith

variable {α : Type} {input : α → Word}

/-- Reading a stack head includes decoding its first stored cell. -/
theorem IsPolyTime.stack_head {tape : α → StackTape Symbol}
    (h : IsPolyTime input (fun a => stackTapeEncoding (tape a))) :
    IsPolyTime input (fun a => finiteEncoding (Option Symbol) (tape a).head) := by
  convert h.list_headD none using 1
  funext a
  cases hvalues : (tape a).toList <;> simp [StackTape.head, hvalues]

/-- Removing a stack head is an encoded list operation. -/
theorem IsPolyTime.stack_tail {tape : α → StackTape Symbol}
    (h : IsPolyTime input (fun a => stackTapeEncoding (tape a))) :
    IsPolyTime input (fun a => stackTapeEncoding (tape a).tail) := by
  simpa only [stackTapeEncoding_apply, StackTape.tail_toList] using h.list_tail

/-- Prepending a cell preserves the canonical omission of trailing blanks. -/
theorem IsPolyTime.stack_cons {symbol : α → Option Symbol} {tape : α → StackTape Symbol}
    (hsymbol : IsPolyTime input (fun a => finiteEncoding (Option Symbol) (symbol a)))
    (htape : IsPolyTime input (fun a => stackTapeEncoding (tape a))) :
    IsPolyTime input (fun a => stackTapeEncoding (StackTape.cons (symbol a) (tape a))) := by
  apply hsymbol.finite_cases (branch := fun symbol a =>
    stackTapeEncoding (StackTape.cons symbol (tape a)))
  intro symbol
  have hcons := (isPolyTime_const input (finiteEncoding (Option Symbol) symbol)).list_cons htape
  cases symbol with
  | some symbol => exact hcons
  | none =>
    have h := (htape.list_unaryLength.unary_eq (isPolyTime_const input (unaryEncoding 0))).ite
      (isPolyTime_const input []) hcons
    convert h using 1
    funext a
    cases tape a with | mk values h => cases values <;> simp [StackTape.cons]

/-- Construct a bidirectional tape from three efficiently computed components. -/
theorem IsPolyTime.biTape_mk {head : α → Option Symbol} {left right : α → StackTape Symbol}
    (hhead : IsPolyTime input (fun a => finiteEncoding (Option Symbol) (head a)))
    (hleft : IsPolyTime input (fun a => stackTapeEncoding (left a)))
    (hright : IsPolyTime input (fun a => stackTapeEncoding (right a))) :
    IsPolyTime input (fun a => biTapeEncoding ⟨head a, left a, right a⟩) :=
  hhead.pair (hleft.pair hright)

/-- Read the current cell of a computed tape. -/
theorem IsPolyTime.biTape_head {tape : α → BiTape Symbol}
    (h : IsPolyTime input (fun a => biTapeEncoding (tape a))) :
    IsPolyTime input (fun a => finiteEncoding (Option Symbol) (tape a).head) := h.fst

/-- Extract the stored left side of a computed tape. -/
theorem IsPolyTime.biTape_left {tape : α → BiTape Symbol}
    (h : IsPolyTime input (fun a => biTapeEncoding (tape a))) :
    IsPolyTime input (fun a => stackTapeEncoding (tape a).left) := h.snd.fst

/-- Extract the stored right side of a computed tape. -/
theorem IsPolyTime.biTape_right {tape : α → BiTape Symbol}
    (h : IsPolyTime input (fun a => biTapeEncoding (tape a))) :
    IsPolyTime input (fun a => stackTapeEncoding (tape a).right) := h.snd.snd

/-- Move left using `BiTape.moveLeft`. -/
theorem IsPolyTime.biTape_moveLeft {tape : α → BiTape Symbol}
    (h : IsPolyTime input (fun a => biTapeEncoding (tape a))) :
    IsPolyTime input (fun a => biTapeEncoding (tape a).moveLeft) :=
  h.biTape_left.stack_head.biTape_mk h.biTape_left.stack_tail
    (h.biTape_head.stack_cons h.biTape_right)

/-- Move right using `BiTape.moveRight`. -/
theorem IsPolyTime.biTape_moveRight {tape : α → BiTape Symbol}
    (h : IsPolyTime input (fun a => biTapeEncoding (tape a))) :
    IsPolyTime input (fun a => biTapeEncoding (tape a).moveRight) :=
  h.biTape_right.stack_head.biTape_mk (h.biTape_head.stack_cons h.biTape_left)
    h.biTape_right.stack_tail

/-- Write an efficiently computed symbol under the current head. -/
theorem IsPolyTime.biTape_write {tape : α → BiTape Symbol} {symbol : α → Option Symbol}
    (htape : IsPolyTime input (fun a => biTapeEncoding (tape a)))
    (hsymbol : IsPolyTime input (fun a => finiteEncoding (Option Symbol) (symbol a))) :
    IsPolyTime input (fun a => biTapeEncoding ((tape a).write (symbol a))) :=
  hsymbol.biTape_mk htape.biTape_left htape.biTape_right

/-- Each fixed native action has a polynomial-time implementation on the encoded tape. -/
theorem IsPolyTime.biTape_step {tape : α → BiTape Symbol}
    (h : IsPolyTime input (fun a => biTapeEncoding (tape a)))
    (action : Option (Option Symbol) × SignType) :
    IsPolyTime input (fun a => biTapeEncoding ((tape a).step action)) := by
  have hwrite : IsPolyTime input (fun a => biTapeEncoding
      (action.1.elim (tape a) (tape a).write)) := by
    cases action.1 with
    | none => exact h
    | some symbol => exact h.biTape_write (isPolyTime_const input _)
  cases hmove : action.2 with
  | neg => simpa only [BiTape.step, hmove] using hwrite.biTape_moveLeft
  | zero => simpa only [BiTape.step, hmove] using hwrite
  | pos => simpa only [BiTape.step, hmove] using hwrite.biTape_moveRight

/-- Loading an encoded list on a tape uses the same list map and projections as ordinary data. -/
theorem IsPolyTime.biTape_mk₁ {values : α → List Symbol}
    (h : IsPolyTime input (fun a => listEncoding (finiteEncoding Symbol) (values a))) :
    IsPolyTime input (fun a => biTapeEncoding (BiTape.mk₁ (values a))) := by
  have hsome := h.list_map (isPolyTime_of_finite (finiteEncoding Symbol)
    (fun symbol => finiteEncoding (Option Symbol) (some symbol)))
  have hhead := hsome.list_headD none
  have hright : IsPolyTime input (fun a => stackTapeEncoding
      (StackTape.mapSome (values a).tail)) := by
    simpa only [stackTapeEncoding_apply,
      StackTape.mapSome, List.map_tail] using hsome.list_tail
  convert hhead.biTape_mk (isPolyTime_const input (stackTapeEncoding (StackTape.nil :
    StackTape Symbol))) hright using 1
  funext a
  cases values a <;> rfl

end Cslib.Probability
