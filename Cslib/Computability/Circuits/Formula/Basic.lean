/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Circuits.Basis

@[expose] public section

/-! # Boolean Formulas

A Boolean formula is a tree-structured expression built from variables and gates drawn
from a `Basis`. Unlike circuits, formulas require every gate output to feed into exactly
one parent — there is no fan-out sharing.

## Main definitions

- `Formula` — inductive type of Boolean formulas
- `Formula.eval` — evaluate a formula given a variable assignment
- `Formula.map` — rename variables

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

namespace Cslib.Circuits

/-- A Boolean formula over variables of type `Var` and gate operations of type `Op`.
Formulas are trees: each gate takes a list of sub-formulas as children. -/
inductive Formula (Var : Type*) (Op : Type*) where
  /-- A variable leaf. -/
  | var : Var → Formula Var Op
  /-- A gate applied to a list of sub-formula children. -/
  | gate : Op → List (Formula Var Op) → Formula Var Op

namespace Formula

variable {Var Var' : Type*} {Op : Type*}

/-- Evaluate a formula given a variable assignment and a `Basis` for the gate operations.
At each gate, the arity is checked via the `Decidable` instance on `Arity.admits`;
if the children count does not match, the gate evaluates to `false`. -/
@[simp, scoped grind =]
def eval [Basis Op] (assignment : Var → Bool) : Formula Var Op → Bool
  | .var v => assignment v
  | .gate op children =>
    let bs := children.map (eval assignment)
    if h : (Basis.arity op).admits bs.length then
      Basis.eval op bs h
    else
      false

/-- Rename variables in a formula by applying `f` to every variable leaf. -/
@[scoped grind =]
def map (f : Var → Var') : Formula Var Op → Formula Var' Op
  | .var v => .var (f v)
  | .gate op children => .gate op (children.map (Formula.map f))

/-- Custom induction principle for `Formula` that provides `∀ c ∈ children, motive c`
as the induction hypothesis for the `gate` case. Use with `induction f using Formula.ind`. -/
@[elab_as_elim]
def ind {motive : Formula Var Op → Prop}
    (hvar : ∀ v, motive (.var v))
    (hgate : ∀ op children, (∀ c ∈ children, motive c) → motive (.gate op children))
    : ∀ f, motive f
  | .var v => hvar v
  | .gate op children => hgate op children fun c hc =>
      have : sizeOf c < 1 + sizeOf op + sizeOf children :=
        Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem hc) (Nat.le_add_left _ _)
      ind hvar hgate c
termination_by f => sizeOf f

end Formula

end Cslib.Circuits
