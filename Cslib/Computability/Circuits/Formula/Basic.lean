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
one parent — there is no fan-out sharing. This means every formula is a tree (not a DAG),
and its size is an upper bound on the number of distinct sub-computations.

## Design notes

The `Formula` type itself is basis-agnostic — it is parameterized by an arbitrary operation
type `Op` without requiring a `Basis` instance. This keeps the structural operations (`map`,
`size`, `depth`, etc.) independent of evaluation semantics.

Arity enforcement happens at evaluation time: `Formula.eval` uses the `Decidable` instance
on `Arity.admits` to check whether each gate's children count matches its declared arity.
Gates with mismatched arity evaluate to `false`. For well-formed formulas (e.g., those built
via the smart constructors in `Formula.Std`), this check always succeeds.

## Main definitions

- `Formula` — inductive type of Boolean formulas over variables `Var` and gates `Op`
- `Formula.eval` — evaluate a formula under a variable assignment (requires `[Basis Op]`)
- `Formula.map` — rename variables by applying a function to every leaf
- `Formula.ind` — custom induction principle with membership-based hypothesis

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

namespace Cslib.Circuits

/-- A Boolean formula over variables of type `Var` and gate operations of type `Op`.

Formulas are trees: each gate takes a list of sub-formulas as children. The type
does not enforce arity constraints — any operation can be applied to any number of
children. Arity is checked dynamically during `eval`. -/
inductive Formula (Var : Type*) (Op : Type*) where
  /-- A variable leaf. -/
  | var : Var → Formula Var Op
  /-- A gate applied to a list of sub-formula children. -/
  | gate : Op → List (Formula Var Op) → Formula Var Op

namespace Formula

variable {Var Var' : Type*} {Op : Type*}

/-- Evaluate a formula under a variable assignment.

Variables are looked up directly. At each gate, children are evaluated recursively and
the resulting list is passed to `Basis.eval` if the arity check succeeds (via the
`Decidable` instance on `Arity.admits`). If the children count does not match the
operation's declared arity, the gate evaluates to `false`. -/
@[simp, scoped grind =]
def eval [Basis Op] (assignment : Var → Bool) : Formula Var Op → Bool
  | .var v => assignment v
  | .gate op children =>
    let bs := children.map (eval assignment)
    if h : (Basis.arity op).admits bs.length then
      Basis.eval op bs h
    else
      false

/-- Rename variables in a formula by applying `f` to every variable leaf.
Gate structure and operations are preserved; only the `var` nodes change. -/
@[scoped grind =]
def map (f : Var → Var') : Formula Var Op → Formula Var' Op
  | .var v => .var (f v)
  | .gate op children => .gate op (children.map (Formula.map f))

/-- Custom induction principle for `Formula` that provides `∀ c ∈ children, motive c`
as the induction hypothesis for the `gate` case, rather than Lean's default structural
induction on the nested `List`. Use with `induction f using Formula.ind`. -/
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
