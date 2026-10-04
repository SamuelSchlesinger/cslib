/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.List

/-!
# Encoded tables over a fixed finite index type

`piEncoding` stores a finite family as an encoded list. The entries themselves can be unbounded
objects, such as words or tapes. Construction, projection and updates reuse the certified list
operations. The index type is fixed independently of the runtime input.
-/

@[expose] public section

namespace Cslib.Probability

/-- Encode a family over a fixed finite type by listing its entries in a fixed order. -/
noncomputable def piEncoding {Index Value : Type} [Fintype Index] (element : Value ↪ Word) :
    (Index → Value) ↪ Word where
  toFun values := listEncoding element
    (List.ofFn (fun i => values ((Fintype.equivFin Index).symm i)))
  inj' := by
    intro values others h
    have heq := List.ofFn_injective ((listEncoding element).injective h)
    funext i
    simpa using congrFun heq (Fintype.equivFin Index i)

/-- The encoded table size is linear in its fixed number of entries and their maximum size. -/
theorem length_piEncoding_le {Index Value : Type} [Fintype Index] (element : Value ↪ Word)
    (values : Index → Value) (bound : ℕ) (h : ∀ i, (element (values i)).length ≤ bound) :
    (piEncoding element values).length ≤ Fintype.card Index * (2 * bound + 1) := by
  simpa [piEncoding] using length_listEncoding_le element
    (values := List.ofFn (fun i => values ((Fintype.equivFin Index).symm i)))
    (fun value hvalue => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hvalue
      exact h _)

/-- A fixed tuple of efficiently computed entries can be written as an encoded list. -/
theorem IsPolyTime.ofFn {α Value : Type} {input : α → Word} {element : Value ↪ Word}
    {count : ℕ} {values : α → Fin count → Value}
    (h : ∀ i, IsPolyTime input (fun a => element (values a i))) :
    IsPolyTime input (fun a => listEncoding element (List.ofFn (values a))) := by
  induction count with
  | zero => simpa using isPolyTime_const input []
  | succ count ih =>
    simpa only [List.ofFn_succ] using (h 0).list_cons
      (ih (values := fun a i => values a i.succ) (fun i => h i.succ))

/-- Construct a table by computing each of its finitely many entries. -/
theorem IsPolyTime.pi {α Index Value : Type} [Fintype Index]
    {input : α → Word} {element : Value ↪ Word} {values : α → Index → Value}
    (h : ∀ i, IsPolyTime input (fun a => element (values a i))) :
    IsPolyTime input (fun a => piEncoding element (values a)) :=
  IsPolyTime.ofFn (fun i => h ((Fintype.equivFin Index).symm i))

/-- Project a fixed entry from an encoded table. Reading and decoding its stored prefix are
included in the complexity certificate. -/
theorem IsPolyTime.pi_apply {α Index Value : Type} [Fintype Index] [Inhabited Value]
    {input : α → Word} {element : Value ↪ Word} {values : α → Index → Value}
    (h : IsPolyTime input (fun a => piEncoding element (values a))) (i : Index) :
    IsPolyTime input (fun a => element (values a i)) := by
  change IsPolyTime input (fun a => listEncoding element
    (List.ofFn (fun j => values a ((Fintype.equivFin Index).symm j)))) at h
  simpa using h.list_getD (isPolyTime_const input (unaryEncoding (Fintype.equivFin Index i).val))
    default

/-- Updating a fixed table entry is efficient, with all preserved entries charged as well. -/
theorem IsPolyTime.pi_update {α Index Value : Type} [Fintype Index] [DecidableEq Index]
    [Inhabited Value] {input : α → Word} {element : Value ↪ Word}
    {values : α → Index → Value} {value : α → Value}
    (hvalues : IsPolyTime input (fun a => piEncoding element (values a)))
    (hvalue : IsPolyTime input (fun a => element (value a))) (i : Index) :
    IsPolyTime input (fun a => piEncoding element (Function.update (values a) i (value a))) := by
  apply IsPolyTime.pi
  intro j
  by_cases h : j = i
  · subst j
    simpa using hvalue
  · simpa [Function.update_of_ne h] using hvalues.pi_apply j

end Cslib.Probability
