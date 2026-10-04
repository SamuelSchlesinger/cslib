/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.List
public import Cslib.Computability.Probabilistic.Composition

/-!
# Efficient case analysis over a fixed finite type

A computed finite tag may select among certified branches, each retaining the original input.
The number of cases is fixed independently of the input. This supports ordinary finite control
and transition tables without assigning a unit cost to arbitrary functions on infinite types.
-/

@[expose] public section

namespace Cslib.Probability

/-- Encode a fixed finite type by unary ranks. The enumeration is chosen once, independently
of every runtime input. No efficient enumeration of a growing type is asserted. -/
noncomputable def finiteEncoding (α : Type) [Finite α] : α ↪ Word := by
  let _ := Fintype.ofFinite α
  exact {
    toFun := fun a => unaryEncoding (Fintype.equivFin α a).val
    inj' := fun _ _ h => (Fintype.equivFin α).injective
      (Fin.ext (unaryEncoding.injective h)) }

/-- Finite tags have a fixed size bound, even when used inside unbounded data structures. -/
theorem length_finiteEncoding_lt {α : Type} [Finite α] (a : α) :
    (finiteEncoding α a).length < Nat.card α := by
  let _ := Fintype.ofFinite α
  simp [finiteEncoding, Nat.card_eq_fintype_card]

private theorem select_eq {Tag Value : Type*} [DecidableEq Tag] (tags : List Tag)
    (tag : Tag) (branch : Tag → Value) (fallback : Value) (h : tag ∈ tags) :
    tags.foldr (fun candidate rest => if tag = candidate then branch candidate else rest)
      fallback = branch tag := by
  induction tags with
  | nil => simp at h
  | cons candidate tags ih =>
    by_cases heq : tag = candidate
    · simp [heq]
    · simp only [List.foldr_cons, heq, ↓reduceIte]
      exact ih (List.mem_cons.mp h |>.resolve_left heq)

/-- A fixed finite tag can select a certified deterministic branch with captured input. -/
theorem IsPolyTime.finite_cases {α Tag : Type} [Finite Tag]
    {input : α → Word} {tagEncoding : Tag ↪ Word} {tag : α → Tag}
    {branch : Tag → α → Word}
    (htag : IsPolyTime input (fun a => tagEncoding (tag a)))
    (hbranch : ∀ choice, IsPolyTime input (branch choice)) :
    IsPolyTime input (fun a => branch (tag a) a) := by
  classical
  let _ := Fintype.ofFinite Tag
  have hcondition (choice : Tag) : IsPolyTime input (fun a => [decide (tag a = choice)]) := by
    simpa only [beq_eq_decide, tagEncoding.injective.eq_iff] using
      htag.beq (isPolyTime_const input (tagEncoding choice))
  have hselect (tags : List Tag) : IsPolyTime input (fun a =>
      tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest) []) := by
    induction tags with
    | nil => exact isPolyTime_const input []
    | cons choice tags ih => exact (hcondition choice).ite (hbranch choice) ih
  convert hselect (Finset.univ.toList : List Tag) using 1
  funext a
  exact (select_eq _ (tag a) (fun choice => branch choice a) [] (by simp)).symm

/-- Every function on a fixed finite encoded domain is polynomial time. The chosen finite table
and its output words are part of the one fixed machine, independently of its runtime input. -/
theorem isPolyTime_of_finite {α : Type} [Finite α] (input : α ↪ Word) (f : α → Word) :
    IsPolyTime input f :=
  (isPolyTime_input input).finite_cases (tag := id) (branch := fun choice _ => f choice)
    (fun choice => isPolyTime_const input (f choice))

/-- Apply a fixed function to an efficiently computed finite value. Its complete output encoding
is charged; the function may be any fixed table on that finite domain. -/
theorem IsPolyTime.finite_map {α Tag : Type} [Finite Tag]
    {input : α → Word} {tagEncoding : Tag ↪ Word} {tag : α → Tag}
    (htag : IsPolyTime input (fun a => tagEncoding (tag a))) (f : Tag → Word) :
    IsPolyTime input (fun a => f (tag a)) :=
  (isPolyTime_of_finite tagEncoding f).comp_encoded htag

/-- Finite case analysis also selects among certified probabilistic programs, retaining the
original input for the chosen branch. -/
theorem IsPPTOn.finite_cases {α β Tag : Type} [Finite Tag]
    {input : α ↪ Word} {output : β ↪ Word} {tagEncoding : Tag ↪ Word} {tag : α → Tag}
    {branch : Tag → α → ProbComp β}
    (htag : IsPolyTime input (fun a => tagEncoding (tag a)))
    (hbranch : ∀ choice, IsPPTOn input output (branch choice)) :
    IsPPTOn input output (fun a => branch (tag a) a) := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    have hzero : IsPPTOn input wordEncoding (fun _ => pure ([] : Word)) :=
      (isPolyTime_const input []).isPPTOn
    obtain ⟨k, states, machine, c, d, _⟩ := hzero
    exact ⟨k, states, machine, c, d, fun a => isEmptyElim (tag a)⟩
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hcondition (choice : Tag) :
        IsPolyTime input (fun a => [decide (tag a = choice)]) := by
      simpa only [beq_eq_decide, tagEncoding.injective.eq_iff] using
        htag.beq (isPolyTime_const input (tagEncoding choice))
    have hselect (tags : List Tag) : IsPPTOn input output (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih => exact IsPPTOn.ite (hcondition choice) (hbranch choice) ih
    convert hselect (Finset.univ.toList : List Tag) using 1
    funext a
    exact (select_eq _ (tag a) (fun choice => branch choice a) (branch fallback a) (by simp)).symm

end Cslib.Probability
