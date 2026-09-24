/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Circuit.Composition
public import Cslib.Computability.Circuit.Dependency

import Mathlib.Tactic.FinCases

/-!
# Restricting Boolean circuits

Partial evaluation of a De Morgan gate after fixing an input can leave a
constant, an existing wire, or a new gate. This module records that choice and
proves the local simplifier correct. Circuit size counts every operation. Constants
stay symbolic during partial evaluation, and a nonconstant output needs no extra
gate to materialize them.

`restrictProgram` constructs a certified restriction. The deletion lemmas identify
omitted gates, and `exists_restricted_circuit` turns the restriction into a circuit
with an exact size bound.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- A Boolean constant or a wire of a partially evaluated program. -/
inductive Residual (n g : ℕ) where
  | constant (value : Bool)
  | wire (wire : Wire n g)
  deriving DecidableEq

/-- Evaluate a residual value in the rebuilt program. -/
def Residual.eval (value : Residual n g) (program : Program signature n g)
    (input : Fin n → Bool) : Bool :=
  match value with
  | .constant b => b
  | .wire w => program.trace interpretation input w

/-- Widen a residual value when a gate is appended. -/
def Residual.castSucc : Residual n g → Residual n (g + 1)
  | .constant b => .constant b
  | .wire w => .wire w.castSucc

@[simp] theorem Residual.eval_castSucc (value : Residual n g)
    (program : Program signature n g) (line : Line signature n g)
    (input : Fin n → Bool) :
    value.castSucc.eval (program.gate line) input = value.eval program input := by
  cases value with
  | constant b => rfl
  | wire w => exact Program.trace_gate_castSucc program line interpretation input w

/-- The result of simplifying a gate: either reuse a value or append a gate. -/
inductive Simplified (n g : ℕ) where
  | reuse (value : Residual n g)
  | gate (line : Line signature n g)

/-- Evaluate a simplification choice. -/
def Simplified.eval (choice : Simplified n g) (program : Program signature n g)
    (input : Fin n → Bool) : Bool :=
  match choice with
  | .reuse residual => residual.eval program input
  | .gate line => line.eval interpretation input (program.eval interpretation input)

/-- Simplify one De Morgan operation applied to residual arguments. -/
def simplify (op : Op) (args : Fin (signature.Arity op) → Residual n g) :
    Simplified n g :=
  match op with
  | .const b => .reuse (.constant b)
  | .not =>
      match args 0 with
      | .constant b => .reuse (.constant (!b))
      | .wire w => .gate ⟨.not, fun _ => w⟩
  | .and =>
      match args 0, args 1 with
      | .constant a, .constant b => .reuse (.constant (a && b))
      | .constant a, .wire w => if a then .reuse (.wire w) else .reuse (.constant false)
      | .wire w, .constant b => if b then .reuse (.wire w) else .reuse (.constant false)
      | .wire w, .wire v => .gate ⟨.and, Fin.cons w (fun _ => v)⟩
  | .or =>
      match args 0, args 1 with
      | .constant a, .constant b => .reuse (.constant (a || b))
      | .constant a, .wire w => if a then .reuse (.constant true) else .reuse (.wire w)
      | .wire w, .constant b => if b then .reuse (.constant true) else .reuse (.wire w)
      | .wire w, .wire v => .gate ⟨.or, Fin.cons w (fun _ => v)⟩

/-- The local simplifier preserves the value of its source operation. -/
theorem simplify_eval (op : Op) (args : Fin (signature.Arity op) → Residual n g)
    (program : Program signature n g) (input : Fin n → Bool) :
    (simplify op args).eval program input =
      interpretation op (fun i => (args i).eval program input) := by
  cases op with
  | const b => simp [simplify, Simplified.eval, Residual.eval, interpretation]
  | not =>
      cases h : args 0 with
      | constant b => cases b <;> simp [simplify, Simplified.eval, Residual.eval,
          interpretation, h]
      | wire w => simp [simplify, Simplified.eval, Residual.eval, Line.eval,
          Program.trace, interpretation, h]
  | and =>
      cases h₀ : args 0 with
      | constant a =>
          cases h₁ : args 1 with
          | constant b => cases a <;> cases b <;>
              simp [simplify, Simplified.eval, Residual.eval, interpretation, h₀, h₁]
          | wire w => cases a <;>
              simp [simplify, Simplified.eval, Residual.eval, interpretation, h₀, h₁]
      | wire w =>
          cases h₁ : args 1 with
          | constant b => cases b <;>
              simp [simplify, Simplified.eval, Residual.eval, interpretation, h₀, h₁]
          | wire v => simp [simplify, Simplified.eval, Residual.eval, Line.eval,
              Program.trace, interpretation, h₀, h₁]
  | or =>
      cases h₀ : args 0 with
      | constant a =>
          cases h₁ : args 1 with
          | constant b => cases a <;> cases b <;>
              simp [simplify, Simplified.eval, Residual.eval, interpretation, h₀, h₁]
          | wire w => cases a <;>
              simp [simplify, Simplified.eval, Residual.eval, interpretation, h₀, h₁]
      | wire w =>
          cases h₁ : args 1 with
          | constant b => cases b <;>
              simp [simplify, Simplified.eval, Residual.eval, interpretation, h₀, h₁]
          | wire v => simp [simplify, Simplified.eval, Residual.eval, Line.eval,
              Program.trace, interpretation, h₀, h₁]

/-- Restrict a program while tracking each deleted gate and the value of every
source wire. -/
structure ProgramRestriction (source : Program signature (n + 1) g)
    (selected : Fin (n + 1)) (fixed : Bool) where
  /-- Number of gates in the residual program. -/
  gateCount : ℕ
  /-- Residual program. -/
  result : Program signature n gateCount
  /-- The residual value of each original wire. -/
  values : Wire (n + 1) g → Residual n gateCount
  /-- Correctness on every source wire. -/
  trace_eq : ∀ input sourceWire,
    (values sourceWire).eval result input =
      source.trace interpretation (Fin.insertNth selected fixed input) sourceWire
  /-- Gates omitted from the residual program. -/
  deleted : Finset (Fin g)
  /-- Every source gate is either retained or deleted. -/
  count_eq : gateCount + deleted.card = g

namespace ProgramRestriction

/-- Restricting an empty program only changes the input map. -/
private def empty (selected : Fin (n + 1)) (fixed : Bool) :
    ProgramRestriction (Program.empty : Program signature (n + 1) 0) selected fixed where
  gateCount := 0
  result := .empty
  values := Fin.insertNth selected (.constant fixed)
    (fun remaining => .wire (Wire.input remaining))
  trace_eq := by
    intro input sourceWire
    let restrictedInput : Fin (n + 1) → Bool :=
      Fin.insertNth selected fixed input
    have htrace (i : Fin (n + 1)) :
        (Program.empty : Program signature (n + 1) 0).trace interpretation
            restrictedInput i = restrictedInput i := by
      simpa [Wire.input] using
        Program.trace_input (Program.empty : Program signature (n + 1) 0)
          interpretation restrictedInput i
    refine Fin.succAboveCases selected ?_ (fun remaining => ?_) sourceWire
    · simp [Residual.eval, htrace, restrictedInput]
    · simp [Residual.eval, htrace, restrictedInput]
  deleted := ∅
  count_eq := rfl

/-- A source gate that simplifies to an existing residual value is deleted. -/
private def reuseLast {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)} {fixed : Bool}
    (prior : ProgramRestriction source selected fixed)
    (line : Line signature (n + 1) g)
    (value : Residual n prior.gateCount)
    (value_eq : ∀ input,
      value.eval prior.result input =
        line.eval interpretation (Fin.insertNth selected fixed input)
          (source.eval interpretation (Fin.insertNth selected fixed input))) :
    ProgramRestriction (source.gate line) selected fixed where
  gateCount := prior.gateCount
  result := prior.result
  values := Fin.lastCases value prior.values
  trace_eq := by
    intro input sourceWire
    refine Fin.lastCases ?_ (fun oldWire => ?_) sourceWire
    · have hgate := Program.trace_gate_last source line interpretation
        (Fin.insertNth selected fixed input)
      simpa [Nat.add_assoc] using (value_eq input).trans hgate.symm
    · simpa only [Fin.lastCases_castSucc, Program.trace_gate_castSucc] using
        prior.trace_eq input oldWire
  deleted := insert (Fin.last g) (prior.deleted.map Fin.castSuccEmb)
  count_eq := by
    have hnot : Fin.last g ∉ prior.deleted.map Fin.castSuccEmb := by simp
    rw [Finset.card_insert_of_notMem hnot, Finset.card_map]
    have := prior.count_eq
    omega

/-- A source gate that remains nontrivial is appended to the residual program. -/
private def keepLast {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)} {fixed : Bool}
    (prior : ProgramRestriction source selected fixed)
    (line : Line signature (n + 1) g)
    (mappedLine : Line signature n prior.gateCount)
    (line_eq : ∀ input,
      mappedLine.eval interpretation input (prior.result.eval interpretation input) =
        line.eval interpretation (Fin.insertNth selected fixed input)
          (source.eval interpretation (Fin.insertNth selected fixed input))) :
    ProgramRestriction (source.gate line) selected fixed where
  gateCount := prior.gateCount + 1
  result := prior.result.gate mappedLine
  values := Fin.lastCases (.wire (Fin.last (n + prior.gateCount)))
    (fun oldWire => (prior.values oldWire).castSucc)
  trace_eq := by
    intro input sourceWire
    refine Fin.lastCases ?_ (fun oldWire => ?_) sourceWire
    · simpa [Residual.eval, Program.trace_gate_last, Nat.add_assoc] using
        line_eq input
    · simpa only [Fin.lastCases_castSucc, Residual.eval_castSucc,
        Program.trace_gate_castSucc] using prior.trace_eq input oldWire
  deleted := prior.deleted.map Fin.castSuccEmb
  count_eq := by
    rw [Finset.card_map]
    have := prior.count_eq
    omega

/-- Apply one local simplification, also reusing any semantically equivalent
constant or existing wire. -/
private noncomputable def step {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)} {fixed : Bool}
    (prior : ProgramRestriction source selected fixed)
    (line : Line signature (n + 1) g)
    (choice : Simplified n prior.gateCount)
    (hline : ∀ input,
      choice.eval prior.result input =
        line.eval interpretation (Fin.insertNth selected fixed input)
          (source.eval interpretation (Fin.insertNth selected fixed input))) :
    ProgramRestriction (source.gate line) selected fixed := by
  cases choice with
  | reuse value => exact prior.reuseLast line value hline
  | gate mappedLine =>
      classical
      by_cases hduplicate : ∃ value : Residual n prior.gateCount,
          ∀ input, value.eval prior.result input =
            mappedLine.eval interpretation input (prior.result.eval interpretation input)
      · let value := Classical.choose hduplicate
        have hvalue := Classical.choose_spec hduplicate
        exact prior.reuseLast line value (by
          intro input
          exact (hvalue input).trans (hline input))
      · exact prior.keepLast line mappedLine hline

/-- Later simplification preserves every previously deleted gate. -/
private theorem step_deleted_castSucc {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)} {fixed : Bool}
    (prior : ProgramRestriction source selected fixed)
    (line : Line signature (n + 1) g)
    (choice : Simplified n prior.gateCount)
    (hline : ∀ input,
      choice.eval prior.result input =
        line.eval interpretation (Fin.insertNth selected fixed input)
          (source.eval interpretation (Fin.insertNth selected fixed input)))
    (gate : Fin g) (hdeleted : gate ∈ prior.deleted) :
    gate.castSucc ∈ (prior.step line choice hline).deleted := by
  cases choice with
  | reuse value =>
      simp [step, reuseLast, hdeleted]
  | gate mappedLine =>
      simp only [step]
      split <;> simp [reuseLast, keepLast, hdeleted]

/-- A gate equal to an existing residual value is omitted. -/
private theorem step_eq_deleted {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)} {fixed : Bool}
    (prior : ProgramRestriction source selected fixed)
    (line : Line signature (n + 1) g)
    (choice : Simplified n prior.gateCount)
    (hline : ∀ input,
      choice.eval prior.result input =
        line.eval interpretation (Fin.insertNth selected fixed input)
          (source.eval interpretation (Fin.insertNth selected fixed input)))
    (value : Residual n prior.gateCount)
    (heq : ∀ input, value.eval prior.result input =
      line.eval interpretation (Fin.insertNth selected fixed input)
        (source.eval interpretation (Fin.insertNth selected fixed input))) :
    Fin.last g ∈ (prior.step line choice hline).deleted := by
  cases choice with
  | reuse residual => simp [step, reuseLast]
  | gate mappedLine =>
    have hduplicate : ∃ residual : Residual n prior.gateCount,
        ∀ input, residual.eval prior.result input =
          mappedLine.eval interpretation input (prior.result.eval interpretation input) :=
      ⟨value, fun input => (heq input).trans (hline input).symm⟩
    simp [step, hduplicate, reuseLast]

/-- A gate whose restricted output is constant is deleted, even when that
constant is discovered through several earlier simplifications. -/
private theorem step_constant_deleted {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)} {fixed : Bool}
    (prior : ProgramRestriction source selected fixed)
    (line : Line signature (n + 1) g)
    (choice : Simplified n prior.gateCount)
    (hline : ∀ input,
      choice.eval prior.result input =
        line.eval interpretation (Fin.insertNth selected fixed input)
          (source.eval interpretation (Fin.insertNth selected fixed input)))
    (value : Bool)
    (hconstant : ∀ input,
      line.eval interpretation (Fin.insertNth selected fixed input)
        (source.eval interpretation (Fin.insertNth selected fixed input)) = value) :
    Fin.last g ∈ (prior.step line choice hline).deleted :=
  prior.step_eq_deleted line choice hline (.constant value)
    (fun input => (hconstant input).symm)

/-- Simplifying a line on residual values preserves its restricted semantics. -/
private theorem simplify_line_eval {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)} {fixed : Bool}
    (prior : ProgramRestriction source selected fixed)
    (line : Line signature (n + 1) g) (input : Fin n → Bool) :
    (simplify line.op (fun i => prior.values (line.wires i))).eval prior.result input =
      line.eval interpretation (Fin.insertNth selected fixed input)
        (source.eval interpretation (Fin.insertNth selected fixed input)) := by
  rw [simplify_eval]
  unfold Line.eval
  congr 1
  funext i
  simpa only [Program.trace, Function.comp_apply] using
    prior.trace_eq input (line.wires i)

end ProgramRestriction

/-- Partially evaluate every gate in program order after fixing one input.
When a gate is semantically constant or duplicates an existing wire, it is
reused instead of being retained. -/
@[no_expose] noncomputable def restrictProgram (selected : Fin (n + 1)) (fixed : Bool) :
    (source : Program signature (n + 1) g) →
      ProgramRestriction source selected fixed
  | .empty => ProgramRestriction.empty selected fixed
  | .gate source line => by
      let prior := restrictProgram selected fixed source
      exact prior.step line (simplify line.op (fun i => prior.values (line.wires i)))
        (prior.simplify_line_eval line)

/-- A gate whose output becomes constant after restriction is deleted. -/
private theorem restrictProgram_deletes_constant_last {source : Program signature (n + 1) g}
    (line : Line signature (n + 1) g)
    (selected : Fin (n + 1)) (fixed value : Bool)
    (hconstant : ∀ input : Fin n → Bool,
      line.eval interpretation (Fin.insertNth selected fixed input)
        (source.eval interpretation (Fin.insertNth selected fixed input)) = value) :
    Fin.last g ∈ (restrictProgram selected fixed (source.gate line)).deleted := by
  let prior := restrictProgram selected fixed source
  exact prior.step_constant_deleted line _ (prior.simplify_line_eval line) value hconstant

/-- A source gate deleted in a prefix stays deleted when another gate is processed. -/
private theorem restrictProgram_deleted_castSucc {source : Program signature (n + 1) g}
    (line : Line signature (n + 1) g)
    (selected : Fin (n + 1)) (fixed : Bool)
    (gate : Fin g)
    (hdeleted : gate ∈ (restrictProgram selected fixed source).deleted) :
    gate.castSucc ∈ (restrictProgram selected fixed (source.gate line)).deleted := by
  let prior := restrictProgram selected fixed source
  exact prior.step_deleted_castSucc line _ (prior.simplify_line_eval line) gate hdeleted

/-- A nonconstant restricted output is represented by a wire, giving a smaller
circuit without materializing an extra constant gate. -/
theorem exists_restricted_circuit (c : Circuit signature (n + 1) 1)
    (selected : Fin (n + 1)) (fixed : Bool)
    (nonconstant : ∃ x y : Fin n → Bool,
      c.eval interpretation (Fin.insertNth selected fixed x) 0 ≠
        c.eval interpretation (Fin.insertNth selected fixed y) 0) :
    ∃ d : Circuit signature n 1,
      d.size + (restrictProgram selected fixed c.program).deleted.card = c.size ∧
        ∀ input, d.eval interpretation input =
          c.eval interpretation (Fin.insertNth selected fixed input) := by
  let restriction := restrictProgram selected fixed c.program
  cases hvalue : restriction.values (c.outputs 0) with
  | constant value =>
      obtain ⟨x, y, hxy⟩ := nonconstant
      have hx := restriction.trace_eq x (c.outputs 0)
      have hy := restriction.trace_eq y (c.outputs 0)
      rw [hvalue] at hx hy
      simp only [Residual.eval] at hx hy
      exfalso
      apply hxy
      exact hx.symm.trans hy
  | wire wire =>
      let d : Circuit signature n 1 := ⟨restriction.result, fun _ => wire⟩
      refine ⟨d, restriction.count_eq, ?_⟩
      intro input
      funext output
      have houtput : output = 0 := Subsingleton.elim _ _
      subst output
      have htrace := restriction.trace_eq input (c.outputs 0)
      rw [hvalue] at htrace
      exact htrace

/-- A gate duplicating an earlier wire after restriction is omitted. -/
private theorem restrictProgram_deletes_equal_last {source : Program signature (n + 1) g}
    (line : Line signature (n + 1) g)
    (selected : Fin (n + 1)) (fixed : Bool) (wire : Wire (n + 1) g)
    (heq : ∀ input : Fin n → Bool,
      line.eval interpretation (Fin.insertNth selected fixed input)
        (source.eval interpretation (Fin.insertNth selected fixed input)) =
      source.trace interpretation (Fin.insertNth selected fixed input) wire) :
    Fin.last g ∈ (restrictProgram selected fixed (source.gate line)).deleted := by
  let prior := restrictProgram selected fixed source
  exact prior.step_eq_deleted line _ (prior.simplify_line_eval line) (prior.values wire)
    (fun input => (prior.trace_eq input wire).trans (heq input).symm)

/-- A semantically constant gate is omitted, at any position in the program. -/
theorem restrictProgram_deletes_constant (source : Program signature (n + 1) g)
    (selected : Fin (n + 1)) (fixed value : Bool) (gate : Fin g)
    (hconstant : ∀ input : Fin n → Bool,
      source.eval interpretation (Fin.insertNth selected fixed input) gate = value) :
    gate ∈ (restrictProgram selected fixed source).deleted := by
  induction source with
  | empty => exact gate.elim0
  | gate source line ih =>
    induction gate using Fin.lastCases with
    | last =>
      exact restrictProgram_deletes_constant_last line selected fixed value
        (by simpa using hconstant)
    | cast gate =>
      apply restrictProgram_deleted_castSucc line selected fixed gate
      exact ih gate (by simpa using hconstant)

/-- A gate duplicating an earlier wire is omitted, at any position in the program. -/
theorem restrictProgram_deletes_equal (source : Program signature (n + 1) g)
    (selected : Fin (n + 1)) (fixed : Bool) (gate : Fin g) (wire : Wire (n + 1) g)
    (hbefore : wire.val < n + 1 + gate.val)
    (heq : ∀ input : Fin n → Bool,
      source.eval interpretation (Fin.insertNth selected fixed input) gate =
      source.trace interpretation (Fin.insertNth selected fixed input) wire) :
    gate ∈ (restrictProgram selected fixed source).deleted := by
  induction source with
  | empty => exact gate.elim0
  | @gate g source line ih =>
    have hw : wire.val < n + 1 + g := by omega
    let prior : Wire (n + 1) g := ⟨wire.val, hw⟩
    have hwire : wire = prior.castSucc := rfl
    rw [hwire] at heq
    induction gate using Fin.lastCases with
    | last =>
      apply restrictProgram_deletes_equal_last line selected fixed prior
      simpa using heq
    | cast gate =>
      apply restrictProgram_deleted_castSucc line selected fixed gate
      apply ih gate prior hbefore
      simpa using heq

/-- Constant internal gates can be eliminated when the output is nonconstant. -/
theorem _root_.Cslib.Circuits.Circuit.exists_smaller_of_constant (c : Circuit signature n 1)
    (hnonconstant : ∃ x y, c.eval interpretation x 0 ≠ c.eval interpretation y 0)
    (gate : Fin c.size) (value : Bool)
    (hconstant : ∀ x, c.program.eval interpretation x gate = value) :
    ∃ d : Circuit signature n 1,
      d.eval interpretation = c.eval interpretation ∧ d.size < c.size := by
  -- An unused input lets restriction serve as constant-eliminating normalization.
  let lifted := c.comp (Circuit.wiring signature Fin.succ)
  have heval (x : Fin n → Bool) :
      lifted.eval interpretation (Fin.insertNth 0 false x) = c.eval interpretation x := by
    simp [lifted, Function.comp_def]
  have hnonconstant' : ∃ x y,
      lifted.eval interpretation (Fin.insertNth 0 false x) 0 ≠
        lifted.eval interpretation (Fin.insertNth 0 false y) 0 := by
    simpa only [heval] using hnonconstant
  obtain ⟨d, hsize, hd⟩ := exists_restricted_circuit lifted 0 false hnonconstant'
  refine ⟨d, funext fun x => (hd x).trans (heval x), ?_⟩
  have hgate : (Fin.natAdd 0 gate) ∈ (restrictProgram 0 false lifted.program).deleted := by
    apply restrictProgram_deletes_constant lifted.program 0 false value (Fin.natAdd 0 gate)
    intro x
    have htrace := Program.trace_append_appendWire
      (Program.empty : Program signature (n + 1) 0)
      (fun i => Wire.input i.succ) interpretation (Fin.insertNth 0 false x)
      c.program (Wire.gate gate)
    have htrace' : lifted.program.eval interpretation
        (Fin.insertNth 0 false x) (Fin.natAdd 0 gate) =
          c.program.eval interpretation x gate := by
      simpa [lifted, Circuit.comp, Program.gateFunction] using htrace
    exact htrace'.trans (hconstant x)
  have hpositive : 0 < (restrictProgram (0 : Fin (n + 1)) false lifted.program).deleted.card :=
    Finset.card_pos.mpr ⟨_, hgate⟩
  have : lifted.size = c.size := by simp [lifted]
  omega

/-- A De Morgan operation with a constant argument reduces to a constant or an argument. -/
theorem Op.eval_eq_of_constant_argument (op : Op)
    (args : Fin (signature.Arity op) → (Fin n → Bool) → Bool)
    (argument : Fin (signature.Arity op)) (value : Bool)
    (hconstant : ∀ x, args argument x = value) :
    (∃ b, ∀ x, interpretation op (fun a => args a x) = b) ∨
      (∃ a, ∀ x, interpretation op (fun a => args a x) = args a x) := by
  cases op with
  | const b => exact Or.inl ⟨b, fun _ => rfl⟩
  | not =>
    have hzero : argument = 0 := Fin.eq_zero argument
    subst argument
    exact Or.inl ⟨!value, fun x => by simp [interpretation, hconstant]⟩
  | and =>
    fin_cases argument <;> cases value <;> dsimp at hconstant
    · exact Or.inl ⟨false, fun x => by simp [interpretation, hconstant]⟩
    · exact Or.inr ⟨1, fun x => by simp [interpretation, hconstant]⟩
    · exact Or.inl ⟨false, fun x => by simp [interpretation, hconstant]⟩
    · exact Or.inr ⟨0, fun x => by simp [interpretation, hconstant]⟩
  | or =>
    fin_cases argument <;> cases value <;> dsimp at hconstant
    · exact Or.inr ⟨1, fun x => by simp [interpretation, hconstant]⟩
    · exact Or.inl ⟨true, fun x => by simp [interpretation, hconstant]⟩
    · exact Or.inr ⟨0, fun x => by simp [interpretation, hconstant]⟩
    · exact Or.inl ⟨true, fun x => by simp [interpretation, hconstant]⟩

/-- A gate with a semantically constant argument is omitted. -/
theorem restrictProgram_deletes_of_constant_argument (p : Program signature (n + 1) g)
    (selected : Fin (n + 1)) (fixed : Bool) (gate : Fin g)
    (argument : Fin (signature.Arity (p.lines gate).op)) (value : Bool)
    (hconstant : ∀ x, p.trace interpretation (Fin.insertNth selected fixed x)
      ((p.lines gate).wires argument) = value) :
    gate ∈ (restrictProgram selected fixed p).deleted := by
  have heval (x : Fin n → Bool) :
      p.eval interpretation (Fin.insertNth selected fixed x) gate =
        interpretation (p.lines gate).op (fun a => p.trace interpretation
          (Fin.insertNth selected fixed x) ((p.lines gate).wires a)) :=
    (p.lines_eval _ _ _).symm
  obtain ⟨value, hv⟩ | ⟨a, ha⟩ := Op.eval_eq_of_constant_argument (p.lines gate).op
    (fun a x => p.trace interpretation (Fin.insertNth selected fixed x)
      ((p.lines gate).wires a)) argument value hconstant
  · exact restrictProgram_deletes_constant p selected fixed value gate
      (fun x => (heval x).trans (hv x))
  · exact restrictProgram_deletes_equal p selected fixed gate ((p.lines gate).wires a)
      (p.lines_wires_lt gate a) (fun x => (heval x).trans (ha x))

/-- Every consumer of a wire made constant by restriction is omitted. -/
theorem restrictProgram_deletes_consumer (p : Program signature (n + 1) g)
    (selected : Fin (n + 1)) (fixed : Bool) (gate : Fin g) (wire : Wire (n + 1) g)
    (hread : p.Reads gate wire) (value : Bool)
    (hconstant : ∀ x, p.trace interpretation (Fin.insertNth selected fixed x) wire = value) :
    gate ∈ (restrictProgram selected fixed p).deleted := by
  obtain ⟨argument, hwire⟩ := hread
  apply restrictProgram_deletes_of_constant_argument p selected fixed gate argument value
  simpa only [hwire] using hconstant

end Cslib.Circuits.Boolean
