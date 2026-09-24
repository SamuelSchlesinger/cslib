/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Boolean.Parity
public import Cslib.Computability.Circuit.Boolean.Restriction
public import Cslib.Computability.Circuit.Normalization

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FinCases

/-!
# Red'kin's exact circuit complexity of parity

`complexity_parity_succ` proves that parity on `n + 1` inputs requires exactly `4 * n`
gates in the De Morgan basis. AND, OR, NOT, and constant gates each cost one;
input wires and designated output wires are free.

The lower bound follows Red'kin's gate elimination argument, as presented by Lozhkin.
We minimize over parity and its complement together, so bypassing a sole NOT consumer
of an input is a valid minimality contradiction. A restriction that makes two direct
consumers constant saves four gates, including when their outgoing paths meet.
Consequently a counterexample must give every input exactly one AND and one OR consumer.
The first gate then reads two inputs. Distinct complementary consumers yield a fourth
deletion by sensitivity; a shared complementary consumer forces crossed AND/OR successors,
where the same sensitivity argument applies. Induction completes the lower bound.

## References

* [N. P. Red'kin, *Proof of minimality of some circuits consisting of functional
  elements*][Redkin1970].
* [S. A. Lozhkin, *Additional Chapters of Cybernetics*][Lozhkin2013],
  Chapter 2, Section 2, pp. 61–65.
* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012],
  Chapter 1.
-/

namespace Cslib.Circuits.Boolean

namespace Redkin

variable {n : ℕ}

private def binary (polarity a b : Bool) : Bool := if polarity then a || b else a && b

private theorem Line.reads_view (line : Line signature n g) (wire : Wire n g)
    (hread : ∃ a, line.wires a = wire) :
    (line.op = .not ∧ (∀ w, (∃ a, line.wires a = w) ↔ w = wire) ∧
      ∀ values : Wire n g → Bool,
        interpretation line.op (values ∘ line.wires) = !(values wire)) ∨
    (∃ polarity : Bool, ∃ other : Wire n g,
      line.op = (if polarity then .or else .and) ∧
      (∀ w, (∃ a, line.wires a = w) ↔ w = wire ∨ w = other) ∧
      ∀ values : Wire n g → Bool,
        interpretation line.op (values ∘ line.wires) =
          binary polarity (values wire) (values other)) := by
  obtain ⟨op, wires⟩ := line
  obtain ⟨argument, hwire⟩ := hread
  cases op with
  | const b => exact argument.elim0
  | not =>
    have ha : argument = 0 := Fin.eq_zero argument
    subst argument
    dsimp at hwire
    subst wire
    refine Or.inl ⟨rfl, ?_, fun _ => rfl⟩
    intro w
    simp [Fin.exists_fin_one, eq_comm]
  | and =>
    fin_cases argument <;> dsimp at hwire <;> subst wire
    · refine Or.inr ⟨false, wires 1, rfl, ?_, fun _ => rfl⟩
      intro w
      simp [Fin.exists_fin_two, eq_comm]
    · refine Or.inr ⟨false, wires 0, rfl, ?_, ?_⟩
      · intro w
        simp only [Fin.exists_fin_two, eq_comm]
        exact or_comm
      · intro values
        exact Bool.and_comm _ _
  | or =>
    fin_cases argument <;> dsimp at hwire <;> subst wire
    · refine Or.inr ⟨true, wires 1, rfl, ?_, fun _ => rfl⟩
      intro w
      simp [Fin.exists_fin_two, eq_comm]
    · refine Or.inr ⟨true, wires 0, rfl, ?_, ?_⟩
      · intro w
        simp only [Fin.exists_fin_two, eq_comm]
        exact or_comm
      · intro values
        exact Bool.or_comm _ _

/-- Minimize over both phases: removing a sole NOT consumer may change the phase. -/
private structure MinimalParity (phase : Bool) (c : Circuit signature n 1) : Prop where
  /-- The circuit computes the chosen phase of parity. -/
  computes : c.Computes interpretation (fun x _ => parityPhase n phase x)
  /-- No circuit for either phase of parity is smaller. -/
  minimal : ∀ (phase : Bool) (d : Circuit signature n 1),
    d.Computes interpretation (fun x _ => parityPhase n phase x) → c.size ≤ d.size

private theorem exists_minimalParity (n : ℕ) :
    ∃ phase : Bool, ∃ c : Circuit signature n 1, MinimalParity phase c := by
  have hphase : ∃ phase : Bool, ∀ other : Bool,
      complexity interpretation (fun x (_ : Fin 1) => parityPhase n phase x) ≤
        complexity interpretation (fun x (_ : Fin 1) => parityPhase n other x) := by
    rcases le_total
        (complexity interpretation (fun x (_ : Fin 1) => parityPhase n false x))
        (complexity interpretation (fun x (_ : Fin 1) => parityPhase n true x)) with h | h
    · refine ⟨false, fun other => ?_⟩
      cases other
      · exact le_rfl
      · exact h
    · refine ⟨true, fun other => ?_⟩
      cases other
      · exact h
      · exact le_rfl
  obtain ⟨phase, hphase⟩ := hphase
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation)
    (F := fun x (_ : Fin 1) => parityPhase n phase x)
  refine ⟨phase, c, hc, fun other d hd => ?_⟩
  rw [hsize]
  exact (hphase other).trans (complexity_le_of_computes d hd)

namespace MinimalParity
variable {c : Circuit signature (n + 1) 1} {phase : Bool} (h : MinimalParity phase c)
include h

private theorem eval (x : Fin (n + 1) → Bool) :
    c.eval interpretation x 0 = parityPhase (n + 1) phase x :=
  congrFun (h.computes x) 0

private theorem nonconstant : ∃ x y, c.eval interpretation x 0 ≠ c.eval interpretation y 0 := by
  let x : Fin (n + 1) → Bool := fun _ => false
  refine ⟨x, flip x 0, ?_⟩
  rw [h.eval, h.eval, parityPhase_flip]
  cases parityPhase (n + 1) phase x <;> decide

private theorem optimal (d : Circuit signature (n + 1) 1)
    (hd : d.eval interpretation = c.eval interpretation) : c.size ≤ d.size :=
  h.minimal phase d (fun x => (congrFun hd x).trans (h.computes x))

private theorem gate_nonconstant (gate : Fin c.size) (value : Bool) :
    ¬ ∀ x, c.program.eval interpretation x gate = value := by
  intro heq
  obtain ⟨d, hd, hsize⟩ := Circuit.exists_smaller_of_constant c h.nonconstant gate value heq
  exact Nat.not_lt_of_ge (h.optimal d hd) hsize

private theorem gate_ne_wire (gate : Fin c.size) (wire : Wire (n + 1) c.size)
    (hbefore : wire.val < n + 1 + gate.val) :
    c.program.gateFunction interpretation gate ≠ c.program.wireFunction interpretation wire := by
  intro heq
  obtain ⟨d, hd, hsize⟩ := c.exists_smaller_of_equal gate wire hbefore heq
  exact Nat.not_lt_of_ge (h.optimal d hd) hsize

private theorem gate_has_consumer (gate : Fin c.size) (houtput : c.outputs 0 ≠ Wire.gate gate) :
    ∃ consumer, c.program.Reads consumer (Wire.gate gate) := by
  by_contra hnone
  have hread : ∀ j, ¬ c.program.Reads j (Wire.gate gate) := by simpa using hnone
  obtain ⟨d, hd, hsize⟩ := c.exists_smaller_of_unused 0 gate hread houtput
  exact Nat.not_lt_of_ge (h.optimal d hd) hsize

private theorem output_ne_input (hn : 0 < n) (selected : Fin (n + 1)) :
    c.outputs 0 ≠ Wire.input selected := by
  intro hout
  let other := selected.succAbove (⟨0, hn⟩ : Fin n)
  have hother : selected ≠ other := (Fin.succAbove_ne _ _).symm
  have heval (x : Fin (n + 1) → Bool) : parityPhase (n + 1) phase x = x selected := by
    rw [← h.eval]
    simp [Circuit.eval, hout]
  have heq := heval (flip (fun _ => false) other)
  rw [parityPhase_flip, heval] at heq
  simp [flip, hother] at heq

end MinimalParity

private theorem Op.exists_absorbing (op : Op) (argument : Fin (signature.Arity op)) :
    ∃ fixed value : Bool, ∀ args : Fin (signature.Arity op) → Bool,
      args argument = fixed → interpretation op args = value := by
  cases op with
  | const b => exact ⟨false, b, fun _ _ => rfl⟩
  | not =>
    have hzero : argument = 0 := Fin.eq_zero argument
    subst argument
    exact ⟨false, true, fun args ha => by simp [interpretation, ha]⟩
  | and =>
    refine ⟨false, false, ?_⟩
    intro args ha
    fin_cases argument <;> dsimp at ha <;> simp [interpretation, ha]
  | or =>
    refine ⟨true, true, ?_⟩
    intro args ha
    fin_cases argument <;> dsimp at ha <;> simp [interpretation, ha]

namespace MinimalParity
variable {c : Circuit signature (n + 1) 1} {phase : Bool} (h : MinimalParity phase c)
include h

private theorem output_ne_consumer (hn : 0 < n) (selected : Fin (n + 1)) (gate : Fin c.size)
    (hread : c.program.Reads gate (Wire.input selected)) :
    c.outputs 0 ≠ Wire.gate gate := by
  intro hout
  obtain ⟨argument, hwire⟩ := hread
  obtain ⟨fixed, value, hconstant⟩ := Op.exists_absorbing (c.program.lines gate).op argument
  have heval (x : Fin n → Bool) :
      c.eval interpretation (Fin.insertNth selected fixed x) 0 = value := by
    simp only [Circuit.eval, Function.comp_apply, hout, Program.trace_gateWire,
      Program.gateFunction]
    rw [← c.program.lines_eval]
    apply hconstant
    change c.program.trace interpretation (Fin.insertNth selected fixed x)
      ((c.program.lines gate).wires argument) = fixed
    simp [hwire]
  obtain ⟨x, y, hxy⟩ := parityPhase_restrict_nonconstant hn phase selected fixed
  apply hxy
  have hx := h.eval (Fin.insertNth selected fixed x)
  have hy := h.eval (Fin.insertNth selected fixed y)
  rw [← hx, ← hy, heval, heval]

end MinimalParity

/-- If an AND/OR gate is the only route across a boundary for an input to influence
the output, full sensitivity forces that gate to copy the input. -/
private theorem bottleneck_eq_input {m : ℕ} (c : Circuit signature n 1)
    (substitution : (Fin m → Bool) → (Fin n → Bool)) (selected : Fin m)
    (boundary : Set (Wire n c.size)) (gate : Fin c.size) (other : Wire n c.size)
    (operation : Bool → Bool → Bool)
    (cancel : ∀ a b, operation a b ≠ operation (!a) b → operation a b = a)
    (hgate : ∀ x, c.program.eval interpretation (substitution x) gate =
      operation (x selected) (c.program.trace interpretation (substitution x) other))
    (hother : other ∉ boundary) (hbefore : other.val < n + gate.val)
    (houtput : c.outputs 0 ∉ boundary)
    (hsensitive : ∀ x, c.eval interpretation (substitution x) 0 ≠
      c.eval interpretation (substitution (flip x selected)) 0)
    (hinput : ∀ x i, Wire.input i ∉ boundary →
      substitution x i = substitution (flip x selected) i)
    (hcross : ∀ x j, Wire.gate j ∉ boundary → j ≠ gate →
      (∃ a, (c.program.lines j).wires a ∈ boundary) →
        c.program.eval interpretation (substitution x) j =
          c.program.eval interpretation (substitution (flip x selected)) j) :
    ∀ x, c.program.eval interpretation (substitution x) gate = x selected := by
  intro x
  have hstable : c.program.trace interpretation (substitution x) other =
      c.program.trace interpretation (substitution (flip x selected)) other := by
    apply c.program.trace_eq_of_boundary interpretation _ _ boundary (n + gate.val)
      (hinput x) _ other hother hbefore
    intro j hj hb ha
    apply hcross x j hb _ ha
    intro h
    subst j
    omega
  have hchange : c.program.eval interpretation (substitution x) gate ≠
      c.program.eval interpretation (substitution (flip x selected)) gate := by
    intro heq
    apply hsensitive x
    apply c.program.trace_eq_of_boundary interpretation _ _ boundary (n + c.size)
      (hinput x) _ (c.outputs 0) houtput (c.outputs 0).isLt
    intro j _ hb ha
    by_cases hj : j = gate
    · subst j
      exact heq
    · exact hcross x j hb hj ha
  rw [hgate] at hchange ⊢
  apply cancel
  simpa [hgate, flip, ← hstable] using hchange

/-- Bypass a sole NOT consumer by flipping its input, saving one gate. -/
private theorem smaller_of_unique_not_consumer (c : Circuit signature n 1)
    (selected : Fin n) (gate : Fin c.size)
    (hnot : ∀ x, c.program.eval interpretation x gate = !(x selected))
    (hread : ∀ j, c.program.Reads j (Wire.input selected) → j = gate)
    (houtput : c.outputs 0 ≠ Wire.input selected) :
    ∃ d : Circuit signature n 1,
      (∀ x, d.eval interpretation x = c.eval interpretation (flip x selected)) ∧
        d.size < c.size := by
  classical
  let f (j : Fin c.size) : BooleanFunction n :=
    fun x => c.program.eval interpretation (flip x selected) j
  let cost (j : Fin c.size) : ℕ := if j = gate then 0 else 1
  have hcost : (∑ j, cost j) + 1 = c.size := by
    simp [cost, Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem,
      Nat.sub_add_cancel (show 1 ≤ c.size from by have := gate.isLt; omega)]
  have hs : Synthesis interpretation (inputs n) (inputs n ∪ Set.range f) (∑ j, cost j) := by
    apply Synthesis.with_sources
    apply Synthesis.ordered_family f cost
    intro j
    by_cases hj : j = gate
    · subst j
      have heq : f gate = fun x => x selected := by
        funext x
        simp [f, hnot, flip]
      simp only [cost, ite_eq_left rfl, heq]
      exact Synthesis.of_mem (Or.inl ⟨selected, rfl⟩)
    · simp only [cost, hj, ite_false]
      have hargs (a : Fin (signature.Arity (c.program.lines j).op)) :
          (fun x => c.program.trace interpretation (flip x selected)
            ((c.program.lines j).wires a)) ∈ inputs n ∪ f '' {i | i < j} := by
        have hlt := c.program.lines_wires_lt j a
        generalize hw : (c.program.lines j).wires a = wire at hlt ⊢
        induction wire using Fin.addCases with
        | left i =>
          have hne : i ≠ selected := by
            intro heq
            subst i
            exact hj (hread j ⟨a, hw⟩)
          refine Or.inl ⟨i, ?_⟩
          funext x
          simp [flip, hne]
        | right i =>
          refine Or.inr ⟨i, by simpa using hlt, ?_⟩
          funext x
          simp [f, Program.gateFunction]
      have hs' := Synthesis.gate (I := interpretation) (c.program.lines j).op
        (fun a x => c.program.trace interpretation (flip x selected)
          ((c.program.lines j).wires a)) hargs
      have heq : (fun x => interpretation (c.program.lines j).op
          (fun a => c.program.trace interpretation (flip x selected)
            ((c.program.lines j).wires a))) = f j := by
        funext x
        exact c.program.lines_eval interpretation (flip x selected) j
      rwa [heq] at hs'
  have hout : (fun x => c.eval interpretation (flip x selected) 0) ∈
      inputs n ∪ Set.range f := by
    simp only [Circuit.eval, Function.comp_apply]
    generalize hw : c.outputs 0 = wire at houtput ⊢
    induction wire using Fin.addCases with
    | left i =>
      have hne : i ≠ selected := fun h => houtput (congrArg (Fin.castAdd c.size) h)
      refine Or.inl ⟨i, ?_⟩
      funext x
      simp [flip, hne]
    | right j => exact Or.inr ⟨j, by funext x; simp [f, Program.gateFunction]⟩
  obtain ⟨d, hd, hsize⟩ :=
    (hs.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr hout) le_rfl).exists_circuit
  refine ⟨d, ?_, by omega⟩
  intro x
  funext output
  have hzero : output = 0 := Subsingleton.elim _ _
  subst output
  exact congrFun (hd x) 0

namespace MinimalParity
variable {c : Circuit signature (n + 1) 1} {phase : Bool} (h : MinimalParity phase c)
include h

private theorem sensitive (x : Fin (n + 1) → Bool) (selected : Fin (n + 1)) :
    c.eval interpretation x 0 ≠ c.eval interpretation (flip x selected) 0 := by
  rw [h.eval, h.eval, parityPhase_flip]
  cases parityPhase (n + 1) phase x <;> decide

/-- A single consumer either copies the input or can be bypassed by changing phase. -/
private theorem not_unique_consumer (hn : 0 < n) (selected : Fin (n + 1))
    (gate : Fin c.size) (hread : c.program.Reads gate (Wire.input selected))
    (hunique : ∀ j, c.program.Reads j (Wire.input selected) → j = gate) : False := by
  obtain ⟨_, _, hnot⟩ | ⟨polarity, other, _, hreads, hbinary⟩ :=
    Line.reads_view (c.program.lines gate) (Wire.input selected) hread
  · have heval (x : Fin (n + 1) → Bool) :
        c.program.eval interpretation x gate = !(x selected) := by
      rw [← c.program.lines_eval]
      simpa [Line.eval, Program.trace, Function.comp_def] using
        hnot (c.program.trace interpretation x)
    obtain ⟨d, hd, hsize⟩ := smaller_of_unique_not_consumer c selected gate heval hunique
      (h.output_ne_input hn selected)
    have hd' : d.Computes interpretation (fun x _ => parityPhase (n + 1) (!phase) x) := by
      intro x
      rw [hd, h.computes]
      funext output
      simp [parityPhase, parity_flip]
    exact Nat.not_lt_of_ge (h.minimal (!phase) d hd') hsize
  · have heval (x : Fin (n + 1) → Bool) : c.program.eval interpretation x gate =
        binary polarity (x selected) (c.program.trace interpretation x other) := by
      rw [← c.program.lines_eval]
      simpa [Line.eval, Program.trace, Function.comp_def] using
        hbinary (c.program.trace interpretation x)
    have hearly : (Wire.input selected : Wire (n + 1) c.size).val < n + 1 + gate.val := by
      simp only [Wire.input, Fin.val_castAdd]
      omega
    have hother : other ≠ Wire.input selected := by
      intro heq
      apply h.gate_ne_wire gate (Wire.input selected) hearly
      funext x
      simp only [Program.gateFunction_apply, Program.wireFunction_input]
      rw [heval, heq, Program.trace_input]
      cases polarity <;> simp [binary]
    have hgate' := bottleneck_eq_input c id selected {Wire.input selected} gate other
      (binary polarity) (by intro a b; cases polarity <;> cases a <;> cases b <;> decide)
      heval hother ((hreads other).mpr (Or.inr rfl) |> Program.Reads.lt)
      (h.output_ne_input hn selected) (fun x => h.sensitive x selected)
      (fun x i hi => by
        have hne : i ≠ selected := by intro heq; subst i; exact hi rfl
        simp [flip, hne])
      (fun _ j _ hj hc => by
        have hread : c.program.Reads j (Wire.input selected) := by simpa [Program.Reads] using hc
        exact (hj (hunique j hread)).elim)
    apply h.gate_ne_wire gate (Wire.input selected) hearly
    funext x
    simpa [Program.gateFunction] using hgate' x

private theorem two_le_input_consumers (hn : 0 < n) (selected : Fin (n + 1)) :
    2 ≤ (c.program.consumers (Wire.input selected)).card := by
  have hexists : ∃ gate, c.program.Reads gate (Wire.input selected) := by
    by_contra hnone
    have heq := c.program.trace_eq_of_boundary interpretation (fun _ => false)
      (flip (fun _ => false) selected) {Wire.input selected} (n + 1 + c.size)
      (fun i hi => by
        have hne : i ≠ selected := by intro heq; subst i; exact hi rfl
        simp [flip, hne])
      (fun j _ _ hc => (hnone ⟨j, by simpa [Program.Reads] using hc⟩).elim)
      (c.outputs 0) (h.output_ne_input hn selected) (c.outputs 0).isLt
    exact h.sensitive (fun _ => false) selected heq
  obtain ⟨gate, hgate⟩ := hexists
  by_contra hcard
  have hcard : (c.program.consumers (Wire.input selected)).card ≤ 1 := by omega
  apply h.not_unique_consumer hn selected gate hgate
  intro j hj
  exact Finset.card_le_one.mp hcard j (by simpa using hj) gate (by simpa using hgate)

/-- Two direct consumers of the same input cannot read one another in a minimal circuit:
absorption, idempotence, or complementation would make the later gate redundant. -/
private theorem no_read_between_consumers (selected : Fin (n + 1)) (a b : Fin c.size)
    (ha : c.program.Reads a (Wire.input selected))
    (hb : c.program.Reads b (Wire.input selected)) :
    ¬ c.program.Reads b (Wire.gate a) := by
  intro hab
  have hne : (Wire.gate a : Wire (n + 1) c.size) ≠ Wire.input selected := by
    intro heq
    have := congrArg Fin.val heq
    simp only [Wire.gate, Wire.input, Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  obtain ⟨_, hreads, _⟩ | ⟨pb, other, _, hreads, hbinary⟩ :=
    Line.reads_view (c.program.lines b) (Wire.input selected) hb
  · exact hne ((hreads (Wire.gate a)).mp hab)
  have hother : other = Wire.gate a := by
    rcases (hreads (Wire.gate a)).mp hab with hi | ho
    · exact (hne hi).elim
    · exact ho.symm
  have hevalb (x : Fin (n + 1) → Bool) : c.program.eval interpretation x b =
      binary pb (x selected) (c.program.eval interpretation x a) := by
    rw [← c.program.lines_eval]
    simpa [hother, Line.eval, Program.trace, Program.gateFunction, Function.comp_def] using
      hbinary (c.program.trace interpretation x)
  obtain ⟨_, _, hnot⟩ | ⟨pa, other, _, _, hbinary⟩ :=
    Line.reads_view (c.program.lines a) (Wire.input selected) ha
  · apply h.gate_nonconstant b pb
    intro x
    rw [hevalb, ← c.program.lines_eval interpretation x a]
    have hnota : (c.program.lines a).eval interpretation x (c.program.eval interpretation x) =
        !(x selected) := by
      simpa [Line.eval, Program.trace, Function.comp_def] using
        hnot (c.program.trace interpretation x)
    rw [hnota]
    cases pb <;> cases x selected <;> rfl
  · have hevala (x : Fin (n + 1) → Bool) : c.program.eval interpretation x a =
        binary pa (x selected) (c.program.trace interpretation x other) := by
      rw [← c.program.lines_eval]
      simpa [Line.eval, Program.trace, Function.comp_def] using
        hbinary (c.program.trace interpretation x)
    let wire : Wire (n + 1) c.size := if pa = pb then Wire.gate a else Wire.input selected
    have hbefore : wire.val < n + 1 + b.val := by
      dsimp [wire]
      split
      · exact hab.lt
      · simp only [Wire.input, Fin.val_castAdd]
        omega
    apply h.gate_ne_wire b wire hbefore
    funext x
    simp only [Program.gateFunction_apply]
    rw [hevalb, hevala]
    cases pa <;> cases pb <;>
      simp only [wire, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false,
        Program.wireFunction_input, Program.wireFunction_gate,
        Program.gateFunction_apply, hevala] <;>
      cases x selected <;>
      cases c.program.trace interpretation x other <;> rfl

private theorem output_ne_of_restricted_constant (hn : 0 < n) (selected : Fin (n + 1))
    (fixed : Bool) (gate : Fin c.size) (value : Bool)
    (hconstant : ∀ x, c.program.eval interpretation (Fin.insertNth selected fixed x) gate = value) :
    c.outputs 0 ≠ Wire.gate gate := by
  intro hout
  obtain ⟨x, y, hxy⟩ := parityPhase_restrict_nonconstant hn phase selected fixed
  apply hxy
  rw [← h.eval, ← h.eval]
  simp only [Circuit.eval, Function.comp_apply, hout, Program.trace_gateWire,
    Program.gateFunction]
  rw [hconstant, hconstant]

/-- Two constant direct consumers save four gates. If their successors coincide,
that common successor is constant too, and its successor provides the fourth deletion. -/
private theorem four_deleted_of_two_constants (hn : 0 < n) (selected : Fin (n + 1))
    (fixed : Bool) (a b : Fin c.size)
    (ha : c.program.Reads a (Wire.input selected))
    (hb : c.program.Reads b (Wire.input selected)) (hab : a ≠ b)
    (va vb : Bool)
    (hva : ∀ x, c.program.eval interpretation (Fin.insertNth selected fixed x) a = va)
    (hvb : ∀ x, c.program.eval interpretation (Fin.insertNth selected fixed x) b = vb) :
    4 ≤ (restrictProgram selected fixed c.program).deleted.card := by
  let deleted := (restrictProgram selected fixed c.program).deleted
  have hda : a ∈ deleted := restrictProgram_deletes_constant _ _ _ _ _ hva
  have hdb : b ∈ deleted := restrictProgram_deletes_constant _ _ _ _ _ hvb
  obtain ⟨d, had⟩ := h.gate_has_consumer a
    (h.output_ne_of_restricted_constant hn selected fixed a va hva)
  obtain ⟨e, hbe⟩ := h.gate_has_consumer b
    (h.output_ne_of_restricted_constant hn selected fixed b vb hvb)
  have hdd : d ∈ deleted := restrictProgram_deletes_consumer _ _ _ _ _ had va
    (by simpa [Program.gateFunction] using hva)
  have hde : e ∈ deleted := restrictProgram_deletes_consumer _ _ _ _ _ hbe vb
    (by simpa [Program.gateFunction] using hvb)
  have hnd : ¬ c.program.Reads d (Wire.input selected) := fun hd =>
    h.no_read_between_consumers selected a d ha hd had
  have hne : ¬ c.program.Reads e (Wire.input selected) := fun he =>
    h.no_read_between_consumers selected b e hb he hbe
  have had' : a ≠ d := by intro heq; subst d; exact hnd ha
  have hae' : a ≠ e := by intro heq; subst e; exact hne ha
  have hbd' : b ≠ d := by intro heq; subst d; exact hnd hb
  have hbe' : b ≠ e := by intro heq; subst e; exact hne hb
  by_cases hde' : d = e
  · subst e
    have hne : (Wire.gate a : Wire (n + 1) c.size) ≠ Wire.gate b := by
      simpa using hab
    obtain ⟨_, hreads, _⟩ | ⟨polarity, other, _, hreads, hbinary⟩ :=
      Line.reads_view (c.program.lines d) (Wire.gate a) had
    · exact (hne ((hreads _).mp hbe).symm).elim
    have hother : other = Wire.gate b := by
      rcases (hreads _).mp hbe with heq | heq
      · exact (hne heq.symm).elim
      · exact heq.symm
    have hvd (x : Fin n → Bool) :
        c.program.eval interpretation (Fin.insertNth selected fixed x) d =
          binary polarity va vb := by
      rw [← c.program.lines_eval]
      simpa [Line.eval, Program.trace, Function.comp_def, hother, hva, hvb] using
        hbinary (c.program.trace interpretation (Fin.insertNth selected fixed x))
    obtain ⟨e, hde⟩ := h.gate_has_consumer d
      (h.output_ne_of_restricted_constant hn selected fixed d _ hvd)
    have hmem : e ∈ deleted := restrictProgram_deletes_consumer _ _ _ _ _ hde _
      (by simpa [Program.gateFunction] using hvd)
    have hltad : a.val < d.val := by have := had.lt; simpa [Wire.gate] using this
    have hltbd : b.val < d.val := by have := hbe.lt; simpa [Wire.gate] using this
    have hltde : d.val < e.val := by have := hde.lt; simpa [Wire.gate] using this
    exact Finset.three_lt_card_iff.mpr ⟨a, b, d, e, hda, hdb, hdd, hmem, hab,
      had', by intro heq; subst e; omega, hbd', by intro heq; subst e; omega,
      by intro heq; subst e; omega⟩
  · exact Finset.three_lt_card_iff.mpr
      ⟨a, b, d, e, hda, hdb, hdd, hde, hab, had', hae', hbd', hbe', hde'⟩

omit h in
private theorem constant_on_input (selected : Fin (n + 1)) (fixed : Bool) (gate : Fin c.size)
    (hread : c.program.Reads gate (Wire.input selected))
    (hop : (c.program.lines gate).op = .not ∨
      (c.program.lines gate).op = (if fixed then .or else .and)) :
    ∃ value, ∀ x, c.program.eval interpretation (Fin.insertNth selected fixed x) gate = value := by
  obtain ⟨_, _, hnot⟩ | ⟨polarity, other, hpolarity, _, hbinary⟩ :=
    Line.reads_view (c.program.lines gate) (Wire.input selected) hread
  · refine ⟨!fixed, fun x => ?_⟩
    rw [← c.program.lines_eval]
    simpa [Line.eval, Program.trace, Function.comp_def] using
      hnot (c.program.trace interpretation (Fin.insertNth selected fixed x))
  · have hsame : polarity = fixed := by
      cases polarity <;> cases fixed <;> simp_all
    subst polarity
    refine ⟨fixed, fun x => ?_⟩
    rw [← c.program.lines_eval]
    have hv := hbinary (c.program.trace interpretation (Fin.insertNth selected fixed x))
    cases fixed <;> simpa [Line.eval, Program.trace, Function.comp_def, binary] using hv

omit h in
private theorem binary_op_of_reads {g : ℕ} (p : Program signature (n + 1) g)
    (selected : Fin (n + 1)) (gate : Fin g)
    (hread : p.Reads gate (Wire.input selected)) (hnot : (p.lines gate).op ≠ .not) :
    ∃ polarity : Bool, (p.lines gate).op = (if polarity then .or else .and) := by
  obtain ⟨hop, _, _⟩ | ⟨polarity, _, hop, _, _⟩ :=
    Line.reads_view (p.lines gate) (Wire.input selected) hread
  · exact (hnot hop).elim
  · exact ⟨polarity, hop⟩

/-- A counterexample has exactly one AND and one OR consumer for every input. -/
private theorem mixed_consumers (hn : 0 < n)
    (hnofour : ∀ selected fixed, (restrictProgram selected fixed c.program).deleted.card < 4)
    (selected : Fin (n + 1)) :
    ∃ a b : Fin c.size,
      (c.program.lines a).op = .and ∧ (c.program.lines b).op = .or ∧
      (∀ j, c.program.Reads j (Wire.input selected) ↔ j = a ∨ j = b) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (h.two_le_input_consumers hn selected)
  simp only [Program.mem_consumers] at ha hb
  have hother (j : Fin c.size) : ∃ k, c.program.Reads k (Wire.input selected) ∧ j ≠ k := by
    by_cases hj : j = a
    · exact ⟨b, hb, by simpa only [hj] using hab⟩
    · exact ⟨a, ha, hj⟩
  have hnot (j : Fin c.size) (hj : c.program.Reads j (Wire.input selected)) :
      (c.program.lines j).op ≠ .not := by
    intro hop
    obtain ⟨k, hk, hjk⟩ := hother j
    obtain ⟨hopk, _, _⟩ | ⟨polarity, _, hopk, _, _⟩ :=
      Line.reads_view (c.program.lines k) (Wire.input selected) hk
    · obtain ⟨vj, hvj⟩ := constant_on_input selected false j hj (Or.inl hop)
      obtain ⟨vk, hvk⟩ := constant_on_input selected false k hk (Or.inl hopk)
      exact Nat.not_le_of_gt (hnofour selected false)
        (h.four_deleted_of_two_constants hn selected false j k hj hk hjk vj vk hvj hvk)
    · obtain ⟨vj, hvj⟩ := constant_on_input selected polarity j hj (Or.inl hop)
      obtain ⟨vk, hvk⟩ := constant_on_input selected polarity k hk (Or.inr hopk)
      exact Nat.not_le_of_gt (hnofour selected polarity)
        (h.four_deleted_of_two_constants hn selected polarity j k hj hk hjk vj vk hvj hvk)
  have hsame (polarity : Bool) (j k : Fin c.size)
      (hj : c.program.Reads j (Wire.input selected)) (hk : c.program.Reads k (Wire.input selected))
      (hopj : (c.program.lines j).op = (if polarity then .or else .and))
      (hopk : (c.program.lines k).op = (if polarity then .or else .and)) : j = k := by
    by_contra hjk
    obtain ⟨vj, hvj⟩ := constant_on_input selected polarity j hj (Or.inr hopj)
    obtain ⟨vk, hvk⟩ := constant_on_input selected polarity k hk (Or.inr hopk)
    exact Nat.not_le_of_gt (hnofour selected polarity)
      (h.four_deleted_of_two_constants hn selected polarity j k hj hk hjk vj vk hvj hvk)
  have hbuild (a b : Fin c.size)
      (ha : c.program.Reads a (Wire.input selected)) (hb : c.program.Reads b (Wire.input selected))
      (hopa : (c.program.lines a).op = .and) (hopb : (c.program.lines b).op = .or) :
      ∀ j, c.program.Reads j (Wire.input selected) ↔ j = a ∨ j = b := by
    intro j
    constructor
    · intro hj
      obtain ⟨polarity, hop⟩ := binary_op_of_reads c.program selected j hj (hnot j hj)
      cases polarity
      · exact Or.inl (hsame false j a hj ha hop hopa)
      · exact Or.inr (hsame true j b hj hb hop hopb)
    · rintro (rfl | rfl) <;> assumption
  obtain ⟨pa, hopa⟩ := binary_op_of_reads c.program selected a ha (hnot a ha)
  obtain ⟨pb, hopb⟩ := binary_op_of_reads c.program selected b hb (hnot b hb)
  cases pa <;> cases pb
  · exact (hab (hsame false a b ha hb hopa hopb)).elim
  · exact ⟨a, b, hopa, hopb, hbuild a b ha hb hopa hopb⟩
  · exact ⟨b, a, hopb, hopa, hbuild b a hb ha hopb hopa⟩
  · exact (hab (hsame true a b ha hb hopa hopb)).elim

private theorem complementary_consumer (hn : 0 < n)
    (hnofour : ∀ selected fixed, (restrictProgram selected fixed c.program).deleted.card < 4)
    (selected : Fin (n + 1)) (a : Fin c.size) (polarity : Bool)
    (ha : c.program.Reads a (Wire.input selected))
    (hopa : (c.program.lines a).op = (if polarity then .or else .and)) :
    ∃ b : Fin c.size,
      (c.program.lines b).op = (if !polarity then .or else .and) ∧
      (∀ j, c.program.Reads j (Wire.input selected) ↔ j = a ∨ j = b) := by
  obtain ⟨u, v, hu, hv, hreads⟩ := h.mixed_consumers hn hnofour selected
  rcases (hreads a).mp ha with rfl | rfl
  · cases polarity
    · exact ⟨v, hv, hreads⟩
    · simp_all
  · cases polarity
    · simp_all
    · refine ⟨u, hu, fun j => ?_⟩
      rw [hreads]
      exact or_comm

/-- The first gate of a counterexample combines two distinct inputs. -/
private theorem first_gate (hn : 0 < n)
    (hnofour : ∀ selected fixed, (restrictProgram selected fixed c.program).deleted.card < 4) :
    ∃ (a : Fin c.size) (polarity : Bool) (x y : Fin (n + 1)), x ≠ y ∧
      (c.program.lines a).op = (if polarity then .or else .and) ∧
      (∀ w, c.program.Reads a w ↔ w = Wire.input x ∨ w = Wire.input y) ∧
      (∀ input, c.program.eval interpretation input a =
        binary polarity (input x) (input y)) := by
  have hsize : 0 < c.size := by
    obtain ⟨a, _, b, _, _⟩ := Finset.one_lt_card.mp (h.two_le_input_consumers hn 0)
    exact Nat.zero_lt_of_lt a.isLt
  let a : Fin c.size := ⟨0, hsize⟩
  have hconst (value : Bool) : (c.program.lines a).op ≠ .const value := by
    intro heq
    apply h.gate_nonconstant a value
    intro input
    rw [← c.program.lines_eval]
    generalize hline : c.program.lines a = line at heq ⊢
    obtain ⟨op, wires⟩ := line
    dsimp at heq
    subst op
    rfl
  have harity : 0 < signature.Arity (c.program.lines a).op := by
    cases hop : (c.program.lines a).op with
    | const value => exact (hconst value hop).elim
    | not => decide
    | and => decide
    | or => decide
  let argument : Fin (signature.Arity (c.program.lines a).op) := ⟨0, harity⟩
  let wire := (c.program.lines a).wires argument
  have hwire : wire.val < n + 1 := by simpa [a] using c.program.lines_wires_lt a argument
  let x : Fin (n + 1) := ⟨wire.val, hwire⟩
  have hread : c.program.Reads a (Wire.input x) := ⟨argument, Fin.ext rfl⟩
  obtain ⟨hop, _, _⟩ | ⟨polarity, other, hop, hreads, hbinary⟩ :=
    Line.reads_view (c.program.lines a) (Wire.input x) hread
  · obtain ⟨u, v, hu, hv, hreads⟩ := h.mixed_consumers hn hnofour x
    rcases (hreads a).mp hread with rfl | rfl <;> simp_all
  · have hlt : other.val < n + 1 := by
      have := Program.Reads.lt ((hreads other).mpr (Or.inr rfl))
      simpa [a] using this
    let y : Fin (n + 1) := ⟨other.val, hlt⟩
    have hy : other = Wire.input y := Fin.ext rfl
    have heval (input : Fin (n + 1) → Bool) : c.program.eval interpretation input a =
        binary polarity (input x) (input y) := by
      rw [← c.program.lines_eval]
      simpa [hy, Line.eval, Program.trace, Function.comp_def] using
        hbinary (c.program.trace interpretation input)
    refine ⟨a, polarity, x, y, ?_, hop, ?_, heval⟩
    · intro hxy
      apply h.gate_ne_wire a (Wire.input x) hread.lt
      funext input
      simp only [Program.gateFunction_apply, Program.wireFunction_input]
      rw [heval, hxy]
      cases polarity <;> simp [binary]
    · intro w
      simpa only [Program.Reads, hy] using hreads w

omit h in
private theorem binary_view (gate : Fin c.size) (wire : Wire (n + 1) c.size) (polarity : Bool)
    (hread : c.program.Reads gate wire)
    (hop : (c.program.lines gate).op = (if polarity then .or else .and)) :
    ∃ other : Wire (n + 1) c.size,
      (∀ w, c.program.Reads gate w ↔ w = wire ∨ w = other) ∧
      (∀ input, c.program.eval interpretation input gate = binary polarity
        (c.program.trace interpretation input wire)
        (c.program.trace interpretation input other)) := by
  obtain ⟨hop', _, _⟩ | ⟨polarity', other, hop', hreads, hbinary⟩ :=
    Line.reads_view (c.program.lines gate) wire hread
  · cases polarity <;> simp_all
  · have heq : polarity' = polarity := by cases polarity' <;> cases polarity <;> simp_all
    subst polarity'
    refine ⟨other, hreads, fun input => ?_⟩
    rw [← c.program.lines_eval]
    simpa [Line.eval, Program.trace, Function.comp_def] using
      hbinary (c.program.trace interpretation input)

omit h in
/-- A binary gate reading two distinct inputs has no gate arguments and evaluates
directly on those inputs. -/
private theorem binary_inputs (gate : Fin c.size) (x y : Fin (n + 1)) (hxy : x ≠ y)
    (polarity : Bool) (hx : c.program.Reads gate (Wire.input x))
    (hy : c.program.Reads gate (Wire.input y))
    (hop : (c.program.lines gate).op = (if polarity then .or else .and)) :
    (∀ j, ¬ c.program.Reads gate (Wire.gate j)) ∧
      (∀ input, c.program.eval interpretation input gate =
        binary polarity (input x) (input y)) := by
  obtain ⟨other, hreads, heval⟩ := binary_view gate (Wire.input x) polarity hx hop
  have hother : other = Wire.input y := by
    rcases (hreads _).mp hy with hh | hh
    · have heq : y = x := by simpa [Wire.input] using hh
      exact (hxy heq.symm).elim
    · exact hh.symm
  have hdisjoint (i : Fin (n + 1)) (j : Fin c.size) :
      (Wire.gate j : Wire (n + 1) c.size) ≠ Wire.input i := by
    intro heq
    have := congrArg Fin.val heq
    simp only [Wire.gate, Wire.input, Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  refine ⟨?_, ?_⟩
  · intro j hread
    rcases (hreads _).mp hread with hh | hh
    · exact hdisjoint x j hh
    · exact hdisjoint y j (hh.trans hother)
  · intro input
    simpa only [hother, Program.trace_input] using heval input

private theorem binary_other_ne (gate : Fin c.size) (wire other : Wire (n + 1) c.size)
    (polarity : Bool) (hread : c.program.Reads gate wire)
    (heval : ∀ input, c.program.eval interpretation input gate = binary polarity
      (c.program.trace interpretation input wire) (c.program.trace interpretation input other)) :
    other ≠ wire := by
  intro heq
  apply h.gate_ne_wire gate wire hread.lt
  funext input
  change c.program.eval interpretation input gate = c.program.trace interpretation input wire
  rw [heval, heq]
  cases polarity <;> simp [binary]

omit h in
private theorem insert_flip (selected : Fin (n + 1)) (fixed : Bool) (input : Fin n → Bool)
    (remaining : Fin n) :
    Fin.insertNth selected fixed (flip input remaining) =
      flip (Fin.insertNth selected fixed input) (selected.succAbove remaining) := by
  funext i
  refine Fin.succAboveCases selected ?_ (fun j => ?_) i
  · simp [flip, Ne.symm (Fin.succAbove_ne _ _)]
  · simp [flip]

private theorem restricted_bottleneck (selected : Fin (n + 1)) (fixed : Bool) (remaining : Fin n)
    (boundary : Set (Wire (n + 1) c.size))
    (hboundary : Wire.input (selected.succAbove remaining) ∈ boundary)
    (gate : Fin c.size) (other : Wire (n + 1) c.size) (polarity : Bool)
    (hgate : ∀ x, c.program.eval interpretation (Fin.insertNth selected fixed x) gate =
      binary polarity (x remaining)
        (c.program.trace interpretation (Fin.insertNth selected fixed x) other))
    (hother : other ∉ boundary) (hbefore : other.val < n + 1 + gate.val)
    (houtput : c.outputs 0 ∉ boundary)
    (hcross : ∀ x j, Wire.gate j ∉ boundary → j ≠ gate →
      (∃ a, (c.program.lines j).wires a ∈ boundary) →
        c.program.eval interpretation (Fin.insertNth selected fixed x) j =
          c.program.eval interpretation (Fin.insertNth selected fixed (flip x remaining)) j) :
    ∀ x, c.program.eval interpretation (Fin.insertNth selected fixed x) gate = x remaining := by
  refine bottleneck_eq_input (n := n + 1) (m := n) c (fun x => Fin.insertNth selected fixed x)
    remaining boundary gate other (binary polarity) ?_ hgate hother hbefore houtput ?_ ?_ hcross
  · intro a b
    cases polarity <;> cases a <;> cases b <;> decide
  · intro x
    rw [h.eval, h.eval, parityPhase_insertNth, parityPhase_insertNth, parityPhase_flip]
    cases parityPhase n (phase ^^ fixed) x <;> decide
  · intro x i hi
    rw [insert_flip]
    have hne : i ≠ selected.succAbove remaining := by
      intro heq
      subst i
      exact hi hboundary
    simp [flip, hne]

/-- If the two inputs of a first gate have different complementary consumers, fixing
one input leaves a single route for the other, forcing the fourth deletion. -/
private theorem four_deleted_of_distinct_consumers (hn : 0 < n)
    (x y : Fin (n + 1)) (hxy : x ≠ y) (a b d : Fin c.size) (polarity : Bool)
    (hopa : (c.program.lines a).op = (if polarity then .or else .and))
    (hopb : (c.program.lines b).op = (if !polarity then .or else .and))
    (hopd : (c.program.lines d).op = (if !polarity then .or else .and))
    (hx : ∀ j, c.program.Reads j (Wire.input x) ↔ j = a ∨ j = b)
    (hy : ∀ j, c.program.Reads j (Wire.input y) ↔ j = a ∨ j = d)
    (hbd : b ≠ d) :
    4 ≤ (restrictProgram x polarity c.program).deleted.card := by
  have hax := (hx a).mpr (Or.inl rfl)
  have hbx := (hx b).mpr (Or.inr rfl)
  have hay := (hy a).mpr (Or.inl rfl)
  have hdy := (hy d).mpr (Or.inr rfl)
  have hab : a ≠ b := by intro heq; subst b; cases polarity <;> simp_all
  have had : a ≠ d := by intro heq; subst d; cases polarity <;> simp_all
  obtain ⟨value, hva⟩ := constant_on_input x polarity a hax (Or.inr hopa)
  obtain ⟨remaining, hremaining⟩ := Fin.exists_succAbove_eq hxy.symm
  obtain ⟨other, hreads, heval⟩ := binary_view d (Wire.input y) (!polarity) hdy hopd
  have hgate (input : Fin n → Bool) :
      c.program.eval interpretation (Fin.insertNth x polarity input) d =
        binary (!polarity) (input remaining)
          (c.program.trace interpretation (Fin.insertNth x polarity input) other) := by
    rw [heval, Program.trace_input, ← hremaining]
    simp
  have hcopy := h.restricted_bottleneck x polarity remaining {Wire.input y}
    (by simp [hremaining]) d other (!polarity) hgate
    (h.binary_other_ne d (Wire.input y) other (!polarity) hdy heval)
    ((hreads other).mpr (Or.inr rfl)).lt (h.output_ne_input hn y)
    (fun input j _ hj hcross => by
      have hread : c.program.Reads j (Wire.input y) := by simpa [Program.Reads] using hcross
      rcases (hy j).mp hread with rfl | rfl
      · rw [hva, hva]
      · exact (hj rfl).elim)
  have hdd : d ∈ (restrictProgram x polarity c.program).deleted := by
    apply restrictProgram_deletes_equal c.program x polarity d (Wire.input y) hdy.lt
    intro input
    rw [hcopy, Program.trace_input, ← hremaining]
    simp
  obtain ⟨e, hae⟩ := h.gate_has_consumer a
    (h.output_ne_of_restricted_constant hn x polarity a value hva)
  have he : e ∈ (restrictProgram x polarity c.program).deleted :=
    restrictProgram_deletes_consumer _ _ _ _ _ hae value
      (by simpa [Program.gateFunction] using hva)
  have he_notx : ¬ c.program.Reads e (Wire.input x) := fun hh =>
    h.no_read_between_consumers x a e hax hh hae
  have he_noty : ¬ c.program.Reads e (Wire.input y) := fun hh =>
    h.no_read_between_consumers y a e hay hh hae
  have hda : a ∈ (restrictProgram x polarity c.program).deleted :=
    restrictProgram_deletes_constant _ _ _ _ _ hva
  have hdb : b ∈ (restrictProgram x polarity c.program).deleted :=
    restrictProgram_deletes_consumer _ _ _ _ _ hbx polarity (by simp)
  exact Finset.three_lt_card_iff.mpr ⟨a, b, d, e, hda, hdb, hdd, he, hab, had,
    by intro heq; subst e; exact he_notx hax, hbd,
    by intro heq; subst e; exact he_notx hbx,
    by intro heq; subst e; exact he_noty hdy⟩

omit h in
private theorem binary_constant_input (selected : Fin (n + 1)) (polarity : Bool) (gate : Fin c.size)
    (hread : c.program.Reads gate (Wire.input selected))
    (hop : (c.program.lines gate).op = (if polarity then .or else .and)) :
    ∀ input,
      c.program.eval interpretation (Fin.insertNth selected polarity input) gate = polarity := by
  obtain ⟨other, _, heval⟩ := binary_view gate (Wire.input selected) polarity hread hop
  intro input
  rw [heval, Program.trace_input]
  cases polarity <;> simp [binary]

omit h in
private theorem constant_of_read {m : ℕ} (substitution : (Fin m → Bool) → (Fin (n + 1) → Bool))
    (gate : Fin c.size) (wire : Wire (n + 1) c.size) (value : Bool)
    (hread : c.program.Reads gate wire)
    (hvalue : ∀ input, c.program.trace interpretation (substitution input) wire = value)
    (hop : (c.program.lines gate).op = .not ∨
      (c.program.lines gate).op = (if value then .or else .and)) :
    ∃ result, ∀ input, c.program.eval interpretation (substitution input) gate = result := by
  obtain ⟨_, _, hnot⟩ | ⟨polarity, other, hpolarity, _, hbinary⟩ :=
    Line.reads_view (c.program.lines gate) wire hread
  · refine ⟨!value, fun input => ?_⟩
    have heval : c.program.eval interpretation (substitution input) gate =
        !(c.program.trace interpretation (substitution input) wire) := by
      rw [← c.program.lines_eval]
      simpa [Line.eval, Program.trace, Function.comp_def] using
        hnot (c.program.trace interpretation (substitution input))
    rw [heval, hvalue]
  · have hsame : polarity = value := by cases polarity <;> cases value <;> simp_all
    subst polarity
    refine ⟨value, fun input => ?_⟩
    have heval : c.program.eval interpretation (substitution input) gate =
        binary value (c.program.trace interpretation (substitution input) wire)
          (c.program.trace interpretation (substitution input) other) := by
      rw [← c.program.lines_eval]
      simpa [Line.eval, Program.trace, Function.comp_def] using
        hbinary (c.program.trace interpretation (substitution input))
    rw [heval, hvalue]
    cases value <;> simp [binary]

private theorem four_deleted_of_constant_chain (hn : 0 < n) (selected : Fin (n + 1)) (fixed : Bool)
    (a b d : Fin c.size) (hab : a ≠ b)
    (hb : c.program.Reads b (Wire.input selected))
    (hroot : ∀ j, ¬ c.program.Reads b (Wire.gate j))
    (had : c.program.Reads d (Wire.gate a)) (va vd : Bool)
    (hva : ∀ input, c.program.eval interpretation (Fin.insertNth selected fixed input) a = va)
    (hvd : ∀ input, c.program.eval interpretation (Fin.insertNth selected fixed input) d = vd) :
    4 ≤ (restrictProgram selected fixed c.program).deleted.card := by
  obtain ⟨e, hde⟩ := h.gate_has_consumer d
    (h.output_ne_of_restricted_constant hn selected fixed d vd hvd)
  have hda := restrictProgram_deletes_constant _ selected fixed va a hva
  have hdb := restrictProgram_deletes_consumer c.program selected fixed b _ hb fixed (by simp)
  have hdd := restrictProgram_deletes_constant _ selected fixed vd d hvd
  have hmem := restrictProgram_deletes_consumer c.program selected fixed e _ hde vd
    (by simpa [Program.gateFunction] using hvd)
  have hadlt : a.val < d.val := by simpa [Wire.gate] using had.lt
  have hdelt : d.val < e.val := by simpa [Wire.gate] using hde.lt
  exact Finset.three_lt_card_iff.mpr ⟨a, b, d, e, hda, hdb, hdd, hmem, hab,
    by intro heq; subst d; omega, by intro heq; subst e; omega,
    by intro heq; subst d; exact hroot a had,
    by intro heq; subst e; exact hroot d hde,
    by intro heq; subst e; omega⟩

/-- A constant-producing successor would start a chain of four deletions, so a
successor must have the opposite binary operation. -/
private theorem opposite_successor (hn : 0 < n)
    (hnofour : ∀ selected fixed, (restrictProgram selected fixed c.program).deleted.card < 4)
    (selected : Fin (n + 1)) (polarity : Bool) (a b d : Fin c.size) (hab : a ≠ b)
    (ha : c.program.Reads a (Wire.input selected))
    (hb : c.program.Reads b (Wire.input selected))
    (hroot : ∀ j, ¬ c.program.Reads b (Wire.gate j))
    (hopa : (c.program.lines a).op = (if polarity then .or else .and))
    (had : c.program.Reads d (Wire.gate a)) :
    (c.program.lines d).op = (if !polarity then .or else .and) := by
  have hva := binary_constant_input selected polarity a ha hopa
  have hbad (hopd : (c.program.lines d).op = .not ∨
      (c.program.lines d).op = (if polarity then .or else .and)) : False := by
    obtain ⟨value, hvd⟩ := constant_of_read (fun input => Fin.insertNth selected polarity input)
      d (Wire.gate a) polarity had (by simpa [Program.gateFunction] using hva) hopd
    exact Nat.not_le_of_gt (hnofour selected polarity)
      (h.four_deleted_of_constant_chain hn selected polarity a b d hab hb hroot had
        polarity value hva hvd)
  obtain ⟨hopd, _, _⟩ | ⟨pd, _, hopd, _, _⟩ :=
    Line.reads_view (c.program.lines d) (Wire.gate a) had
  · exact (hbad (Or.inl hopd)).elim
  · have hne : pd ≠ polarity := by intro heq; subst pd; exact hbad (Or.inr hopd)
    have heq : pd = !polarity := by cases pd <;> cases polarity <;> simp_all
    simpa [heq] using hopd

private theorem unique_successor
    (hnofour : ∀ selected fixed, (restrictProgram selected fixed c.program).deleted.card < 4)
    (selected : Fin (n + 1)) (polarity : Bool) (a b d e : Fin c.size) (hab : a ≠ b)
    (ha : c.program.Reads a (Wire.input selected))
    (hb : c.program.Reads b (Wire.input selected))
    (hopa : (c.program.lines a).op = (if polarity then .or else .and))
    (had : c.program.Reads d (Wire.gate a)) (hae : c.program.Reads e (Wire.gate a)) : d = e := by
  by_contra hde
  have hva := binary_constant_input selected polarity a ha hopa
  have hda := restrictProgram_deletes_constant _ selected polarity polarity a hva
  have hdb := restrictProgram_deletes_consumer c.program selected polarity b _ hb polarity (by simp)
  have hdd := restrictProgram_deletes_consumer c.program selected polarity d _ had polarity
    (by simpa [Program.gateFunction] using hva)
  have hmem := restrictProgram_deletes_consumer c.program selected polarity e _ hae polarity
    (by simpa [Program.gateFunction] using hva)
  have hnd : ¬ c.program.Reads d (Wire.input selected) := fun hd =>
    h.no_read_between_consumers selected a d ha hd had
  have hne : ¬ c.program.Reads e (Wire.input selected) := fun he =>
    h.no_read_between_consumers selected a e ha he hae
  apply Nat.not_le_of_gt (hnofour selected polarity)
  exact Finset.three_lt_card_iff.mpr ⟨a, b, d, e, hda, hdb, hdd, hmem, hab,
    by intro heq; subst d; exact hnd ha,
    by intro heq; subst e; exact hne ha,
    by intro heq; subst d; exact hnd hb,
    by intro heq; subst e; exact hne hb, hde⟩

/-- When both inputs share their AND and OR consumers, their successors must have
opposite operations. Sensitivity through the sole successor of one branch forces
the fourth deletion. -/
private theorem not_shared_roots (hn : 0 < n)
    (hnofour : ∀ selected fixed, (restrictProgram selected fixed c.program).deleted.card < 4)
    (x y : Fin (n + 1)) (hxy : x ≠ y) (a b : Fin c.size) (polarity : Bool)
    (hopa : (c.program.lines a).op = (if polarity then .or else .and))
    (hopb : (c.program.lines b).op = (if !polarity then .or else .and))
    (hx : ∀ j, c.program.Reads j (Wire.input x) ↔ j = a ∨ j = b)
    (hy : ∀ j, c.program.Reads j (Wire.input y) ↔ j = a ∨ j = b) : False := by
  -- The shared AND/OR pair reads only the two inputs.
  have hax := (hx a).mpr (Or.inl rfl)
  have hay := (hy a).mpr (Or.inl rfl)
  have hbx := (hx b).mpr (Or.inr rfl)
  have hby := (hy b).mpr (Or.inr rfl)
  have hab : a ≠ b := by intro heq; subst b; cases polarity <;> simp_all
  obtain ⟨hroota, _⟩ := binary_inputs a x y hxy polarity hax hay hopa
  obtain ⟨hrootb, hevalb⟩ := binary_inputs b x y hxy (!polarity) hbx hby hopb
  -- Their successors have opposite operations, hence are distinct.
  obtain ⟨d, had⟩ := h.gate_has_consumer a (h.output_ne_consumer hn x a hax)
  obtain ⟨e, hbe⟩ := h.gate_has_consumer b (h.output_ne_consumer hn x b hbx)
  have hopd := h.opposite_successor hn hnofour x polarity a b d hab hax hbx hrootb hopa had
  have hope : (c.program.lines e).op = (if polarity then .or else .and) := by
    simpa using h.opposite_successor hn hnofour x (!polarity) b a e hab.symm
      hbx hax hroota hopb hbe
  have hde : d ≠ e := by intro heq; subst d; cases polarity <;> simp_all
  have hunique (j : Fin c.size) (hj : c.program.Reads j (Wire.gate b)) : j = e :=
    h.unique_successor hnofour x (!polarity) b a j e hab.symm hbx hax hopb hj hbe
  have hnd : ¬ c.program.Reads d (Wire.input x) := fun hd =>
    h.no_read_between_consumers x a d hax hd had
  have hne : ¬ c.program.Reads e (Wire.input x) := fun he =>
    h.no_read_between_consumers x b e hbx he hbe
  have hney : ¬ c.program.Reads e (Wire.input y) := fun he =>
    h.no_read_between_consumers y b e hby he hbe
  obtain ⟨other, hreads, heval⟩ := binary_view e (Wire.gate b) polarity hbe hope
  have hotherb' : other ≠ Wire.gate b :=
    h.binary_other_ne e (Wire.gate b) other polarity hbe heval
  have hothery : other ≠ Wire.input y := by
    intro heq
    have hread := (hreads other).mpr (Or.inr rfl)
    rw [heq] at hread
    exact hney hread
  -- Fixing x makes gate a constant, while gate b copies the remaining input y.
  obtain ⟨remaining, hremaining⟩ := Fin.exists_succAbove_eq hxy.symm
  have hva := binary_constant_input x polarity a hax hopa
  have hvb (input : Fin n → Bool) :
      c.program.eval interpretation (Fin.insertNth x polarity input) b = input remaining := by
    rw [hevalb]
    cases polarity <;> simp [binary, ← hremaining]
  have hgate (input : Fin n → Bool) :
      c.program.eval interpretation (Fin.insertNth x polarity input) e =
        binary polarity (input remaining)
          (c.program.trace interpretation (Fin.insertNth x polarity input) other) := by
    rw [heval, Program.trace_gateWire, Program.gateFunction, hvb]
  -- Sensitivity across the boundary {y, b} forces e to copy y.
  have hcopy := h.restricted_bottleneck x polarity remaining {Wire.input y, Wire.gate b}
    (by simp [hremaining]) e other polarity hgate
    (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
      And.intro hothery hotherb')
    ((hreads other).mpr (Or.inr rfl)).lt
    (by
      intro hout
      rcases hout with hout | hout
      · exact h.output_ne_input hn y hout
      · exact h.output_ne_consumer hn x b hbx hout)
    (fun input j hjb hje hcross => by
      obtain ⟨argument, hwire⟩ := hcross
      rcases hwire with hwire | hwire
      · have hjy : c.program.Reads j (Wire.input y) := ⟨argument, hwire⟩
        rcases (hy j).mp hjy with rfl | rfl
        · rw [hva, hva]
        · exact (hjb (by simp)).elim
      · exact (hje (hunique j ⟨argument, hwire⟩)).elim)
  -- The shared pair and both successors are four distinct deleted gates.
  have hda := restrictProgram_deletes_constant c.program x polarity polarity a hva
  have hdb := restrictProgram_deletes_consumer c.program x polarity b _ hbx polarity (by simp)
  have hdd := restrictProgram_deletes_consumer c.program x polarity d _ had polarity
    (by simpa [Program.gateFunction] using hva)
  have hmem : e ∈ (restrictProgram x polarity c.program).deleted := by
    apply restrictProgram_deletes_equal c.program x polarity e (Wire.input y)
    · simp only [Wire.input, Fin.val_castAdd]
      omega
    · intro input
      rw [hcopy, Program.trace_input, ← hremaining]
      simp
  apply Nat.not_le_of_gt (hnofour x polarity)
  exact Finset.three_lt_card_iff.mpr ⟨a, b, d, e, hda, hdb, hdd, hmem, hab,
    by intro heq; subst d; exact hnd hax,
    by intro heq; subst e; exact hne hax,
    by intro heq; subst d; exact hnd hbx,
    by intro heq; subst e; exact hne hbx, hde⟩

/-- Red'kin's structural step, including both possible ways the first two inputs share gates. -/
private theorem four_deleted (hn : 0 < n) :
    ∃ selected fixed, 4 ≤ (restrictProgram selected fixed c.program).deleted.card := by
  by_contra hnone
  have hnofour : ∀ selected fixed, (restrictProgram selected fixed c.program).deleted.card < 4 := by
    simpa only [not_exists, Nat.not_le] using hnone
  obtain ⟨a, polarity, x, y, hxy, hopa, hroota, _⟩ := h.first_gate hn hnofour
  obtain ⟨b, hopb, hx⟩ := h.complementary_consumer hn hnofour x a polarity
    ((hroota _).mpr (Or.inl rfl)) hopa
  obtain ⟨d, hopd, hy⟩ := h.complementary_consumer hn hnofour y a polarity
    ((hroota _).mpr (Or.inr rfl)) hopa
  by_cases hbd : b = d
  · subst d
    exact h.not_shared_roots hn hnofour x y hxy a b polarity hopa hopb hx hy
  · exact Nat.not_le_of_gt (hnofour x polarity)
      (h.four_deleted_of_distinct_consumers hn x y hxy a b d polarity hopa hopb hopd hx hy hbd)

end MinimalParity

/-- Four gates deleted by a restriction yield a smaller parity circuit. -/
private theorem exists_smaller_parity_of_four_deleted {n : ℕ} (hn : 0 < n) (phase : Bool)
    (c : Circuit signature (n + 1) 1)
    (hc : c.Computes interpretation (fun x _ => parityPhase (n + 1) phase x))
    (selected : Fin (n + 1)) (fixed : Bool)
    (hsave : 4 ≤ (restrictProgram selected fixed c.program).deleted.card) :
    ∃ (nextPhase : Bool) (d : Circuit signature n 1),
      d.Computes interpretation (fun x _ => parityPhase n nextPhase x) ∧
        d.size + 4 ≤ c.size := by
  have hnonconstant : ∃ x y : Fin n → Bool,
      c.eval interpretation (Fin.insertNth selected fixed x) 0 ≠
        c.eval interpretation (Fin.insertNth selected fixed y) 0 := by
    obtain ⟨x, y, hxy⟩ := parityPhase_restrict_nonconstant hn phase selected fixed
    refine ⟨x, y, ?_⟩
    have hx := congrFun (hc (Fin.insertNth selected fixed x)) 0
    have hy := congrFun (hc (Fin.insertNth selected fixed y)) 0
    rw [hx, hy]
    exact hxy
  obtain ⟨d, hcount, hcompute⟩ :=
    exists_restricted_circuit c selected fixed hnonconstant
  refine ⟨Bool.xor phase fixed, d, ?_, ?_⟩
  · intro x
    rw [hcompute, hc]
    funext output
    exact parityPhase_insertNth phase selected fixed x
  · omega

end Redkin

/-- Red'kin's lower bound holds for parity and its complement. -/
public theorem parityPhase_size_lowerBound (n : ℕ) (phase : Bool) (c : Circuit signature (n + 1) 1)
    (hc : c.Computes interpretation (fun x _ => parityPhase (n + 1) phase x)) :
    4 * n ≤ c.size := by
  induction n generalizing phase with
  | zero => omega
  | succ n ih =>
    obtain ⟨minimalPhase, minimal, hminimal⟩ := Redkin.exists_minimalParity (n + 1 + 1)
    obtain ⟨selected, fixed, hsave⟩ := hminimal.four_deleted (by omega)
    obtain ⟨nextPhase, d, hd, hstep⟩ := Redkin.exists_smaller_parity_of_four_deleted (by omega)
      minimalPhase minimal hminimal.computes selected fixed hsave
    have hsmall := ih nextPhase d hd
    have hbound := hminimal.minimal phase c hc
    omega

/-- Red'kin's theorem: parity on `n + 1` inputs has complexity exactly `4 * n`. -/
@[simp] public theorem complexity_parity_succ (n : ℕ) :
    complexity interpretation (fun x (_ : Fin 1) => parity (n + 1) x) = 4 * n := by
  apply Nat.le_antisymm (complexity_parity_succ_le n)
  apply le_complexity_iff.mpr
  intro c hc
  exact parityPhase_size_lowerBound n false c (by simpa [parityPhase] using hc)

/-- The usual `4 * (n - 1)` form of Red'kin's theorem, for nonempty inputs. -/
public theorem complexity_parity {n : ℕ} (hn : 0 < n) :
    complexity interpretation (fun x (_ : Fin 1) => parity n x) = 4 * (n - 1) := by
  cases n with
  | zero => omega
  | succ n => simp

end Cslib.Circuits.Boolean
