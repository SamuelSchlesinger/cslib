/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Synthesis
public import Cslib.Computability.Circuit.Complexity

/-!
# Parity circuits

The De Morgan basis counts AND, OR, and NOT as unit-cost gates. A four-gate XOR
construction gives the upper bound `4 * n` for parity on `n + 1` inputs.

The matching lower bound is proved in `Cslib.Computability.Circuit.Boolean.Redkin`.

## References

* [N. P. Red'kin, *Proof of minimality of some circuits consisting of functional
  elements*][Redkin1970].
* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012],
  Chapter 1.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- The XOR of all input bits, with the empty XOR equal to false. -/
def parity (n : ℕ) : BooleanFunction n :=
  fun x => Fin.foldr n (fun i acc => Bool.xor (x i) acc) false

@[simp] theorem parity_zero (x : Fin 0 → Bool) : parity 0 x = false := by
  simp [parity]

/-- Isolating the first bit leaves parity, with its phase flipped when that bit is true. -/
theorem parity_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    parity (n + 1) x = Bool.xor (x 0) (parity n (fun i => x i.succ)) := by
  simp only [parity, Fin.foldr_succ]

/-- Flip a single input bit. -/
def flip (x : Fin n → Bool) (selected : Fin n) : Fin n → Bool :=
  fun i => if i = selected then !x i else x i

/-- Parity changes whenever one input bit is flipped. -/
theorem parity_flip {n : ℕ} (x : Fin n → Bool) (selected : Fin n) :
    parity n (flip x selected) = !(parity n x) := by
  induction n with
  | zero => exact selected.elim0
  | succ n ih =>
      refine Fin.cases ?_ (fun remaining => ?_) selected
      · rw [parity_succ, parity_succ]
        have htail : (fun i : Fin n => flip x 0 i.succ) =
            (fun i : Fin n => x i.succ) := by
          funext i
          simp [flip]
        rw [htail]
        simp [flip]
      · rw [parity_succ, parity_succ]
        have hhead : flip x remaining.succ 0 = x 0 := by
          simp [flip, Ne.symm (Fin.succ_ne_zero remaining)]
        have htail : (fun i : Fin n => flip x remaining.succ i.succ) =
            flip (fun i : Fin n => x i.succ) remaining := by
          funext i
          simp [flip]
        rw [hhead, htail, ih]
        simp

/-- Restricting any one input gives parity on the remaining inputs, up to phase. -/
theorem parity_insertNth {n : ℕ} (selected : Fin (n + 1))
    (fixed : Bool) (x : Fin n → Bool) :
    parity (n + 1) (Fin.insertNth selected fixed x) =
      Bool.xor fixed (parity n x) := by
  induction n with
  | zero =>
      have hs : selected = 0 := Fin.eq_zero selected
      subst selected
      simp [parity_succ]
  | succ n ih =>
      refine Fin.cases ?_ (fun remaining => ?_) selected
      · simp [parity_succ, Fin.insertNth_zero']
      · rw [show x = Fin.cons (x 0) (fun i => x i.succ) from
          (Fin.cons_self_tail x).symm]
        rw [Fin.insertNth_succ_cons]
        conv_lhs => rw [parity_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [ih]
        conv_rhs => rw [parity_succ]
        simp [Bool.xor_left_comm]

/-- Parity with a possible output complement. Restrictions of parity remain in this family. -/
def parityPhase (n : ℕ) (phase : Bool) : BooleanFunction n :=
  fun x => Bool.xor phase (parity n x)

/-- The phase after fixing an arbitrary input. -/
theorem parityPhase_insertNth {n : ℕ} (phase : Bool)
    (selected : Fin (n + 1)) (fixed : Bool) (x : Fin n → Bool) :
    parityPhase (n + 1) phase (Fin.insertNth selected fixed x) =
      parityPhase n (Bool.xor phase fixed) x := by
  simp [parityPhase, parity_insertNth]

/-- Flipping an input also flips phase parity. -/
theorem parityPhase_flip {n : ℕ} (phase : Bool) (x : Fin n → Bool)
    (selected : Fin n) :
    parityPhase n phase (flip x selected) = !(parityPhase n phase x) := by
  simp only [parityPhase, parity_flip]
  cases phase <;> cases parity n x <;> decide

/-- After one input is fixed, parity remains nonconstant if an input remains. -/
theorem parityPhase_restrict_nonconstant {n : ℕ} (hn : 0 < n)
    (phase : Bool) (selected : Fin (n + 1)) (fixed : Bool) :
    ∃ x y : Fin n → Bool,
      parityPhase (n + 1) phase (Fin.insertNth selected fixed x) ≠
        parityPhase (n + 1) phase (Fin.insertNth selected fixed y) := by
  let remaining : Fin n := ⟨0, hn⟩
  let x : Fin n → Bool := fun _ => false
  refine ⟨x, flip x remaining, ?_⟩
  rw [parityPhase_insertNth, parityPhase_insertNth, parityPhase_flip]
  cases parityPhase n (Bool.xor phase fixed) x <;> decide

/-- Iterating the shared four-gate XOR construction computes parity. -/
theorem synthesis_parity_succ (n : ℕ) :
    Synthesis interpretation (inputs (n + 1)) {parity (n + 1)} (4 * n) := by
  have hstep (f g : BooleanFunction (n + 1)) :
      Synthesis interpretation {f, g} {fun x => Bool.xor (f x) (g x)} 4 :=
    Synthesis.xor_of_mem (by simp) (by simp)
  have hseed : Synthesis interpretation (inputs (n + 1))
      {fun x => x (Fin.last n)} 0 :=
    Synthesis.of_mem ⟨Fin.last n, rfl⟩
  have hfold := Synthesis.foldr Bool.xor 4 hstep (List.finRange n)
    (f := fun i x => x i.castSucc) (cost := fun _ => 0)
    (seed := fun x => x (Fin.last n)) hseed
    (fun i _ => Synthesis.of_mem ⟨i.castSucc, rfl⟩)
  have htarget :
      (fun x => (List.finRange n).foldr
        (fun i acc => Bool.xor (x i.castSucc) acc) (x (Fin.last n))) =
        parity (n + 1) := by
    funext x
    simp [parity, Fin.foldr_succ_last, Fin.foldr_eq_finRange_foldr]
  simpa [htarget, Nat.mul_comm] using hfold

/-- Parity on `n + 1` inputs has a circuit of at most `4 * n` gates. -/
theorem complexity_parity_succ_le (n : ℕ) :
    complexity interpretation (fun x (_ : Fin 1) => parity (n + 1) x) ≤ 4 * n :=
  (synthesis_parity_succ n).complexity_le

/-- A single input wire computes one-bit parity at zero cost. -/
theorem complexity_parity_one :
    complexity interpretation (fun x (_ : Fin 1) => parity 1 x) = 0 := by
  have h := complexity_parity_succ_le 0
  exact Nat.eq_zero_of_le_zero (by simpa using h)

/-- Fixing the first input updates only the parity phase. -/
theorem parityPhase_cons (phase value : Bool) (x : Fin n → Bool) :
    parityPhase (n + 1) phase (Fin.cons value x) =
      parityPhase n (Bool.xor phase value) x := by
  simp [parityPhase, parity_succ]

end Cslib.Circuits.Boolean
