/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
import Mathlib.Algebra.BigOperators.Fin

/-!
# Composition of Deterministic Multi-Tape Turing Machines

This file constructs a multi-tape Turing machine that computes the composition of two
string-valued functions.

The composite machine uses the work tapes of the first machine, one intermediate tape, and the
work tapes of the second machine. During the first phase, output symbols are redirected to the
intermediate tape. The tape is then rewound and used as a virtual read-only input tape for the
second phase.

The real input tape is clamped to the two blank cells immediately outside its input. A work tape
does not have this built-in boundary behavior, so the composite machine records whether its virtual
input head is at the left boundary, inside the input, or at the right boundary. A classification
step after each simulated input-head move restores this information. Consequently, one step of the
second machine takes two steps of the composite machine.

Both component machines use the same tape alphabet. Thus the first output can become the second
input directly, and the public input/output encoding is unchanged by composition.

## Main declarations

* `MultiTapeTM.comp`: sequential composition of two deterministic multi-tape Turing machines.
* `MultiTapeTM.comp_haltsWithOutput`: operational correctness at exact component halting times.
* `MultiTapeTM.Composition.timeBound` and `MultiTapeTM.Composition.spaceBound`: reusable resource
  bounds for sequential composition.
* `MultiTapeTM.comp_computesFunInTimeAndSpace`: correctness and time/space bounds for composition.
-/

@[expose] public section

open Cslib Relation

namespace Turing

namespace MultiTapeTM

variable {k₀ k₁ : ℕ}
variable {Symbol State₀ State₁ : Type*}

/-- Number of work tapes used by the composition of a `k₀`- and a `k₁`-tape machine. -/
abbrev compositionTapeCount (k₀ k₁ : ℕ) := k₀ + 1 + k₁

/-- Physical coordinate of work tape `i` of the first machine. -/
def compositionFirstTapeIdx (k₁ : ℕ) (i : Fin k₀) : Fin (compositionTapeCount k₀ k₁) :=
  ⟨i, by simp [compositionTapeCount]; omega⟩

/-- Physical coordinate of the tape containing the intermediate output. -/
def compositionIntermediateTapeIdx (k₀ k₁ : ℕ) : Fin (compositionTapeCount k₀ k₁) :=
  ⟨k₀, by simp only [compositionTapeCount]; omega⟩

/-- Physical coordinate of work tape `i` of the second machine. -/
def compositionSecondTapeIdx (k₀ k₁ : ℕ) (i : Fin k₁) :
    Fin (compositionTapeCount k₀ k₁) :=
  ⟨k₀ + 1 + i, by simp only [compositionTapeCount]; omega⟩

@[simp]
lemma compositionFirstTapeIdx_val (k₁ : ℕ) (i : Fin k₀) :
    (compositionFirstTapeIdx k₁ i).val = i.val := rfl

@[simp]
lemma compositionIntermediateTapeIdx_val (k₀ k₁ : ℕ) :
    (compositionIntermediateTapeIdx k₀ k₁).val = k₀ := rfl

@[simp]
lemma compositionSecondTapeIdx_val (k₀ : ℕ) (i : Fin k₁) :
    (compositionSecondTapeIdx k₀ k₁ i).val = k₀ + 1 + i.val := rfl

/-- Location of the virtual input head during the second phase. -/
inductive CompositionInputMode
  | left
  | inside
  | right
deriving DecidableEq

/-- Boundary toward which a virtual input-head move was made. -/
inductive CompositionBoundary
  | left
  | right

/-- Control states of a composed multi-tape Turing machine. -/
inductive CompositionState (State₀ State₁ : Type*)
  | first (q : State₀)
  | rewindStart
  | rewind
  | second (q : State₁) (mode : CompositionInputMode)
  | classify (q : State₁) (boundary : CompositionBoundary)

/-- A tape containing exactly the symbols of `xs` at positions `0, ..., xs.length - 1`. -/
private def listTape (xs : List Symbol) : ℤ → Option Symbol
  | .ofNat n => xs[n]?
  | .negSucc _ => none

@[simp]
private lemma listTape_ofNat (xs : List Symbol) (n : ℕ) : listTape xs n = xs[n]? := rfl

@[simp]
private lemma listTape_negSucc (xs : List Symbol) (n : ℕ) : listTape xs (.negSucc n) = none := rfl

private lemma listTape_append_single (xs : List Symbol) (x : Symbol) :
    listTape (xs ++ [x]) = Function.update (listTape xs) (xs.length : ℤ) (some x) := by
  funext z
  cases z with
  | negSucc n => simp [listTape]
  | ofNat n =>
      simp only [listTape]
      rw [List.getElem?_append]
      by_cases h : n = xs.length
      · subst n
        simp
      · by_cases hn : n < xs.length
        · simp [hn, h]
        · have hle : xs.length ≤ n := Nat.le_of_not_gt hn
          have hlt : xs.length < n := lt_of_le_of_ne hle (Ne.symm h)
          have hsub : n - xs.length ≠ 0 := by omega
          simp [h, hn, hsub]

/-- Movement of the virtual input head, with outward boundary moves clamped. -/
def CompositionInputMode.move : CompositionInputMode → SignType → SignType
  | .left, .neg => 0
  | .right, .pos => 0
  | _, move => move

/-- Boundary to use if the cell reached by a virtual input-head move is blank. -/
def CompositionInputMode.nextBoundary :
    CompositionInputMode → SignType → CompositionBoundary
  | .left, .neg | .left, .zero => .left
  | .right, .pos | .right, .zero => .right
  | _, .neg => .left
  | _, .pos => .right
  | .inside, .zero => .right

/-- Convert a boundary classifier result to an input mode. -/
def CompositionBoundary.inputMode : CompositionBoundary → CompositionInputMode
  | .left => .left
  | .right => .right

namespace Composition

/-- A work-tape action that neither writes nor moves. -/
def idleWorkAction : Option (Option Symbol) × SignType := (none, 0)

/-- Read the work symbols seen by the first component machine. -/
def firstWorkSymbols
    (work : Fin (compositionTapeCount k₀ k₁) → Option Symbol) :
    Fin k₀ → Option Symbol :=
  fun i => work (compositionFirstTapeIdx k₁ i)

/-- Read the work symbols seen by the second component machine. -/
def secondWorkSymbols
    (work : Fin (compositionTapeCount k₀ k₁) → Option Symbol) :
    Fin k₁ → Option Symbol :=
  fun i => work (compositionSecondTapeIdx k₀ k₁ i)

/-- Embed the first component's work actions and redirect its output to the intermediate tape. -/
def firstWorkActions
    (actions : Fin k₀ → Option (Option Symbol) × SignType)
    (outS : Option Symbol) :
    Fin (compositionTapeCount k₀ k₁) →
      Option (Option Symbol) × SignType :=
  fun i =>
    if h : i.val < k₀ then
      actions ⟨i, h⟩
    else if i.val = k₀ then
      match outS with
      | none => idleWorkAction
      | some s => (some (some s), 1)
    else
      idleWorkAction

/-- Park every tape except the intermediate tape and move that tape by `move`. -/
def moveIntermediate (move : SignType) :
    Fin (compositionTapeCount k₀ k₁) →
      Option (Option Symbol) × SignType :=
  fun i => if i.val = k₀ then (none, move) else idleWorkAction

/-- Embed the second component's work actions and move the intermediate virtual-input tape. -/
def secondWorkActions
    (inputMove : SignType)
    (actions : Fin k₁ → Option (Option Symbol) × SignType) :
    Fin (compositionTapeCount k₀ k₁) →
      Option (Option Symbol) × SignType :=
  fun i =>
    if i.val = k₀ then
      (none, inputMove)
    else if h : k₀ + 1 ≤ i.val then
      actions ⟨i.val - (k₀ + 1), by
        have hi := i.isLt
        simp only [compositionTapeCount] at hi
        omega⟩
    else
      idleWorkAction

/-- Classify a virtual-input cell after moving onto it. -/
def classifyMode
    (cell : Option Symbol)
    (boundary : CompositionBoundary) : CompositionInputMode :=
  if cell.isSome then .inside else boundary.inputMode

end Composition

/-- Sequential composition of two deterministic multi-tape Turing machines. -/
def comp
    (tm₀ : MultiTapeTM k₀ Symbol State₀)
    (tm₁ : MultiTapeTM k₁ Symbol State₁) :
    MultiTapeTM (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) where
  q₀ := .first tm₀.q₀
  tr q input work :=
    match q with
    | .first q₀ =>
        let out := tm₀.tr q₀ input (Composition.firstWorkSymbols work)
        {
          inputMove := out.inputMove
          workActions := Composition.firstWorkActions out.workActions out.outS
          outS := none
          q' := some (match out.q' with
            | some q' => .first q'
            | none => .rewindStart)
        }
    | .rewindStart =>
        {
          inputMove := 0
          workActions := Composition.moveIntermediate (-1)
          outS := none
          q' := some .rewind
        }
    | .rewind =>
        if (work (compositionIntermediateTapeIdx k₀ k₁)).isSome then
          {
            inputMove := 0
            workActions := Composition.moveIntermediate (-1)
            outS := none
            q' := some .rewind
          }
        else
          {
            inputMove := 0
            workActions := Composition.moveIntermediate 1
            outS := none
            q' := some (.classify tm₁.q₀ .right)
          }
    | .second q₁ mode =>
        let clampMove := mode.move
        let out := tm₁.tr q₁
          (if mode = .inside then work (compositionIntermediateTapeIdx k₀ k₁) else none)
          (Composition.secondWorkSymbols work)
        {
          inputMove := 0
          workActions := Composition.secondWorkActions (clampMove out.inputMove) out.workActions
          outS := out.outS
          q' := out.q'.map fun q' => .classify q' (mode.nextBoundary out.inputMove)
        }
    | .classify q₁ boundary =>
        {
          inputMove := 0
          workActions := fun _ => Composition.idleWorkAction
          outS := none
          q' := some (.second q₁
            (Composition.classifyMode (work (compositionIntermediateTapeIdx k₀ k₁)) boundary))
        }

section Correctness

variable
    (tm₀ : MultiTapeTM k₀ Symbol State₀)
    (tm₁ : MultiTapeTM k₁ Symbol State₁)

/-!
## First-phase simulation
-/

/-- Embed a first-machine configuration into the first phase of the composite machine. -/
private def compositionFirstCfg
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input where
  state := match cfg.state with
    | some q => some (.first q)
    | none => some .rewindStart
  inputPos := cfg.inputPos
  workTapes i :=
    if h : i.val < k₀ then
      cfg.workTapes ⟨i, h⟩
    else if i.val = k₀ then
      listTape cfg.output
    else
      fun _ => none
  workTapePos i :=
    if h : i.val < k₀ then cfg.workTapePos ⟨i, h⟩
    else if i.val = k₀ then cfg.output.length
    else 0
  output := []

/-- The first-phase embedding sends an initial configuration to the composite initial
configuration. -/
private lemma compositionFirstCfg_initCfg (input : List Symbol) :
    compositionFirstCfg tm₀ tm₁ (tm₀.initCfg input) =
      (comp tm₀ tm₁).initCfg input := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i p
    by_cases hfirst : i.val < k₀
    · simp [compositionFirstCfg, hfirst]
    · by_cases hmiddle : i.val = k₀
      · cases p <;> simp [compositionFirstCfg, hmiddle, listTape]
      · simp [compositionFirstCfg, hfirst, hmiddle]
  · funext i
    simp [compositionFirstCfg]
  · rfl

/-- The first-phase embedding preserves the symbol read from the real input. -/
@[simp]
private lemma compositionFirstCfg_inputSymbol {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    (compositionFirstCfg tm₀ tm₁ cfg).inputSymbol = cfg.inputSymbol := rfl

/-- The first-phase embedding preserves every symbol read from a first-machine work tape. -/
private lemma Composition.firstWorkSymbols_compositionFirstCfg {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    Composition.firstWorkSymbols
      (compositionFirstCfg tm₀ tm₁ cfg).workTapeSymbols =
      cfg.workTapeSymbols := by
  funext i
  simp [Composition.firstWorkSymbols, Cfg.workTapeSymbols, compositionFirstCfg,
    compositionFirstTapeIdx]

/-- One first-machine step is one composite first-phase step. A halt of the first machine enters
the rewind phase instead of halting the composite machine. -/
private lemma step_compositionFirstCfg {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (hactive : cfg.state ≠ none) :
    (comp tm₀ tm₁).step (compositionFirstCfg tm₀ tm₁ cfg) =
      compositionFirstCfg tm₀ tm₁ (tm₀.step cfg) := by
  cases hstate : cfg.state with
  | none => exact absurd hstate hactive
  | some q =>
      have hinput := compositionFirstCfg_inputSymbol tm₀ tm₁ cfg
      have hwork := Composition.firstWorkSymbols_compositionFirstCfg tm₀ tm₁ cfg
      unfold step
      rw [show (compositionFirstCfg tm₀ tm₁ cfg).state =
        some (.first q) by simp [compositionFirstCfg, hstate]]
      rw [hstate]
      simp only [comp]
      rw [hinput, hwork]
      generalize htr : tm₀.tr q cfg.inputSymbol cfg.workTapeSymbols = trOut
      obtain ⟨inputMove, workActions, outS, q'⟩ := trOut
      simp only [htr]
      apply Cfg.ext
      · cases q' <;> rfl
      · rfl
      · funext i p
        by_cases hfirst : i.val < k₀
        · cases hwrite : (workActions ⟨i.val, hfirst⟩).1 with
          | none =>
              simp [compositionFirstCfg, Composition.firstWorkActions, hfirst, hwrite]
          | some s =>
              by_cases hp : p = cfg.workTapePos ⟨i.val, hfirst⟩
              · simp [compositionFirstCfg, Composition.firstWorkActions,
                  Function.update_apply, hfirst, hwrite, hp]
              · simp [compositionFirstCfg, Composition.firstWorkActions,
                  hfirst, hwrite, hp]
        · by_cases hmiddle : i.val = k₀
          · cases outS with
            | none =>
                simp [compositionFirstCfg, Composition.firstWorkActions, hmiddle,
                  Composition.idleWorkAction]
            | some s =>
                simp [compositionFirstCfg, Composition.firstWorkActions, hmiddle,
                  listTape_append_single]
          · simp [compositionFirstCfg, Composition.firstWorkActions, hfirst, hmiddle,
              Composition.idleWorkAction]
      · funext i
        by_cases hfirst : i.val < k₀
        · simp [compositionFirstCfg, Composition.firstWorkActions, hfirst]
        · by_cases hmiddle : i.val = k₀
          · cases outS <;>
              simp [compositionFirstCfg, Composition.firstWorkActions, hmiddle,
                Composition.idleWorkAction]
          · simp [compositionFirstCfg, Composition.firstWorkActions, hfirst, hmiddle,
              Composition.idleWorkAction]
      · rfl

/-- Simulation of the first component up to a time at which it has not halted earlier. -/
private lemma runFrom_firstPhase (input : List Symbol) (n : ℕ)
    (hactive : ∀ m < n, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none) :
    (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input) n =
      compositionFirstCfg tm₀ tm₁
        (tm₀.runFrom (tm₀.initCfg input) n) := by
  induction n with
  | zero => simpa using (compositionFirstCfg_initCfg tm₀ tm₁ input).symm
  | succ n ih =>
      rw [tm₀.runFrom_succ_eq_step', (comp tm₀ tm₁).runFrom_succ_eq_step',
        ih (fun m hm => hactive m (by omega))]
      exact step_compositionFirstCfg tm₀ tm₁
        (tm₀.runFrom (tm₀.initCfg input) n) (hactive n (by omega))

/-!
## Virtual input representation
-/

/-- View a native input-head position as a position on the intermediate work tape. -/
private def compositionVirtualInputPos {input : List Symbol} (p : Fin (input.length + 2)) : ℤ :=
  p.val - 1

/-- Classify a native input-head position as the left boundary, an input cell, or the right
boundary. -/
private def compositionInputMode {input : List Symbol}
    (p : Fin (input.length + 2)) : CompositionInputMode :=
  if p = 0 then .left else if p.val = input.length + 1 then .right else .inside

/-- Embed a second-machine configuration into the second phase of the composite machine. -/
private def compositionSecondCfg
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput) :
    Cfg (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) firstInput where
  state := match secondCfg.state with
    | some q => some (.second q (compositionInputMode secondCfg.inputPos))
    | none => none
  inputPos := firstCfg.inputPos
  workTapes i :=
    if h : i.val < k₀ then
      firstCfg.workTapes ⟨i, h⟩
    else if hmiddle : i.val = k₀ then
      listTape secondInput
    else
      secondCfg.workTapes ⟨i.val - (k₀ + 1), by
        have hi := i.isLt
        simp only [compositionTapeCount] at hi
        omega⟩
  workTapePos i :=
    if h : i.val < k₀ then firstCfg.workTapePos ⟨i, h⟩
    else if hmiddle : i.val = k₀ then compositionVirtualInputPos secondCfg.inputPos
    else secondCfg.workTapePos ⟨i.val - (k₀ + 1), by
      have hi := i.isLt
      simp only [compositionTapeCount] at hi
      omega⟩
  output := secondCfg.output

/-- The virtual input cell in a second-phase embedding is exactly the native input symbol. -/
private lemma compositionSecondCfg_inputSymbol
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput) :
    (if compositionInputMode secondCfg.inputPos = .inside then
      (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg).workTapeSymbols
        (compositionIntermediateTapeIdx k₀ k₁)
    else none) = secondCfg.inputSymbol := by
  simp only [Cfg.workTapeSymbols, compositionSecondCfg, compositionIntermediateTapeIdx,
    lt_self_iff_false, ↓reduceDIte]
  by_cases hleft : secondCfg.inputPos = 0
  · simp [compositionInputMode, hleft, Cfg.inputSymbol]
  · by_cases hright : secondCfg.inputPos.val = secondInput.length + 1
    · simp [compositionInputMode, hleft, hright, Cfg.inputSymbol]
    · have hp : 0 < secondCfg.inputPos.val :=
        Nat.pos_of_ne_zero (fun hz => hleft (Fin.ext hz))
      have hi : secondCfg.inputPos.val - 1 < secondInput.length := by omega
      have hmode : compositionInputMode secondCfg.inputPos = .inside := by
        simp [compositionInputMode, hleft, hright]
      simp only [hmode, ↓reduceIte]
      rw [inputSymbolInner (p := secondCfg.inputPos.val - 1) (by omega) hi]
      have hz : ((secondCfg.inputPos.val : ℤ) - 1) =
          (secondCfg.inputPos.val - 1 : ℕ) := by omega
      rw [show compositionVirtualInputPos secondCfg.inputPos =
        (secondCfg.inputPos.val : ℤ) - 1 by rfl, hz]
      simp [listTape, hi]

/-- A second-phase embedding preserves every symbol read from a second-machine work tape. -/
private lemma Composition.secondWorkSymbols_compositionSecondCfg
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput) :
    Composition.secondWorkSymbols
      (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg).workTapeSymbols =
      secondCfg.workTapeSymbols := by
  funext i
  have hlt : ¬k₀ + 1 + i.val < k₀ := by omega
  have hne : k₀ + 1 + i.val ≠ k₀ := by omega
  simp [Composition.secondWorkSymbols, Cfg.workTapeSymbols, compositionSecondCfg,
    compositionSecondTapeIdx, hlt, hne]

/-- The intermediate configuration between the moving and classifying halves of a simulated
second-machine step. -/
private def compositionClassifyCfg
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (boundary : CompositionBoundary) :
    Cfg (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) firstInput :=
  { compositionSecondCfg _tm₀ _tm₁ firstCfg secondCfg with
    state := secondCfg.state.map fun q => .classify q boundary }

/-!
## Rewinding the intermediate tape
-/

/-- A first-phase boundary configuration with a chosen control state and intermediate head
position. -/
private def compositionIntermediateCfg
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input)
    (state : CompositionState State₀ State₁)
    (pos : ℤ) :
    Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input :=
  { compositionFirstCfg _tm₀ _tm₁ cfg with
    state := some state
    workTapePos := fun i =>
      if i.val = k₀ then pos
      else (compositionFirstCfg _tm₀ _tm₁ cfg).workTapePos i }

/-- At position zero, the post-rewind classifier configuration is the classifier half of the
second machine's initial configuration. -/
private lemma compositionIntermediateCfg_classify_init {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    compositionIntermediateCfg tm₀ tm₁ cfg
        (.classify tm₁.q₀ .right) 0 =
      compositionClassifyCfg tm₀ tm₁ cfg (tm₁.initCfg cfg.output) .right := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i p
    by_cases hfirst : i.val < k₀
    · simp [compositionIntermediateCfg, compositionFirstCfg, compositionClassifyCfg,
        compositionSecondCfg, hfirst]
    · by_cases hmiddle : i.val = k₀
      · simp [compositionIntermediateCfg, compositionFirstCfg, compositionClassifyCfg,
          compositionSecondCfg, hmiddle]
      · simp [compositionIntermediateCfg, compositionFirstCfg, compositionClassifyCfg,
          compositionSecondCfg, hfirst, hmiddle]
  · funext i
    by_cases hfirst : i.val < k₀
    · have hmiddle : i.val ≠ k₀ := by omega
      simp [compositionIntermediateCfg, compositionFirstCfg, compositionClassifyCfg,
        compositionSecondCfg, compositionVirtualInputPos, hfirst, hmiddle]
    · by_cases hmiddle : i.val = k₀ <;>
        simp [compositionIntermediateCfg, compositionFirstCfg, compositionClassifyCfg,
          compositionSecondCfg, compositionVirtualInputPos, hfirst, hmiddle]
  · rfl

/-- Entering the rewind phase moves the intermediate head one cell to the left. -/
private lemma step_rewindStart {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).step (compositionFirstCfg tm₀ tm₁ cfg) =
      compositionIntermediateCfg tm₀ tm₁ cfg .rewind
        (cfg.output.length - 1) := by
  apply Cfg.ext
  · simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt]
  · simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt]
  · funext i p
    by_cases hmiddle : i.val = k₀ <;>
      simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt,
        Composition.moveIntermediate, Composition.idleWorkAction, hmiddle]
  · funext i
    by_cases hmiddle : i.val = k₀
    · simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt,
        Composition.moveIntermediate, Composition.idleWorkAction, hmiddle]
      omega
    · simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt,
        Composition.moveIntermediate, Composition.idleWorkAction, hmiddle]
  · simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt]

/-- One rewind step over a nonblank intermediate cell. -/
private lemma step_rewind_some {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (pos : ℤ)
    (hcell : (listTape cfg.output pos).isSome) :
    (comp tm₀ tm₁).step
        (compositionIntermediateCfg tm₀ tm₁ cfg .rewind pos) =
      compositionIntermediateCfg tm₀ tm₁ cfg .rewind (pos - 1) := by
  apply Cfg.ext
  · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
      Cfg.workTapeSymbols, hcell, Composition.moveIntermediate, Composition.idleWorkAction]
  · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
      Cfg.workTapeSymbols, hcell]
  · funext i p
    by_cases hmiddle : i.val = k₀ <;>
      simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
        Cfg.workTapeSymbols, hcell, Composition.moveIntermediate,
        Composition.idleWorkAction, hmiddle]
  · funext i
    by_cases hmiddle : i.val = k₀
    · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
        Cfg.workTapeSymbols, hcell, Composition.moveIntermediate,
        Composition.idleWorkAction, hmiddle]
      omega
    · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
        Cfg.workTapeSymbols, hcell, Composition.moveIntermediate,
        Composition.idleWorkAction, hmiddle]
  · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
      Cfg.workTapeSymbols, hcell]

/-- The blank just left of the intermediate output ends rewinding and moves the head to cell
zero for classification. -/
private lemma step_rewind_none {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (pos : ℤ)
    (hcell : listTape cfg.output pos = none) :
    (comp tm₀ tm₁).step
        (compositionIntermediateCfg tm₀ tm₁ cfg .rewind pos) =
      compositionIntermediateCfg tm₀ tm₁ cfg
        (.classify tm₁.q₀ .right) (pos + 1) := by
  apply Cfg.ext
  · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
      Cfg.workTapeSymbols, hcell]
  · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
      Cfg.workTapeSymbols, hcell]
  · funext i p
    by_cases hmiddle : i.val = k₀ <;>
      simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
        Cfg.workTapeSymbols, hcell, Composition.moveIntermediate,
        Composition.idleWorkAction, hmiddle]
  · funext i
    by_cases hmiddle : i.val = k₀ <;>
      simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
        Cfg.workTapeSymbols, hcell, Composition.moveIntermediate,
        Composition.idleWorkAction, hmiddle]
  · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
      Cfg.workTapeSymbols, hcell]

/-- A canonical list tape is nonblank at every position inside the represented list. -/
private lemma listTape_isSome_of_lt (xs : List Symbol) {r : ℕ} (h : r < xs.length) :
    (listTape xs ((xs.length : ℤ) - 1 - r)).isSome := by
  have hp : (xs.length : ℤ) - 1 - r = (xs.length - 1 - r : ℕ) := by omega
  rw [hp]
  simp [listTape]
  omega

/-- Rewinding scans exactly the cells occupied by the intermediate output. -/
private lemma runFrom_rewind {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input)
    (r : ℕ) (hr : r ≤ cfg.output.length) :
    (comp tm₀ tm₁).runFrom
        (compositionIntermediateCfg tm₀ tm₁ cfg .rewind
          ((cfg.output.length : ℤ) - 1)) r =
      compositionIntermediateCfg tm₀ tm₁ cfg .rewind
        ((cfg.output.length : ℤ) - 1 - r) := by
  induction r with
  | zero => simp [runFrom]
  | succ r ih =>
      rw [(comp tm₀ tm₁).runFrom_succ_eq_step', ih (by omega)]
      have hcell :
          (listTape cfg.output ((cfg.output.length : ℤ) - 1 - r)).isSome := by
        simpa using
          (listTape_isSome_of_lt cfg.output
            (r := r) (show r < cfg.output.length by omega))
      convert step_rewind_some tm₀ tm₁ cfg
        ((cfg.output.length : ℤ) - 1 - r) hcell using 1
      congr 1
      omega

/-- The prefix of the post-halting phase that consists of entering and running the rewind loop. -/
private lemma runFrom_firstHalt_rewind {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none)
    (r : ℕ) (hr : r ≤ cfg.output.length) :
    (comp tm₀ tm₁).runFrom
        (compositionFirstCfg tm₀ tm₁ cfg) (r + 1) =
      compositionIntermediateCfg tm₀ tm₁ cfg .rewind
        ((cfg.output.length : ℤ) - 1 - r) := by
  rw [(comp tm₀ tm₁).runFrom_succ_eq_step, step_rewindStart tm₀ tm₁ cfg hhalt]
  exact runFrom_rewind tm₀ tm₁ cfg r hr

/-- The configuration immediately after the rewind loop is the initial classifier
configuration at intermediate-tape position zero. -/
private lemma runFrom_firstHalt_classify {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).runFrom
        (compositionFirstCfg tm₀ tm₁ cfg) (cfg.output.length + 2) =
      compositionIntermediateCfg tm₀ tm₁ cfg
        (.classify tm₁.q₀ .right) 0 := by
  rw [show cfg.output.length + 2 = (cfg.output.length + 1) + 1 by omega,
    (comp tm₀ tm₁).runFrom_succ_eq_step']
  rw [runFrom_firstHalt_rewind tm₀ tm₁ cfg hhalt cfg.output.length le_rfl]
  rw [show (cfg.output.length : ℤ) - 1 - cfg.output.length = -1 by omega]
  simpa using step_rewind_none tm₀ tm₁ cfg (-1) (by rfl)

/-!
## Virtual input movement and classification
-/

/-- The virtual work-tape position follows the clamped native input-head movement. -/
private lemma compositionVirtualInputPos_move {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType) :
    compositionVirtualInputPos (moveInputPos p move) =
      compositionVirtualInputPos p + (compositionInputMode p).move move := by
  cases move with
  | zero => simp [CompositionInputMode.move]
  | neg =>
      by_cases hleft : p = 0
      · rw [hleft]
        simp [compositionInputMode, CompositionInputMode.move]
      · rw [moveInputPos_neg_of_ne_left p hleft]
        unfold compositionVirtualInputPos
        have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => hleft (Fin.ext hz))
        by_cases hright : p.val = input.length + 1 <;>
          simp [compositionInputMode, hleft, hright, CompositionInputMode.move] <;> omega
  | pos =>
      by_cases hright : p.val = input.length + 1
      · have hp : p = ⟨input.length + 1, by omega⟩ := Fin.ext hright
        rw [hp]
        simp [compositionInputMode, CompositionInputMode.move]
      · rw [moveInputPos_pos_of_ne_right p hright]
        unfold compositionVirtualInputPos
        by_cases hleft : p = 0 <;>
          simp [compositionInputMode, hleft, hright, CompositionInputMode.move]

/-- The boundary hint selected before a move is left whenever the resulting native position is
the left boundary. -/
private lemma compositionNextBoundary_eq_left {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType)
    (hmove : moveInputPos p move = 0) :
    (compositionInputMode p).nextBoundary move = .left := by
  cases move with
  | zero =>
      have hp : p = 0 := by simpa using hmove
      simp [hp, compositionInputMode, CompositionInputMode.nextBoundary]
  | neg =>
      by_cases hp : p = 0
      · simp [hp, compositionInputMode, CompositionInputMode.nextBoundary]
      · by_cases hright : p.val = input.length + 1 <;>
          simp [hp, hright, compositionInputMode, CompositionInputMode.nextBoundary]
  | pos =>
      by_cases hright : p.val = input.length + 1
      · have hp : p = ⟨input.length + 1, by omega⟩ := Fin.ext hright
        rw [hp] at hmove
        simp at hmove
      · rw [moveInputPos_pos_of_ne_right p hright] at hmove
        have hp := congrArg Fin.val hmove
        simp at hp

/-- The boundary hint selected before a move is right whenever the resulting native position is
the right boundary. -/
private lemma compositionNextBoundary_eq_right {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType)
    (hmove : (moveInputPos p move).val = input.length + 1) :
    (compositionInputMode p).nextBoundary move = .right := by
  cases move with
  | zero =>
      have hright : p.val = input.length + 1 := by simpa using hmove
      have hleft : p ≠ 0 := by
        intro h
        rw [h] at hright
        simp at hright
      simp [compositionInputMode, hright, hleft, CompositionInputMode.nextBoundary]
  | pos =>
      by_cases hright : p.val = input.length + 1
      · have hleft : p ≠ 0 := by
          intro h
          rw [h] at hright
          simp at hright
        simp [compositionInputMode, hright, hleft, CompositionInputMode.nextBoundary]
      · by_cases hleft : p = 0 <;>
          simp [compositionInputMode, hright, hleft, CompositionInputMode.nextBoundary]
  | neg =>
      by_cases hleft : p = 0
      · rw [hleft] at hmove
        simp at hmove
      · rw [moveInputPos_neg_of_ne_left p hleft] at hmove
        simp at hmove
        have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => hleft (Fin.ext hz))
        omega

/-- Classifying the canonical intermediate tape recovers a native input-head mode, provided the
boundary hint agrees at the two blank boundary cells. -/
private lemma Composition.classifyMode_listTape {input : List Symbol}
    (p : Fin (input.length + 2)) (boundary : CompositionBoundary)
    (hleft : p = 0 → boundary = .left)
    (hright : p.val = input.length + 1 → boundary = .right) :
    Composition.classifyMode
      (listTape input (compositionVirtualInputPos p)) boundary =
      compositionInputMode p := by
  by_cases hp0 : p = 0
  · have hb := hleft hp0
    rw [hp0]
    have hv : compositionVirtualInputPos (0 : Fin (input.length + 2)) = -1 := by
      unfold compositionVirtualInputPos
      simp
    rw [hv]
    simp [Composition.classifyMode, compositionInputMode, hb, CompositionBoundary.inputMode]
    rfl
  · by_cases hpr : p.val = input.length + 1
    · have hb := hright hpr
      have hp : p = ⟨input.length + 1, by omega⟩ := Fin.ext hpr
      rw [hp]
      have hv : compositionVirtualInputPos
          (⟨input.length + 1, by omega⟩ : Fin (input.length + 2)) = input.length := by
        unfold compositionVirtualInputPos
        omega
      rw [hv]
      simp [Composition.classifyMode, compositionInputMode, hb, CompositionBoundary.inputMode]
    · have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => hp0 (Fin.ext hz))
      have hi : p.val - 1 < input.length := by omega
      have hv : compositionVirtualInputPos p = (p.val - 1 : ℕ) := by
        unfold compositionVirtualInputPos
        omega
      rw [hv]
      simp [Composition.classifyMode, compositionInputMode, hp0, hpr, hi]

/-- Classifying the intermediate cell reached by a virtual move recovers the native clamped
input-head mode after that move. -/
private lemma Composition.classifyMode_move {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType) :
    Composition.classifyMode
      (listTape input
        (compositionVirtualInputPos p + (compositionInputMode p).move move))
      ((compositionInputMode p).nextBoundary move) =
      compositionInputMode (moveInputPos p move) := by
  rw [← compositionVirtualInputPos_move p move]
  apply Composition.classifyMode_listTape
  · exact compositionNextBoundary_eq_left p move
  · exact compositionNextBoundary_eq_right p move

/-- The classifying half of a simulated second-machine step only restores the native input mode. -/
private lemma step_compositionClassifyCfg
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (boundary : CompositionBoundary)
    (hmode :
      Composition.classifyMode
        (listTape secondInput (compositionVirtualInputPos secondCfg.inputPos)) boundary =
        compositionInputMode secondCfg.inputPos) :
    (comp tm₀ tm₁).step
        (compositionClassifyCfg tm₀ tm₁ firstCfg secondCfg boundary) =
      compositionSecondCfg tm₀ tm₁ firstCfg secondCfg := by
  cases hstate : secondCfg.state with
  | none =>
      simp [step, compositionClassifyCfg, compositionSecondCfg, hstate]
  | some q =>
      apply Cfg.ext
      · simp [step, compositionClassifyCfg, compositionSecondCfg, comp, hstate,
          Cfg.workTapeSymbols, compositionIntermediateTapeIdx, hmode]
      · simp [step, compositionClassifyCfg, compositionSecondCfg, comp, hstate]
      · funext i p
        simp [step, compositionClassifyCfg, compositionSecondCfg, comp, hstate,
          Composition.idleWorkAction]
      · funext i
        simp [step, compositionClassifyCfg, compositionSecondCfg, comp, hstate,
          Composition.idleWorkAction]
      · simp [step, compositionClassifyCfg, compositionSecondCfg, comp, hstate]

/-- After rewinding, one classification step enters the second machine's initial configuration. -/
private lemma step_compositionIntermediateCfg_classify_init {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    (comp tm₀ tm₁).step
        (compositionIntermediateCfg tm₀ tm₁ cfg
          (.classify tm₁.q₀ .right) 0) =
      compositionSecondCfg tm₀ tm₁ cfg (tm₁.initCfg cfg.output) := by
  rw [compositionIntermediateCfg_classify_init]
  apply step_compositionClassifyCfg
  cases cfg.output <;>
    simp [Composition.classifyMode, compositionInputMode, compositionVirtualInputPos,
      CompositionBoundary.inputMode, listTape]

/-- Starting from a halted first-machine configuration, rewinding and initialization take exactly
the output length plus three steps. -/
private lemma runFrom_firstHalt_to_secondInit {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).runFrom
        (compositionFirstCfg tm₀ tm₁ cfg) (cfg.output.length + 3) =
      compositionSecondCfg tm₀ tm₁ cfg (tm₁.initCfg cfg.output) := by
  rw [show cfg.output.length + 3 = (cfg.output.length + 2) + 1 by omega,
    (comp tm₀ tm₁).runFrom_succ_eq_step', runFrom_firstHalt_classify tm₀ tm₁ cfg hhalt]
  exact step_compositionIntermediateCfg_classify_init tm₀ tm₁ cfg

/-- Running the first phase and rewinding its output reaches the second machine's initial
configuration. -/
private lemma runFrom_to_secondInit (input : List Symbol) (u : ℕ)
    (hhalt : (tm₀.runFrom (tm₀.initCfg input) u).state = none)
    (hactive : ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none) :
    (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
        (u + ((tm₀.runFrom (tm₀.initCfg input) u).output.length + 3)) =
      compositionSecondCfg tm₀ tm₁
        (tm₀.runFrom (tm₀.initCfg input) u)
        (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) := by
  rw [(comp tm₀ tm₁).runFrom_add, runFrom_firstPhase tm₀ tm₁ input u hactive,
    runFrom_firstHalt_to_secondInit tm₀ tm₁ _ hhalt]

/-!
## Second-phase simulation
-/

/-- The moving half of a simulated second-machine step performs all native tape actions and enters
the classifier state. -/
private lemma step_compositionSecondCfg
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (q : State₁) (hstate : secondCfg.state = some q) :
    (comp tm₀ tm₁).step
        (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg) =
      compositionClassifyCfg tm₀ tm₁ firstCfg (tm₁.step secondCfg)
        ((compositionInputMode secondCfg.inputPos).nextBoundary
          (tm₁.tr q secondCfg.inputSymbol secondCfg.workTapeSymbols).inputMove) := by
  have hinput := compositionSecondCfg_inputSymbol
    tm₀ tm₁ firstCfg secondCfg
  have hwork := Composition.secondWorkSymbols_compositionSecondCfg
    tm₀ tm₁ firstCfg secondCfg
  unfold step
  rw [show
    (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg).state =
      some (.second q (compositionInputMode secondCfg.inputPos)) by
        simp [compositionSecondCfg, hstate]]
  rw [hstate]
  simp only [comp]
  rw [hinput, hwork]
  generalize htr : tm₁.tr q secondCfg.inputSymbol secondCfg.workTapeSymbols = out
  obtain ⟨inputMove, workActions, outS, q'⟩ := out
  simp only [htr]
  apply Cfg.ext
  · cases q' <;> rfl
  · simp [compositionClassifyCfg, compositionSecondCfg]
  · funext i p
    by_cases hfirst : i.val < k₀
    · have hmiddle : i.val ≠ k₀ := by omega
      have hsecond : ¬k₀ + 1 ≤ i.val := by omega
      simp [compositionClassifyCfg, compositionSecondCfg, Composition.secondWorkActions,
        hstate, hfirst, hmiddle, hsecond, Composition.idleWorkAction]
    · by_cases hmiddle : i.val = k₀
      · simp [compositionClassifyCfg, compositionSecondCfg, Composition.secondWorkActions,
          hstate, hmiddle]
      · have hsecond : k₀ + 1 ≤ i.val := by omega
        let j : Fin k₁ := ⟨i.val - (k₀ + 1), by
          have hi := i.isLt
          simp only [compositionTapeCount] at hi
          omega⟩
        cases hwrite : (workActions j).1 with
        | none =>
            simp [compositionClassifyCfg, compositionSecondCfg,
              Composition.secondWorkActions, hstate, hfirst, hmiddle,
              hsecond, j, hwrite]
        | some s =>
            simp [compositionClassifyCfg, compositionSecondCfg,
              Composition.secondWorkActions, hstate, hfirst, hmiddle, hsecond, j, hwrite]
  · funext i
    by_cases hfirst : i.val < k₀
    · have hmiddle : i.val ≠ k₀ := by omega
      have hsecond : ¬k₀ + 1 ≤ i.val := by omega
      simp [compositionClassifyCfg, compositionSecondCfg, Composition.secondWorkActions,
        hstate, hfirst, hmiddle, hsecond, Composition.idleWorkAction]
    · by_cases hmiddle : i.val = k₀
      · simp only [compositionSecondCfg, hstate, hmiddle, lt_self_iff_false, ↓reduceDIte,
          Composition.secondWorkActions, ↓reduceIte, compositionClassifyCfg]
        exact (compositionVirtualInputPos_move secondCfg.inputPos inputMove).symm
      · have hsecond : k₀ + 1 ≤ i.val := by omega
        simp [compositionClassifyCfg, compositionSecondCfg, Composition.secondWorkActions,
          hstate, hfirst, hmiddle, hsecond]
  · rfl

/-- One native second-machine step is exactly two steps of the composite machine. -/
private lemma runFrom_two_compositionSecondCfg
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (q : State₁) (hstate : secondCfg.state = some q) :
    (comp tm₀ tm₁).runFrom
        (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg) 2 =
      compositionSecondCfg tm₀ tm₁ firstCfg (tm₁.step secondCfg) := by
  change (comp tm₀ tm₁).step
    ((comp tm₀ tm₁).step (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg)) = _
  rw [step_compositionSecondCfg tm₀ tm₁ firstCfg secondCfg q hstate]
  apply step_compositionClassifyCfg
  unfold step
  rw [hstate]
  generalize htr : tm₁.tr q secondCfg.inputSymbol secondCfg.workTapeSymbols = out
  obtain ⟨inputMove, workActions, outS, q'⟩ := out
  simp only [htr]
  rw [compositionVirtualInputPos_move]
  exact Composition.classifyMode_move secondCfg.inputPos inputMove

/-- Simulation of the second machine, at a cost of two composite steps per native step. -/
private lemma runFrom_secondPhase
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (n : ℕ)
    (hactive : ∀ m < n, (tm₁.runFrom secondCfg m).state ≠ none) :
    (comp tm₀ tm₁).runFrom
        (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg) (2 * n) =
      compositionSecondCfg tm₀ tm₁ firstCfg
        (tm₁.runFrom secondCfg n) := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, runFrom_add]
      rw [ih (fun m hm => hactive m (by omega))]
      cases hstate : (tm₁.runFrom secondCfg n).state with
      | none => exact absurd hstate (hactive n (by omega))
      | some q =>
          simpa only [tm₁.runFrom_succ_eq_step'] using
            runFrom_two_compositionSecondCfg tm₀ tm₁ firstCfg
              (tm₁.runFrom secondCfg n) q hstate

/--
After both component machines halt, the composite machine halts with the output of the second
machine.

If the first machine halts on `input` at exactly time `u` having produced `out₀`, and the second
machine halts on input `out₀` at exactly time `v` having produced `out₁`, then after
`u + (out₀.length + 3) + 2 * v` steps — the first machine's run, a rewind of the intermediate
output, and a two-steps-per-step simulation of the second machine — the composite machine on
`input` has halted with output exactly `out₁`.
-/
theorem comp_haltsWithOutput
    {input out₀ out₁ : List Symbol} {u v : ℕ}
    (hhalt₀ : (tm₀.runFrom (tm₀.initCfg input) u).state = none)
    (hactive₀ : ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none)
    (hout₀ : (tm₀.runFrom (tm₀.initCfg input) u).output = out₀)
    (hhalt₁ : (tm₁.runFrom (tm₁.initCfg out₀) v).state = none)
    (hactive₁ : ∀ m < v, (tm₁.runFrom (tm₁.initCfg out₀) m).state ≠ none)
    (hout₁ : (tm₁.runFrom (tm₁.initCfg out₀) v).output = out₁) :
    ((comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
        (u + (out₀.length + 3) + 2 * v)).state = none ∧
      ((comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
          (u + (out₀.length + 3) + 2 * v)).output = out₁ := by
  subst out₀
  subst out₁
  have hmid :
      (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
          (u + ((tm₀.runFrom (tm₀.initCfg input) u).output.length + 3)) =
        compositionSecondCfg tm₀ tm₁
          (tm₀.runFrom (tm₀.initCfg input) u)
          (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) :=
    runFrom_to_secondInit tm₀ tm₁ input u hhalt₀ hactive₀
  have hfinal :
      (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
          (u + ((tm₀.runFrom (tm₀.initCfg input) u).output.length + 3) + 2 * v) =
        compositionSecondCfg tm₀ tm₁
          (tm₀.runFrom (tm₀.initCfg input) u)
          (tm₁.runFrom
            (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) v) := by
    rw [(comp tm₀ tm₁).runFrom_add ((comp tm₀ tm₁).initCfg input)
      (u + ((tm₀.runFrom (tm₀.initCfg input) u).output.length + 3)) (2 * v)]
    rw [hmid]
    exact runFrom_secondPhase tm₀ tm₁
      (tm₀.runFrom (tm₀.initCfg input) u)
      (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) v hactive₁
  rw [hfinal]
  constructor
  · change Option.map _
      (tm₁.runFrom
        (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) v).state = none
    rw [hhalt₁]
    rfl
  · rfl


/-- The odd-numbered composite steps of the second phase are precisely the intermediate
classifier configurations. -/
private lemma runFrom_secondPhase_odd
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (n : ℕ)
    (hactive : ∀ m ≤ n, (tm₁.runFrom secondCfg m).state ≠ none) :
    ∃ boundary,
      (comp tm₀ tm₁).runFrom
          (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg) (2 * n + 1) =
        compositionClassifyCfg tm₀ tm₁ firstCfg
          (tm₁.runFrom secondCfg (n + 1)) boundary := by
  rw [(comp tm₀ tm₁).runFrom_add
    (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg) (2 * n) 1]
  rw [runFrom_secondPhase tm₀ tm₁ firstCfg secondCfg n
    (fun m hm => hactive m (by omega))]
  obtain ⟨q, hq⟩ : ∃ q, (tm₁.runFrom secondCfg n).state = some q := by
    cases hstate : (tm₁.runFrom secondCfg n).state with
    | none => exact absurd hstate (hactive n le_rfl)
    | some q => exact ⟨q, rfl⟩
  let boundary :=
    (compositionInputMode (tm₁.runFrom secondCfg n).inputPos).nextBoundary
      (tm₁.tr q
        (tm₁.runFrom secondCfg n).inputSymbol
        (tm₁.runFrom secondCfg n).workTapeSymbols).inputMove
  refine ⟨boundary, ?_⟩
  change (comp tm₀ tm₁).step
    (compositionSecondCfg tm₀ tm₁ firstCfg (tm₁.runFrom secondCfg n)) = _
  rw [step_compositionSecondCfg tm₀ tm₁ firstCfg
    (tm₁.runFrom secondCfg n) q hq]
  simp only [runFrom, Function.iterate_succ_apply', boundary]

/-- Final first-component configuration used throughout the resource analysis. -/
@[simp] private abbrev firstFinalCfg
    (tm₀ : MultiTapeTM k₀ Symbol State₀) (input : List Symbol) (u : ℕ) :
    Cfg k₀ Symbol State₀ input :=
  tm₀.runFrom (tm₀.initCfg input) u

/-- A named phase witness for a configuration occurring in a complete composite run. -/
private inductive CompositionCfgPhase
    (tm₀ : MultiTapeTM k₀ Symbol State₀)
    (tm₁ : MultiTapeTM k₁ Symbol State₁)
    (input : List Symbol) (u v : ℕ)
    (cfg : Cfg (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) input) : Prop
  | first (m : ℕ) (hm : m ≤ u)
      (hcfg : cfg = compositionFirstCfg tm₀ tm₁
        (tm₀.runFrom (tm₀.initCfg input) m))
  | rewind (s : ℕ)
      (hs : s ≤ ((firstFinalCfg tm₀ input u).output).length)
      (hcfg : cfg = compositionIntermediateCfg tm₀ tm₁
          (firstFinalCfg tm₀ input u)
          .rewind
          ((((firstFinalCfg tm₀ input u).output).length : ℤ) - 1 - s))
  | initialClassify
      (hcfg : cfg = compositionIntermediateCfg tm₀ tm₁
          (firstFinalCfg tm₀ input u)
          (.classify tm₁.q₀ .right) 0)
  | second (m : ℕ) (hm : m ≤ v)
      (hcfg : cfg = compositionSecondCfg tm₀ tm₁
          (firstFinalCfg tm₀ input u)
          (tm₁.runFrom
            (tm₁.initCfg ((firstFinalCfg tm₀ input u).output)) m))
  | secondClassify (m : ℕ) (hm : m < v) (boundary : CompositionBoundary)
      (hcfg : cfg = compositionClassifyCfg tm₀ tm₁
          (firstFinalCfg tm₀ input u)
          (tm₁.runFrom
            (tm₁.initCfg ((firstFinalCfg tm₀ input u).output)) (m + 1))
          boundary)

/--
Every prefix of a complete composite run is in one of the configurations described by
the first simulation, the rewind, the initial classifier, or an even or odd second-phase step.
-/
private lemma runFrom_composition_cases
    (input : List Symbol) (u v r : ℕ)
    (hhalt₀ :
      (firstFinalCfg tm₀ input u).state = none)
    (hactive₀ :
      ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none)
    (hactive₁ :
      ∀ m < v,
        (tm₁.runFrom
          (tm₁.initCfg ((firstFinalCfg tm₀ input u).output)) m).state ≠ none)
    (hr :
      r ≤ u + (((firstFinalCfg tm₀ input u).output).length + 3) + 2 * v) :
    CompositionCfgPhase tm₀ tm₁ input u v
      ((comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input) r) := by
  by_cases hru : r ≤ u
  · exact .first r hru
      (runFrom_firstPhase tm₀ tm₁ input r
        (fun m hm => hactive₀ m (lt_of_lt_of_le hm hru)))
  · have hur : u < r := Nat.lt_of_not_ge hru
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hur)
    have hdpos : 0 < d := by omega
    have hdle :
        d ≤ ((firstFinalCfg tm₀ input u).output).length + 3 + 2 * v := by
      omega
    by_cases hrewind :
        d ≤ ((firstFinalCfg tm₀ input u).output).length + 1
    · have hcfg :
          (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input) r =
            compositionIntermediateCfg tm₀ tm₁
              (firstFinalCfg tm₀ input u)
              .rewind
              ((((firstFinalCfg tm₀ input u).output).length : ℤ) -
                1 - ((d - 1 : ℕ) : ℤ)) := by
        rw [hd, (comp tm₀ tm₁).runFrom_add
          ((comp tm₀ tm₁).initCfg input) u d]
        rw [runFrom_firstPhase tm₀ tm₁ input u hactive₀]
        conv_lhs => rw [show d = d - 1 + 1 by omega]
        exact runFrom_firstHalt_rewind tm₀ tm₁
          (firstFinalCfg tm₀ input u) hhalt₀ (d - 1) (by omega)
      exact .rewind (d - 1) (by omega) hcfg
    · by_cases hclassify :
          d = ((firstFinalCfg tm₀ input u).output).length + 2
      · have hcfg :
            (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input) r =
              compositionIntermediateCfg tm₀ tm₁
                (firstFinalCfg tm₀ input u)
                (.classify tm₁.q₀ .right) 0 := by
          rw [hd, runFrom_add]
          rw [runFrom_firstPhase tm₀ tm₁ input u hactive₀]
          simpa [hclassify] using
            runFrom_firstHalt_classify tm₀ tm₁
              (firstFinalCfg tm₀ input u) hhalt₀
        exact .initialClassify hcfg
      · have hdsecond :
            ((firstFinalCfg tm₀ input u).output).length + 3 ≤ d := by
          omega
        let e := d - (((firstFinalCfg tm₀ input u).output).length + 3)
        have hde :
            d = ((firstFinalCfg tm₀ input u).output).length + 3 + e := by
          dsimp only [e]
          omega
        have he : e ≤ 2 * v := by omega
        rcases Nat.even_or_odd' e with ⟨m, heven | hodd⟩
        · have hmv : m ≤ v := by omega
          have hcfg :
              (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input) r =
                compositionSecondCfg tm₀ tm₁
                  (firstFinalCfg tm₀ input u)
                  (tm₁.runFrom
                    (tm₁.initCfg
                      ((firstFinalCfg tm₀ input u).output)) m) := by
            rw [hd, hde, heven]
            rw [show
              u + (((firstFinalCfg tm₀ input u).output).length + 3 + 2 * m) =
                (u + (((firstFinalCfg tm₀ input u).output).length + 3)) +
                  2 * m by omega]
            rw [(comp tm₀ tm₁).runFrom_add
              ((comp tm₀ tm₁).initCfg input)
              (u + (((firstFinalCfg tm₀ input u).output).length + 3))
              (2 * m)]
            rw [runFrom_to_secondInit tm₀ tm₁ input u hhalt₀ hactive₀]
            exact runFrom_secondPhase tm₀ tm₁
              (firstFinalCfg tm₀ input u)
              (tm₁.initCfg ((firstFinalCfg tm₀ input u).output)) m
              (fun j hj => hactive₁ j (lt_of_lt_of_le hj hmv))
          exact .second m hmv hcfg
        · have hmv : m < v := by omega
          obtain ⟨boundary, hboundary⟩ :=
            runFrom_secondPhase_odd tm₀ tm₁
              (firstFinalCfg tm₀ input u)
              (tm₁.initCfg ((firstFinalCfg tm₀ input u).output)) m
              (fun j hj => hactive₁ j (lt_of_le_of_lt hj hmv))
          have hcfg :
              (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input) r =
                compositionClassifyCfg tm₀ tm₁
                  (firstFinalCfg tm₀ input u)
                  (tm₁.runFrom
                    (tm₁.initCfg
                      ((firstFinalCfg tm₀ input u).output)) (m + 1))
                  boundary := by
            rw [hd, hde, hodd]
            rw [show
              u + (((firstFinalCfg tm₀ input u).output).length + 3 +
                  (2 * m + 1)) =
                (u + (((firstFinalCfg tm₀ input u).output).length + 3)) +
                  (2 * m + 1) by omega]
            rw [(comp tm₀ tm₁).runFrom_add
              ((comp tm₀ tm₁).initCfg input)
              (u + (((firstFinalCfg tm₀ input u).output).length + 3))
              (2 * m + 1)]
            rw [runFrom_to_secondInit tm₀ tm₁ input u hhalt₀ hactive₀]
            exact hboundary
          exact .secondClassify m hmv boundary hcfg

/-!
## Resource bounds and function-level correctness
-/

namespace Composition

/-- Time bound produced by sequentially composing computations with bounds `T₀` and `T₁`. -/
def timeBound (T₀ T₁ : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * T₀ n + 3 + 2 * T₁ (T₀ n)

/-- Space bound produced by sequential composition, including its intermediate work tape. -/
def spaceBound (T₀ S₀ S₁ : ℕ → ℕ) (n : ℕ) : ℕ :=
  S₀ n + (T₀ n + 2) + S₁ (T₀ n)

/-- Sequential composition preserves monotonicity of time bounds. -/
lemma timeBound_mono {T₀ T₁ : ℕ → ℕ} (hT₀ : Monotone T₀) (hT₁ : Monotone T₁) :
    Monotone (timeBound T₀ T₁) := by
  intro m n hmn
  have hT₀mn := hT₀ hmn
  have hT₁mn := hT₁ hT₀mn
  simp only [timeBound]
  omega

/-- Sequential composition preserves monotonicity of space bounds. -/
lemma spaceBound_mono {T₀ S₀ S₁ : ℕ → ℕ}
    (hT₀ : Monotone T₀) (hS₀ : Monotone S₀) (hS₁ : Monotone S₁) :
    Monotone (spaceBound T₀ S₀ S₁) := by
  intro m n hmn
  have hT₀mn := hT₀ hmn
  have hS₀mn := hS₀ hmn
  have hS₁mn := hS₁ hT₀mn
  simp only [spaceBound]
  omega

end Composition

/-- Decompose composite space usage into the first, intermediate, and second tape blocks. -/
private lemma compositionSpaceUsed_eq
    {input : List Symbol}
    (cfg : Cfg (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) input)
    (t : ℕ) :
    (comp tm₀ tm₁).spaceUsed cfg t =
      (∑ i : Fin k₀, (comp tm₀ tm₁).spaceUsedByTape cfg t
        (compositionFirstTapeIdx k₁ i)) +
      (comp tm₀ tm₁).spaceUsedByTape cfg t
        (compositionIntermediateTapeIdx k₀ k₁) +
      ∑ i : Fin k₁, (comp tm₀ tm₁).spaceUsedByTape cfg t
        (compositionSecondTapeIdx k₀ k₁ i) := by
  unfold spaceUsed
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  congr 1

/-- Every first-component tape position in a complete composite run occurs in the first run. -/
private lemma exists_firstComponent_tapePos_eq
    (input : List Symbol) (u v r : ℕ)
    (hhalt₀ :
      (tm₀.runFrom (tm₀.initCfg input) u).state = none)
    (hactive₀ :
      ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none)
    (hactive₁ :
      ∀ m < v,
        (tm₁.runFrom
          (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) m).state ≠ none)
    (hr :
      r ≤ u + (((tm₀.runFrom (tm₀.initCfg input) u).output).length + 3) + 2 * v)
    (i : Fin k₀) :
    ∃ m ≤ u,
      ((comp tm₀ tm₁).runFrom
        ((comp tm₀ tm₁).initCfg input) r).workTapePos
          (compositionFirstTapeIdx k₁ i) =
        (tm₀.runFrom (tm₀.initCfg input) m).workTapePos i := by
  have hphase := runFrom_composition_cases tm₀ tm₁ input u v r
    hhalt₀ hactive₀ hactive₁ hr
  cases hphase with
  | first m hm hcfg =>
    refine ⟨m, hm, ?_⟩
    rw [hcfg]
    simp [compositionFirstCfg, compositionFirstTapeIdx]
  | rewind _ _ hcfg =>
    refine ⟨u, le_rfl, ?_⟩
    rw [hcfg]
    have hne : i.val ≠ k₀ := by omega
    simp [compositionIntermediateCfg, compositionFirstCfg, compositionFirstTapeIdx, hne]
  | initialClassify hcfg =>
    refine ⟨u, le_rfl, ?_⟩
    rw [hcfg]
    have hne : i.val ≠ k₀ := by omega
    simp [compositionIntermediateCfg, compositionFirstCfg, compositionFirstTapeIdx, hne]
  | second _ _ hcfg =>
    refine ⟨u, le_rfl, ?_⟩
    rw [hcfg]
    simp [compositionSecondCfg, compositionFirstTapeIdx]
  | secondClassify _ _ _ hcfg =>
    refine ⟨u, le_rfl, ?_⟩
    rw [hcfg]
    simp [compositionClassifyCfg, compositionSecondCfg, compositionFirstTapeIdx]

/-- Every second-component tape position in a complete composite run occurs in the second run. -/
private lemma exists_secondComponent_tapePos_eq
    (input : List Symbol) (u v r : ℕ)
    (hhalt₀ :
      (tm₀.runFrom (tm₀.initCfg input) u).state = none)
    (hactive₀ :
      ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none)
    (hactive₁ :
      ∀ m < v,
        (tm₁.runFrom
          (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) m).state ≠ none)
    (hr :
      r ≤ u + (((tm₀.runFrom (tm₀.initCfg input) u).output).length + 3) + 2 * v)
    (i : Fin k₁) :
    ∃ m ≤ v,
      ((comp tm₀ tm₁).runFrom
        ((comp tm₀ tm₁).initCfg input) r).workTapePos
          (compositionSecondTapeIdx k₀ k₁ i) =
        (tm₁.runFrom
          (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) m).workTapePos i := by
  have hphase := runFrom_composition_cases tm₀ tm₁ input u v r
    hhalt₀ hactive₀ hactive₁ hr
  cases hphase with
  | first _ _ hcfg =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [hcfg]
    have hlt : ¬k₀ + 1 + i.val < k₀ := by omega
    have hne : k₀ + 1 + i.val ≠ k₀ := by omega
    simp [compositionFirstCfg, compositionSecondTapeIdx, runFrom, hlt, hne]
  | rewind _ _ hcfg =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [hcfg]
    have hlt : ¬k₀ + 1 + i.val < k₀ := by omega
    have hne : k₀ + 1 + i.val ≠ k₀ := by omega
    simp [compositionIntermediateCfg, compositionFirstCfg, compositionSecondTapeIdx, runFrom,
      hlt, hne]
  | initialClassify hcfg =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [hcfg]
    have hlt : ¬k₀ + 1 + i.val < k₀ := by omega
    have hne : k₀ + 1 + i.val ≠ k₀ := by omega
    simp [compositionIntermediateCfg, compositionFirstCfg, compositionSecondTapeIdx, runFrom,
      hlt, hne]
  | second m hm hcfg =>
    refine ⟨m, hm, ?_⟩
    rw [hcfg]
    have hlt : ¬k₀ + 1 + i.val < k₀ := by omega
    have hne : k₀ + 1 + i.val ≠ k₀ := by omega
    simp [compositionSecondCfg, compositionSecondTapeIdx, hlt, hne]
  | secondClassify m hm _ hcfg =>
    refine ⟨m + 1, by omega, ?_⟩
    rw [hcfg]
    have hlt : ¬k₀ + 1 + i.val < k₀ := by omega
    have hne : k₀ + 1 + i.val ≠ k₀ := by omega
    simp [compositionClassifyCfg, compositionSecondCfg, compositionSecondTapeIdx, hlt, hne]

/-- Throughout a complete composite run, the intermediate head stays between cells `-1` and `u`,
where `u` is the first component's halting time. -/
private lemma compositionIntermediateTapePos_mem_Icc
    (input : List Symbol) (u v r : ℕ)
    (hhalt₀ :
      (tm₀.runFrom (tm₀.initCfg input) u).state = none)
    (hactive₀ :
      ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none)
    (hactive₁ :
      ∀ m < v,
        (tm₁.runFrom
          (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) m).state ≠ none)
    (hr :
      r ≤ u + (((tm₀.runFrom (tm₀.initCfg input) u).output).length + 3) + 2 * v) :
    ((comp tm₀ tm₁).runFrom
      ((comp tm₀ tm₁).initCfg input) r).workTapePos
        (compositionIntermediateTapeIdx k₀ k₁) ∈
      Finset.Icc (-1) (u : ℤ) := by
  have houtput :
      ((tm₀.runFrom (tm₀.initCfg input) u).output).length ≤ u :=
    by simpa using tm₀.runFrom_output_length_le (tm₀.initCfg input) u
  have hphase := runFrom_composition_cases tm₀ tm₁ input u v r
    hhalt₀ hactive₀ hactive₁ hr
  cases hphase with
  | first m hm hcfg =>
    have hmoutput :
        ((tm₀.runFrom (tm₀.initCfg input) m).output).length ≤ m :=
      by simpa using tm₀.runFrom_output_length_le (tm₀.initCfg input) m
    rw [hcfg]
    simp only [compositionFirstCfg, compositionIntermediateTapeIdx_val,
      lt_self_iff_false, ↓reduceDIte, ↓reduceIte, Finset.mem_Icc]
    constructor <;> omega
  | rewind s hs hcfg =>
    rw [hcfg]
    simp only [firstFinalCfg, compositionIntermediateCfg, compositionIntermediateTapeIdx_val,
      ↓reduceIte, Finset.mem_Icc] at hs ⊢
    constructor <;> omega
  | initialClassify hcfg =>
    rw [hcfg]
    simp [compositionIntermediateCfg]
  | second m _ hcfg =>
    have hp :=
      (tm₁.runFrom
        (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) m).inputPos.isLt
    rw [hcfg]
    simp only [firstFinalCfg, compositionSecondCfg, compositionIntermediateTapeIdx_val,
      lt_self_iff_false, ↓reduceDIte, Finset.mem_Icc]
    unfold compositionVirtualInputPos
    constructor <;> omega
  | secondClassify m _ _ hcfg =>
    have hp :=
      (tm₁.runFrom
        (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) (m + 1)).inputPos.isLt
    rw [hcfg]
    simp only [firstFinalCfg, compositionClassifyCfg, compositionSecondCfg,
      compositionIntermediateTapeIdx_val, lt_self_iff_false, ↓reduceDIte,
      Finset.mem_Icc]
    unfold compositionVirtualInputPos
    constructor <;> omega

/-- The intermediate work tape visits at most `u + 2` cells in a complete composite run. -/
private lemma compositionIntermediateSpace_le
    (input : List Symbol) (u v : ℕ)
    (hhalt₀ :
      (tm₀.runFrom (tm₀.initCfg input) u).state = none)
    (hactive₀ :
      ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none)
    (hactive₁ :
      ∀ m < v,
        (tm₁.runFrom
          (tm₁.initCfg ((tm₀.runFrom (tm₀.initCfg input) u).output)) m).state ≠ none) :
    (comp tm₀ tm₁).spaceUsedByTape
        ((comp tm₀ tm₁).initCfg input)
        (u + (((tm₀.runFrom (tm₀.initCfg input) u).output).length + 3) + 2 * v)
        (compositionIntermediateTapeIdx k₀ k₁) ≤
      u + 2 := by
  unfold spaceUsedByTape
  have hsub :
      (comp tm₀ tm₁).visitedByTapeHead
        ((comp tm₀ tm₁).initCfg input)
        (u + (((tm₀.runFrom (tm₀.initCfg input) u).output).length + 3) + 2 * v)
        (compositionIntermediateTapeIdx k₀ k₁) ⊆
      Finset.Icc (-1) (u : ℤ) := by
    intro p hp
    simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    exact compositionIntermediateTapePos_mem_Icc tm₀ tm₁ input u v r
      hhalt₀ hactive₀ hactive₁ (by omega)
  calc ((comp tm₀ tm₁).visitedByTapeHead
        ((comp tm₀ tm₁).initCfg input)
        (u + (((tm₀.runFrom (tm₀.initCfg input) u).output).length + 3) + 2 * v)
        (compositionIntermediateTapeIdx k₀ k₁)).card
      ≤ (Finset.Icc (-1) (u : ℤ)).card := Finset.card_le_card hsub
    _ = u + 2 := by
        rw [Int.card_Icc]
        omega

/--
Function composition for deterministic multi-tape Turing machines.

The composite runs the first machine, rewinds its output in linear time, and simulates each step
of the second machine in two steps. Its first and second work-tape blocks use the respective
component space bounds, while the intermediate tape visits at most `T₀ n + 2` cells.

The monotonicity hypotheses on `T₁` and `S₁` allow the second component's bounds to be evaluated
at the first component's time bound, which also bounds the intermediate output length.
-/
theorem comp_computesFunInTimeAndSpace
    {IOSymbol : Type*}
    {f g : List IOSymbol → List IOSymbol}
    (embedding : IOSymbol ↪ Symbol)
    {T₀ S₀ T₁ S₁ : ℕ → ℕ}
    (h₀ : ComputesFunInTimeAndSpace tm₀ f embedding T₀ S₀)
    (h₁ : ComputesFunInTimeAndSpace tm₁ g embedding T₁ S₁)
    (hT₁ : Monotone T₁)
    (hS₁ : Monotone S₁) :
    ComputesFunInTimeAndSpace
      (comp tm₀ tm₁) (g ∘ f) embedding
      (Composition.timeBound T₀ T₁)
      (Composition.spaceBound T₀ S₀ S₁) := by
  intro input
  obtain ⟨t₀, ht₀, s₀, hs₀, hhalt₀', hout₀, hspace₀⟩ := h₀ input
  obtain ⟨u, hut₀, hhaltu, hactiveu⟩ :=
    exists_minimal_halting_time tm₀ (tm₀.initCfg (input.map embedding)) t₀ hhalt₀'
  have hfirstOutput :
      (tm₀.runFrom (tm₀.initCfg (input.map embedding)) u).output =
        (f input).map embedding := by
    rw [← hout₀]
    exact (tm₀.runFrom_output_eq_of_halt _ hut₀ hhaltu).symm
  have hfirstOutputLength :
      ((tm₀.runFrom (tm₀.initCfg (input.map embedding)) u).output).length =
        (f input).length := by
    rw [hfirstOutput, List.length_map]
  have hfirstOutputLength_le_u : (f input).length ≤ u := by
    rw [← hfirstOutputLength]
    simpa using tm₀.runFrom_output_length_le (tm₀.initCfg (input.map embedding)) u
  have hu_le_T₀ : u ≤ T₀ input.length := le_trans hut₀ ht₀
  have hfirstOutputLength_le_T₀ : (f input).length ≤ T₀ input.length :=
    le_trans hfirstOutputLength_le_u hu_le_T₀
  obtain ⟨t₁, ht₁, s₁, hs₁, hhalt₁', hout₁, hspace₁⟩ := h₁ (f input)
  obtain ⟨v, hvt₁, hhaltv, hactivev⟩ :=
    exists_minimal_halting_time tm₁
      (tm₁.initCfg ((f input).map embedding)) t₁ hhalt₁'
  have hsecondOutput :
      (tm₁.runFrom (tm₁.initCfg ((f input).map embedding)) v).output =
        (g (f input)).map embedding := by
    rw [← hout₁]
    exact (tm₁.runFrom_output_eq_of_halt _ hvt₁ hhaltv).symm
  have hv_le_T₁ : v ≤ T₁ (f input).length := le_trans hvt₁ ht₁
  have hv_le_bound : v ≤ T₁ (T₀ input.length) :=
    le_trans hv_le_T₁ (hT₁ hfirstOutputLength_le_T₀)
  have hactivev_firstOutput :
      ∀ m < v,
        (tm₁.runFrom
          (tm₁.initCfg
            ((tm₀.runFrom (tm₀.initCfg (input.map embedding)) u).output)) m).state ≠ none := by
    rw [hfirstOutput]
    exact hactivev
  have hhaltv_firstOutput :
      (tm₁.runFrom
        (tm₁.initCfg
          ((tm₀.runFrom (tm₀.initCfg (input.map embedding)) u).output)) v).state = none := by
    rw [hfirstOutput]
    exact hhaltv
  let totalTime := u + ((f input).length + 3) + 2 * v
  have htotalTime_le :
      totalTime ≤ Composition.timeBound T₀ T₁ input.length := by
    dsimp only [totalTime, Composition.timeBound]
    omega
  have htotalTime_eq :
      totalTime =
        u +
          (((tm₀.runFrom (tm₀.initCfg (input.map embedding)) u).output).length + 3) +
          2 * v := by
    dsimp only [totalTime]
    rw [hfirstOutputLength]
  have hcomp :=
    comp_haltsWithOutput tm₀ tm₁ (input := input.map embedding)
      hhaltu hactiveu rfl hhaltv_firstOutput hactivev_firstOutput rfl
  have hfinalState :
      ((comp tm₀ tm₁).runFrom
        ((comp tm₀ tm₁).initCfg (input.map embedding)) totalTime).state = none := by
    rw [htotalTime_eq]
    exact hcomp.1
  have hfinalOutput :
      ((comp tm₀ tm₁).runFrom
          ((comp tm₀ tm₁).initCfg (input.map embedding)) totalTime).output =
        (g (f input)).map embedding := by
    rw [htotalTime_eq, hcomp.2, hfirstOutput]
    exact hsecondOutput
  have hfirstSpace :
      (∑ i : Fin k₀, (comp tm₀ tm₁).spaceUsedByTape
        ((comp tm₀ tm₁).initCfg (input.map embedding)) totalTime
        (compositionFirstTapeIdx k₁ i)) ≤
      tm₀.spaceUsed (tm₀.initCfg (input.map embedding)) u := by
    unfold spaceUsed
    apply Finset.sum_le_sum
    intro i _
    apply spaceUsedByTape_le_of_positions
      (comp tm₀ tm₁) tm₀
      ((comp tm₀ tm₁).initCfg (input.map embedding))
      (tm₀.initCfg (input.map embedding))
      totalTime u (compositionFirstTapeIdx k₁ i) i
    intro r hr
    exact exists_firstComponent_tapePos_eq tm₀ tm₁ (input.map embedding) u v r
      hhaltu hactiveu hactivev_firstOutput
      (by rw [← htotalTime_eq]; exact hr) i
  have hmiddleSpace :
      (comp tm₀ tm₁).spaceUsedByTape
        ((comp tm₀ tm₁).initCfg (input.map embedding)) totalTime
        (compositionIntermediateTapeIdx k₀ k₁) ≤ u + 2 := by
    rw [htotalTime_eq]
    exact compositionIntermediateSpace_le tm₀ tm₁ (input.map embedding) u v
      hhaltu hactiveu hactivev_firstOutput
  have hsecondTapeBlock :
      (∑ i : Fin k₁, (comp tm₀ tm₁).spaceUsedByTape
        ((comp tm₀ tm₁).initCfg (input.map embedding)) totalTime
        (compositionSecondTapeIdx k₀ k₁ i)) ≤
      tm₁.spaceUsed
        (tm₁.initCfg
          ((tm₀.runFrom (tm₀.initCfg (input.map embedding)) u).output)) v := by
    unfold spaceUsed
    apply Finset.sum_le_sum
    intro i _
    apply spaceUsedByTape_le_of_positions
      (comp tm₀ tm₁) tm₁
      ((comp tm₀ tm₁).initCfg (input.map embedding))
      (tm₁.initCfg
        ((tm₀.runFrom (tm₀.initCfg (input.map embedding)) u).output))
      totalTime v (compositionSecondTapeIdx k₀ k₁ i) i
    intro r hr
    exact exists_secondComponent_tapePos_eq tm₀ tm₁ (input.map embedding) u v r
      hhaltu hactiveu hactivev_firstOutput
      (by rw [← htotalTime_eq]; exact hr) i
  have hspace₀_le :
      tm₀.spaceUsed (tm₀.initCfg (input.map embedding)) u ≤ S₀ input.length := by
    calc
      tm₀.spaceUsed (tm₀.initCfg (input.map embedding)) u
          ≤ tm₀.spaceUsed (tm₀.initCfg (input.map embedding)) t₀ :=
            spaceUsed_mono tm₀ _ hut₀
      _ = s₀ := hspace₀
      _ ≤ S₀ input.length := hs₀
  have hspace₁_le :
      tm₁.spaceUsed (tm₁.initCfg ((f input).map embedding)) v ≤
        S₁ (T₀ input.length) := by
    calc
      tm₁.spaceUsed (tm₁.initCfg ((f input).map embedding)) v
          ≤ tm₁.spaceUsed (tm₁.initCfg ((f input).map embedding)) t₁ :=
            spaceUsed_mono tm₁ _ hvt₁
      _ = s₁ := hspace₁
      _ ≤ S₁ (f input).length := hs₁
      _ ≤ S₁ (T₀ input.length) := hS₁ hfirstOutputLength_le_T₀
  have hcompositeSpace_le :
      (comp tm₀ tm₁).spaceUsed
          ((comp tm₀ tm₁).initCfg (input.map embedding)) totalTime ≤
        Composition.spaceBound T₀ S₀ S₁ input.length := by
    unfold Composition.spaceBound
    rw [compositionSpaceUsed_eq]
    have hsecondTapeBlock_le :
        (∑ i : Fin k₁, (comp tm₀ tm₁).spaceUsedByTape
          ((comp tm₀ tm₁).initCfg (input.map embedding)) totalTime
          (compositionSecondTapeIdx k₀ k₁ i)) ≤
        tm₁.spaceUsed (tm₁.initCfg ((f input).map embedding)) v := by
      rw [← hfirstOutput]
      exact hsecondTapeBlock
    omega
  refine ⟨totalTime, htotalTime_le,
    (comp tm₀ tm₁).spaceUsed
      ((comp tm₀ tm₁).initCfg (input.map embedding)) totalTime,
    hcompositeSpace_le, hfinalState, ?_, rfl⟩
  simpa only [Function.comp_apply] using hfinalOutput


end Correctness

end MultiTapeTM

end Turing
