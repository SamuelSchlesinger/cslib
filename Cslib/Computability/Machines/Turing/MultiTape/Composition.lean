/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

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

/-- A work-tape action that neither writes nor moves. -/
def idleWorkAction : Option (Option Symbol) × SignType := (none, 0)

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

/-- Read the work symbols seen by the first component machine. -/
def compositionFirstWorkSymbols
    (work : Fin (compositionTapeCount k₀ k₁) → Option Symbol) :
    Fin k₀ → Option Symbol :=
  fun i => work (compositionFirstTapeIdx k₁ i)

/-- Read the work symbols seen by the second component machine. -/
def compositionSecondWorkSymbols
    (work : Fin (compositionTapeCount k₀ k₁) → Option Symbol) :
    Fin k₁ → Option Symbol :=
  fun i => work (compositionSecondTapeIdx k₀ k₁ i)

/-- Embed the first component's work actions and redirect its output to the intermediate tape. -/
def compositionFirstWorkActions
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
def compositionMoveIntermediate (move : SignType) :
    Fin (compositionTapeCount k₀ k₁) →
      Option (Option Symbol) × SignType :=
  fun i => if i.val = k₀ then (none, move) else idleWorkAction

/-- Embed the second component's work actions and move the intermediate virtual-input tape. -/
def compositionSecondWorkActions
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
def compositionClassifyMode
    (cell : Option Symbol)
    (boundary : CompositionBoundary) : CompositionInputMode :=
  if cell.isSome then .inside else boundary.inputMode

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
        let out := tm₀.tr q₀ input (compositionFirstWorkSymbols work)
        {
          inputMove := out.inputMove
          workActions := compositionFirstWorkActions out.workActions out.outS
          outS := none
          q' := some (match out.q' with
            | some q' => .first q'
            | none => .rewindStart)
        }
    | .rewindStart =>
        {
          inputMove := 0
          workActions := compositionMoveIntermediate (-1)
          outS := none
          q' := some .rewind
        }
    | .rewind =>
        if (work (compositionIntermediateTapeIdx k₀ k₁)).isSome then
          {
            inputMove := 0
            workActions := compositionMoveIntermediate (-1)
            outS := none
            q' := some .rewind
          }
        else
          {
            inputMove := 0
            workActions := compositionMoveIntermediate 1
            outS := none
            q' := some (.classify tm₁.q₀ .right)
          }
    | .second q₁ mode =>
        let inputMove := mode.move
        let out := tm₁.tr q₁
          (if mode = .inside then work (compositionIntermediateTapeIdx k₀ k₁) else none)
          (compositionSecondWorkSymbols work)
        {
          inputMove := 0
          workActions := compositionSecondWorkActions (inputMove out.inputMove) out.workActions
          outS := out.outS
          q' := out.q'.map fun q' => .classify q' (mode.nextBoundary out.inputMove)
        }
    | .classify q₁ boundary =>
        {
          inputMove := 0
          workActions := fun _ => idleWorkAction
          outS := none
          q' := some (.second q₁
            (compositionClassifyMode (work (compositionIntermediateTapeIdx k₀ k₁)) boundary))
        }

section Correctness

variable
    (tm₀ : MultiTapeTM k₀ Symbol State₀)
    (tm₁ : MultiTapeTM k₁ Symbol State₁)

/-!
## First-phase simulation
-/

/-- Embed a first-machine configuration into the first phase of the composite machine, given the
output `out` that the first machine has produced so far. -/
private def compositionFirstCfg
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input)
    (out : List Symbol) :
    Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input where
  state := match cfg.state with
    | some q => some (.first q)
    | none => some .rewindStart
  inputPos := cfg.inputPos
  workTapes i :=
    if h : i.val < k₀ then
      cfg.workTapes ⟨i, h⟩
    else if i.val = k₀ then
      listTape out
    else
      fun _ => none
  workTapePos i :=
    if h : i.val < k₀ then cfg.workTapePos ⟨i, h⟩
    else if i.val = k₀ then out.length
    else 0

/-- The first-phase embedding sends an initial configuration to the composite initial
configuration. -/
private lemma compositionFirstCfg_initCfg (input : List Symbol) :
    compositionFirstCfg tm₀ tm₁ (tm₀.initCfg input) [] =
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

/-- The first-phase embedding preserves the symbol read from the real input. -/
@[simp]
private lemma compositionFirstCfg_inputSymbol {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) :
    (compositionFirstCfg tm₀ tm₁ cfg out).inputSymbol = cfg.inputSymbol := rfl

/-- The first-phase embedding preserves every symbol read from a first-machine work tape. -/
private lemma compositionFirstWorkSymbols_firstCfg {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) :
    compositionFirstWorkSymbols
      (compositionFirstCfg tm₀ tm₁ cfg out).workTapeSymbols =
      cfg.workTapeSymbols := by
  funext i
  simp [compositionFirstWorkSymbols, Cfg.workTapeSymbols, compositionFirstCfg,
    compositionFirstTapeIdx]

/-- One first-machine step is one composite first-phase step. A halt of the first machine enters
the rewind phase instead of halting the composite machine. -/
private lemma step_compositionFirstCfg {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol)
    (hactive : cfg.state ≠ none) :
    (comp tm₀ tm₁).step (compositionFirstCfg tm₀ tm₁ cfg out) =
      compositionFirstCfg tm₀ tm₁ (tm₀.step cfg)
        (out ++ (tm₀.outputSymbol cfg).toList) := by
  cases hstate : cfg.state with
  | none => exact absurd hstate hactive
  | some q =>
      have hinput := compositionFirstCfg_inputSymbol tm₀ tm₁ cfg out
      have hwork := compositionFirstWorkSymbols_firstCfg tm₀ tm₁ cfg out
      rw [show tm₀.outputSymbol cfg =
        (tm₀.tr q cfg.inputSymbol cfg.workTapeSymbols).outS by
          simp [outputSymbol, hstate]]
      unfold step
      rw [show (compositionFirstCfg tm₀ tm₁ cfg out).state =
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
              simp [compositionFirstCfg, compositionFirstWorkActions, hfirst, hwrite]
          | some s =>
              by_cases hp : p = cfg.workTapePos ⟨i.val, hfirst⟩
              · simp [compositionFirstCfg, compositionFirstWorkActions,
                  Function.update_apply, hfirst, hwrite, hp]
              · simp [compositionFirstCfg, compositionFirstWorkActions,
                  hfirst, hwrite, hp]
        · by_cases hmiddle : i.val = k₀
          · cases outS with
            | none =>
                simp [compositionFirstCfg, compositionFirstWorkActions, hmiddle,
                  idleWorkAction]
            | some s =>
                simp [compositionFirstCfg, compositionFirstWorkActions, hmiddle,
                  listTape_append_single]
          · simp [compositionFirstCfg, compositionFirstWorkActions, hfirst, hmiddle,
              idleWorkAction]
      · funext i
        by_cases hfirst : i.val < k₀
        · simp [compositionFirstCfg, compositionFirstWorkActions, hfirst]
        · by_cases hmiddle : i.val = k₀
          · cases outS <;>
              simp [compositionFirstCfg, compositionFirstWorkActions, hmiddle,
                idleWorkAction]
          · simp [compositionFirstCfg, compositionFirstWorkActions, hfirst, hmiddle,
              idleWorkAction]

/-- Simulation of the first component up to a time at which it has not halted earlier. -/
private lemma configs_firstPhase (input : List Symbol) (n : ℕ)
    (hactive : ∀ m < n, (tm₀.configs (tm₀.initCfg input) m).state ≠ none) :
    (comp tm₀ tm₁).configs ((comp tm₀ tm₁).initCfg input) n =
      compositionFirstCfg tm₀ tm₁
        (tm₀.configs (tm₀.initCfg input) n)
        (tm₀.outputString (tm₀.initCfg input) n) := by
  induction n with
  | zero =>
      rw [show tm₀.outputString (tm₀.initCfg input) 0 = [] from rfl]
      exact (compositionFirstCfg_initCfg tm₀ tm₁ input).symm
  | succ n ih =>
      rw [outputString_succ]
      simp only [configs, Function.iterate_succ_apply']
      have ih' := ih (fun m hm => hactive m (by omega))
      simp only [configs] at ih'
      rw [ih']
      exact step_compositionFirstCfg tm₀ tm₁
        (tm₀.configs (tm₀.initCfg input) n)
        (tm₀.outputString (tm₀.initCfg input) n) (hactive n (by omega))

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
private lemma compositionSecondWorkSymbols_secondCfg
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput) :
    compositionSecondWorkSymbols
      (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg).workTapeSymbols =
      secondCfg.workTapeSymbols := by
  funext i
  have hlt : ¬k₀ + 1 + i.val < k₀ := by omega
  have hne : k₀ + 1 + i.val ≠ k₀ := by omega
  simp [compositionSecondWorkSymbols, Cfg.workTapeSymbols, compositionSecondCfg,
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
    (out : List Symbol)
    (state : CompositionState State₀ State₁)
    (pos : ℤ) :
    Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input :=
  { compositionFirstCfg _tm₀ _tm₁ cfg out with
    state := some state
    workTapePos := fun i =>
      if i.val = k₀ then pos
      else (compositionFirstCfg _tm₀ _tm₁ cfg out).workTapePos i }

/-- At position zero, the post-rewind classifier configuration is the classifier half of the
second machine's initial configuration. -/
private lemma compositionIntermediateCfg_classify_init {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) :
    compositionIntermediateCfg tm₀ tm₁ cfg out
        (.classify tm₁.q₀ .right) 0 =
      compositionClassifyCfg tm₀ tm₁ cfg (tm₁.initCfg out) .right := by
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

/-- Entering the rewind phase moves the intermediate head one cell to the left. -/
private lemma step_rewindStart {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).step (compositionFirstCfg tm₀ tm₁ cfg out) =
      compositionIntermediateCfg tm₀ tm₁ cfg out .rewind
        (out.length - 1) := by
  apply Cfg.ext
  · simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt]
  · simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt]
  · funext i p
    by_cases hmiddle : i.val = k₀ <;>
      simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt,
        compositionMoveIntermediate, idleWorkAction, hmiddle]
  · funext i
    by_cases hmiddle : i.val = k₀
    · simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt,
        compositionMoveIntermediate, idleWorkAction, hmiddle]
      omega
    · simp [step, compositionFirstCfg, compositionIntermediateCfg, comp, hhalt,
        compositionMoveIntermediate, idleWorkAction, hmiddle]

/-- One rewind step over a nonblank intermediate cell. -/
private lemma step_rewind_some {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) (pos : ℤ)
    (hcell : (listTape out pos).isSome) :
    (comp tm₀ tm₁).step
        (compositionIntermediateCfg tm₀ tm₁ cfg out .rewind pos) =
      compositionIntermediateCfg tm₀ tm₁ cfg out .rewind (pos - 1) := by
  apply Cfg.ext
  · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
      Cfg.workTapeSymbols, hcell, compositionMoveIntermediate, idleWorkAction]
  · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
      Cfg.workTapeSymbols, hcell]
  · funext i p
    by_cases hmiddle : i.val = k₀ <;>
      simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
        Cfg.workTapeSymbols, hcell, compositionMoveIntermediate, idleWorkAction, hmiddle]
  · funext i
    by_cases hmiddle : i.val = k₀
    · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
        Cfg.workTapeSymbols, hcell, compositionMoveIntermediate, idleWorkAction, hmiddle]
      omega
    · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
        Cfg.workTapeSymbols, hcell, compositionMoveIntermediate, idleWorkAction, hmiddle]

/-- The blank just left of the intermediate output ends rewinding and moves the head to cell
zero for classification. -/
private lemma step_rewind_none {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) (pos : ℤ)
    (hcell : listTape out pos = none) :
    (comp tm₀ tm₁).step
        (compositionIntermediateCfg tm₀ tm₁ cfg out .rewind pos) =
      compositionIntermediateCfg tm₀ tm₁ cfg out
        (.classify tm₁.q₀ .right) (pos + 1) := by
  apply Cfg.ext
  · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
      Cfg.workTapeSymbols, hcell]
  · simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
      Cfg.workTapeSymbols, hcell]
  · funext i p
    by_cases hmiddle : i.val = k₀ <;>
      simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
        Cfg.workTapeSymbols, hcell, compositionMoveIntermediate, idleWorkAction, hmiddle]
  · funext i
    by_cases hmiddle : i.val = k₀ <;>
      simp [step, compositionIntermediateCfg, compositionFirstCfg, comp,
        Cfg.workTapeSymbols, hcell, compositionMoveIntermediate, idleWorkAction, hmiddle]

/-- A canonical list tape is nonblank at every position inside the represented list. -/
private lemma listTape_isSome_of_lt (xs : List Symbol) {r : ℕ} (h : r < xs.length) :
    (listTape xs ((xs.length : ℤ) - 1 - r)).isSome := by
  have hp : (xs.length : ℤ) - 1 - r = (xs.length - 1 - r : ℕ) := by omega
  rw [hp]
  simp [listTape]
  omega

/-- Rewinding scans exactly the cells occupied by the intermediate output. -/
private lemma configs_rewind {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol)
    (r : ℕ) (hr : r ≤ out.length) :
    (comp tm₀ tm₁).configs
        (compositionIntermediateCfg tm₀ tm₁ cfg out .rewind
          ((out.length : ℤ) - 1)) r =
      compositionIntermediateCfg tm₀ tm₁ cfg out .rewind
        ((out.length : ℤ) - 1 - r) := by
  induction r with
  | zero => simp [configs]
  | succ r ih =>
      simp only [configs, Function.iterate_succ_apply']
      have ih' := ih (by omega)
      simp only [configs] at ih'
      rw [ih']
      have hcell :
          (listTape out ((out.length : ℤ) - 1 - r)).isSome := by
        simpa using
          (listTape_isSome_of_lt out
            (r := r) (show r < out.length by omega))
      convert step_rewind_some tm₀ tm₁ cfg out
        ((out.length : ℤ) - 1 - r) hcell using 1
      congr 1
      omega

/-- The prefix of the post-halting phase that consists of entering and running the rewind loop. -/
private lemma configs_firstHalt_rewind {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) (hhalt : cfg.state = none)
    (r : ℕ) (hr : r ≤ out.length) :
    (comp tm₀ tm₁).configs
        (compositionFirstCfg tm₀ tm₁ cfg out) (r + 1) =
      compositionIntermediateCfg tm₀ tm₁ cfg out .rewind
        ((out.length : ℤ) - 1 - r) := by
  rw [show r + 1 = 1 + r by omega, configs_add]
  change (comp tm₀ tm₁).configs
    ((comp tm₀ tm₁).step (compositionFirstCfg tm₀ tm₁ cfg out)) r = _
  rw [step_rewindStart tm₀ tm₁ cfg out hhalt]
  exact configs_rewind tm₀ tm₁ cfg out r hr

/-- The configuration immediately after the rewind loop is the initial classifier
configuration at intermediate-tape position zero. -/
private lemma configs_firstHalt_classify {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).configs
        (compositionFirstCfg tm₀ tm₁ cfg out) (out.length + 2) =
      compositionIntermediateCfg tm₀ tm₁ cfg out
        (.classify tm₁.q₀ .right) 0 := by
  rw [show out.length + 2 = (out.length + 1) + 1 by omega,
    configs_add]
  rw [configs_firstHalt_rewind tm₀ tm₁ cfg out hhalt out.length le_rfl]
  rw [show (out.length : ℤ) - 1 - out.length = -1 by omega]
  change (comp tm₀ tm₁).step
    (compositionIntermediateCfg tm₀ tm₁ cfg out .rewind (-1)) = _
  simpa using step_rewind_none tm₀ tm₁ cfg out (-1) (by rfl)

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
private lemma compositionClassifyMode_listTape {input : List Symbol}
    (p : Fin (input.length + 2)) (boundary : CompositionBoundary)
    (hleft : p = 0 → boundary = .left)
    (hright : p.val = input.length + 1 → boundary = .right) :
    compositionClassifyMode
      (listTape input (compositionVirtualInputPos p)) boundary =
      compositionInputMode p := by
  by_cases hp0 : p = 0
  · have hb := hleft hp0
    rw [hp0]
    have hv : compositionVirtualInputPos (0 : Fin (input.length + 2)) = -1 := by
      unfold compositionVirtualInputPos
      simp
    rw [hv]
    simp [compositionClassifyMode, compositionInputMode, hb, CompositionBoundary.inputMode]
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
      simp [compositionClassifyMode, compositionInputMode, hb, CompositionBoundary.inputMode]
    · have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => hp0 (Fin.ext hz))
      have hi : p.val - 1 < input.length := by omega
      have hv : compositionVirtualInputPos p = (p.val - 1 : ℕ) := by
        unfold compositionVirtualInputPos
        omega
      rw [hv]
      simp [compositionClassifyMode, compositionInputMode, hp0, hpr, hi]

/-- Classifying the intermediate cell reached by a virtual move recovers the native clamped
input-head mode after that move. -/
private lemma compositionClassifyMode_move {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType) :
    compositionClassifyMode
      (listTape input
        (compositionVirtualInputPos p + (compositionInputMode p).move move))
      ((compositionInputMode p).nextBoundary move) =
      compositionInputMode (moveInputPos p move) := by
  rw [← compositionVirtualInputPos_move p move]
  apply compositionClassifyMode_listTape
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
      compositionClassifyMode
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
          idleWorkAction]
      · funext i
        simp [step, compositionClassifyCfg, compositionSecondCfg, comp, hstate,
          idleWorkAction]

/-- After rewinding, one classification step enters the second machine's initial configuration. -/
private lemma step_compositionIntermediateCfg_classify_init {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) :
    (comp tm₀ tm₁).step
        (compositionIntermediateCfg tm₀ tm₁ cfg out
          (.classify tm₁.q₀ .right) 0) =
      compositionSecondCfg tm₀ tm₁ cfg (tm₁.initCfg out) := by
  rw [compositionIntermediateCfg_classify_init]
  apply step_compositionClassifyCfg
  cases out <;>
    simp [compositionClassifyMode, compositionInputMode, compositionVirtualInputPos,
      CompositionBoundary.inputMode, listTape]

/-- Starting from a halted first-machine configuration, rewinding and initialization take exactly
the output length plus three steps. -/
private lemma configs_firstHalt_to_secondInit {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).configs
        (compositionFirstCfg tm₀ tm₁ cfg out) (out.length + 3) =
      compositionSecondCfg tm₀ tm₁ cfg (tm₁.initCfg out) := by
  calc
    (comp tm₀ tm₁).configs
        (compositionFirstCfg tm₀ tm₁ cfg out) (out.length + 3)
        = (comp tm₀ tm₁).configs
            ((comp tm₀ tm₁).step (compositionFirstCfg tm₀ tm₁ cfg out))
            (out.length + 2) := by
              rw [show out.length + 3 = 1 + (out.length + 2) by omega]
              rw [configs_add]
              rfl
    _ = (comp tm₀ tm₁).configs
          (compositionIntermediateCfg tm₀ tm₁ cfg out .rewind
            ((out.length : ℤ) - 1))
          (out.length + 2) := by rw [step_rewindStart _ _ cfg out hhalt]
    _ = (comp tm₀ tm₁).configs
          ((comp tm₀ tm₁).configs
            (compositionIntermediateCfg tm₀ tm₁ cfg out .rewind
              ((out.length : ℤ) - 1))
            out.length) 2 := by rw [← configs_add]
    _ = (comp tm₀ tm₁).configs
          (compositionIntermediateCfg tm₀ tm₁ cfg out .rewind (-1)) 2 := by
            congr 1
            convert configs_rewind tm₀ tm₁ cfg out out.length le_rfl using 1
            congr 1
            omega
    _ = compositionSecondCfg tm₀ tm₁ cfg (tm₁.initCfg out) := by
            change (comp tm₀ tm₁).step
              ((comp tm₀ tm₁).step
                (compositionIntermediateCfg tm₀ tm₁ cfg out .rewind (-1))) = _
            rw [step_rewind_none tm₀ tm₁ cfg out (-1) (by rfl)]
            simpa using step_compositionIntermediateCfg_classify_init tm₀ tm₁ cfg out

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
  have hwork := compositionSecondWorkSymbols_secondCfg
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
      simp [compositionClassifyCfg, compositionSecondCfg, compositionSecondWorkActions,
        hstate, hfirst, hmiddle, hsecond, idleWorkAction]
    · by_cases hmiddle : i.val = k₀
      · simp [compositionClassifyCfg, compositionSecondCfg, compositionSecondWorkActions,
          hstate, hmiddle]
      · have hsecond : k₀ + 1 ≤ i.val := by omega
        let j : Fin k₁ := ⟨i.val - (k₀ + 1), by
          have hi := i.isLt
          simp only [compositionTapeCount] at hi
          omega⟩
        cases hwrite : (workActions j).1 with
        | none =>
            simp [compositionClassifyCfg, compositionSecondCfg,
              compositionSecondWorkActions, hstate, hfirst, hmiddle,
              hsecond, j, hwrite]
        | some s =>
            simp [compositionClassifyCfg, compositionSecondCfg,
              compositionSecondWorkActions, hstate, hfirst, hmiddle, hsecond, j, hwrite]
  · funext i
    by_cases hfirst : i.val < k₀
    · have hmiddle : i.val ≠ k₀ := by omega
      have hsecond : ¬k₀ + 1 ≤ i.val := by omega
      simp [compositionClassifyCfg, compositionSecondCfg, compositionSecondWorkActions,
        hstate, hfirst, hmiddle, hsecond, idleWorkAction]
    · by_cases hmiddle : i.val = k₀
      · simp only [compositionSecondCfg, hstate, hmiddle, lt_self_iff_false, ↓reduceDIte,
          compositionSecondWorkActions, ↓reduceIte, compositionClassifyCfg]
        exact (compositionVirtualInputPos_move secondCfg.inputPos inputMove).symm
      · have hsecond : k₀ + 1 ≤ i.val := by omega
        simp [compositionClassifyCfg, compositionSecondCfg, compositionSecondWorkActions,
          hstate, hfirst, hmiddle, hsecond]

/-- One native second-machine step is exactly two steps of the composite machine. -/
private lemma step_step_compositionSecondCfg
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (q : State₁) (hstate : secondCfg.state = some q) :
    (comp tm₀ tm₁).step
        ((comp tm₀ tm₁).step
          (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg)) =
      compositionSecondCfg tm₀ tm₁ firstCfg (tm₁.step secondCfg) := by
  rw [step_compositionSecondCfg tm₀ tm₁ firstCfg secondCfg q hstate]
  apply step_compositionClassifyCfg
  unfold step
  rw [hstate]
  generalize htr : tm₁.tr q secondCfg.inputSymbol secondCfg.workTapeSymbols = out
  obtain ⟨inputMove, workActions, outS, q'⟩ := out
  simp only [htr]
  rw [compositionVirtualInputPos_move]
  exact compositionClassifyMode_move secondCfg.inputPos inputMove

/-- Simulation of the second machine, at a cost of two composite steps per native step. -/
private lemma configs_secondPhase
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (n : ℕ)
    (hactive : ∀ m < n, (tm₁.configs secondCfg m).state ≠ none) :
    (comp tm₀ tm₁).configs
        (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg) (2 * n) =
      compositionSecondCfg tm₀ tm₁ firstCfg
        (tm₁.configs secondCfg n) := by
  induction n with
  | zero => simp [configs]
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega]
      rw [configs_add]
      rw [ih (fun m hm => hactive m (by omega))]
      obtain ⟨q, hq⟩ : ∃ q, (tm₁.configs secondCfg n).state = some q := by
        cases hstate : (tm₁.configs secondCfg n).state with
        | none => exact absurd hstate (hactive n (by omega))
        | some q => exact ⟨q, rfl⟩
      simp only [configs, Function.iterate_succ_apply']
      exact step_step_compositionSecondCfg tm₀ tm₁ firstCfg
        (tm₁.configs secondCfg n) q hq

/-!
## Output tracking
-/

/-- The composite machine emits an output symbol only in the moving half of a simulated
second-machine step. -/
private lemma outputSymbol_comp_eq_none {input : List Symbol}
    (c : Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input)
    (h : ∀ q mode, c.state ≠ some (.second q mode)) :
    (comp tm₀ tm₁).outputSymbol c = none := by
  unfold outputSymbol
  cases hs : c.state with
  | none => rfl
  | some s =>
      cases s with
      | first q => rfl
      | rewindStart => rfl
      | rewind =>
          by_cases hcell :
              (c.workTapeSymbols (compositionIntermediateTapeIdx k₀ k₁)).isSome <;>
            simp [comp, hcell]
      | second q mode => exact absurd hs (h q mode)
      | classify q boundary => rfl

/-- In the moving half of a simulated second-machine step, the composite machine emits exactly
the second machine's output symbol. -/
private lemma outputSymbol_comp_secondCfg
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput) :
    (comp tm₀ tm₁).outputSymbol (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg) =
      tm₁.outputSymbol secondCfg := by
  have hinput := compositionSecondCfg_inputSymbol tm₀ tm₁ firstCfg secondCfg
  have hwork := compositionSecondWorkSymbols_secondCfg tm₀ tm₁ firstCfg secondCfg
  unfold outputSymbol
  cases hstate : secondCfg.state with
  | none =>
      rw [show (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg).state = none by
        simp [compositionSecondCfg, hstate]]
  | some q =>
      rw [show (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg).state =
        some (.second q (compositionInputMode secondCfg.inputPos)) by
          simp [compositionSecondCfg, hstate]]
      simp only [comp]
      rw [hinput, hwork]

/-- A run of the composite machine that emits no output symbol produces the empty output. -/
private lemma outputString_comp_eq_nil {input : List Symbol}
    (cfg : Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input)
    (t : ℕ)
    (h : ∀ m < t, (comp tm₀ tm₁).outputSymbol ((comp tm₀ tm₁).configs cfg m) = none) :
    (comp tm₀ tm₁).outputString cfg t = [] := by
  simp only [outputString, List.flatMap_eq_nil_iff, List.mem_range]
  intro m hm
  simp [h m hm]

/-- The composite machine produces no output during the first phase. -/
private lemma outputString_firstPhase (input : List Symbol) (n : ℕ)
    (hactive : ∀ m < n, (tm₀.configs (tm₀.initCfg input) m).state ≠ none) :
    (comp tm₀ tm₁).outputString ((comp tm₀ tm₁).initCfg input) n = [] := by
  refine outputString_comp_eq_nil tm₀ tm₁ _ n fun m hm => ?_
  rw [configs_firstPhase tm₀ tm₁ input m fun m' hm' => hactive m' (hm'.trans hm)]
  refine outputSymbol_comp_eq_none tm₀ tm₁ _ fun q mode => ?_
  simp only [compositionFirstCfg]
  cases (tm₀.configs (tm₀.initCfg input) m).state <;> simp

/-- The composite machine produces no output while rewinding and classifying the intermediate
output. -/
private lemma outputString_firstHalt_to_secondInit {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) (out : List Symbol) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).outputString
      (compositionFirstCfg tm₀ tm₁ cfg out) (out.length + 3) = [] := by
  refine outputString_comp_eq_nil tm₀ tm₁ _ _ fun m hm => ?_
  refine outputSymbol_comp_eq_none tm₀ tm₁ _ ?_
  rcases eq_or_ne m 0 with rfl | hm0
  · intro q mode
    simp [configs, compositionFirstCfg, hhalt]
  · rcases Nat.lt_or_ge m (out.length + 2) with hlt | hge
    · obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
      rw [configs_firstHalt_rewind tm₀ tm₁ cfg out hhalt r (by omega)]
      intro q mode
      simp [compositionIntermediateCfg]
    · have hm2 : m = out.length + 2 := by omega
      subst hm2
      rw [configs_firstHalt_classify tm₀ tm₁ cfg out hhalt]
      intro q mode
      simp [compositionIntermediateCfg]

/-- Over the second phase, the composite machine emits exactly the second machine's output. -/
private lemma outputString_secondPhase
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (v : ℕ)
    (hactive : ∀ m < v, (tm₁.configs secondCfg m).state ≠ none) :
    (comp tm₀ tm₁).outputString
        (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg) (2 * v) =
      tm₁.outputString secondCfg v := by
  induction v with
  | zero => simp [outputString]
  | succ v ih =>
      obtain ⟨q, hq⟩ : ∃ q, (tm₁.configs secondCfg v).state = some q := by
        cases hstate : (tm₁.configs secondCfg v).state with
        | none => exact absurd hstate (hactive v (by omega))
        | some q => exact ⟨q, rfl⟩
      have hcfg2v :
          (comp tm₀ tm₁).configs
              (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg) (2 * v) =
            compositionSecondCfg tm₀ tm₁ firstCfg (tm₁.configs secondCfg v) :=
        configs_secondPhase tm₀ tm₁ firstCfg secondCfg v
          (fun m hm => hactive m (by omega))
      rw [show 2 * (v + 1) = 2 * v + 1 + 1 by omega]
      rw [outputString_succ, outputString_succ]
      rw [ih (fun m hm => hactive m (by omega))]
      rw [show (comp tm₀ tm₁).configs
          (compositionSecondCfg tm₀ tm₁ firstCfg secondCfg) (2 * v + 1) =
        compositionClassifyCfg tm₀ tm₁ firstCfg (tm₁.step (tm₁.configs secondCfg v))
          ((compositionInputMode (tm₁.configs secondCfg v).inputPos).nextBoundary
            (tm₁.tr q
              (tm₁.configs secondCfg v).inputSymbol
              (tm₁.configs secondCfg v).workTapeSymbols).inputMove) by
        rw [configs_succ_eq_step', hcfg2v]
        exact step_compositionSecondCfg tm₀ tm₁ firstCfg
          (tm₁.configs secondCfg v) q hq]
      rw [hcfg2v]
      rw [outputSymbol_comp_secondCfg tm₀ tm₁ firstCfg (tm₁.configs secondCfg v)]
      rw [outputSymbol_comp_eq_none tm₀ tm₁ _ (by
        intro q' mode
        cases hstate' : (tm₁.step (tm₁.configs secondCfg v)).state <;>
          simp [compositionClassifyCfg, compositionSecondCfg, hstate'])]
      rw [outputString_succ]
      simp

/--
After both component machines halt, the composite machine halts with the output of the second
machine.

The exact running time consists of the first machine's `u` steps, the intermediate output length
plus three setup steps, and two composite steps for each of the second machine's `v` steps.
-/
theorem comp_haltsWithOutput
    {input : List Symbol} (u v : ℕ)
    (hhalt₀ :
      (tm₀.configs (tm₀.initCfg input) u).state = none)
    (hactive₀ :
      ∀ m < u, (tm₀.configs (tm₀.initCfg input) m).state ≠ none)
    (hhalt₁ :
      (tm₁.configs
        (tm₁.initCfg (tm₀.outputString (tm₀.initCfg input) u)) v).state = none)
    (hactive₁ :
      ∀ m < v,
        (tm₁.configs
          (tm₁.initCfg (tm₀.outputString (tm₀.initCfg input) u)) m).state ≠ none) :
    ((comp tm₀ tm₁).configs ((comp tm₀ tm₁).initCfg input)
        (u + ((tm₀.outputString (tm₀.initCfg input) u).length + 3) + 2 * v)).state =
      none ∧
      (comp tm₀ tm₁).outputString ((comp tm₀ tm₁).initCfg input)
          (u + ((tm₀.outputString (tm₀.initCfg input) u).length + 3) + 2 * v) =
        tm₁.outputString
          (tm₁.initCfg (tm₀.outputString (tm₀.initCfg input) u)) v := by
  have hmid :
      (comp tm₀ tm₁).configs ((comp tm₀ tm₁).initCfg input)
          (u + ((tm₀.outputString (tm₀.initCfg input) u).length + 3)) =
        compositionSecondCfg tm₀ tm₁
          (tm₀.configs (tm₀.initCfg input) u)
          (tm₁.initCfg (tm₀.outputString (tm₀.initCfg input) u)) := by
    rw [(comp tm₀ tm₁).configs_add ((comp tm₀ tm₁).initCfg input) u
      ((tm₀.outputString (tm₀.initCfg input) u).length + 3)]
    rw [configs_firstPhase tm₀ tm₁ input u hactive₀]
    exact configs_firstHalt_to_secondInit tm₀ tm₁
      (tm₀.configs (tm₀.initCfg input) u)
      (tm₀.outputString (tm₀.initCfg input) u) hhalt₀
  constructor
  · rw [(comp tm₀ tm₁).configs_add ((comp tm₀ tm₁).initCfg input)
      (u + ((tm₀.outputString (tm₀.initCfg input) u).length + 3)) (2 * v)]
    rw [hmid]
    rw [configs_secondPhase tm₀ tm₁
      (tm₀.configs (tm₀.initCfg input) u)
      (tm₁.initCfg (tm₀.outputString (tm₀.initCfg input) u)) v hactive₁]
    simp only [compositionSecondCfg]
    rw [hhalt₁]
  · rw [outputString_add_eq_append]
    rw [hmid]
    rw [outputString_secondPhase tm₀ tm₁
      (tm₀.configs (tm₀.initCfg input) u)
      (tm₁.initCfg (tm₀.outputString (tm₀.initCfg input) u)) v hactive₁]
    rw [outputString_add_eq_append]
    rw [configs_firstPhase tm₀ tm₁ input u hactive₀]
    rw [outputString_firstPhase tm₀ tm₁ input u hactive₀]
    rw [outputString_firstHalt_to_secondInit tm₀ tm₁
      (tm₀.configs (tm₀.initCfg input) u)
      (tm₀.outputString (tm₀.initCfg input) u) hhalt₀]
    simp

end Correctness

end MultiTapeTM

end Turing
