/-
Copyright (c) 2026 Christian Reitwiessner, Sam Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Sam Schlesinger
-/

module

public import Mathlib.Data.Part
public import Mathlib.Data.Fintype.Defs
public import Cslib.Foundations.Data.BiTape
public import Cslib.Foundations.Data.BiTape.Canonical
public import Cslib.Foundations.Data.RelatesInSteps
public import Cslib.Computability.Machines.TuringCommon
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Multi-Tape Turing Machines

Defines Turing machines with `k` tapes (bidirectionally infinite, `BiTape`) containing symbols
from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the blank symbol).

## Design

The design of the multi-tape Turing machine follows the one for single-tape Turing machines.
With multiple tapes, it is not immediatly clear how to define the function computed by a Turing
machine. For a single-tape Turing machine, function composition follows easily from composition
of configurations. For multi-tape machines, we focus on composition of tape configurations
(cf. `MultiTapeTM.eval`) and defer the decision of how to define the function computed by a
Turing machine to a later stage.

Since these Turing machines are deterministic, we base the definition of semantics on the sequence
of configurations instead of reachability in a configuration relation, although equivalence
between these two notions is proven.

## Important Declarations

We define a number of structures related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `Cfg`: the configuration of a TM, including internal state and the state of the tapes
* `UsesSpaceUntilStep`: a TM uses at most space `s` when run for up to `t` steps
* `TrasformsTapesInExactTime`: a TM transforms tapes `tapes` to `tapes'` in exactly `t` steps
* `TransformsTapesInTime`: a TM transforms tapes `tapes` to `tapes'` in up to `t` steps
* `TransformsTapes`: a TM transforms tapes `tapes` to `tapes'` in some number of steps
* `TransformsTapesInTimeAndSpace`: a TM transforms tapes `tapes` to `tapes'` in up to `t` steps
  and uses at most `s` space

There are multiple ways to talk about the behaviour of a multi-tape Turing machine:

* `MultiTapeTM.configs`: a sequence of configurations by execution step
* `TransformsTapes`: a TM transforms initial tapes `tapes` and halts with tapes `tapes'`
* `MultiTapeTM.eval`: executes a TM on initial tapes `tapes` and returns the resulting tapes if it
  eventually halts

For machines with designated input and output tapes:

* `MultiTapeTM.HasInputTape`: tape `0` is write-preserving, with a syntactic head-bound
  condition that rules out two consecutive same-direction off-end moves
* `MultiTapeTM.HasOutputTape`: in a machine with at least two tapes, the last tape is write-only
  (`Stmt.IsWriteOnly` on every transition)

The syntactic finite-control reachability machinery underpinning head-boundedness lives in
`Cslib.Computability.Machines.TuringCommon` (`MovesOffBlankInDir`, `MoveThenStays`,
`IsBoundedInDirectionOnTape`).

## TODOs

* Define sequential composition of multi-tape Turing machines.
* Define oracle tapes, and refine space accounting to discount read-only input and write-only
  output tapes from the working-space charge.
* Define the notion of a multi-tape Turing machine computing a function.
* Provide a `Decidable` instance for `IsBoundedInDirectionOnTape` (the existential over reads is
  finite when `Symbol` is `Fintype`, and the reachability relation is finite on a finite state
  set).

-/

open Cslib Relation

namespace Turing

open BiTape StackTape

variable {Symbol : Type}

variable {k : ℕ}

/--
A `k`-tape Turing machine
over the alphabet of `Option Symbol` (where `none` is the blank `BiTape` symbol).
-/
structure MultiTapeTM k Symbol [Inhabited Symbol] [Fintype Symbol] where
  /-- type of state labels -/
  State : Type
  /-- finiteness of the state type -/
  [stateFintype : Fintype State]
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state and a tuple of head symbols to a `Stmt` to invoke
  for each tape and optionally the new state to transition to afterwards (`none` for halt) -/
  tr : State → (Fin k → Option Symbol) → ((Fin k → (Stmt Symbol)) × Option State)

namespace MultiTapeTM

/-!
## Designated input and output tapes

By convention we reserve tape index `0` for a two-way read-only *input* tape and, for
machines with at least two tapes, the last tape index for a write-only *output* tape. The
predicates `HasInputTape` and `HasOutputTape` assert these roles as syntactic properties of
the machine's transition function, so they can be checked without reasoning about the
dynamics of any particular computation.

For the two-way read-only input tape we combine *write-preservation* (tape `0` is never
modified) with a syntactic head-bound condition (`IsBoundedInDirectionOnTape`, defined in
`TuringCommon`): once the head steps off the input in some direction, no chain of stay-moves
on the blank can lead to another off-end step in the same direction.

This suffices to prove a quantitative `±1` bound on the head position over arbitrary traces
from `initCfg`: see `HasInputTape.head_position_bounded`.
-/

variable [Inhabited Symbol] [Fintype Symbol]

/--
`tm` has a *write-preserving, head-bounded input tape* at tape index `0`. This bundles two
conditions on the transition function:

* *read-preservation*: every transition writes back the symbol it read on tape `0`, so tape
  `0` is never modified (see `HasInputTape.step_tape0_eq_optionMove`);
* *syntactic head-bound in both directions* (`IsBoundedInDirectionOnTape`): if the head on
  tape `0` steps off an end of the input in some direction, no chain of stay-moves on the
  blank can lead to another off-end step in the same direction.

The semantic upshot is captured trace-level by `HasInputTape.head_position_bounded`:
along any trace from `initCfg s` with nonempty input, tape `0`'s content matches some
`canonicalInputTape s p` with `p ∈ [-1, s.length]`.
-/
structure HasInputTape {k : ℕ} (tm : MultiTapeTM (k + 1) Symbol) : Prop where
  /-- Every transition writes back the symbol it read on tape `0`. -/
  readPreserving : ∀ q reads, ((tm.tr q reads).1 0).IsReadPreserving (reads 0)
  /-- Once the head steps left off the input, no chain of stay-moves on the blank can lead
  to another left step on the blank. -/
  leftBounded : IsBoundedInDirectionOnTape tm.tr 0 .left
  /-- Once the head steps right off the input, no chain of stay-moves on the blank can lead
  to another right step on the blank. -/
  rightBounded : IsBoundedInDirectionOnTape tm.tr 0 .right

/--
`tm` has a write-only output tape at the last tape index, distinct from tape `0`: on every
transition, the stmt produced on the last tape either writes a blank and stays put or
writes a non-blank symbol and moves the head right.
-/
def HasOutputTape {k : ℕ} (tm : MultiTapeTM (k + 2) Symbol) : Prop :=
  ∀ q reads, ((tm.tr q reads).1 (Fin.last (k + 1))).IsWriteOnly

section Cfg

/-!
## Configurations of a Turing Machine

This section defines the configurations of a Turing machine,
the step function that lets the machine transition from one configuration to the next,
and the intended initial and final configurations.
-/

variable [Inhabited Symbol] [Fintype Symbol] (tm : MultiTapeTM k Symbol)

instance : Inhabited tm.State := ⟨tm.q₀⟩

instance : Fintype tm.State := tm.stateFintype

instance inhabitedStmt : Inhabited (Stmt Symbol) := inferInstance


/--
The configurations of a Turing machine consist of:
an `Option`al state (or none for the halting state),
and a `BiTape` representing the tape contents.
-/
@[ext]
structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.State
  /-- the BiTape contents -/
  tapes : Fin k → BiTape Symbol
deriving Inhabited

/-- The step function corresponding to a `MultiTapeTM`. -/
def step : tm.Cfg → Option tm.Cfg
  | ⟨none, _⟩ =>
    -- If in the halting state, there is no next configuration
    none
  | ⟨some q, tapes⟩ =>
    -- If in state q, perform look up in the transition function
    match tm.tr q (fun i => (tapes i).head) with
    -- and enter a new configuration with state q' (or none for halting)
    -- and tapes updated according to the Stmt
    | ⟨stmts, q'⟩ => some ⟨q', fun i =>
        ((tapes i).write (stmts i).symbol).optionMove (stmts i).movement⟩

/-- Any number of positive steps run from a halting configuration lead to `none`. -/
@[simp, scoped grind =]
lemma step_iter_none_eq_none (tapes : Fin k → BiTape Symbol) (n : ℕ) :
    (Option.bind · tm.step)^[n + 1] (some ⟨none, tapes⟩) = none := by
  rw [Function.iterate_succ_apply]
  induction n with
  | zero => rfl
  | succ n ih => grind [Function.iterate_succ_apply']

/-- A collection of tapes where the first tape contains `s` -/
def firstTape (s : List Symbol) : Fin k → BiTape Symbol
  | ⟨0, _⟩ => BiTape.mk₁ s
  | ⟨_, _⟩ => default

/--
The initial configuration corresponding to a list in the input alphabet.
Note that the entries of the tape constructed by `BiTape.mk₁` are all `some` values.
This is to ensure that distinct lists map to distinct initial configurations.
-/
@[simp]
def initCfg (s : List Symbol) : tm.Cfg :=
  ⟨some tm.q₀, firstTape s⟩

/-- Create an initial configuration given a tuple of tapes. -/
@[simp]
def initCfgTapes (tapes : Fin k → BiTape Symbol) : tm.Cfg :=
  ⟨some tm.q₀, tapes⟩

/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
@[simp]
def haltCfg (s : List Symbol) : tm.Cfg :=
  ⟨none, firstTape s⟩

/-- The final configuration of a Turing machine given a tuple of tapes. -/
@[simp]
def haltCfgTapes (tapes : Fin k → BiTape Symbol) : tm.Cfg :=
  ⟨none, tapes⟩

/-- The sequence of configurations of the Turing machine starting with initial state and
given tapes at step `t`.
If the Turing machine halts, it will eventually get and stay `none` after reaching the halting
configuration. -/
def configs (tapes : Fin k → BiTape Symbol) (t : ℕ) : Option tm.Cfg :=
  (Option.bind · tm.step)^[t] (tm.initCfgTapes tapes)

/--
The space used by a configuration is the sum of the space used by its tapes.
-/
def Cfg.space_used (cfg : tm.Cfg) : ℕ := ∑ i, (cfg.tapes i).space_used

/--
The space used by a configuration grows by at most `k` each step.
-/
lemma Cfg.space_used_step (cfg cfg' : tm.Cfg)
    (hstep : tm.step cfg = some cfg') : cfg'.space_used ≤ cfg.space_used + k := by
  obtain ⟨_ | q, tapes⟩ := cfg
  · simp [step] at hstep
  · simp only [step] at hstep
    generalize h_tr : tm.tr q (fun i => (tapes i).head) = result at hstep
    obtain ⟨stmts, q''⟩ := result
    injection hstep with hstep
    subst hstep
    simp only [space_used]
    trans ∑ i : Fin k, ((tapes i).space_used + 1)
    · refine Finset.sum_le_sum fun i _ => ?_
      unfold BiTape.optionMove
      grind [BiTape.space_used_write, BiTape.space_used_move]
    · simp [Finset.sum_add_distrib]

end Cfg

open Cfg

variable [Inhabited Symbol] [Fintype Symbol]

/--
The `TransitionRelation` corresponding to a `MultiTapeTM k Symbol`
is defined by the `step` function,
which maps a configuration to its next configuration, if it exists.
-/
@[scoped grind =]
def TransitionRelation (tm : MultiTapeTM k Symbol) (c₁ c₂ : tm.Cfg) : Prop :=
  tm.step c₁ = some c₂

/-- A proof that the Turing machine `tm` transforms tapes `tapes` to `tapes'` in exactly
`t` steps. -/
def TransformsTapesInExactTime
    (tm : MultiTapeTM k Symbol)
    (tapes tapes' : Fin k → BiTape Symbol)
    (t : ℕ) : Prop :=
  RelatesInSteps tm.TransitionRelation (tm.initCfgTapes tapes) (tm.haltCfgTapes tapes') t

/-- A proof that the Turing machine `tm` transforms tapes `tapes` to `tapes'` in up to
`t` steps. -/
def TransformsTapesInTime
    (tm : MultiTapeTM k Symbol)
    (tapes tapes' : Fin k → BiTape Symbol)
    (t : ℕ) : Prop :=
  RelatesWithinSteps tm.TransitionRelation (tm.initCfgTapes tapes) (tm.haltCfgTapes tapes') t

/-- The Turing machine `tm` transforms tapes `tapes` to `tapes'`. -/
def TransformsTapes (tm : MultiTapeTM k Symbol) (tapes tapes' : Fin k → BiTape Symbol) : Prop :=
  ∃ t, tm.TransformsTapesInExactTime tapes tapes' t

/-- A proof that the Turing machine `tm` uses at most space `s` when run for up to `t` steps
on initial tapes `tapes`. -/
def UsesSpaceUntilStep
    (tm : MultiTapeTM k Symbol)
    (tapes : Fin k → BiTape Symbol)
    (s t : ℕ) : Prop :=
  ∀ t' ≤ t, match tm.configs tapes t' with
    | none => true
    | some cfg => cfg.space_used ≤ s

/-- A proof that the Turing machine `tm` transforms tapes `tapes` to `tapes'` in exactly `t` steps
and uses at most `s` space. -/
def TransformsTapesInTimeAndSpace
    (tm : MultiTapeTM k Symbol)
    (tapes tapes' : Fin k → BiTape Symbol)
    (t s : ℕ) : Prop :=
  tm.TransformsTapesInExactTime tapes tapes' t ∧
    tm.UsesSpaceUntilStep tapes s t

/-- This lemma translates between the relational notion and the iterated step notion. The latter
can be more convenient especially for deterministic machines as we have here. -/
@[scoped grind =]
lemma relatesInSteps_iff_step_iter_eq_some
    (tm : MultiTapeTM k Symbol)
    (cfg₁ cfg₂ : tm.Cfg)
    (t : ℕ) :
  RelatesInSteps tm.TransitionRelation cfg₁ cfg₂ t ↔
    (Option.bind · tm.step)^[t] cfg₁ = .some cfg₂ := by
  induction t generalizing cfg₁ cfg₂ with
  | zero => simp
  | succ t ih =>
    rw [RelatesInSteps.succ_iff, Function.iterate_succ_apply']
    constructor
    · grind
    · intro h_configs
      cases h : (Option.bind · tm.step)^[t] cfg₁ with
      | none => grind
      | some cfg' =>
        use cfg'
        grind

/-- The Turing machine `tm` halts after exactly `t` steps on initial tapes `tapes`. -/
def haltsAtStep (tm : MultiTapeTM k Symbol) (tapes : Fin k → BiTape Symbol) (t : ℕ) : Bool :=
  match (tm.configs tapes t) with
  | some ⟨none, _⟩ => true
  | _ => false

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiTapeTM k Symbol}
    {tapes : Fin k → BiTape Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep tapes t₁)
    (h_halts₂ : tm.haltsAtStep tapes t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    -- this is a contradiction.
    unfold haltsAtStep configs at h_halts₁ h_halts₂
    split at h_halts₁ <;> try contradiction
    next tapes' h_iter_t₁ =>
      rw [Nat.add_comm t₁ (d + 1), Function.iterate_add_apply, h_iter_t₁,
          step_iter_none_eq_none (tm := tm) tapes' d] at h_halts₂
      simp at h_halts₂

/-- At the halting step, the configuration sequence of a Turing machine is still `some`. -/
lemma configs_isSome_of_haltsAtStep
    {tm : MultiTapeTM k Symbol} {tapes : Fin k → BiTape Symbol} {t : ℕ}
    (h_halts : tm.haltsAtStep tapes t) :
    (tm.configs tapes t).isSome := by
  grind [haltsAtStep]

/-- Execute the Turing machine `tm` on initial tapes `tapes` and return the resulting tapes
if it eventually halts. -/
def eval (tm : MultiTapeTM k Symbol) (tapes : Fin k → BiTape Symbol) :
    Part (Fin k → BiTape Symbol) :=
  ⟨∃ t, tm.haltsAtStep tapes t,
    fun h => ((tm.configs tapes (Nat.find h)).get
      (configs_isSome_of_haltsAtStep (Nat.find_spec h))).tapes⟩

/-- Evaluating a Turing machine on a tuple of tapes `tapes` has a value `tapes'` if and only if
it transforms `tapes` into `tapes'`. -/
@[scoped grind =]
lemma eval_eq_some_iff_transformsTapes
    {tm : MultiTapeTM k Symbol}
    {tapes tapes' : Fin k → BiTape Symbol} :
    tm.eval tapes = .some tapes' ↔ tm.TransformsTapes tapes tapes' := by
  simp only [eval, Part.eq_some_iff, Part.mem_mk_iff]
  constructor
  · intro ⟨h_dom, h_get⟩
    use Nat.find h_dom
    grind [TransformsTapesInExactTime, configs, haltCfgTapes, haltsAtStep]
  · intro ⟨t, h_iter⟩
    rw [TransformsTapesInExactTime, relatesInSteps_iff_step_iter_eq_some, ← configs] at h_iter
    have h_halts_at_t : tm.haltsAtStep tapes t := by grind [haltsAtStep]
    have : ∃ t, tm.haltsAtStep tapes t := ⟨t, h_halts_at_t⟩
    grind [haltCfgTapes, halting_step_unique]

end MultiTapeTM

/-!
## Bridge lemmas: syntactic tape predicates ⇒ semantic invariants

These lemmas show that the syntactic predicates `HasInputTape` and `HasOutputTape` deliver
the semantic guarantees they are intended to capture, by step-by-step inspection of the
underlying `BiTape` operations.
-/

namespace MultiTapeTM

variable [Inhabited Symbol] [Fintype Symbol]

/-! ### Decomposing a step

Auxiliary lemmas that extract the state and tape components of `tm.step cfg = some cfg'`
in terms of the transition function `tm.tr`.
-/

/-- The state component of `tm.step cfg` is `(tm.tr q ...).2` when `cfg.state = some q`. -/
lemma step_state_eq {k : ℕ} {tm : MultiTapeTM k Symbol} {cfg cfg' : tm.Cfg} {q : tm.State}
    (h_state : cfg.state = some q) (h_step : tm.step cfg = some cfg') :
    (tm.tr q fun i => (cfg.tapes i).head).2 = cfg'.state := by
  obtain ⟨_ | _, _⟩ := cfg <;> grind [step]

/-- The tape component of `tm.step cfg` on tape `i` is the result of applying the `i`-th
`Stmt` of the transition function to `cfg.tapes i`, when `cfg.state = some q`. -/
lemma step_tapes_eq {k : ℕ} {tm : MultiTapeTM k Symbol} {cfg cfg' : tm.Cfg} {q : tm.State}
    (h_state : cfg.state = some q) (h_step : tm.step cfg = some cfg') (i : Fin k) :
    cfg'.tapes i =
      ((cfg.tapes i).write ((tm.tr q fun i => (cfg.tapes i).head).1 i).symbol).optionMove
        ((tm.tr q fun i => (cfg.tapes i).head).1 i).movement := by
  obtain ⟨_ | _, _⟩ := cfg <;> grind [step]

/-! ### Read-only input tape -/

/--
**Step decomposition for an input-tape step.** A step from `cfg` to `cfg'` factors through
the predecessor state `q` (witnessed by `cfg.state = some q`) and specifies the tape-`0`
movement explicitly: `cfg'.tapes 0` is `cfg.tapes 0` under `optionMove` with the direction
dictated by `tm.tr q`. The intermediate `tm.step ⟨some q, cfg.tapes⟩ = some cfg'` form is
handy for feeding `MoveThenStaysOnBlank.move`, whose constructor destructures `cfg`.
-/
lemma HasInputTape.step_tape0_decompose
    {k : ℕ} {tm : MultiTapeTM (k + 1) Symbol} (h_input : tm.HasInputTape)
    {cfg cfg' : tm.Cfg} (h_step : tm.step cfg = some cfg') :
    ∃ q : tm.State, cfg.state = some q ∧
      tm.step ⟨some q, cfg.tapes⟩ = some cfg' ∧
      cfg'.tapes 0 = (cfg.tapes 0).optionMove
        ((tm.tr q fun i => (cfg.tapes i).head).1 0).movement := by
  obtain ⟨_ | q, tapes⟩ := cfg
  · simp [step] at h_step
  refine ⟨q, rfl, h_step, ?_⟩
  have h_pre : ((tm.tr q fun i => (tapes i).head).1 0).symbol = (tapes 0).head :=
    h_input.readPreserving q (fun i => (tapes i).head)
  rw [step_tapes_eq rfl h_step 0, h_pre, BiTape.write_head]

/--
A single step of a TM with a designated input tape leaves tape `0` unchanged up to head
movement: the new tape `0` is obtained from the old one by some `optionMove`, and no symbol
on it has changed.
-/
lemma HasInputTape.step_tape0_eq_optionMove
    {k : ℕ} {tm : MultiTapeTM (k + 1) Symbol} (h_input : tm.HasInputTape)
    {cfg cfg' : tm.Cfg} (h_step : tm.step cfg = some cfg') :
    ∃ m : Option Dir, cfg'.tapes 0 = (cfg.tapes 0).optionMove m := by
  obtain ⟨_, _, _, h_tape0⟩ := h_input.step_tape0_decompose h_step
  exact ⟨_, h_tape0⟩

/-! ### Write-only output tape -/

/--
`OutputTapeContents tape out` says that `tape` is in the canonical shape of a write-only
output tape containing the emitted word `out`: the head is on the first blank cell after
the output, there is nothing to its right, and the left stack stores `out` in reverse
order because the nearest cell to the head is the most recently written symbol.
-/
def OutputTapeContents (tape : BiTape Symbol) (out : List Symbol) : Prop :=
  tape.head = none ∧ tape.left = StackTape.map_some out.reverse ∧ tape.right = ∅

omit [Inhabited Symbol] [Fintype Symbol] in
@[simp]
lemma outputTapeContents_nil : OutputTapeContents (BiTape.nil : BiTape Symbol) [] := by
  simp [OutputTapeContents, BiTape.nil]

/--
If the output tape is in canonical output shape before a step, it is in canonical output
shape after the step. The output word either stays the same (blank/stay transition) or
extends by the non-blank symbol written by this step.
-/
lemma HasOutputTape.step_outputTapeContents
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {cfg cfg' : tm.Cfg} {out : List Symbol} (h_step : tm.step cfg = some cfg')
    (h_contents : OutputTapeContents (cfg.tapes (Fin.last (k + 1))) out) :
    ∃ out' : List Symbol,
      OutputTapeContents (cfg'.tapes (Fin.last (k + 1))) out' ∧
        (out' = out ∨ ∃ a, out' = out ++ [a]) := by
  obtain ⟨_ | q, tapes⟩ := cfg
  · simp [step] at h_step
  obtain ⟨_, h_left, h_right⟩ := h_contents
  have h_left' : (tapes (Fin.last (k + 1))).left = StackTape.map_some out.reverse := h_left
  have h_right' : (tapes (Fin.last (k + 1))).right = ∅ := h_right
  rw [step_tapes_eq rfl h_step (Fin.last (k + 1))]
  rcases h_output q (fun i => (tapes i).head) with ⟨h_sym, h_mov⟩ | ⟨h_some, h_mov⟩
  · refine ⟨out, ?_, .inl rfl⟩
    simp [OutputTapeContents, h_sym, h_mov, BiTape.optionMove, BiTape.write, h_left', h_right']
  · obtain ⟨a, h_sym⟩ := Option.isSome_iff_exists.mp h_some
    refine ⟨out ++ [a], ?_, .inr ⟨a, rfl⟩⟩
    simp [OutputTapeContents, h_sym, h_mov, BiTape.optionMove, BiTape.write, BiTape.move,
      BiTape.move_right, h_left', h_right', List.reverse_append]

/--
**Trace-level output-content invariant.** Along any chain of step transitions from a
canonical output tape, the final output tape is canonical for some emitted word.
-/
lemma HasOutputTape.relatesInSteps_outputTapeContents
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {cfg cfg' : tm.Cfg} {t : ℕ} {out : List Symbol}
    (h_rel : Relation.RelatesInSteps tm.TransitionRelation cfg cfg' t)
    (h_contents : OutputTapeContents (cfg.tapes (Fin.last (k + 1))) out) :
    ∃ out' : List Symbol,
      OutputTapeContents (cfg'.tapes (Fin.last (k + 1))) out' := by
  exact h_rel.invariant
    (P := fun c => ∃ out, OutputTapeContents (c.tapes (Fin.last (k + 1))) out)
    (fun h_step h =>
      let ⟨out, h_contents⟩ := h
      let ⟨out', h_contents', _⟩ := h_output.step_outputTapeContents h_step h_contents
      ⟨out', h_contents'⟩)
    ⟨out, h_contents⟩

/--
Starting from a blank output tape, any reachable output tape is canonical for some emitted
word: the head is blank, the right stack is empty, and the left stack is that word in
reverse.
-/
lemma HasOutputTape.relatesInSteps_outputTapeContents_of_nil
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {cfg cfg' : tm.Cfg} {t : ℕ}
    (h_rel : Relation.RelatesInSteps tm.TransitionRelation cfg cfg' t)
    (h_nil : cfg.tapes (Fin.last (k + 1)) = BiTape.nil) :
    ∃ out : List Symbol,
      OutputTapeContents (cfg'.tapes (Fin.last (k + 1))) out := by
  have h_contents : OutputTapeContents (cfg.tapes (Fin.last (k + 1))) [] := by
    rw [h_nil]
    exact outputTapeContents_nil
  exact h_output.relatesInSteps_outputTapeContents h_rel h_contents

/--
**Output-content invariant at `TransformsTapes`.** If the output tape starts in canonical
shape, then on any final tapes `tm` transforms them into, the output tape is again
canonical for some emitted word.
-/
lemma HasOutputTape.transformsTapes_outputTapeContents
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {tapes tapes' : Fin (k + 2) → BiTape Symbol} {out : List Symbol}
    (h_trans : tm.TransformsTapes tapes tapes')
    (h_contents : OutputTapeContents (tapes (Fin.last (k + 1))) out) :
    ∃ out' : List Symbol,
      OutputTapeContents (tapes' (Fin.last (k + 1))) out' := by
  obtain ⟨_, h_rel⟩ := h_trans
  exact h_output.relatesInSteps_outputTapeContents h_rel h_contents

/--
**Output-content invariant at `TransformsTapes`, blank initial output case.**
-/
lemma HasOutputTape.transformsTapes_outputTapeContents_of_nil
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {tapes tapes' : Fin (k + 2) → BiTape Symbol}
    (h_trans : tm.TransformsTapes tapes tapes')
    (h_nil : tapes (Fin.last (k + 1)) = BiTape.nil) :
    ∃ out : List Symbol,
      OutputTapeContents (tapes' (Fin.last (k + 1))) out := by
  obtain ⟨_, h_rel⟩ := h_trans
  exact h_output.relatesInSteps_outputTapeContents_of_nil h_rel h_nil

/--
**Output-content invariant at `eval`.** If `tm.eval tapes = some tapes'` and the output tape
starts in canonical shape, then the final output tape is canonical for some emitted word.
-/
lemma HasOutputTape.eval_outputTapeContents
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {tapes tapes' : Fin (k + 2) → BiTape Symbol} {out : List Symbol}
    (h_eval : tm.eval tapes = .some tapes')
    (h_contents : OutputTapeContents (tapes (Fin.last (k + 1))) out) :
    ∃ out' : List Symbol,
      OutputTapeContents (tapes' (Fin.last (k + 1))) out' :=
  h_output.transformsTapes_outputTapeContents (eval_eq_some_iff_transformsTapes.mp h_eval)
    h_contents

/--
**Output-content invariant at `eval`, blank initial output case.**
-/
lemma HasOutputTape.eval_outputTapeContents_of_nil
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {tapes tapes' : Fin (k + 2) → BiTape Symbol}
    (h_eval : tm.eval tapes = .some tapes')
    (h_nil : tapes (Fin.last (k + 1)) = BiTape.nil) :
    ∃ out : List Symbol,
      OutputTapeContents (tapes' (Fin.last (k + 1))) out :=
  h_output.transformsTapes_outputTapeContents_of_nil (eval_eq_some_iff_transformsTapes.mp h_eval)
    h_nil

/--
If the output tape's right `StackTape` is empty before a step, it is empty after the step.
This is a weaker projection of `HasOutputTape.step_outputTapeContents` that does not assume
the current head cell is blank or that the left stack contains only symbols.
-/
lemma HasOutputTape.step_right_empty
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {cfg cfg' : tm.Cfg} (h_step : tm.step cfg = some cfg')
    (h_right : (cfg.tapes (Fin.last (k + 1))).right = ∅) :
    (cfg'.tapes (Fin.last (k + 1))).right = ∅ := by
  obtain ⟨_ | q, tapes⟩ := cfg
  · simp [step] at h_step
  have h_right' : (tapes (Fin.last (k + 1))).right = ∅ := h_right
  rw [step_tapes_eq rfl h_step (Fin.last (k + 1))]
  rcases h_output q (fun i => (tapes i).head) with ⟨h_sym, h_mov⟩ | ⟨_, h_mov⟩
  · simpa [h_sym, h_mov, BiTape.optionMove, BiTape.write] using h_right'
  · simp [h_mov, BiTape.optionMove, BiTape.write, BiTape.move, BiTape.move_right, h_right']

/--
**Trace-level output invariant.** Along any chain of step transitions starting from a
configuration whose output tape has empty `right` `StackTape`, the output tape's `right`
remains empty. Use `HasOutputTape.relatesInSteps_outputTapeContents` when the stronger
canonical output shape is needed.
-/
lemma HasOutputTape.relatesInSteps_right_empty
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {cfg cfg' : tm.Cfg} {t : ℕ}
    (h_rel : Relation.RelatesInSteps tm.TransitionRelation cfg cfg' t)
    (h_right : (cfg.tapes (Fin.last (k + 1))).right = ∅) :
    (cfg'.tapes (Fin.last (k + 1))).right = ∅ :=
  h_rel.invariant (P := fun c => (c.tapes (Fin.last (k + 1))).right = ∅)
    h_output.step_right_empty h_right

/--
**Output invariant at `TransformsTapes`.** If the output tape's right `StackTape` is empty
on the initial tapes, then on any final tapes `tm` transforms them into, the output tape's
right is again empty.
-/
lemma HasOutputTape.transformsTapes_right_empty
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {tapes tapes' : Fin (k + 2) → BiTape Symbol}
    (h_trans : tm.TransformsTapes tapes tapes')
    (h_right : (tapes (Fin.last (k + 1))).right = ∅) :
    (tapes' (Fin.last (k + 1))).right = ∅ := by
  obtain ⟨_, h_rel⟩ := h_trans
  exact h_output.relatesInSteps_right_empty h_rel h_right

/--
**Output invariant at `eval`.** If `tm.eval tapes = some tapes'` and the output tape's right
`StackTape` starts empty, then the output tape's right is empty on `tapes'`.
-/
lemma HasOutputTape.eval_right_empty
    {k : ℕ} {tm : MultiTapeTM (k + 2) Symbol} (h_output : tm.HasOutputTape)
    {tapes tapes' : Fin (k + 2) → BiTape Symbol}
    (h_eval : tm.eval tapes = .some tapes')
    (h_right : (tapes (Fin.last (k + 1))).right = ∅) :
    (tapes' (Fin.last (k + 1))).right = ∅ :=
  h_output.transformsTapes_right_empty (eval_eq_some_iff_transformsTapes.mp h_eval) h_right

/-! ### Trace-level head boundedness on the input tape

The syntactic predicate `IsBoundedInDirectionOnTape` is phrased on the *finite control* — it
forbids certain reachability patterns in the state graph. To show this rules out actual
computation trajectories that drift off the input, we lift the syntactic chain `MoveThenStays`
to a configuration-level chain `MoveThenStaysOnBlank` and prove that any semantic trace of
the right shape produces a syntactic reachability witness, after which
`IsBoundedInDirectionOnTape` rules out the bad continuation.
-/

/--
A configuration trajectory of the form
`⟨some q₁, _⟩ →[move-d on tape i] cfg₂ →[stay-on-blank-on-tape-i]* cfg`,
parameterized by the starting state `q₁`, the ending state `q₂`, and the ending
configuration `cfg`, whose tapes are inspectable.
-/
inductive MoveThenStaysOnBlank
    {k : ℕ} (tm : MultiTapeTM k Symbol) (i : Fin k) (d : Dir) :
    tm.State → tm.State → tm.Cfg → Prop where
  /-- Single move-`d` step from `q₁`: the resulting configuration is the witness. -/
  | move {q₁ q₂ : tm.State} {tapes₁ : Fin k → BiTape Symbol} {cfg₂ : tm.Cfg}
      (h_step : tm.step ⟨some q₁, tapes₁⟩ = some cfg₂)
      (h_state : cfg₂.state = some q₂)
      (h_mov : ((tm.tr q₁ fun i => (tapes₁ i).head).1 i).movement = some d) :
      MoveThenStaysOnBlank tm i d q₁ q₂ cfg₂
  /-- Extend an existing chain by a stay-on-blank step on tape `i`. -/
  | stay {q₁ q₂ q₃ : tm.State} {cfg₂ cfg₃ : tm.Cfg}
      (h_prev : MoveThenStaysOnBlank tm i d q₁ q₂ cfg₂)
      (h_blank : (cfg₂.tapes i).head = none)
      (h_step : tm.step cfg₂ = some cfg₃)
      (h_state : cfg₃.state = some q₃)
      (h_no_mov : ((tm.tr q₂ fun i => (cfg₂.tapes i).head).1 i).movement = none) :
      MoveThenStaysOnBlank tm i d q₁ q₃ cfg₃

/-- The state of the witness configuration of a chain matches its second state parameter. -/
lemma MoveThenStaysOnBlank.cfg_state_eq
    {k : ℕ} {tm : MultiTapeTM k Symbol} {i : Fin k} {d : Dir}
    {q₁ q₂ : tm.State} {cfg : tm.Cfg}
    (h : MoveThenStaysOnBlank tm i d q₁ q₂ cfg) :
    cfg.state = some q₂ := by
  induction h with
  | move _ h_state _ => exact h_state
  | stay _ _ _ h_state _ => exact h_state

/--
A semantic chain is a witness of the syntactic chain on its endpoint states.
-/
lemma MoveThenStaysOnBlank.moveThenStays
    {k : ℕ} {tm : MultiTapeTM k Symbol} {i : Fin k} {d : Dir}
    {q₁ q₂ : tm.State} {cfg : tm.Cfg}
    (h_chain : MoveThenStaysOnBlank tm i d q₁ q₂ cfg) :
    MoveThenStays tm.tr i d q₁ q₂ := by
  induction h_chain with
  | move h_step h_state h_mov =>
    refine .move _ _ _ h_mov ?_
    rw [step_state_eq rfl h_step, h_state]
  | stay h_prev h_blank h_step h_state h_no_mov ih =>
    refine .stay _ _ _ ih _ h_blank h_no_mov ?_
    rw [step_state_eq h_prev.cfg_state_eq h_step, h_state]

end MultiTapeTM

namespace IsBoundedInDirectionOnTape

variable [Inhabited Symbol] [Fintype Symbol]

/--
**Trace-level boundedness.** Given `IsBoundedInDirectionOnTape tm.tr i d`, no actual
computation trace matching the "move-`d` on tape `i`, then stay-on-blank-on-tape-`i`*"
pattern can end in a state that would move the head further in direction `d` on a blank.

Iterating this gives that the head on tape `i` does not perform two consecutive
direction-`d` moves separated by stay-moves on the blank. The quantitative `±1`-cell
bound on the head position over arbitrary traces is `HasInputTape.head_position_bounded`.
-/
lemma not_movesOffBlankInDir_of_chain
    {k : ℕ} {tm : MultiTapeTM k Symbol} {i : Fin k} {d : Dir}
    (h_bound : IsBoundedInDirectionOnTape tm.tr i d)
    {q₁ q₂ : tm.State} {cfg : tm.Cfg}
    (h_chain : MultiTapeTM.MoveThenStaysOnBlank tm i d q₁ q₂ cfg) :
    ¬ MovesOffBlankInDir tm.tr i d q₂ :=
  h_bound q₁ q₂ h_chain.moveThenStays

end IsBoundedInDirectionOnTape

/-! ### Quantitative head-position bound on the input tape

We promote the qualitative chain-level boundedness to a quantitative `±1` bound on the
tape-`0` head position over arbitrary traces from `initCfg s` (with non-empty input).
The position is read off the `BiTape` geometry via `canonicalInputTape s p`, the unique
shape of tape `0` after the head has moved to integer position `p` relative to the
start of the input (see `Cslib.Foundations.Data.BiTape.Canonical`).
-/

namespace MultiTapeTM

variable [Inhabited Symbol] [Fintype Symbol]

/-! ### Head-boundedness invariant -/

/--
**Head-boundedness invariant at position `p`.** For a configuration `cfg` along a trace
from `initCfg s` of a TM with a designated input tape, tape `0` of `cfg` is in canonical
shape `canonicalInputTape s p` for some integer position `p ∈ [-1, s.length]`.
-/
structure HeadBoundInvariantAt {k : ℕ} (tm : MultiTapeTM (k + 1) Symbol) (s : List Symbol)
    (cfg : tm.Cfg) (p : ℤ) : Prop where
  /-- `p` is at least `-1` (one cell left of the input). -/
  pos_lower : -1 ≤ p
  /-- `p` is at most `s.length` (one cell right of the last input symbol). -/
  pos_upper : p ≤ (s.length : ℤ)
  /-- Tape `0` is in canonical shape at integer position `p`. -/
  tape_eq : cfg.tapes 0 = canonicalInputTape s p

/--
**Strong head-boundedness invariant.** Extends `HeadBoundInvariantAt` with chain witnesses
at the endpoints: when the machine is not halted and the head sits one cell past an end of
the input, a move-stay-blank chain witness records the inbound direction. This is what
threads `IsBoundedInDirectionOnTape` through the inductive step preservation; user-facing
results expose only the underlying `HeadBoundInvariantAt`.
-/
structure HeadBoundInvariantAt.Strong {k : ℕ} (tm : MultiTapeTM (k + 1) Symbol)
    (s : List Symbol) (cfg : tm.Cfg) (p : ℤ) : Prop
    extends HeadBoundInvariantAt tm s cfg p where
  /-- Chain witness at the left endpoint. -/
  chain_left : ∀ q, cfg.state = some q → p = -1 →
    ∃ q₀, MoveThenStaysOnBlank tm 0 .left q₀ q cfg
  /-- Chain witness at the right endpoint. -/
  chain_right : ∀ q, cfg.state = some q → p = (s.length : ℤ) →
    ∃ q₀, MoveThenStaysOnBlank tm 0 .right q₀ q cfg

/--
**Trace-level invariant.** Either the input is empty (in which case tape `0` is forced to
`BiTape.nil` throughout the trace and any canonical position coincides with `nil`), or
some position `p ∈ [-1, s.length]` witnesses the strong invariant. The disjunction handles
empty and nonempty input uniformly along traces.
-/
def HeadBoundInvariantForInput {k : ℕ} (tm : MultiTapeTM (k + 1) Symbol) (s : List Symbol)
    (cfg : tm.Cfg) : Prop :=
  s = [] ∧ cfg.tapes 0 = BiTape.nil ∨ ∃ p : ℤ, HeadBoundInvariantAt.Strong tm s cfg p

/-- The initial configuration satisfies the strong head-boundedness invariant at `p = 0`,
provided the input is nonempty. -/
lemma HeadBoundInvariantAt.Strong.initCfg
    {k : ℕ} {tm : MultiTapeTM (k + 1) Symbol} {s : List Symbol} (h_pos : 0 < s.length) :
    HeadBoundInvariantAt.Strong tm s (tm.initCfg s) 0 where
  pos_lower := by omega
  pos_upper := Int.natCast_nonneg _
  tape_eq := show BiTape.mk₁ s = _ from (canonicalInputTape_zero s).symm
  chain_left _ _ h := absurd h (by omega)
  chain_right _ _ h := absurd h (by exact_mod_cast h_pos.ne)

/-- The initial configuration satisfies the trace-level invariant for any input. -/
lemma HeadBoundInvariantForInput.initCfg
    {k : ℕ} {tm : MultiTapeTM (k + 1) Symbol} (s : List Symbol) :
    HeadBoundInvariantForInput tm s (tm.initCfg s) := by
  by_cases h_pos : 0 < s.length
  · exact .inr ⟨0, .initCfg h_pos⟩
  · have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
    subst hs
    exact .inl ⟨rfl, rfl⟩

/-- **Step preservation of the strong head-boundedness invariant.** A single step of a TM
with an input tape preserves the strong invariant: the head position advances by at most
one cell and stays within `[-1, s.length]`; endpoint chain witnesses are maintained by
extending via `stay` or constructed fresh via `move`; an attempt to step past an endpoint
is ruled out by `IsBoundedInDirectionOnTape.not_movesOffBlankInDir_of_chain`. -/
lemma HeadBoundInvariantAt.Strong.step
    {k : ℕ} {tm : MultiTapeTM (k + 1) Symbol} (h_input : tm.HasInputTape)
    {s : List Symbol} {cfg cfg' : tm.Cfg} {p : ℤ}
    (h_inv : HeadBoundInvariantAt.Strong tm s cfg p) (h_step : tm.step cfg = some cfg') :
    ∃ p' : ℤ, HeadBoundInvariantAt.Strong tm s cfg' p' := by
  obtain ⟨q, h_state_q, h_step_q, h_tape0⟩ := h_input.step_tape0_decompose h_step
  have h_head_eq : (cfg.tapes 0).head = none ↔ (p = -1 ∨ p = (s.length : ℤ)) := by
    rw [h_inv.tape_eq]; exact canonicalInputTape_head_eq_none_iff h_inv.pos_lower h_inv.pos_upper
  cases hm : ((tm.tr q fun i => (cfg.tapes i).head).1 0).movement with
  | none =>
    refine ⟨p, ⟨h_inv.pos_lower, h_inv.pos_upper, ?_⟩, ?_, ?_⟩
    · rw [h_tape0, hm]; exact h_inv.tape_eq
    · intro q' hq' hp_neg_one
      have h_blank : (cfg.tapes 0).head = none := h_head_eq.mpr (Or.inl hp_neg_one)
      obtain ⟨q₀, h_chain⟩ := h_inv.chain_left q h_state_q hp_neg_one
      exact ⟨q₀, MoveThenStaysOnBlank.stay h_chain h_blank h_step hq' hm⟩
    · intro q' hq' hp_len
      have h_blank : (cfg.tapes 0).head = none := h_head_eq.mpr (Or.inr hp_len)
      obtain ⟨q₀, h_chain⟩ := h_inv.chain_right q h_state_q hp_len
      exact ⟨q₀, MoveThenStaysOnBlank.stay h_chain h_blank h_step hq' hm⟩
  | some d =>
    cases d with
    | right =>
      by_cases hp_eq : p = (s.length : ℤ)
      · exfalso
        have h_blank : (cfg.tapes 0).head = none := h_head_eq.mpr (Or.inr hp_eq)
        obtain ⟨q₀, h_chain⟩ := h_inv.chain_right q h_state_q hp_eq
        exact IsBoundedInDirectionOnTape.not_movesOffBlankInDir_of_chain
          h_input.rightBounded h_chain ⟨fun i => (cfg.tapes i).head, h_blank, hm⟩
      · have hp_lt : p < (s.length : ℤ) := by have := h_inv.pos_upper; omega
        have hp_lo := h_inv.pos_lower
        refine ⟨p + 1, ⟨by omega, by omega, ?_⟩, ?_, ?_⟩
        · rw [h_tape0, hm, h_inv.tape_eq]
          exact canonicalInputTape_move_right hp_lo hp_lt
        · intro _ _ hp_neg_one; exfalso; omega
        · intro q' hq' _
          exact ⟨q, MoveThenStaysOnBlank.move h_step_q hq' hm⟩
    | left =>
      by_cases hp_eq : p = -1
      · exfalso
        have h_blank : (cfg.tapes 0).head = none := h_head_eq.mpr (Or.inl hp_eq)
        obtain ⟨q₀, h_chain⟩ := h_inv.chain_left q h_state_q hp_eq
        exact IsBoundedInDirectionOnTape.not_movesOffBlankInDir_of_chain
          h_input.leftBounded h_chain ⟨fun i => (cfg.tapes i).head, h_blank, hm⟩
      · have hp_nn : 0 ≤ p := by have := h_inv.pos_lower; omega
        have hp_hi := h_inv.pos_upper
        refine ⟨p - 1, ⟨by omega, by omega, ?_⟩, ?_, ?_⟩
        · rw [h_tape0, hm, h_inv.tape_eq]
          exact canonicalInputTape_move_left hp_nn hp_hi
        · intro q' hq' _
          exact ⟨q, MoveThenStaysOnBlank.move h_step_q hq' hm⟩
        · intro _ _ hp_len; exfalso; omega

/-- A step of an input-tape-preserving TM keeps `BiTape.nil` on tape `0`. -/
private lemma HasInputTape.step_tape0_nil {k : ℕ} {tm : MultiTapeTM (k + 1) Symbol}
    (h_input : tm.HasInputTape) {cfg cfg' : tm.Cfg}
    (h_tape : cfg.tapes 0 = BiTape.nil) (h_step : tm.step cfg = some cfg') :
    cfg'.tapes 0 = BiTape.nil := by
  obtain ⟨m, h_m⟩ := h_input.step_tape0_eq_optionMove h_step
  rw [h_m, h_tape, BiTape.optionMove_nil]

/-- **Step preservation of the trace-level invariant.** -/
lemma HeadBoundInvariantForInput.step
    {k : ℕ} {tm : MultiTapeTM (k + 1) Symbol} (h_input : tm.HasInputTape)
    {s : List Symbol} {cfg cfg' : tm.Cfg}
    (h_inv : HeadBoundInvariantForInput tm s cfg) (h_step : tm.step cfg = some cfg') :
    HeadBoundInvariantForInput tm s cfg' := by
  rcases h_inv with ⟨h_empty, h_nil⟩ | ⟨_, h_strong⟩
  · exact .inl ⟨h_empty, h_input.step_tape0_nil h_nil h_step⟩
  · exact .inr (h_strong.step h_input h_step)

/-- The trace-level invariant is preserved along any chain of step transitions. -/
lemma HeadBoundInvariantForInput.relatesInSteps
    {k : ℕ} {tm : MultiTapeTM (k + 1) Symbol} (h_input : tm.HasInputTape)
    {s : List Symbol} {cfg cfg' : tm.Cfg} {t : ℕ}
    (h_inv : HeadBoundInvariantForInput tm s cfg)
    (h_rel : Relation.RelatesInSteps tm.TransitionRelation cfg cfg' t) :
    HeadBoundInvariantForInput tm s cfg' :=
  h_rel.invariant (fun h_step h => h.step h_input h_step) h_inv

/-- The trace-level invariant projects to a position bound + canonical tape match. -/
lemma HeadBoundInvariantForInput.exists_pos {k : ℕ} {tm : MultiTapeTM (k + 1) Symbol}
    {s : List Symbol} {cfg : tm.Cfg} (h_inv : HeadBoundInvariantForInput tm s cfg) :
    ∃ p : ℤ, -1 ≤ p ∧ p ≤ (s.length : ℤ) ∧ cfg.tapes 0 = canonicalInputTape s p := by
  rcases h_inv with ⟨h_empty, h_nil⟩ | ⟨p, h_strong⟩
  · subst h_empty
    refine ⟨0, by omega, by simp, ?_⟩
    rw [canonicalInputTape_nil]; exact h_nil
  · exact ⟨p, h_strong.pos_lower, h_strong.pos_upper, h_strong.tape_eq⟩

/-- **Quantitative head-position bound.** Every configuration reachable from `initCfg s`
in `t` steps has its tape-`0` content in canonical shape `canonicalInputTape s p` for some
integer position `p ∈ [-1, s.length]`. In particular, the head on tape `0` stays within
one cell of the input region throughout the trace. -/
theorem HasInputTape.head_position_bounded
    {k : ℕ} {tm : MultiTapeTM (k + 1) Symbol} (h_input : tm.HasInputTape)
    {s : List Symbol} {cfg' : tm.Cfg} {t : ℕ}
    (h_rel : Relation.RelatesInSteps tm.TransitionRelation (tm.initCfg s) cfg' t) :
    ∃ p : ℤ, -1 ≤ p ∧ p ≤ (s.length : ℤ) ∧ cfg'.tapes 0 = canonicalInputTape s p :=
  ((HeadBoundInvariantForInput.initCfg s).relatesInSteps h_input h_rel).exists_pos

end MultiTapeTM

end Turing
