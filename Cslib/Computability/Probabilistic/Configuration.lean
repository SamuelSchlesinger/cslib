/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Tape
public import Cslib.Computability.Probabilistic.Pi
public import Cslib.Computability.Machines.Turing.MultiTape.FiniteConfiguration

/-!
# Efficient operations on finite binary machine configurations

The finite representations of the shared machine are encoded with the word, finite-tag,
product and table encodings. Their observations and native actions are polynomial time by
composition. These certificates belong to the interpreter implementation; cryptographic clients
use the resulting program-level closure rules.
-/

@[expose] public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeMachine Cslib.Turing

variable {k : ℕ} {State : Type} [Finite State]

/-- Encode the finite input, control, input position, work tapes and accumulated output. -/
noncomputable def finiteCfgEncoding : FiniteCfg k Bool State ↪ Word where
  toFun cfg := pairEncoding wordEncoding (pairEncoding (finiteEncoding (Option State))
    (pairEncoding unaryEncoding (pairEncoding (piEncoding biTapeEncoding) wordEncoding)))
    (cfg.input, cfg.state, cfg.inputPos.val, cfg.workTapes, cfg.output)
  inj' := by
    rintro ⟨input, state, pos, work, output⟩ ⟨input', state', pos', work', output'⟩ h
    have heq := (pairEncoding _ _).injective h
    rcases Prod.mk.inj heq with ⟨rfl, heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, heq⟩
    rcases Prod.mk.inj heq with ⟨hpos, heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    cases Fin.ext hpos
    rfl

/-- Encode ordinary finite storage and the fixed family of oracle channels. -/
noncomputable def finiteConfigEncoding {Oracle : Type} [Fintype Oracle] :
    FiniteConfig k Bool State Oracle ↪ Word where
  toFun cfg := pairEncoding finiteCfgEncoding (piEncoding (pairEncoding wordEncoding
    biTapeEncoding)) (cfg.tapes, cfg.channels)
  inj' := fun _ _ h => FiniteConfig.ext (congrArg Prod.fst ((pairEncoding _ _).injective h))
    (congrArg Prod.snd ((pairEncoding _ _).injective h))

variable {α : Type} {input : α → Word}

/-- Assemble an encoded ordinary configuration from certified components. -/
theorem IsPolyTime.finiteCfg_mk {word : α → Word} {state : α → Option State}
    {position : ∀ a, Fin ((word a).length + 2)} {work : α → Fin k → BiTape Bool}
    {output : α → Word} (hword : IsPolyTime input word)
    (hstate : IsPolyTime input (fun a => finiteEncoding (Option State) (state a)))
    (hposition : IsPolyTime input (fun a => unaryEncoding (position a).val))
    (hwork : IsPolyTime input (fun a => piEncoding biTapeEncoding (work a)))
    (houtput : IsPolyTime input output) :
    IsPolyTime input (fun a => finiteCfgEncoding
      ⟨word a, state a, position a, work a, output a⟩) :=
  hword.pair (hstate.pair (hposition.pair (hwork.pair houtput)))

/-- Read a configuration's stored input. -/
theorem IsPolyTime.finiteCfg_input {cfg : α → FiniteCfg k Bool State}
    (h : IsPolyTime input (fun a => finiteCfgEncoding (cfg a))) :
    IsPolyTime input (fun a => (cfg a).input) := h.fst

/-- Read a configuration's finite control. -/
theorem IsPolyTime.finiteCfg_state {cfg : α → FiniteCfg k Bool State}
    (h : IsPolyTime input (fun a => finiteCfgEncoding (cfg a))) :
    IsPolyTime input (fun a => finiteEncoding (Option State) (cfg a).state) := h.snd.fst

/-- Read a configuration's input position as a unary integer. -/
theorem IsPolyTime.finiteCfg_inputPos {cfg : α → FiniteCfg k Bool State}
    (h : IsPolyTime input (fun a => finiteCfgEncoding (cfg a))) :
    IsPolyTime input (fun a => unaryEncoding (cfg a).inputPos.val) := h.snd.snd.fst

/-- Read a configuration's complete finite work tapes. -/
theorem IsPolyTime.finiteCfg_workTapes {cfg : α → FiniteCfg k Bool State}
    (h : IsPolyTime input (fun a => finiteCfgEncoding (cfg a))) :
    IsPolyTime input (fun a => piEncoding biTapeEncoding (cfg a).workTapes) := h.snd.snd.snd.fst

/-- Read a configuration's accumulated output. -/
theorem IsPolyTime.finiteCfg_output {cfg : α → FiniteCfg k Bool State}
    (h : IsPolyTime input (fun a => finiteCfgEncoding (cfg a))) :
    IsPolyTime input (fun a => (cfg a).output) := h.snd.snd.snd.snd

/-- Observe the input cell, including both blank boundary cells. -/
theorem IsPolyTime.finiteCfg_inputSymbol {cfg : α → FiniteCfg k Bool State}
    (h : IsPolyTime input (fun a => finiteCfgEncoding (cfg a))) :
    IsPolyTime input (fun a => finiteEncoding (Option Bool) (cfg a).inputSymbol) := by
  have hsome := h.finiteCfg_input.encode_list_bool.list_map
    (isPolyTime_of_finite boolEncoding (fun bit => finiteEncoding (Option Bool) (some bit)))
  simpa only [FiniteCfg.inputSymbol_eq_getD] using
    ((isPolyTime_const input (finiteEncoding (Option Bool) none)).list_cons hsome).list_getD
      h.finiteCfg_inputPos none

/-- Observe all work heads as one value of a fixed finite type. -/
theorem IsPolyTime.finiteCfg_workTapeSymbols {cfg : α → FiniteCfg k Bool State}
    (h : IsPolyTime input (fun a => finiteCfgEncoding (cfg a))) :
    IsPolyTime input (fun a => finiteEncoding (Fin k → Option Bool) (cfg a).workTapeSymbols) :=
  (IsPolyTime.pi (fun tape => (h.finiteCfg_workTapes.pi_apply tape).biTape_head)).finite_map
    (finiteEncoding (Fin k → Option Bool))

/-- The native clamped input-head movement is efficient on unary positions. -/
theorem IsPolyTime.moveInputPos {word : α → Word} {position : ∀ a, Fin ((word a).length + 2)}
    (hword : IsPolyTime input word)
    (hposition : IsPolyTime input (fun a => unaryEncoding (position a).val)) (move : SignType) :
    IsPolyTime input (fun a => unaryEncoding (moveInputPos (position a) move).val) := by
  cases move with
  | neg =>
    convert hposition.unary_sub (isPolyTime_const input (unaryEncoding 1)) using 1
    funext a
    apply congrArg (fun n => List.replicate n true)
    have h := val_moveInputPos_eq (position a) .neg
    have hp := (position a).isLt
    simp only [SignType.cast] at h
    lia
  | zero => simpa using hposition
  | pos =>
    convert (hposition.unary_add (isPolyTime_const input (unaryEncoding 1))).unary_min
      (hword.unaryLength.unary_add (isPolyTime_const input (unaryEncoding 1))) using 1
    funext a
    apply congrArg (fun n => List.replicate n true)
    have h := val_moveInputPos_eq (position a) .pos
    simp only [SignType.cast] at h
    lia

/-- Execute a fixed ordinary native action on finite storage. -/
theorem IsPolyTime.finiteCfg_step {cfg : α → FiniteCfg k Bool State}
    (h : IsPolyTime input (fun a => finiteCfgEncoding (cfg a))) (action : Action k Bool State) :
    IsPolyTime input (fun a => finiteCfgEncoding ((cfg a).step action)) :=
  h.finiteCfg_input.finiteCfg_mk (isPolyTime_const input _)
    (h.finiteCfg_input.moveInputPos h.finiteCfg_inputPos action.inputTape)
    (IsPolyTime.pi (fun tape => (h.finiteCfg_workTapes.pi_apply tape).biTape_step
      (action.workTapes tape)))
    (h.finiteCfg_output.append (isPolyTime_const input action.output.toList))

/-- Initialize finite storage using the shared machine's input convention. -/
theorem IsPolyTime.finiteCfg_init {word : α → Word} (h : IsPolyTime input word) (state : State) :
    IsPolyTime input (fun a => finiteCfgEncoding (FiniteCfg.init (k := k) state (word a))) := by
  apply h.finiteCfg_mk (isPolyTime_const input _)
  · convert isPolyTime_const input (unaryEncoding 1) using 1
    funext a
    simp
  · exact isPolyTime_const input _
  · exact isPolyTime_const input _

variable {Oracle : Type} [Fintype Oracle]

/-- Assemble a shared-core configuration from ordinary storage and its channels. -/
theorem IsPolyTime.finiteConfig_mk {tapes : α → FiniteCfg k Bool State}
    {channels : α → Oracle → Word × BiTape Bool}
    (htapes : IsPolyTime input (fun a => finiteCfgEncoding (tapes a)))
    (hchannels : IsPolyTime input (fun a =>
      piEncoding (pairEncoding wordEncoding biTapeEncoding) (channels a))) :
    IsPolyTime input (fun a => finiteConfigEncoding ⟨tapes a, channels a⟩) :=
  htapes.pair hchannels

/-- Read the ordinary storage of a shared-core configuration. -/
theorem IsPolyTime.finiteConfig_tapes {cfg : α → FiniteConfig k Bool State Oracle}
    (h : IsPolyTime input (fun a => finiteConfigEncoding (cfg a))) :
    IsPolyTime input (fun a => finiteCfgEncoding (cfg a).tapes) := h.fst

/-- Read all channel buffers and answer tapes. -/
theorem IsPolyTime.finiteConfig_channels {cfg : α → FiniteConfig k Bool State Oracle}
    (h : IsPolyTime input (fun a => finiteConfigEncoding (cfg a))) :
    IsPolyTime input (fun a =>
      piEncoding (pairEncoding wordEncoding biTapeEncoding) (cfg a).channels) := h.snd

/-- Observe all answer heads as one value of a fixed finite type. -/
theorem IsPolyTime.finiteConfig_answerSymbols {cfg : α → FiniteConfig k Bool State Oracle}
    (h : IsPolyTime input (fun a => finiteConfigEncoding (cfg a))) :
    IsPolyTime input (fun a => finiteEncoding (Oracle → Option Bool) (cfg a).answerSymbols) :=
  (IsPolyTime.pi (fun channel =>
    (h.finiteConfig_channels.pi_apply channel).snd.biTape_head)).finite_map
      (finiteEncoding (Oracle → Option Bool))

/-- Execute a fixed local shared-core action, retaining all pending query buffers. -/
theorem IsPolyTime.finiteConfig_step {cfg : α → FiniteConfig k Bool State Oracle}
    (h : IsPolyTime input (fun a => finiteConfigEncoding (cfg a))) (action : Action k Bool State)
    (symbol : Oracle → Option Bool) (move : Oracle → SignType) :
    IsPolyTime input (fun a => finiteConfigEncoding ((cfg a).step action symbol move)) :=
  (h.finiteConfig_tapes.finiteCfg_step action).finiteConfig_mk (IsPolyTime.pi (fun channel =>
    let hc := h.finiteConfig_channels.pi_apply channel
    (hc.fst.append (isPolyTime_const input (symbol channel).toList)).pair
      (hc.snd.biTape_step (none, move channel))))

/-- Install a reply using the native channel reset and continuation state. -/
theorem IsPolyTime.finiteConfig_receive [DecidableEq Oracle]
    {cfg : α → FiniteConfig k Bool State Oracle} {answer : α → Word}
    (h : IsPolyTime input (fun a => finiteConfigEncoding (cfg a)))
    (hanswer : IsPolyTime input answer) (channel : Oracle) (next : State) :
    IsPolyTime input (fun a => finiteConfigEncoding ((cfg a).receive channel next (answer a))) := by
  have ht := h.finiteConfig_tapes
  have hbits : IsPolyTime input (fun a => listEncoding (finiteEncoding Bool) (answer a)) := by
    simpa using hanswer.encode_list_bool.list_map
      (isPolyTime_of_finite boolEncoding (finiteEncoding Bool))
  exact (ht.finiteCfg_input.finiteCfg_mk (isPolyTime_const input _)
    ht.finiteCfg_inputPos ht.finiteCfg_workTapes ht.finiteCfg_output).finiteConfig_mk
      (h.finiteConfig_channels.pi_update
        ((isPolyTime_const input (wordEncoding [])).pair hbits.biTape_mk₁) channel)

/-- Initialize all channels with empty requests and blank answer tapes. -/
theorem IsPolyTime.finiteConfig_init {word : α → Word} (h : IsPolyTime input word)
    (state : State) : IsPolyTime input (fun a => finiteConfigEncoding
      (FiniteConfig.init (k := k) (Oracle := Oracle) state (word a))) :=
  (h.finiteCfg_init state).finiteConfig_mk (isPolyTime_const input _)

/-- The full encoding is linear in the input, elapsed clock and largest reply size. The constant
depends only on the fixed control and channel types and the fixed number of work tapes. -/
theorem length_finiteConfigEncoding_le : ∃ c : ℕ,
    ∀ (inputSize steps answerSize : ℕ) (cfg : FiniteConfig k Bool State Oracle),
      FiniteConfig.SpaceBound inputSize steps answerSize cfg →
      (finiteConfigEncoding cfg).length ≤ c * (inputSize + steps + answerSize + 1) := by
  refine ⟨19 + 4 * Nat.card (Option State) + 132 * k + 39 * Fintype.card Oracle, ?_⟩
  intro inputSize steps answerSize cfg h
  let bound := inputSize + steps + answerSize + 1
  have hpositive : 1 ≤ bound := by dsimp [bound]; lia
  have htape (tape : BiTape Bool) (htape : tape.spaceUsed ≤ bound) :
      (biTapeEncoding tape).length ≤ 16 * bound := by
    have hh := length_biTapeEncoding_le tape
    norm_num [Nat.card_eq_fintype_card] at hh
    exact hh.trans (Nat.mul_le_mul_left 16 htape)
  have hwork : (piEncoding biTapeEncoding cfg.tapes.workTapes).length ≤ 33 * k * bound := by
    calc
      _ ≤ k * (2 * (16 * bound) + 1) := by
        simpa using length_piEncoding_le biTapeEncoding cfg.tapes.workTapes (16 * bound)
          (fun tape => htape _ ((h.work tape).trans (by dsimp [bound]; lia)))
      _ ≤ k * (33 * bound) := Nat.mul_le_mul_left k (by lia)
      _ = _ := by ring
  have hcontrol : (finiteEncoding (Option State) cfg.tapes.state).length ≤
      Nat.card (Option State) * bound :=
    (length_finiteEncoding_lt _).le.trans (by
      simpa using Nat.mul_le_mul_left (Nat.card (Option State)) hpositive)
  have hinput := h.input
  have hposition := cfg.tapes.inputPos.isLt
  have houtput := h.output
  have hcfg : (finiteCfgEncoding cfg.tapes).length ≤
      (9 + 2 * Nat.card (Option State) + 66 * k) * bound := by
    change (pairEncoding _ _ _).length ≤ _
    simp only [length_pairEncoding, wordEncoding, Function.Embedding.refl_apply,
      unaryEncoding_apply, List.length_replicate]
    dsimp [bound] at *
    nlinarith
  have hchannel (channel : Oracle) :
      (pairEncoding wordEncoding biTapeEncoding (cfg.channels channel)).length ≤ 19 * bound := by
    have hquery := h.query channel
    have hanswer := htape _ ((h.answer channel).trans (by dsimp [bound]; lia))
    simp only [length_pairEncoding, wordEncoding, Function.Embedding.refl_apply]
    dsimp [bound] at *
    lia
  have hchannels : (piEncoding (pairEncoding wordEncoding biTapeEncoding) cfg.channels).length ≤
      39 * Fintype.card Oracle * bound := by
    calc
      _ ≤ Fintype.card Oracle * (2 * (19 * bound) + 1) :=
        length_piEncoding_le _ _ _ hchannel
      _ ≤ Fintype.card Oracle * (39 * bound) := Nat.mul_le_mul_left _ (by lia)
      _ = _ := by ring
  change (pairEncoding _ _ _).length ≤ _
  simp only [length_pairEncoding]
  change _ ≤ (19 + 4 * Nat.card (Option State) + 132 * k + 39 * Fintype.card Oracle) * bound
  nlinarith

end Cslib.Probability
