/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Crypto.Computational.OneWay
import Cslib.Crypto.Computational.PseudorandomGenerator
import Cslib.Crypto.Computational.PseudorandomFunction
import Cslib.Crypto.Computational.Hybrid
import Cslib.Computability.Probabilistic.Output

/-!
# Computational cryptography examples

These examples exercise actual PPT certificates, adaptive and stateful oracles, and security-game
semantics. In particular, the repeated-query test distinguishes a fixed random function from an
oracle which resamples on every call, and an explicit oracle PPT adversary shows that a family
answering every query with ones is not pseudorandom.
-/

namespace CslibTests.ComputationalCrypto

open Cslib Cslib.Probability Cslib.Crypto

noncomputable section

/-- A machine writes its fresh random bit and halts. -/
def coinMachine : Turing.OracleTM 0 (Fin 1) :=
  Turing.OracleTM.mk (0) fun _ _ _ _ coin => .step
    { inputTape := 0, workTapes := Fin.elim0, output := some coin, state := none } none 0

example : IsPPT boolEncoding (fun _ _ => OracleComp.uniform Bool) := by
  refine ⟨0, 1, coinMachine, 1, 0, ?_⟩
  intro pair
  simp [Turing.OracleTM.run, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    coinMachine, Turing.OracleTM.Config.step, Turing.Action.apply, OracleComp.uniform,
    boolEncoding, PMF.map, Function.comp_def]

/-- Query the empty word, then copy the first answer bit (or false for an empty answer). -/
def firstAnswerMachine : Turing.OracleTM 0 (Fin 2) :=
  Turing.OracleTM.mk (0) fun state _ _ answer _ =>
    if state = 0 then .query 1
    else .step
      { inputTape := 0, workTapes := Fin.elim0, output := some (answer.getD false), state := none }
      none 0

/-- A high-level oracle program with a concrete two-transition realization. The certificate
quantifies over all stateful oracles and preserves the final oracle state. -/
example : IsOraclePPT boolEncoding
    (fun _ _ => do return (← OracleComp.query []).headD false) := by
  refine ⟨0, 2, firstAnswerMachine, 2, 0, ?_⟩
  intro n x State oracle s
  simp [Turing.OracleTM.run, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    firstAnswerMachine, Turing.OracleTM.Config.step, Turing.OracleTM.Config.receive,
    Turing.OracleTM.Config.answerSymbol, Turing.Action.apply, OracleComp.uniform,
    boolEncoding, PMF.map, Function.comp_def, List.headD_eq_head?_getD, List.head?_eq_getElem?]

/-- The second query is the answer to the first. -/
def adaptive (input : Word) : OracleComp Word (fun _ => Word) Word := do
  let answer ← OracleComp.query input
  OracleComp.query answer

example (f : Word → Word) (input : Word) :
    OracleComp.eval (fun query => PMF.pure (f query)) (adaptive input) =
      PMF.pure (f (f input)) := by
  simp [adaptive]

/-- A private Boolean state alternates the returned bit. -/
def alternatingOracle (_ : Word) : StateT Bool PMF Word :=
  fun state => PMF.pure ([state], !state)

/-- This machine never halts: only its external clock stops the coin stream. -/
def streamingCoinMachine : Turing.OracleTM 0 (Fin 1) :=
  Turing.OracleTM.mk (0) fun _ _ _ _ coin => .step
    { inputTape := 0, workTapes := Fin.elim0, output := some coin, state := some 0 } none 0

/-- Unequal codeword lengths, including erasure, are allowed. -/
def unevenCode (bit : Bool) : Word := if bit then [true, false] else []

/-- After exactly two source steps, exactly one true coin has probability one half.
The expanded machine flushes the complete codeword even though the source never halts. -/
example : OracleComp.eval (fun _ => PMF.pure [])
    ((streamingCoinMachine.expandOutput unevenCode).run 8 []) [true, false] = 1 / 2 := by
  change OracleComp.eval (fun _ => PMF.pure [])
    ((streamingCoinMachine.expandOutput unevenCode).run
      ((Turing.OracleTM.OutputExpansion.width unevenCode + 2) * 2) []) _ = _
  rw [Turing.OracleTM.eval_run_expandOutput]
  norm_num [Turing.OracleTM.run, Turing.OracleTM.runFrom_zero, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    streamingCoinMachine, Turing.OracleTM.Config.step, Turing.Action.apply, OracleComp.uniform,
    unevenCode, PMF.map, Function.comp_def, PMF.bind_apply, PMF.uniformOfFintype_apply,
    tsum_fintype]
  rw [← add_mul, ← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

/-- Erasing the output still performs the query and preserves its effect on private state. -/
example : OracleComp.runState alternatingOracle
    ((firstAnswerMachine.expandOutput (fun _ => [])).run 4 []) false =
      PMF.pure ([], true) := by
  change OracleComp.runState alternatingOracle
    ((firstAnswerMachine.expandOutput (fun _ => [])).run
      ((Turing.OracleTM.OutputExpansion.width (fun _ => []) + 2) * 2) []) false = _
  rw [Turing.OracleTM.runState_run_expandOutput]
  simp [Turing.OracleTM.run, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    firstAnswerMachine, Turing.OracleTM.Config.step, Turing.OracleTM.Config.receive,
    Turing.OracleTM.Config.answerSymbol, Turing.Action.apply, OracleComp.uniform,
    alternatingOracle, PMF.map, Function.comp_def]

/-- A bit emitted on the halting transition is expanded completely. -/
example : OracleComp.eval (fun _ => PMF.pure [])
    (((returnBitMachine true).expandOutput unevenCode).run 4 []) =
      PMF.pure [true, false] := by
  change OracleComp.eval (fun _ => PMF.pure [])
    (((returnBitMachine true).expandOutput unevenCode).run
      ((Turing.OracleTM.OutputExpansion.width unevenCode + 2) * 1) []) = _
  rw [Turing.OracleTM.eval_run_expandOutput]
  simp [Turing.OracleTM.run, Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    returnBitMachine, Turing.OracleTM.Config.step, Turing.Action.apply, OracleComp.uniform,
    unevenCode, PMF.map, Function.comp_def]

/-- Pause just after the query, then resume with the saved answer and oracle state. -/
example :
    OracleComp.runState alternatingOracle
      (do
        let cfg ← firstAnswerMachine.runConfigFrom 1 (firstAnswerMachine.initialConfig [])
        firstAnswerMachine.runFrom 1 cfg) false = PMF.pure ([false], true) := by
  rw [← Turing.OracleTM.runFrom_add]
  simp [Turing.OracleTM.runFrom_succ,
    Turing.OracleTM.initialConfig, Turing.OracleTM.initial_mk, Turing.OracleTM.transition_mk,
    firstAnswerMachine,
    Turing.OracleTM.Config.step, Turing.OracleTM.Config.receive,
    Turing.OracleTM.Config.answerSymbol, Turing.Action.apply, OracleComp.uniform,
    alternatingOracle, PMF.map, Function.comp_def]

example :
    OracleComp.runState alternatingOracle
      (do
        let first ← OracleComp.query []
        let second ← OracleComp.query []
        return first != second) false = PMF.pure (true, false) := by
  simp [alternatingOracle, PMF.pure_map]
  rfl

/-- Query the same valid input twice and check equality of the responses. -/
def repeatQuery : OracleDistinguisher := fun n _ => do
  let input := List.replicate n false
  let first ← OracleComp.query input
  let second ← OracleComp.query input
  return first == second

example (family : Word → Word → Word) (n : ℕ) :
    ProbComp.eval (prfRealGame family repeatQuery n) = PMF.pure true := by
  simp [prfRealGame, repeatQuery, ProbComp.eval, PMF.map,
    Function.comp_def]

example (n : ℕ) : ProbComp.eval (prfIdealGame repeatQuery n) = PMF.pure true := by
  simp [prfIdealGame, repeatQuery, ProbComp.eval, OracleComp.uniform,
    PMF.map, Function.comp_def]

/-- Fresh independent answers pass the repeated-query test with probability one half. -/
example :
    OracleComp.eval (fun _ : Word => (PMF.uniformOfFintype Bool).map (fun bit => [bit]))
      (repeatQuery 1 []) true = 1 / 2 := by
  norm_num [repeatQuery, PMF.map, Function.comp_def, PMF.bind_apply,
    PMF.uniformOfFintype_apply, tsum_fintype]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

example (word : Word) : ¬ OneWay (fun _ => word) := not_oneWay_const word

/-- A different preimage is accepted, even when it has a different length from the sampled input. -/
example (n : ℕ) :
    ProbComp.eval (inversionGame (fun _ => [true]) (fun _ _ => pure []) n) = PMF.pure true :=
  eval_inversionGame_of_rightInverse _ (fun _ => []) (fun _ => rfl) n

example (X Y Z : ℕ → PMF Word) (hXY : ComputationallyIndistinguishable X Y)
    (hYZ : ComputationallyIndistinguishable Y Z) : ComputationallyIndistinguishable X Z :=
  hXY.trans hYZ

section NotPseudorandom

open Turing

/-- Copy the unary security parameter into the query buffer, submit it, and output the first bit
of the answer. -/
def firstBitMachine : OracleTM 0 (Fin 2) :=
  OracleTM.mk 0 fun state symbol _ answer _ =>
    if state = 0 then
      match symbol with
      | some true => .step ⟨1, Fin.elim0, none, some 0⟩ (some true) 0
      | _ => .query 1
    else .step ⟨0, Fin.elim0, some (answer.getD false), none⟩ none 0

/-- Query the all-ones word of the parameter's length and return the first answer bit. -/
def firstBit (n : ℕ) (_ : Word) : OracleComp Word (fun _ => Word) Bool := do
  let answer ← OracleComp.query (List.replicate n true)
  return answer.headD false

theorem transition_scan (w : Fin 0 → Option Bool) (a : Option Bool) (c : Bool) :
    firstBitMachine.transition 0 (some true) w a c =
      .step ⟨1, Fin.elim0, none, some 0⟩ (some true) 0 := by
  simp [firstBitMachine]

theorem transition_submit (w : Fin 0 → Option Bool) (a : Option Bool) (c : Bool) :
    firstBitMachine.transition 0 (some false) w a c = .query 1 := by
  simp [firstBitMachine]

theorem transition_answer (symbol : Option Bool) (w : Fin 0 → Option Bool) (a : Option Bool)
    (c : Bool) : firstBitMachine.transition 1 symbol w a c =
      .step ⟨0, Fin.elim0, some (a.getD false), none⟩ none 0 := by
  simp [firstBitMachine]

/-- The machine after copying `j` bits of the unary parameter. -/
def scanCfg (n : ℕ) (input : Word) (j : ℕ) (hj : j ≤ n) :
    OracleTM.Config 0 (Fin 2) (parameterInput n input) where
  tapes := ⟨some 0, ⟨j + 1, by simp [length_parameterInput]; omega⟩, fun _ _ => none,
    fun _ => 0, []⟩
  queryBuffer := List.replicate j true

/-- Copying the remaining bits of the parameter consumes coins but no oracle calls. -/
theorem runState_scan {State : Type} (oracle : Word → StateT State PMF Word) (s : State)
    (n : ℕ) (input : Word) (fuel : ℕ) : ∀ m j (hj : j + m = n),
      OracleComp.runState oracle
          (firstBitMachine.runFrom (fuel + m) (scanCfg n input j (by omega))) s =
        OracleComp.runState oracle (firstBitMachine.runFrom fuel (scanCfg n input n le_rfl)) s := by
  intro m
  induction m with
  | zero => intro j hj; subst hj; rfl
  | succ m ih =>
    intro j hj
    have hsym : (scanCfg n input j (by omega)).tapes.inputSymbol = some true := by
      rw [inputSymbolInner (cfg := (scanCfg n input j (by omega)).tapes) j
        (by simp [scanCfg]; omega) (by simp [length_parameterInput]; omega)]
      simp [parameterInput,
        List.getElem_append_left (by simp; omega : j < (List.replicate n true).length)]
    have hstep : (scanCfg n input j (by omega)).step ⟨1, Fin.elim0, none, some 0⟩ (some true) 0 =
        scanCfg n input (j + 1) (by omega) := by
      apply OracleTM.Config.ext
      · apply Cfg.ext
        · rfl
        · apply Fin.ext
          have h := val_moveInputPos_eq (⟨j + 1, by simp [length_parameterInput]; omega⟩ :
            Fin ((parameterInput n input).length + 2)) 1
          simp only [length_parameterInput] at h ⊢
          simp only [scanCfg, OracleTM.Config.step, Action.apply_inputPos]
          simp [SignType.cast] at h
          omega
        · funext i; exact i.elim0
        · funext i; exact i.elim0
        · simp [scanCfg, OracleTM.Config.step, Action.apply]
      · simp [scanCfg, OracleTM.Config.step, List.replicate_succ']
      · simp [scanCfg, OracleTM.Config.step]
      · simp [scanCfg, OracleTM.Config.step]
    rw [show fuel + (m + 1) = (fuel + m) + 1 by omega, OracleTM.runFrom_succ, hsym]
    simp only [show (scanCfg n input j (by omega)).tapes.state = some 0 from rfl, transition_scan,
      hstep, OracleComp.uniform, OracleComp.runState_sample_bind, PMF.bind_const]
    exact ih (j + 1) (by omega)

/-- The adversary has a concrete realization, valid for every stateful oracle. -/
theorem isOraclePPT_firstBit : IsOraclePPT boolEncoding firstBit := by
  refine ⟨0, 2, firstBitMachine, 1, 1, ?_⟩
  intro n input State oracle s
  have hfuel : 1 * ((parameterInput n input).length + 1) ^ 1 = (input.length + 2) + n := by
    simp [length_parameterInput]; omega
  have hinit : firstBitMachine.initialConfig (parameterInput n input) =
      scanCfg n input 0 (Nat.zero_le _) := by
    apply OracleTM.Config.ext
    · apply Cfg.ext <;> rfl
    all_goals rfl
  rw [hfuel, OracleTM.run, hinit,
    runState_scan oracle s n input (input.length + 2) n 0 (by omega)]
  have hsym : (scanCfg n input n le_rfl).tapes.inputSymbol = some false := by
    rw [inputSymbolInner (cfg := (scanCfg n input n le_rfl).tapes) n
      (by simp [scanCfg]; omega) (by simp [length_parameterInput])]
    simp [parameterInput]
  rw [show input.length + 2 = (input.length + 1) + 1 by omega, OracleTM.runFrom_succ, hsym]
  simp only [show (scanCfg n input n le_rfl).tapes.state = some 0 from rfl, transition_submit,
    OracleComp.uniform, OracleComp.runState_sample_bind, PMF.bind_const]
  have hfinish (a : Word) (s' : State) : OracleComp.runState oracle
      (firstBitMachine.runFrom (input.length + 1) ((scanCfg n input n le_rfl).receive 1 a)) s' =
        PMF.pure ([a.headD false], s') := by
    rw [OracleTM.runFrom_succ]
    simp only [show ((scanCfg n input n le_rfl).receive 1 a).tapes.state = some 1 from rfl,
      transition_answer, OracleComp.uniform, OracleComp.runState_sample_bind]
    rw [OracleTM.runFrom_halted _ _ _ rfl]
    simp [OracleTM.Config.step, Action.apply, OracleTM.Config.answerSymbol,
      OracleTM.Config.receive, scanCfg, List.headD_eq_head?_getD, List.head?_eq_getElem?]
  simp only [OracleComp.runState_bind, OracleComp.runState_query, hfinish, firstBit,
    OracleComp.runState_map, OracleComp.runState_pure]
  rw [PMF.map_bind]
  simp [scanCfg, boolEncoding, PMF.pure_map]

/-- A keyed family that answers every valid query with ones. -/
def onesFamily (key _ : Word) : Word := List.replicate key.length true

theorem eval_real (n : ℕ) (hn : 1 ≤ n) :
    ProbComp.eval (prfRealGame onesFamily firstBit n) = PMF.pure true := by
  simp only [prfRealGame, firstBit, prfOracle, onesFamily, List.headD_eq_head?_getD,
    bind_pure_comp, OracleComp.simulate_map, OracleComp.simulate_query, List.length_replicate,
    ↓reduceIte, map_pure, ProbComp.eval_map, ProbComp.eval_sample]
  rw [PMF.map_congr_on_support _ _ (fun _ => true)]
  · exact PMF.map_const _ _
  intro key hkey
  rw [length_of_mem_support_uniformBits hkey]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [List.replicate_succ]

theorem eval_ideal (n : ℕ) (hn : 1 ≤ n) :
    ProbComp.eval (prfIdealGame firstBit n) = PMF.uniformOfFintype Bool := by
  simp only [prfIdealGame, randomFunctionOracle, firstBit, List.headD_eq_head?_getD,
    bind_pure_comp, OracleComp.simulate_map, OracleComp.simulate_query, List.length_replicate,
    ↓reduceIte, Fin.is_lt, getElem?_pos, List.getElem_replicate, Option.getD_some, map_pure,
    ProbComp.eval_map]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [List.ofFn_succ, List.head?_cons, Option.getD_some, OracleComp.uniform,
    ProbComp.eval_sample]
  rw [show (fun a : BitString (m + 1) → BitString (m + 1) => a (fun _ => true) 0) =
      (fun b : BitString (m + 1) => b 0) ∘ (fun a => a (fun _ => true)) from rfl, ← PMF.map_comp,
    ← PMF.pi_uniformOfFintype, PMF.pi_map_eval, ← PMF.pi_uniformOfFintype, PMF.pi_map_eval]

/-- Answering every query with ones is not pseudorandom: the first answer bit distinguishes it
from a random function with advantage one half. -/
theorem not_pseudorandomFunction_ones : ¬ PseudorandomFunction onesFamily := by
  intro h
  apply not_negligible_const (c := 1 / 2) (by norm_num)
  refine (h.secure firstBit isOraclePPT_firstBit).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [eval_real n hn, eval_ideal n hn]
  simp [Game.advantage, Game.winProbability, PMF.uniformOfFintype_apply]
  norm_num

end NotPseudorandom

/-- A negligible bound for each fixed hop is insufficient for a growing hybrid sequence. -/
def isolatedAdvantage (i n : ℕ) : ℝ := if n = i then 1 else 0

example (i : ℕ) : Negligible (isolatedAdvantage i) := by
  apply negligible_zero.congr'
  filter_upwards [Filter.eventually_gt_atTop i] with n hn
  simp [isolatedAdvantage, Nat.ne_of_gt hn]

example : ¬ Negligible (fun n => isolatedAdvantage n n) := by
  simpa [isolatedAdvantage] using (not_negligible_const (c := 1) one_ne_zero)

end

end CslibTests.ComputationalCrypto
