/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.OracleSimulation
public import Cslib.Languages.Probabilistic.Presample

/-!
# Efficient simulation with saved samples

An oracle reduction may replace fresh draws by a supplied list. The handler's local invariant and
resource allowance must hold for every supplied value, including the fallback on short lists.
The sample list only shrinks, so its storage requires no additional growth invariant.

This certificate is independent of the pre-sampling distribution law: all supplied lists are
handled efficiently, whether or not they were drawn from the intended distribution.
-/

public section

namespace Cslib.Probability

/-- Supply saved samples to a closed stateful handler, preserving the efficiency of an oracle
adversary. The local contract bounds replies and added storage for every supplied value.
The certificate charges for sample consumption and retains the final ordinary private state. -/
theorem IsOraclePPT.simulateWithSamples {β Caller State Value : Type}
    {input : Caller ↪ Word} {output : β ↪ Word} {stateEncoding : State ↪ Word}
    {valueEncoding : Value ↪ Word} {program : ℕ → Word → OracleComp Word (fun _ => Word) β}
    {handler : Caller → Value → Word → State → ProbComp (Word × State)}
    {prepare : Caller → ℕ × Word} {initial : Caller → State} {values : Caller → List Value}
    {resources : Caller → Word → ℕ}
    (hprogram : IsOraclePPT output program) (fallback : Value)
    (hprepare : IsPolyTime input (fun a => parameterEncoding (prepare a)))
    (hhandler : IsPPTOn
      (pairEncoding (pairEncoding input valueEncoding) (pairEncoding wordEncoding stateEncoding))
      (pairEncoding wordEncoding stateEncoding)
      (fun pair => handler pair.1.1 pair.1.2 pair.2.1 pair.2.2))
    (hinitial : IsPolyTime input (fun a => stateEncoding (initial a)))
    (hvalues : IsPolyTime input (fun a => listEncoding valueEncoding (values a)))
    (invariant : Caller → State → Prop) (hinit : ∀ a, invariant a (initial a))
    (hresources : IsPolyTime (pairEncoding input wordEncoding)
      (fun pair => unaryEncoding (resources pair.1 pair.2)))
    (hpreserve : ∀ a value query state, invariant a state →
      ∀ result ∈ (ProbComp.eval (handler a value query state)).support,
        invariant a result.2 ∧ result.1.length ≤ resources a query ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length + resources a query) :
    IsPPTOn input (pairEncoding output stateEncoding) (fun a =>
      OracleComp.simulateWithSamples fallback (handler a)
        (program (prepare a).1 (prepare a).2) (initial a) (values a)) := by
  let storage := pairEncoding stateEncoding (listEncoding valueEncoding)
  have hwrapped : IsPPTOn (pairEncoding input (pairEncoding wordEncoding storage))
      (pairEncoding wordEncoding storage) (fun pair =>
        OracleComp.withSampleList fallback (handler pair.1) pair.2.1 pair.2.2) := by
    unfold OracleComp.withSampleList storage
    ppt
  have hrun : IsPPTOn input (pairEncoding output storage) (fun a =>
      OracleComp.simulateState (OracleComp.withSampleList fallback (handler a))
        (program (prepare a).1 (prepare a).2) (initial a, values a)) := by
    refine hprogram.simulateState_preprocess hprepare hwrapped (hinitial.pair hvalues)
      (fun a state => invariant a state.1) hinit
      (resources := fun a query => 2 * resources a query) (by polytime) ?_
    intro a query state hstate result hresult
    simp only [OracleComp.withSampleList, ProbComp.eval_map, PMF.mem_support_map_iff] at hresult
    obtain ⟨⟨answer, next⟩, hresult, rfl⟩ := hresult
    obtain ⟨hnext, hreply, hgrowth⟩ :=
      hpreserve a (state.2.headD fallback) query state.1 hstate (answer, next) hresult
    have htail := length_listEncoding_drop_le valueEncoding state.2 1
    simp only [List.drop_one] at htail
    refine ⟨hnext, by dsimp at hreply ⊢; lia, ?_⟩
    simp only [storage, length_pairEncoding]
    dsimp at hgrowth ⊢
    lia
  exact hrun.map (by unfold storage; polytime)

end Cslib.Probability
