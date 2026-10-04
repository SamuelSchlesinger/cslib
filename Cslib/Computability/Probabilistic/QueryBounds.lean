/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Probabilistic.Oracle
public import Cslib.Computability.Machines.Turing.MultiTape.Oracle.QueryBounds

/-!
# Polynomial query bounds for oracle programs

An oracle PPT certificate supplies polynomial bounds on both the number and the encoded length
of requests. The bounds hold for every stateful oracle, including unbounded replies, and need no
extra assumption from the caller. They follow by observing transcripts in the stateful
realization contract.

These are bounds on calls made by the program. Calls made internally by an oracle's own handler
belong to that handler's separate efficiency analysis.
-/

public section

namespace Cslib.Probability

/-- A single polynomial bounds the number and length of every oracle request, uniformly over
all inputs and all shared stateful handlers. The machine witness stays inside the proof. -/
theorem IsOraclePPTOn.query_bounds {Operation α β : Type} [DecidableEq Operation]
    {input : α → Word} {output : β ↪ Word} {program : α → WordOracleComp Operation β}
    (h : IsOraclePPTOn input output program) :
    ∃ c d : ℕ, ∀ a, (program a).HasQueryBounds (fun request => request.2.length)
      (c * ((input a).length + 1) ^ d) (c * ((input a).length + 1) ^ d) := by
  obtain ⟨_, k, Control, _, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a => (OracleComp.hasQueryBounds_map_iff output (program a) ..).mp ?_⟩
  intro State oracle s s' result transcript hresult
  rw [h a] at hresult
  exact Turing.MultiTapePTM.query_bounds_run machine (fun op word => (op, word))
    (fun request => request.2.length) (fun _ _ => le_rfl) oracle _ (input a) s s' result
    transcript hresult

/-- The single-operation cryptographic interface has the same polynomial query guarantees. -/
theorem IsOraclePPT.query_bounds {α : Type} {output : α ↪ Word}
    {program : ℕ → Word → OracleComp Word (fun _ => Word) α}
    (h : IsOraclePPT output program) :
    ∃ c d : ℕ, ∀ n input, (program n input).HasQueryBounds List.length
      (c * (n + input.length + 2) ^ d) (c * (n + input.length + 2) ^ d) := by
  obtain ⟨k, states, machine, c, d, h⟩ := h
  refine ⟨c, d, fun n input =>
    (OracleComp.hasQueryBounds_map_iff output (program n input) ..).mp ?_⟩
  intro State oracle s s' result transcript hresult
  rw [h n input, ← Turing.OracleTM.run_core] at hresult
  simpa [Nat.add_assoc] using Turing.MultiTapePTM.query_bounds_run machine
    (fun _ word => word) List.length (fun _ _ => le_rfl) oracle _ (parameterInput n input)
    s s' result transcript hresult

end Cslib.Probability
