/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Circuits.Basis

@[expose] public section

/-! # Boolean Circuits (DAG-based)

A Boolean circuit is a directed acyclic graph (DAG) of gates, unlike a `Formula` which is
a tree (no fan-out sharing). A polynomial-size circuit can compute functions that would
require an exponential-size formula, making circuits the standard model for non-uniform
complexity classes like P/poly and SIZE(s).

## Design notes

A circuit over `n` input variables is represented as a list of `Gate`s in topological order.
Wires `0..n-1` carry the input variables; wire `n + i` carries the output of `gates[i]`.
Each gate references its inputs by wire index, and the circuit designates one wire as the
output.

There is no well-formedness constraint in the `Circuit` structure. Instead, `Circuit.eval`
uses defensive evaluation: out-of-bounds wire references produce `false`, and arity
mismatches produce `false`. This mirrors the `Formula.eval` design.

## Main definitions

- `Gate` — a gate with an operation and a list of input wire indices
- `Circuit` — a circuit with `n` input variables, a list of gates, and an output wire
- `Circuit.eval` — evaluate a circuit on an input assignment
- `Circuit.size` — number of gates in a circuit
- `Circuit.depth` — longest path from an input to the output
- `CircuitFamily` — a family of circuits indexed by input size
- `CircuitFamily.Decides` — a circuit family decides a language

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraB2009]
-/

namespace Cslib.Circuits

/-- A gate in a circuit, consisting of an operation and a list of input wire indices. -/
structure Gate (Op : Type*) where
  /-- The gate operation. -/
  op : Op
  /-- The wire indices feeding into this gate. -/
  inputs : List ℕ

/-- A Boolean circuit with `n` input variables.

Wires `0..n-1` are input wires. Wire `n + i` is the output of `gates[i]`.
The circuit produces its result on `outputWire`. -/
structure Circuit (Op : Type*) (n : ℕ) where
  /-- The gates of the circuit, in topological order. -/
  gates : List (Gate Op)
  /-- The wire carrying the circuit's output. -/
  outputWire : ℕ

namespace Gate

variable {Op Op' : Type*}

/-- Map a function over the operation of a gate, preserving wire structure. -/
def mapOp (f : Op → Op') (g : Gate Op) : Gate Op' :=
  { op := f g.op, inputs := g.inputs }

end Gate

namespace Circuit

variable {Op : Type*} {n : ℕ}

/-! ### Evaluation -/

/-- Evaluate a circuit on an input assignment.

Builds a list of wire values by folding over the gates in order. Each gate reads its
inputs from previous wire values (defaulting to `false` for out-of-bounds references)
and appends its output. The result is the value on `outputWire`. -/
@[simp, scoped grind =]
def eval [Basis Op] (C : Circuit Op n) (input : Fin n → Bool) : Bool :=
  let inputList := List.ofFn input
  let allWires := C.gates.foldl (fun wires gate =>
    let gateInputs := gate.inputs.map (wires.getD · false)
    let output := if h : (Basis.arity gate.op).admits gateInputs.length
                  then Basis.eval gate.op gateInputs h
                  else false
    wires ++ [output]) inputList
  allWires.getD C.outputWire false

/-! ### Measures -/

/-- The number of gates in a circuit. -/
@[simp, scoped grind =]
def size (C : Circuit Op n) : ℕ := C.gates.length

/-- The depth of a circuit: the longest path from any input wire to the output wire.

Computed by tracking the depth of each wire. Input wires have depth 0. Each gate's depth
is one more than the maximum depth of its inputs. The circuit's depth is the depth of the
output wire. Returns 0 if the output wire is out of bounds. -/
@[simp, scoped grind =]
def depth [Basis Op] (C : Circuit Op n) : ℕ :=
  let inputDepths := List.replicate n 0
  let allDepths := C.gates.foldl (fun depths gate =>
    let gateDepth := gate.inputs.foldl (fun maxD i => max maxD (depths.getD i 0)) 0 + 1
    depths ++ [gateDepth]) inputDepths
  allDepths.getD C.outputWire 0

/-! ### Well-formedness -/

/-- A circuit is **gates-well-formed** if every gate's input list has a length
admitted by the gate's operation arity. This ensures that `eval` never hits the
defensive `false` fallback for arity mismatches. -/
def GatesWellFormed [Basis Op] (C : Circuit Op n) : Prop :=
  ∀ g ∈ C.gates, (Basis.arity g.op).admits g.inputs.length

/-! ### Gate and circuit mapping -/

variable {Op' : Type*}

/-- Map a function over the operations of every gate in a circuit.
This is used to embed a circuit over one basis into another
(e.g., `NCOp → ACOp` for the `NC ⊆ AC` inclusion). -/
def mapOp (f : Op → Op') (C : Circuit Op n) : Circuit Op' n :=
  { gates := C.gates.map (Gate.mapOp f), outputWire := C.outputWire }

@[simp]
theorem size_mapOp (f : Op → Op') (C : Circuit Op n) :
    (C.mapOp f).size = C.size := by
  simp [mapOp, size]

/-- `mapOp` preserves gate well-formedness when the mapping preserves
arity admissibility: if every admitted input count for `op` is also
admitted for `f op`, then well-formedness transfers. -/
theorem GatesWellFormed_mapOp [Basis Op] [Basis Op'] (f : Op → Op') (C : Circuit Op n)
    (hadmits : ∀ op n, (Basis.arity op).admits n → (Basis.arity (f op)).admits n)
    (hWF : C.GatesWellFormed) :
    (C.mapOp f).GatesWellFormed := by
  intro g hg
  simp only [mapOp, List.mem_map] at hg
  obtain ⟨g', hg'_mem, hg'_eq⟩ := hg
  subst hg'_eq
  simp only [Gate.mapOp]
  exact hadmits g'.op g'.inputs.length (hWF g' hg'_mem)

/-- `mapOp` preserves depth because depth only depends on wire connectivity,
not on gate operations. -/
theorem depth_mapOp [Basis Op] [Basis Op'] (f : Op → Op') (C : Circuit Op n) :
    (C.mapOp f).depth = C.depth := by
  simp only [depth, mapOp]
  -- The depth foldl step function only uses gate.inputs, which mapOp preserves
  suffices ∀ (gs : List (Gate Op)) (acc : List ℕ),
    (gs.map (Gate.mapOp f)).foldl
      (fun depths gate =>
        depths ++ [gate.inputs.foldl
          (fun maxD i => max maxD (depths.getD i 0)) 0 + 1])
      acc =
    gs.foldl
      (fun depths gate =>
        depths ++ [gate.inputs.foldl
          (fun maxD i => max maxD (depths.getD i 0)) 0 + 1])
      acc by
    exact congr_arg (·.getD C.outputWire 0) (this C.gates _)
  intro gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons, Gate.mapOp]
    exact ih _

/-- `mapOp` preserves evaluation when the function preserves gate semantics:
same arity and same evaluation on admitted inputs. -/
theorem eval_mapOp [Basis Op] [Basis Op'] (f : Op → Op') (C : Circuit Op n)
    (harity : ∀ op, Basis.arity (f op) = Basis.arity op)
    (heval : ∀ op bs (h : (Basis.arity op).admits bs.length),
      Basis.eval (f op) bs (harity op ▸ h) = Basis.eval op bs h)
    (input : Fin n → Bool) :
    (C.mapOp f).eval input = C.eval input := by
  simp only [eval, mapOp]
  suffices ∀ (gs : List (Gate Op)) (acc : List Bool),
    (gs.map (Gate.mapOp f)).foldl
      (fun wires gate =>
        wires ++ [if h : (Basis.arity gate.op).admits
                    (gate.inputs.map (wires.getD · false)).length
                  then Basis.eval gate.op (gate.inputs.map (wires.getD · false)) h
                  else false])
      acc =
    gs.foldl
      (fun wires gate =>
        wires ++ [if h : (Basis.arity gate.op).admits
                    (gate.inputs.map (wires.getD · false)).length
                  then Basis.eval gate.op (gate.inputs.map (wires.getD · false)) h
                  else false])
      acc by
    exact congr_arg (·.getD C.outputWire false) (this C.gates _)
  intro gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons, Gate.mapOp]
    -- Show the gate output is the same for f g.op vs g.op with same inputs
    have h_output :
      (if h : (Basis.arity (f g.op)).admits
              (g.inputs.map (acc.getD · false)).length
       then Basis.eval (f g.op) (g.inputs.map (acc.getD · false)) h
       else false) =
      (if h : (Basis.arity g.op).admits
              (g.inputs.map (acc.getD · false)).length
       then Basis.eval g.op (g.inputs.map (acc.getD · false)) h
       else false) := by
      set bs := g.inputs.map (acc.getD · false)
      by_cases hadmits : (Basis.arity g.op).admits bs.length
      · have hadmits' : (Basis.arity (f g.op)).admits bs.length := by rw [harity]; exact hadmits
        rw [dif_pos hadmits', dif_pos hadmits]
        exact heval g.op bs hadmits
      · have hadmits' : ¬(Basis.arity (f g.op)).admits bs.length := by rw [harity]; exact hadmits
        rw [dif_neg hadmits', dif_neg hadmits]
    rw [h_output]
    exact ih _

/-! ### Basic lemmas -/

@[simp]
theorem size_mk (gates : List (Gate Op)) (out : ℕ) :
    (Circuit.mk gates out : Circuit Op n).size = gates.length := rfl

end Circuit

/-! ### Circuit Families -/

/-- A circuit family assigns a circuit to each input size `n`. -/
def CircuitFamily (Op : Type*) := (n : ℕ) → Circuit Op n

namespace CircuitFamily

variable {Op : Type*}

/-- A circuit family `C` **decides** a language `L : Set (List Bool)` when
for every input `x`, membership in `L` is equivalent to the circuit of size `x.length`
accepting `x`. -/
def Decides [Basis Op] (C : CircuitFamily Op) (L : Set (List Bool)) : Prop :=
  ∀ x : List Bool, x ∈ L ↔ (C x.length).eval (x.get ·) = true

end CircuitFamily

end Cslib.Circuits
