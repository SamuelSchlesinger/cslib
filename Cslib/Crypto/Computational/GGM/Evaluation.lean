/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import Cslib.Tactic.PolyTime
public import Cslib.Computability.Probabilistic.Encoding

/-!
# Evaluating the GGM tree

Starting from a secret root label, follow the query bits down a binary tree. Each expansion
provides two labels of the current seed width. The evaluator is an ordinary word fold, and its
polynomial-time certificate comes from the fold compiler.

Extra generator output is discarded. In particular, a generator of length `2 * n + 1` supplies
both `n`-bit children even at `n = 0`, where the result is the empty word.

This module proves evaluation and size properties. Pseudorandomness requires the adaptive
oracle hybrid argument in addition to these facts.

## References

O. Goldreich, S. Goldwasser, S. Micali,
[*How to Construct Random Functions*](https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf),
Section 3.2.
-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Probability

/-- Select one of the two consecutive child labels, discarding any surplus expansion bits. -/
def selectChild (width : ℕ) (expansion : Word) (bit : Bool) : Word :=
  if bit then (expansion.drop width).take width else expansion.take width

/-- Each child fits in the declared width, even when the expansion is short. -/
theorem length_selectChild_le (width : ℕ) (expansion : Word) (bit : Bool) :
    (selectChild width expansion bit).length ≤ width := by
  cases bit <;> simp [selectChild]

/-- Child selection inspects only the first two labels. -/
@[simp] theorem selectChild_take (width : ℕ) (expansion : Word) (bit : Bool) :
    selectChild width (expansion.take (2 * width)) bit = selectChild width expansion bit := by
  cases bit <;>
    simp [selectChild, List.drop_take, List.take_take,
      show 2 * width - width = width by lia, Nat.min_eq_left (by lia : width ≤ 2 * width)]

/-- Expand a node and select the child indicated by one query bit. -/
def child (generator : Word → Word) (seed : Word) (bit : Bool) : Word :=
  selectChild seed.length (generator seed) bit

/-- Follow a query from a root seed, reading its bits from left to right. -/
def eval (generator : Word → Word) (seed query : Word) : Word :=
  query.foldl (child generator) seed

/-- Tree evaluation uses only the first two labels of every generator output. -/
@[simp] theorem eval_truncate (generator : Word → Word) :
    eval (fun seed => (generator seed).take (2 * seed.length)) = eval generator := by
  funext seed query
  unfold eval child
  simp only [selectChild_take]

@[simp] theorem eval_nil (generator : Word → Word) (seed : Word) :
    eval generator seed [] = seed := rfl

@[simp] theorem eval_cons (generator : Word → Word) (seed : Word) (bit : Bool) (query : Word) :
    eval generator seed (bit :: query) = eval generator (child generator seed bit) query := rfl

/-- A shared query prefix leads to the same intermediate node. -/
theorem eval_append (generator : Word → Word) (seed path suffix : Word) :
    eval generator seed (path ++ suffix) = eval generator (eval generator seed path) suffix :=
  List.foldl_append

/-- Expose the next edge of a nonempty suffix using its position in the original query. -/
theorem eval_drop_succ (generator : Word → Word) (seed query : Word) (depth : ℕ)
    (hdepth : depth < query.length) :
    eval generator seed (query.drop depth) =
      eval generator (child generator seed (query[depth]?.getD false))
        (query.drop (depth + 1)) := by
  rw [List.drop_eq_getElem_cons hdepth]
  simp only [eval_cons, List.getElem?_eq_getElem hdepth, Option.getD_some]

/-- Truncation bounds intermediate labels even for an arbitrary generator. -/
theorem length_child_le (generator : Word → Word) (seed : Word) (bit : Bool) :
    (child generator seed bit).length ≤ seed.length :=
  length_selectChild_le _ _ _

/-- A generator providing two full labels preserves the seed width on each edge. -/
theorem length_child {generator : Word → Word}
    (hlength : ∀ seed, 2 * seed.length ≤ (generator seed).length) (seed : Word) (bit : Bool) :
    (child generator seed bit).length = seed.length := by
  have := hlength seed
  cases bit <;>
    simp only [child, selectChild, Bool.false_eq_true, ↓reduceIte,
      List.length_take, List.length_drop]
  all_goals lia

/-- All labels encountered by tree evaluation fit in the original seed width. -/
theorem length_eval_le (generator : Word → Word) (seed query : Word) :
    (eval generator seed query).length ≤ seed.length := by
  induction query generalizing seed with
  | nil => simp
  | cons bit query ih => exact (ih _).trans (length_child_le generator seed bit)

/-- Tree evaluation preserves the seed width at every depth when both children are full length. -/
theorem length_eval {generator : Word → Word}
    (hlength : ∀ seed, 2 * seed.length ≤ (generator seed).length) (seed query : Word) :
    (eval generator seed query).length = seed.length := by
  induction query generalizing seed with
  | nil => simp
  | cons bit query ih => rw [eval_cons, ih, length_child hlength]

/-- Selecting a child uses ordinary runtime word slicing. -/
theorem isPolyTime_selectChild {α : Type} {input : α ↪ Word}
    {width : α → ℕ} {expansion : α → Word} {bit : α → Bool}
    (hwidth : IsPolyTime input (fun a => unaryEncoding (width a)))
    (hexpansion : IsPolyTime input expansion)
    (hbit : IsPolyTime input (fun a => boolEncoding (bit a))) :
    IsPolyTime input (fun a => selectChild (width a) (expansion a) (bit a)) := by
  unfold selectChild
  polytime

attribute [aesop safe apply (rule_sets := [PolyTime])] isPolyTime_selectChild

/-- Computing one child only invokes the certified generator and ordinary word slicing. -/
theorem isPolyTime_child {generator : Word → Word}
    (hgenerator : IsPolyTime wordEncoding generator) :
    IsPolyTime (pairEncoding wordEncoding boolEncoding)
      (fun pair => child generator pair.1 pair.2) := by
  unfold child
  polytime

/-- The GGM evaluator is polynomial time whenever its generator is. Its fold has no state growth,
so this certificate needs no security or output-length assumption. -/
theorem isPolyTime_eval {generator : Word → Word} (hgenerator : IsPolyTime wordEncoding generator) :
    IsPolyTime (pairEncoding wordEncoding wordEncoding)
      (fun pair => eval generator pair.1 pair.2) := by
  exact (isPolyTime_snd wordEncoding wordEncoding).foldl_of_bounded_growth
    (stateEncoding := wordEncoding) (step := child generator) (growth := 0)
    (isPolyTime_fst wordEncoding wordEncoding) (isPolyTime_child hgenerator)
    (by simpa [wordEncoding] using length_child_le generator)

end Cslib.Crypto.GGM
