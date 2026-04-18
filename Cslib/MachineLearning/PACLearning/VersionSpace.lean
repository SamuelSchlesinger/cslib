/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/

module

public import Cslib.MachineLearning.PACLearning.Defs

@[expose] public section

/-! # Version Space

The *version space* of a concept class `C` given a labeled sample `S` is the set
of concepts in `C` whose labels agree with `S` on every observed point. It is the
classical abstraction of "concepts still consistent with the data," introduced by
Mitchell (1982) and systematised by Angluin (1980) and Mitchell (1997).

Version space is the structural companion to `sampleComplexity`: where sample
complexity monotonicity expresses "more samples make PAC easier," version space
antitonicity expresses "more data shrinks the consistent concept set." Together
they describe the two monotonicities of the passive learning setup.

## Main definitions

- `VersionSpace C S`: the subset of `C` whose concepts agree with `S` on every
  sample point.
- `IsConsistent A C`: a learner is consistent with `C` if its output always lies
  in the version space at the received sample.

## Main results

- `versionSpace_subset`: the version space is a subset of the original class.
- `versionSpace_empty_sample`: with no data, the version space is the whole
  concept class.
- `versionSpace_antitone`: *structural monotonicity* — more samples give a
  smaller version space.
- `IsConsistent.output_mem_conceptClass`: consistent learners output concepts
  in the class.
- `mem_versionSpace_of_realizable`: under a realizable sample (labeled by some
  `c ∈ C`), the version space is nonempty.

## Cross-link to sample complexity

Under a realizable distribution on `α × β` (where labels are deterministically
given by some target `c ∈ C`), a consistent learner's output lies in
`VersionSpace C S` for every sample by definition. By `versionSpace_antitone`,
this version space shrinks monotonically as the sample size grows. Combined with
finiteness of `C` (not assumed here — deferred to future work via Occam /
Chernoff characterisations), this yields realizable PAC learnability via the
classical consistent-learning-implies-PAC theorem.

## References

* [T. Mitchell, *Generalization as Search*, Artificial Intelligence 18(2)][Mitchell1982]
* [D. Angluin, *Inductive Inference of Formal Languages from Positive Data*,
  Information and Control 45(2)][Angluin1980]
* [T. Mitchell, *Machine Learning*, McGraw-Hill][Mitchell1997]
-/

open Set

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*} {β : Type*}

/-! ### Version Space -/

/-- The *version space* of a concept class `C` given a labeled sample `S`:
the set of concepts in `C` whose labels agree with `S` on every observed point.

Equivalently, `VersionSpace C S = C ∩ {h | ∀ i, h (S i).1 = (S i).2}`. -/
def VersionSpace {m : ℕ} (C : ConceptClass α β) (S : LabeledSample α β m) :
    ConceptClass α β :=
  {h ∈ C | ∀ i : Fin m, h (S i).1 = (S i).2}

/-- Membership in the version space unfolds to concept membership plus
per-sample consistency. -/
theorem mem_versionSpace_iff {m : ℕ} {C : ConceptClass α β}
    {S : LabeledSample α β m} {h : α → β} :
    h ∈ VersionSpace C S ↔ h ∈ C ∧ ∀ i : Fin m, h (S i).1 = (S i).2 := Iff.rfl

/-- The version space is a subset of the original concept class. -/
theorem versionSpace_subset {m : ℕ} (C : ConceptClass α β)
    (S : LabeledSample α β m) :
    VersionSpace C S ⊆ C := fun _ hh => hh.1

/-- Version space on the empty sample equals the whole concept class: no data,
no constraint on hypotheses. -/
theorem versionSpace_empty_sample (C : ConceptClass α β)
    (S : LabeledSample α β 0) :
    VersionSpace C S = C := by
  ext h
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, fun i => i.elim0⟩⟩

/-- *Version space antitonicity.* Given a sample of size `n` and `m ≤ n`, the
version space on all `n` observations is a subset of the version space on the
first `m` observations. More data never enlarges the version space.

This is the structural dual to sample complexity monotonicity: where sample
complexity says more samples make PAC easier to achieve, version space
antitonicity says more samples make the consistent concept set smaller.
Together these describe the two monotonicities of the passive learning setup. -/
theorem versionSpace_antitone {m n : ℕ} (hmn : m ≤ n) (C : ConceptClass α β)
    (S : LabeledSample α β n) :
    VersionSpace C S ⊆ VersionSpace C (fun i => S (Fin.castLE hmn i)) := by
  intro h hh
  exact ⟨hh.1, fun i => hh.2 (Fin.castLE hmn i)⟩

/-! ### Consistent Learners -/

/-- A learner is *consistent* with the concept class `C` if, on every labeled
sample it receives, its output hypothesis lies in the version space of `C` at
that sample. Equivalently, the learner's output always agrees with every
observed labeled pair, provided a consistent hypothesis exists in `C`.

This is the classical consistency condition, central to Angluin's inductive
inference framework and Mitchell's candidate-elimination algorithm. -/
def IsConsistent {m : ℕ} (A : Learner α β m) (C : ConceptClass α β) : Prop :=
  ∀ S : LabeledSample α β m, A S ∈ VersionSpace C S

/-- A consistent learner's output is always in the concept class. -/
theorem IsConsistent.output_mem_conceptClass {m : ℕ} {A : Learner α β m}
    {C : ConceptClass α β} (hA : IsConsistent A C) (S : LabeledSample α β m) :
    A S ∈ C := (hA S).1

/-- A consistent learner's output agrees with the sample on every observed
point. -/
theorem IsConsistent.output_consistent {m : ℕ} {A : Learner α β m}
    {C : ConceptClass α β} (hA : IsConsistent A C) (S : LabeledSample α β m)
    (i : Fin m) :
    A S (S i).1 = (S i).2 := (hA S).2 i

/-! ### Realizable case -/

/-- *Realizable version-space nonemptiness.* If a target concept `c` lies in
`C` and the sample `S` is labeled by `c` (i.e. every `(S i).2 = c (S i).1`),
then `c` itself lies in the version space `VersionSpace C S`, so the version
space is nonempty.

This is the realizable-case correctness condition: when data comes from a
concept in the class, a consistent learner always has at least one legal
choice. -/
theorem mem_versionSpace_of_realizable {m : ℕ} {C : ConceptClass α β}
    (c : α → β) (hc : c ∈ C) (S : LabeledSample α β m)
    (hS : ∀ i : Fin m, (S i).2 = c (S i).1) :
    c ∈ VersionSpace C S :=
  ⟨hc, fun i => (hS i).symm⟩

/-- Corollary: under realizable data, the version space is nonempty. -/
theorem versionSpace_nonempty_of_realizable {m : ℕ} {C : ConceptClass α β}
    {c : α → β} (hc : c ∈ C) (S : LabeledSample α β m)
    (hS : ∀ i : Fin m, (S i).2 = c (S i).1) :
    (VersionSpace C S).Nonempty :=
  ⟨c, mem_versionSpace_of_realizable c hc S hS⟩

end Cslib.MachineLearning.PACLearning
