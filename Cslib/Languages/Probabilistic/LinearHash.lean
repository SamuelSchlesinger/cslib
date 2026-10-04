/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Languages.Probabilistic.BitString
public import Cslib.Languages.Probabilistic.Repeat
public import Cslib.Probability.LinearHash

/-!
# Extracting with a sampled linear hash

`LinearHash.extract count input` samples a fresh hash matrix and returns its seed followed by
`count` hashed bits. On a source of words of a fixed length the output distribution is the
finite matrix hash experiment, so the leftover hash lemma bounds its distance from uniform.
-/

@[expose] public section

namespace Cslib.Probability.LinearHash

open Cslib.Probability.PMF

/-- Sample an independent hash matrix and return its seed followed by the extracted bits. -/
noncomputable def extract (count : ℕ) (input : Word) : ProbComp Word := do
  let seed ← OracleComp.sampleBits (count * input.length)
  return seed ++ wordHash count seed input

/-- Every extractor output contains the complete matrix seed and exactly `count` digest bits. -/
theorem length_extract (count : ℕ) (input : Word) {output : Word}
    (houtput : output ∈ (ProbComp.eval (extract count input)).support) :
    output.length = count * input.length + count := by
  simp only [extract, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_sampleBits,
    PMF.mem_support_map_iff] at houtput
  obtain ⟨seed, hseed, rfl⟩ := houtput
  simp only [List.length_append, length_wordHash, mem_support_uniformBits_iff.mp hseed]

/-- The word extractor agrees exactly with the finite strong-extraction experiment. -/
theorem eval_extract_bind {n m : ℕ} (source : PMF (BitString n)) :
    (source.map List.ofFn).bind (fun input => ProbComp.eval (extract m input)) =
      (seededHash (PMF.uniformOfFintype (BitString (m * n))) source
        (fun seed => hash (maskEquiv m n seed))).map
          (fun pair => List.ofFn pair.1 ++ List.ofFn pair.2) := by
  simp only [PMF.bind_map, Function.comp_def, extract, ProbComp.eval, OracleComp.eval_bind,
    OracleComp.eval_pure, OracleComp.eval_sampleBits, List.length_ofFn]
  simp only [uniformBits, seededHash, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    Function.comp_def]
  rw [PMF.bind_comm]
  simp only [PMF.map, Function.comp_def,
    wordHash_eq_ofFn, masksFromWord, wordBits_ofFn]

/-- The word extractor's exact finite law on one fixed-width input. -/
theorem eval_extract_ofFn {n m : ℕ} (input : BitString n) :
    ProbComp.eval (extract m (List.ofFn input)) =
      (PMF.uniformOfFintype (BitString (m * n))).map
        (fun seed => List.ofFn seed ++ List.ofFn (hash (maskEquiv m n seed) input)) := by
  simpa only [PMF.pure_map, PMF.pure_bind, seededHash_eq_bind, PMF.map_comp,
    Function.comp_def] using
    eval_extract_bind (m := m) (PMF.pure input)

/-- Hashing concatenated independent fixed-width words has the tuple extraction law. -/
theorem eval_extract_replicate {width : ℕ} (source : ProbComp (BitString width))
    (count outputBits : ℕ) :
    ProbComp.eval (OracleComp.replicate count (List.ofFn <$> source) >>=
      fun words => extract outputBits words.flatten) =
        (seededHash (PMF.uniformOfFintype (BitString (outputBits * (count * width))))
          (ProbComp.eval (OracleComp.replicate count source))
          (fun seed values => hash (maskEquiv outputBits (count * width) seed)
            (wordBits (count * width) (values.map List.ofFn).flatten))).map
              (fun result => List.ofFn result.1 ++ List.ofFn result.2) := by
  simp only [OracleComp.replicate_map, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_replicate, PMF.bind_map, PMF.map_comp, PMF.map_bind,
    seededHash_eq_bind, Function.comp_def, List.map_ofFn, ← ofFn_maskEquiv_symm,
    wordBits_ofFn, eval_extract_ofFn]

/-- The executable extractor satisfies the strong leftover hash bound on a finite word source. -/
theorem extract_distance_le {n m : ℕ} (source : PMF (BitString n)) :
    dist ((source.map List.ofFn).bind (fun input => ProbComp.eval (extract m input)))
        (uniformBits (m * n + m)) ≤
      Real.sqrt ((2 : ℝ) ^ m * collisionProbability source) / 2 := by
  have h := (isTwoUniversal_flat n m).leftover_hash source
  have hideal : ((PMF.uniformOfFintype (BitString (m * n))).bind
      (fun seed => (PMF.uniformOfFintype (BitString m)).map (seed, ·))).map
      (fun pair => List.ofFn pair.1 ++ List.ofFn pair.2) = uniformBits (m * n + m) := by
    rw [uniformBits_add]
    simp only [uniformBits, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
  rw [eval_extract_bind, ← hideal]
  exact (dist_map_le _ _ _).trans (by simpa [BitString] using h)

end Cslib.Probability.LinearHash
