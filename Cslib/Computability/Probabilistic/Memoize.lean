/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Control.Monad.Memoize
public import Cslib.Computability.Probabilistic.Composition
public import Cslib.Computability.Probabilistic.List
public import Cslib.Languages.Probabilistic.RandomOracle

/-!
# Efficient memoized sampling

An ordinary association-list cache preserves the efficiency of a closed probabilistic sampler.
The certificate charges for comparing complete key encodings, looking up a cached answer, and
writing the updated cache. The sampler and query may capture the original input.

`memoize_call_size_le` supplies a local invariant and storage-growth bound for the stateful
interpreter. `memoize_cache_size_le` also bounds the complete cache representation using a query
bound and a reply-size bound.
-/

public section

namespace Cslib.Probability

private theorem lookup_eq_head_filter {Key Value : Type} [BEq Key]
    (key : Key) (cache : List (Key × Value)) :
    cache.lookup key = ((cache.filter (fun entry => key == entry.1)).head?).map Prod.snd := by
  induction cache with
  | nil => rfl
  | cons entry cache ih =>
    rcases entry with ⟨key', value⟩
    cases h : key == key' <;> simp [List.lookup_cons, h, ih]

/-- Cache a certified sampler's results using an ordinary list. Runtime query data, captured
inputs, and the complete returned cache are all included in the efficiency certificate. -/
theorem IsPPTOn.memoize {α Key Value : Type} [BEq Key] [LawfulBEq Key]
    [Inhabited Key] [Inhabited Value] {input : α ↪ Word}
    {keyEncoding : Key ↪ Word} {valueEncoding : Value ↪ Word}
    {compute : α → Key → ProbComp Value} {query : α → Key} {cache : α → List (Key × Value)}
    (hcompute : IsPPTOn input valueEncoding (fun a => compute a (query a)))
    (hquery : IsPolyTime input (fun a => keyEncoding (query a)))
    (hcache : IsPolyTime input
      (fun a => listEncoding (pairEncoding keyEncoding valueEncoding) (cache a))) :
    IsPPTOn input
      (pairEncoding valueEncoding (listEncoding (pairEncoding keyEncoding valueEncoding)))
      (fun a => memoize (compute a) (query a) (cache a)) := by
  let entry := pairEncoding keyEncoding valueEncoding
  have hmatches := hcache.list_filter_with (predicate := fun key entry => key == entry.1) hquery
    ((isPolyTime_fst keyEncoding entry).beq_encoded
      (isPolyTime_snd keyEncoding entry).fst)
  have hcondition := hmatches.list_unaryLength.unary_eq
    (g := fun _ => 0) (isPolyTime_const input [])
  have hcaller := isPolyTime_fst input valueEncoding
  have hvalue := isPolyTime_snd input valueEncoding
  have hstore := hvalue.pair
    (((hquery.comp_encoded hcaller).pair hvalue).list_cons (hcache.comp_encoded hcaller))
  have hmiss := hcompute.map_with (output := pairEncoding valueEncoding (listEncoding entry))
    (f := fun a value => (value, (query a, value) :: cache a)) hstore
  have hhit := ((hmatches.list_headD default).snd.pair hcache).isPPTOn
  apply (IsPPTOn.ite hcondition hmiss hhit).congr
  intro a
  have hlookup := lookup_eq_head_filter (query a) (cache a)
  cases hmatches : (cache a).filter (fun entry => query a == entry.1) with
  | nil =>
    simp only [hmatches, List.head?_nil, Option.map_none] at hlookup
    simp [Cslib.memoize, hlookup, ProbComp.eval_map,
      PMF.map, Function.comp_def]
  | cons entry rest =>
    simp only [hmatches, List.head?_cons, Option.map_some] at hlookup
    simp [Cslib.memoize, hlookup]

/-- A cached call preserves a reply-size invariant and adds at most one encoded entry.
The bound charges the complete key and value, including both layers of delimiters. -/
theorem memoize_call_size_le {Key Value : Type} [BEq Key] [LawfulBEq Key]
    (keyEncoding : Key ↪ Word) (valueEncoding : Value ↪ Word)
    (distribution : Key → PMF Value) (key : Key) (cache : List (Key × Value)) (maxValue : ℕ)
    (hcache : ∀ entry ∈ cache, (valueEncoding entry.2).length ≤ maxValue)
    (hvalues : ∀ value ∈ (distribution key).support, (valueEncoding value).length ≤ maxValue)
    (result : Value × List (Key × Value))
    (hresult : result ∈ (memoize distribution key cache).support) :
    (valueEncoding result.1).length ≤ maxValue ∧
      (∀ entry ∈ result.2, (valueEncoding entry.2).length ≤ maxValue) ∧
      (listEncoding (pairEncoding keyEncoding valueEncoding) result.2).length ≤
        (listEncoding (pairEncoding keyEncoding valueEncoding) cache).length +
          4 * (keyEncoding key).length + 2 * maxValue + 3 := by
  obtain ⟨hreply, hcache'⟩ := RandomOracle.memoize_invariant distribution
    (fun _ value => (valueEncoding value).length ≤ maxValue) key cache hcache hvalues result hresult
  refine ⟨hreply, hcache', ?_⟩
  cases hlookup : cache.lookup key with
  | none =>
    rw [memoize_of_none _ _ _ hlookup] at hresult
    change result ∈ ((distribution key).map (fun value => (value, (key, value) :: cache))).support
      at hresult
    obtain ⟨value, hvalue, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    have hv := hvalues value hvalue
    simp only [listEncoding_cons, length_pairEncoding]
    lia
  | some value =>
    rw [memoize_of_some _ _ _ _ hlookup] at hresult
    change result ∈ (PMF.pure (value, cache)).support at hresult
    simp only [PMF.mem_support_pure_iff] at hresult
    subst result
    dsimp
    lia

/-- Bounds on calls, encoded keys and sampled replies bound the entire cache representation.
The factor includes the delimiters and tags of the pair and list encodings. -/
theorem memoize_cache_size_le {α Key Value : Type} [BEq Key]
    (keyEncoding : Key ↪ Word) (valueEncoding : Value ↪ Word)
    (distribution : Key → PMF Value) (program : OracleComp Key (fun _ => Value) α)
    (calls maxKey maxValue : ℕ)
    (hqueries : program.HasQueryBounds (fun key => (keyEncoding key).length) calls maxKey)
    (hvalues : ∀ key, (keyEncoding key).length ≤ maxKey →
      ∀ value ∈ (distribution key).support, (valueEncoding value).length ≤ maxValue)
    (cache cache' : List (Key × Value))
    (hcache : ∀ entry ∈ cache,
      (keyEncoding entry.1).length ≤ maxKey ∧ (valueEncoding entry.2).length ≤ maxValue)
    (result : α)
    (h : (result, cache') ∈
      (OracleComp.runState (Cslib.memoize distribution) program cache).support) :
    (listEncoding (pairEncoding keyEncoding valueEncoding) cache').length ≤
      (cache.length + calls) * (4 * maxKey + 2 * maxValue + 3) := by
  obtain ⟨hcount, hentries⟩ := RandomOracle.memoize_cache_bounds distribution program
    (fun key => (keyEncoding key).length) calls maxKey hqueries cache cache' result h
  have hentry : ∀ entry ∈ cache', (pairEncoding keyEncoding valueEncoding entry).length ≤
      2 * maxKey + maxValue + 1 := by
    intro entry hentry
    have hbounds : (keyEncoding entry.1).length ≤ maxKey ∧
        (valueEncoding entry.2).length ≤ maxValue := by
      rcases hentries entry hentry with h | ⟨hkey, hvalue⟩
      · exact hcache entry h
      · exact ⟨hkey, hvalues entry.1 hkey entry.2 hvalue⟩
    simp only [length_pairEncoding]
    lia
  have hlength := (length_listEncoding_le _ hentry).trans
    (Nat.mul_le_mul_right (2 * (2 * maxKey + maxValue + 1) + 1) hcount)
  convert hlength using 1
  ring

end Cslib.Probability
