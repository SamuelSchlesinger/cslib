/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

@[expose] public section

/-!
# Oracle Interactions

An **oracle interaction** models an adversary that adaptively queries
an oracle, choosing each query based on the responses to all previous
queries. This is the standard model for security games where the
adversary has oracle access (e.g., signing oracles in EUF-CMA).

## Main Definitions

* `OracleInteraction Q R A` — an inductive type representing an
  adaptive sequence of queries of type `Q` receiving responses of
  type `R`, eventually producing a result of type `A`
* `OracleInteraction.run` — execute an interaction against a concrete
  oracle with a fuel budget, returning the query log and result

## Design Notes

The interaction is modeled as a free monad over the query/response
interface. The `run` function uses fuel-based recursion to ensure
termination: each query consumes one unit of fuel, and the oracle
at step `i` is indexed by `Fin fuel` to enable structural recursion
on the fuel parameter.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

/-- An **oracle interaction** where the adversary adaptively queries
an oracle of type `Q → R` and eventually produces a value of type `A`.

- `done a` — the adversary is finished and returns `a`
- `query q k` — the adversary asks query `q` and continues with
  the continuation `k` applied to the oracle's response -/
inductive OracleInteraction (Q : Type) (R : Type) (A : Type) where
  /-- The adversary is done and returns a result -/
  | done : A → OracleInteraction Q R A
  /-- The adversary makes a query and continues based on the response -/
  | query : Q → (R → OracleInteraction Q R A) → OracleInteraction Q R A

/-- Execute an oracle interaction against a concrete oracle, with a
fuel budget limiting the number of queries.

The oracle is `Fin fuel → Q → R`, where the `Fin fuel` index
represents which query step we are at (enabling the game to use
independent randomness for each query). Returns `none` if the
fuel is exhausted before the interaction completes, or
`some (queries, result)` with the list of queries made and the
final result.

Uses structural recursion on `fuel`. -/
def OracleInteraction.run {Q R A : Type}
    : (interaction : OracleInteraction Q R A) →
      (fuel : Nat) →
      (oracle : Fin fuel → Q → R) →
      Option (List Q × A)
  | .done a, _, _ => some ([], a)
  | .query _ _, 0, _ => none
  | .query q k, fuel + 1, oracle =>
    let response := oracle ⟨0, Nat.zero_lt_succ fuel⟩ q
    let shiftedOracle : Fin fuel → Q → R :=
      fun i => oracle ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    match (k response).run fuel shiftedOracle with
    | none => none
    | some (qs, a) => some (q :: qs, a)

end
