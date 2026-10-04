<pre>
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
</pre>

# Computational cryptography

This directory develops cryptography against uniform probabilistic polynomial-time (PPT)
adversaries. Games are ordinary probabilistic programs written in Lean `do` notation. Efficiency is
a separate contract: a program is PPT when one fixed multi-tape Turing machine with a polynomial
clock realizes its exact output distribution. Cryptographic arguments compose such contracts
without mentioning tapes or machine configurations.

The [definition checks](../../../CslibTests/ComputationalCrypto.lean) and the
[programming examples](../../../CslibTests/ComputationalCryptoPrograms.lean) are a good place to
start reading.

## Security definitions

`Word` is `List Bool`. The security parameter `n` is given to adversaries in unary.

| Notion | Definition |
| --- | --- |
| [`Negligible`](../Negligible.lean) | Mathlib's `SuperpolynomialDecay` at natural parameters. |
| [`Game.Secure`](../Game.lean) | Every admissible adversary has negligible advantage. The adversary is quantified before its negligible bound. |
| [`OneWay`](OneWay.lean) | Deterministic polynomial-time evaluation; every PPT inverter given `n` and `f x` for uniform `n`-bit `x` finds **some** preimage with negligible probability. |
| [`PseudorandomGenerator`](PseudorandomGenerator.lean) | Deterministic polynomial-time evaluation, output length `length n > n` at every seed length `n`, and outputs indistinguishable from uniform by PPT tests. |
| [`PseudorandomFunction`](PseudorandomFunction.lean) | Deterministic polynomial-time evaluation with `n`-bit keys, queries and answers; adaptive oracle PPT adversaries cannot distinguish it from one uniformly random function. Repeated queries reuse their answers, and both games reject malformed queries with the empty word. |

Advantage is the absolute difference of acceptance probabilities, without the factor of one half
used for guessing a challenge bit. Computational security shares its experiments with the
semantic [PRG interface](../Primitives/PRG), so statistical arguments about distributions can be
used as hops in computational proofs.

## Efficiency contracts

The contracts live in [PPT](../../Computability/Probabilistic/PPT.lean):

- `IsPolyTime encode f`: one deterministic machine computes `f` within `c * (|encode a| + 1) ^ d`
  steps on every input.
- `IsPPTOn input output program`: one fair-coin machine, clocked by a fixed polynomial in the input
  length, has exactly the output distribution of `program a` on every input `a`.
- `IsPPT output adversary` specializes `IsPPTOn` to a unary security parameter and an auxiliary
  word.
- `IsOraclePPT` additionally preserves the joint distribution of the result and the final oracle
  state, for every stateful oracle. Writing queries and reading answers is charged; the oracle's own
  computation is not.

Time is strict polynomial time on every coin sequence, not expected time. Sampling uses fair bits,
so an arbitrary distribution may appear in a game but must be realized by a machine before an
algorithm may use it. In particular, exact sampling from a non-dyadic distribution is generally
not PPT under this convention. [Clock](../../Computability/Probabilistic/Clock.lean) shows that
every clocked certificate also has a genuinely halting realization, and
[CoinTape](../../Computability/Probabilistic/CoinTape.lean) shows that every PPT program is a
polynomial-time function of a polynomial-length uniform random tape.

The [`polytime`](../../Tactic/PolyTime.lean) and [`ppt`](../../Tactic/PPT.lean) tactics compose
proved closure rules: tuples, maps, filters, folds, word slicing, unary arithmetic, bounded search,
sampling, conditionals and calls to certified algorithms. An algorithm that is not built from these
rules needs its own certificate; registering it with `@[program_certificate]` lets proof search
use it instead of unfolding the algorithm.

```lean
import Cslib.Crypto.Computational.PseudorandomGenerator
import Cslib.Tactic.PPT

open Cslib Cslib.Probability Cslib.Crypto

noncomputable def realGame (generator : Word → Word) (adversary : Distinguisher)
    (n : ℕ) : ProbComp Bool := do
  let seed ← OracleComp.sampleBits n
  adversary n (generator seed)

theorem isPPT_realGame (generator : Word → Word) (adversary : Distinguisher)
    (hgenerator : IsPolyTime wordEncoding generator)
    (hadversary : IsPPT boolEncoding adversary) :
    IsPPT boolEncoding (fun n _ => realGame generator adversary n) := by
  unfold realGame
  ppt
```

Loops use [Iteration](../../Computability/Probabilistic/Iteration.lean),
[Fold](../../Computability/Probabilistic/Fold.lean) and
[Adaptive](../../Computability/Probabilistic/Adaptive.lean). Their specification rules take a single
invariant that proves the postcondition and bounds every intermediate state. A polynomial number of
iterations is not enough by itself: the intermediate states must also stay polynomially bounded.

The machine-level implementations live in [Realization](../../Computability/Probabilistic/Realization)
and in CSLib's [multi-tape machines](../../Computability/Machines/Turing/MultiTape).

## Oracles

`OracleComp Query Response α` supports adaptive queries, dependent responses and shared hidden
state. [`simulateState`](../../Languages/Probabilistic/Simulation.lean) substitutes stateful
programs for oracle calls; a one-call simulation relation, possibly randomized and restricted to an
invariant, lifts to entire adaptive programs. [`RandomOracle`](../../Languages/Probabilistic/RandomOracle.lean)
proves that sampling a random function eagerly and sampling its answers lazily agree, including
the final table, and refines the lazy cache to the association-list
[`memoize`](../../Foundations/Control/Monad/Memoize.lean) combinator.

An oracle PPT certificate bounds the number and length of queries, see
[QueryBounds](../../Computability/Probabilistic/QueryBounds.lean).
[OracleSimulation](../../Computability/Probabilistic/OracleSimulation.lean) uses these bounds to
certify an oracle PPT adversary run against a closed PPT handler, given a local invariant and a
bound on each reply and on the storage each call adds. The handler may capture the reduction's
challenge, and the final handler state is retained.

Composition that keeps an external oracle interface open is not covered: an unfinished query
cannot be discarded by a dummy call when the oracle's state is observable. All reductions in this
directory compose closed programs.

## Sources

- Sanjeev Arora and Boaz Barak, *Computational Complexity: A Modern Approach*, Chapter 9, and
  Dan Boneh and Victor Shoup, *A Graduate Course in Applied Cryptography*, for the security
  definitions.
