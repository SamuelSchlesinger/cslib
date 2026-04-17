/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Pim Spelier, Daan van Gent
-/

module

public import Cslib.Init
public import Mathlib.Computability.TuringMachine.Tape

@[expose] public section

namespace Turing

/--
A Turing machine "statement" is just a `Option`al command to move left or right,
and write a symbol (i.e. an `Option Symbol`, where `none` is the blank symbol) on the `BiTape`
-/
structure Stmt (Symbol : Type) where
  /-- The symbol to write at the current head position -/
  symbol : Option Symbol
  /-- The direction to move the tape head -/
  movement : Option Dir
deriving Inhabited

instance inhabitedStmt : Inhabited (Stmt Symbol) := inferInstance

namespace Stmt

variable {Symbol : Type}

/--
A `Stmt` is *write-only* if it either writes a blank and stays put, or writes a non-blank
symbol and moves the head right.

A transition function that produces only write-only `Stmt`s on a given tape implements a
"write-only output tape" in the sense of Arora–Barak when started from a blank output
tape: the head remains on the first blank cell after the output, and the tape content to
the left of the head is the reverse of the sequence of non-blank writes.

Note that the "write a blank, move right" case is deliberately excluded: on a write-only
output tape, blanks only appear in cells the head has not yet visited. Admitting blank
writes would break the "left of the head is the reverse of the emitted output" reading.
-/
def IsWriteOnly (s : Stmt Symbol) : Prop :=
  (s.symbol = none ∧ s.movement = none) ∨
    (s.symbol.isSome ∧ s.movement = some .right)

/--
A `Stmt` is *read-preserving with respect to the currently read symbol `r`* if it writes
back exactly what it read. The head is free to move in either direction (or stay).

A transition function that produces only read-preserving `Stmt`s on a given tape never
modifies that tape. This is the syntactic half of the classical "two-way read-only input
tape" condition; the complementary *boundedness* property—that the head stays within the
input region plus at most one cell on either side—cannot be stated purely on the
transition function (a transition reading a blank cannot distinguish the left blank from
the right blank) and is left to a separate predicate.
-/
def IsReadPreserving (r : Option Symbol) (s : Stmt Symbol) : Prop :=
  s.symbol = r

end Stmt

/-! ## Syntactic predicates on multi-tape transition functions

These predicates characterise reachability patterns in the finite control of a transition
function `tr` of the multi-tape shape, independently of any wrapping machine structure.
They are used to phrase head-boundedness of designated input tapes syntactically.
-/

variable {State Symbol : Type} {k : ℕ}

/--
State `q` is *harmful in direction `d`* on tape index `i` of transition function `tr` if some
transition from `q` reads a blank on tape `i` and moves the head on tape `i` in direction `d`.

These are the states whose firing would step the head one cell further past an end of the
input region.
-/
def MovesOffBlankInDir
    (tr : State → (Fin k → Option Symbol) → ((Fin k → Stmt Symbol) × Option State))
    (i : Fin k) (d : Dir) (q : State) : Prop :=
  ∃ reads, reads i = none ∧ ((tr q reads).1 i).movement = some d

/--
`MoveThenStays tr i d q q'` holds if `q'` is reachable from `q` by a tape-`i` trajectory
of the form `q →[move in direction d] q₁ →[stay while reading blank]* q'`.

The initial transition's read is unconstrained — the head may have been on an input cell
before stepping out to the blank — but every subsequent transition keeps the head fixed at
the blank, hence reads blank on tape `i` and produces no movement on tape `i`.
-/
inductive MoveThenStays
    (tr : State → (Fin k → Option Symbol) → ((Fin k → Stmt Symbol) × Option State))
    (i : Fin k) (d : Dir) : State → State → Prop where
  /-- Single move in direction `d`, with no constraint on the read. -/
  | move (q q' : State) (reads : Fin k → Option Symbol)
      (h_mov : ((tr q reads).1 i).movement = some d)
      (h_next : (tr q reads).2 = some q') :
      MoveThenStays tr i d q q'
  /-- Extend an existing chain by a stay-move while reading blank on tape `i`. -/
  | stay (q q' q'' : State)
      (h_prev : MoveThenStays tr i d q q')
      (reads : Fin k → Option Symbol)
      (h_reads : reads i = none)
      (h_mov : ((tr q' reads).1 i).movement = none)
      (h_next : (tr q' reads).2 = some q'') :
      MoveThenStays tr i d q q''

/--
Transition function `tr` is *bounded in direction `d`* on tape `i` if no chain of the form
"move in direction `d`, then stay-on-blank repeatedly, then move in direction `d` again"
exists. Equivalently: no harmful state in direction `d` is reachable via a post-`d`-move
stay-on-blank chain.

This is the syntactic condition we use to keep the head within the input region (plus one
cell on either side): once the head steps off the input in direction `d`, it cannot step
further in direction `d` without returning first. The condition is finitary — both the
reachability relation and the existential in `MovesOffBlankInDir` range over finite types.
-/
def IsBoundedInDirectionOnTape
    (tr : State → (Fin k → Option Symbol) → ((Fin k → Stmt Symbol) × Option State))
    (i : Fin k) (d : Dir) : Prop :=
  ∀ q q', MoveThenStays tr i d q q' → ¬ MovesOffBlankInDir tr i d q'

end Turing
