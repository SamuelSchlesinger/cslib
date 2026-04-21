# PR #162 Review Comments

Source: https://github.com/crei/cslib/pull/162

- [x] `Cslib/Foundations/Data/StackTape.lean:94` - Recheck whether the added `grind` annotation is necessary, since `cons` is already marked for `grind` and the proof is `rfl`.
  https://github.com/crei/cslib/pull/162#discussion_r3116378467
  Plan: Remove the `scoped grind =` tags from the `cons_*` simp lemmas first, keeping the `simp` tags. Rebuild `StackTape.lean`, `BiTape.lean`, and the multi-tape file; if anything breaks, re-add only the specific `grind` annotation that is actually needed and leave a local reason.

- [x] `Cslib/Computability/Machines/MultiTapeTuring/Basic.lean:144` - Consider simplifying `IsReadPreserving` by making it take a transition function and tape number directly.
  https://github.com/crei/cslib/pull/162#discussion_r3116455172
  Plan: Move from the statement-level shape `Stmt.IsReadPreserving r stmt` to a transition-level predicate in `TuringCommon`, roughly `IsReadPreservingOnTape tr i := ∀ q reads, ((tr q reads).1 i).symbol = reads i`. Then change `HasInputTape.readPreserving` to store that predicate for tape `0`, update `HasInputTape.step_tape0_decompose`, and adjust the surrounding docs so the field no longer expands a long lambda at the use site.

- [x] `Cslib/Foundations/Data/BiTape/Canonical.lean:42` - Consider defining `canonicalInputTapeNat` via repeated `move_right` from `mk₁ s`; also account for the possible reusable `move_int` helper from related branches.
  https://github.com/crei/cslib/pull/162#discussion_r3116539142
  Plan: Port the reusable `BiTape.move_int` API from `crei/move_routine` in a minimal form: `move_int`, `move_int_zero_eq_id`, `move_int_one_eq_move_right`, `move_int_neg_one_eq_move_left`, and `move_int_move_int`. Then redefine `canonicalInputTapeNat s n` as `(BiTape.move_right^[n]) (BiTape.mk₁ s)` or prove it equivalent as an intermediate step if replacing the definition causes too much proof churn.

- [x] `Cslib/Foundations/Data/BiTape/Canonical.lean:57` - Clarify whether negative positions should be clipped while positive positions beyond the input length are allowed, or whether this should instead behave like `move_int (mk₁ s) p`.
  https://github.com/crei/cslib/pull/162#discussion_r3116552226
  Plan: Adopt the `move_int (BiTape.mk₁ s) p` semantics for `canonicalInputTape s p`, so both far-left and far-right positions are represented by actual blank-cell moves rather than by asymmetric clipping. Keep the head-bound theorem range `-1 ≤ p ≤ s.length`, and add compatibility lemmas for that valid range if existing proofs need the old closed form.

- [x] `Cslib/Foundations/Data/BiTape/Canonical.lean:80` - If switching to `move_int`, generalize the associated lemmas so they are useful beyond this custom canonical tape definition.
  https://github.com/crei/cslib/pull/162#discussion_r3116559654
  Plan: Prove the one-step movement facts at the `BiTape.move_int` level, then make the canonical lemmas thin wrappers. The target general lemmas are `move_int_move_int`, one-step right/left corollaries, and, if needed for clean extensional proofs, the `nth`/`ext_nth` support from Crei's branch. After that, restate `canonicalInputTape_move_right`, `canonicalInputTape_move_left`, and `canonicalInputTape_head_eq_none_iff` using the general API.

- [x] `Cslib/Computability/Machines/TuringCommon.lean:123` - The current argument assumes the first tape is not written to; consider making this self-contained by adding that condition to `MoveThenStays`.
  https://github.com/crei/cslib/pull/162#discussion_r3116620478
  Plan: After introducing the transition-level read-preservation predicate, strengthen `MoveThenStays` so blank stay steps also record that tape `i` is not changed, at least by requiring the statement writes back the blank it read. Then update `MoveThenStaysOnBlank.moveThenStays` to take the read-preservation proof and supply the new constructor fields. This keeps `IsBoundedInDirectionOnTape` from silently relying on an external "input tape is read-only" assumption.

- [x] `Cslib/Computability/Machines/MultiTapeTuring/Basic.lean:936` - Avoid relying on `tm.initCfg` if possible; reformulate the theorem around an arbitrary configuration whose head starts inside the input so it composes better with other machines.
  https://github.com/crei/cslib/pull/162#discussion_r3116657636
  Plan: Add a public initializer for the invariant from an arbitrary configuration, e.g. if `cfg.tapes 0 = canonicalInputTape s p` and `0 ≤ p ∧ p < s.length`, then `HeadBoundInvariantAt.Strong tm s cfg p` holds with endpoint chain witnesses vacuous. Prove a new theorem over `Relation.RelatesInSteps tm.TransitionRelation cfg cfg' t` using that starting invariant, and keep the existing `head_position_bounded` from `tm.initCfg s` as a wrapper.
