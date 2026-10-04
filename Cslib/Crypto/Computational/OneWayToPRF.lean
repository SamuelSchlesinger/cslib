/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Computational.OneWayToPRG
public import Cslib.Crypto.Computational.GGM.Security

/-!
# Pseudorandom functions from one-way functions

Combine the general OWF-to-PRG theorem with the GGM construction. The conclusion includes an
efficient deterministic evaluator and security against uniform adaptive oracle PPT adversaries.
Existence of the one-way function is the sole cryptographic assumption.

The first implication follows Holenstein's simplification of the Håstad–Impagliazzo–Levin–Luby
construction, as documented in `OneWayToPRG`. The second follows Goldreich, Goldwasser and Micali,
[*How to Construct Random Functions*](https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf),
Sections 3.2–3.3, as documented in `GGM.Security`.
-/

public section

namespace Cslib.Crypto

open Probability

/-- Every uniform one-way function implies a uniform pseudorandom function secure against
adaptive, strict polynomial-time oracle adversaries. -/
theorem OneWay.exists_pseudorandomFunction {f : Word → Word} (hf : OneWay f) :
    ∃ family : Word → Word → Word, PseudorandomFunction family := by
  obtain ⟨generator, hgenerator⟩ := hf.exists_pseudorandomGenerator
  exact hgenerator.exists_pseudorandomFunction

end Cslib.Crypto
