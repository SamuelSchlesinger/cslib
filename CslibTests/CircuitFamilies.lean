/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.Synthesis
import Cslib.Computability.Circuit.Family

/-!
# Circuit family tests

Slices of languages built from slices, and a constant-size family for the empty language.
-/

namespace CslibTests.CircuitFamilies

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

example (f : ∀ n, BooleanFunction n) : (Language.ofSlices f).slice 3 = f 3 := by
  simp

-- Every slice of the empty language is the constant `false`, which costs one gate.
example : DecidableInSize (0 : Language Bool) interpretation id fun _ => 1 := by
  rw [decidableInSize_id_iff_ecomplexity_le]
  intro n
  have h : (0 : Language Bool).slice n = fun _ => false := by
    funext x
    rw [Bool.eq_iff_iff]
    simp [Language.notMem_zero]
  rw [h]
  exact (Synthesis.const false).ecomplexity_le

end CslibTests.CircuitFamilies
