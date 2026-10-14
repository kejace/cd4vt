/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Challenge.Forward.Discrete.Defs

/-!
# Challenge: `Gluck/Discrete/SideTangentDFV.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/SideTangentDFV.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

open scoped BigOperators

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- The coefficient that arises by cyclic summation by parts of scaled edges. -/
def radiusDifference (ρ : ZMod n → ℝ) (i : ZMod n) : ℝ := ρ (i - 1) - ρ i

end Gluck.Discrete.SideTangent
