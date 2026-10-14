/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Challenge.Discrete.SideTangentConverse

/-!
# Challenge: `Gluck/Discrete/GlobalContinuity/LevelBands.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/GlobalContinuity/LevelBands.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

namespace Gluck.Discrete.GlobalContinuity

/-- The band profile `κ^s` of the paper's hexagon path, `s ∈ [0, 1]`. -/
def bandProfile (s : ℝ) : ZMod 6 → ℝ :=
  ![14, 11, 10 + 3 * s, 5, 7 - 3 * s, 3]

end Gluck.Discrete.GlobalContinuity
