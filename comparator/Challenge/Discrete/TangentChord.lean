/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Challenge.Discrete.Converse

/-!
# Challenge: `Gluck/Discrete/TangentChord.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/TangentChord.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

namespace Gluck.Discrete

open scoped Real

attribute [local instance] Complex.finrank_real_complex_fact

/-- The signed twice-area of a planar triple: the `z`-component of the cross
product `(B - A) × (C - A) = Im(conj(B-A) · (C-A))`. Positive when `A, B, C`
turn left. -/
def crossR2 (A B C : ℂ) : ℝ :=
  (B - A).re * (C - A).im - (B - A).im * (C - A).re

/-- The signed Menger curvature of an ordered planar triple. On a nondegenerate
triple its absolute value is the reciprocal circumradius; the sign records the
triple's orientation. -/
noncomputable def signedMengerR2 (A B C : ℂ) : ℝ :=
  2 * crossR2 A B C / (dist A B * dist B C * dist C A)

end Gluck.Discrete
