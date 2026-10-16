/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Challenge.Discrete.LocalContinuity

/-!
# Challenge: `Gluck/Forward/Kernel.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Forward/Kernel.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

@[expose] public section

namespace Gluck.Forward

open scoped Real

/-- A Euclidean circle with centre `O` and positive radius `R` through a triple. -/
def CircumcircleR2 (A B C O : ℂ) (R : ℝ) : Prop :=
  0 < R ∧ dist O A = R ∧ dist O B = R ∧ dist O C = R

/-- The closed convex vertex cone at `B`, spanned by the rays toward `A` and
`C`.  Dahlberg's regularity asks that the circumcenter lie in this cone. -/
def InVertexCone (A B C O : ℂ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
    O - B = (a : ℂ) * (A - B) + (b : ℂ) * (C - B)

end Gluck.Forward
