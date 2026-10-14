/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Challenge.Discrete.TabachnikovReduction

/-!
# Challenge: `Gluck/Discrete/TabachnikovConverse.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/TabachnikovConverse.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

namespace Gluck.Discrete

open Complex (normSq)

variable {n : ℕ}

/-- **At least two local maxima and two local minima** (Tabachnikov's
hypothesis), with local extrema counted plateau-aware in Dahlberg's sense:
a maximal constant run whose two outside neighbours are both strictly lower
(resp. higher), and two extrema are distinct when their runs are disjoint. -/
def IsPlateauTwoMaxTwoMin (r : ZMod n → ℝ) : Prop :=
  HasTwoPlateauMaxRuns r ∧ HasTwoPlateauMinRuns r

/-- **Coherent convex polygon** (Tabachnikov, Problem 2): a simple polygon,
strictly convex and counterclockwise (every vertex lies strictly to the left
of every edge not incident to it), and coherent. -/
def IsCoherentConvexPolygon (v : ZMod n → ℂ) : Prop :=
  IsSimplePolygon v ∧
    (∀ a c : ZMod n, c ≠ a → c ≠ a + 1 → 0 < crossR2 (v a) (v (a + 1)) (v c)) ∧
    CoherentR2 v

/-- The radius of the circle through the consecutive triple
`v (i - 1), v i, v (i + 1)`. -/
noncomputable def vertexCircumradius (v : ZMod n → ℂ) (i : ZMod n) : ℝ :=
  dist (circumcenterR2 (v i) (v (i - 1)) (v (i + 1))) (v i)

end Gluck.Discrete
