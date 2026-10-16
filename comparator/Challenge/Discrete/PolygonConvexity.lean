/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Challenge.Discrete.TabachnikovConverse

/-!
# Challenge: `Gluck/Discrete/PolygonConvexity.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/PolygonConvexity.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

@[expose] public section

namespace Gluck.Discrete

open scoped Pointwise Real

variable {n : ℕ}

/-- Every vertex other than the endpoints lies in the open left half-plane of
each oriented edge. -/
def StrictConvexEdgeSupport (v : ZMod n → ℂ) : Prop :=
  ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 →
    0 < crossR2 (v i) (v (i + 1)) (v j)

end Gluck.Discrete
