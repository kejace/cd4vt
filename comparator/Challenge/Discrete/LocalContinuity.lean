/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Challenge.Discrete.PolygonConvexity

/-!
# Challenge: `Gluck/Discrete/LocalContinuity.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/LocalContinuity.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

@[expose] public section

namespace Gluck.Discrete

open Filter Set
open scoped Topology

variable {n : ℕ} [NeZero n]

/-- A local family in the literal geometry of `RealizesR2`. The same length
function supplies exact closure, a full turn, and the simple polygon. -/
structure LocalDiscreteRealizationFamily (κ₀ : ZMod n → ℝ) where
  neighborhood : Set (ZMod n → ℝ)
  isOpen_neighborhood : IsOpen neighborhood
  base_mem : κ₀ ∈ neighborhood
  lengths : (ZMod n → ℝ) → (ZMod n → ℝ)
  contDiffOn_lengths : ContDiffOn ℝ 1 lengths neighborhood
  positive : ∀ κ ∈ neighborhood, ∀ i, 0 < κ i
  moderate : ∀ κ ∈ neighborhood, ModerateArc 0 κ (lengths κ)
  closure : ∀ κ ∈ neighborhood, closureGap κ (lengths κ) = 0
  fullTurn : ∀ κ ∈ neighborhood, turningSum κ (lengths κ) = 2 * Real.pi
  simple : ∀ κ ∈ neighborhood, IsSimplePolygon (polygonR2 κ (lengths κ))
  contDiffOn_vertices : ContDiffOn ℝ 1 (fun κ => polygonR2 κ (lengths κ)) neighborhood

end Gluck.Discrete
