/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Challenge.Discrete.SideTangentDFV

/-!
# Challenge: `Gluck/Discrete/SideTangentConverse.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/SideTangentConverse.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- The three inward signed-distance equations at a given central edge. -/
def ThreeLineCircle (P N : ZMod n → ℂ) (i : ZMod n) (C : ℂ) (r : ℝ) : Prop :=
  ⟪N (i - 1), P i - C⟫_ℝ = r ∧ ⟪N i, P i - C⟫_ℝ = r ∧
    ⟪N (i + 1), P (i + 1) - C⟫_ℝ = r

/-- Exact supporting-line realization of the prescribed cyclic radii. -/
structure IsSideTangentRealization [NeZero n] (ρ : ZMod n → ℝ)
    (P N C : ZMod n → ℂ) : Prop where
  radius_pos : ∀ i, 0 < ρ i
  simple : IsSimplePolygon P
  strict_convex : StrictConvexEdgeSupport P
  unit_normal : ∀ i, ‖N i‖ = 1
  oriented_edge : ∀ i, ∃ ℓ : ℝ, 0 < ℓ ∧ P (i + 1) - P i = ℓ • (Complex.I * N i)
  supporting : ∀ i j, ⟪N i, P j - P i⟫_ℝ ≤ 0
  circles : ∀ i, ThreeLineCircle P N i (C i) (ρ i)
  unique_circle : ∀ i D r, ThreeLineCircle P N i D r → D = C i ∧ r = ρ i
  central_contact : ∀ i, C i + ρ i • N i ∈ openSegment ℝ (P i) (P (i + 1))

/-- A simple strictly convex polygon with the exact three-line radius at every edge. -/
def RealizesSideTangent [NeZero n] (ρ : ZMod n → ℝ) : Prop :=
  ∃ P N C : ZMod n → ℂ, IsSideTangentRealization ρ P N C

/-- Original constant-or-four-sign-change admissibility, with zero differences retained. -/
def SideTangentAdmissible (ρ : ZMod n → ℝ) : Prop :=
  (∀ i, 0 < ρ i) ∧ ((∃ r, ∀ i, ρ i = r) ∨ DFV (radiusDifference ρ) 0)

end Gluck.Discrete.SideTangent
