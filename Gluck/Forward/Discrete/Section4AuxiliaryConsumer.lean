/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4AuxiliaryRigidity
import Gluck.Forward.Discrete.MinimalDiskBoundaryRadius

/-!
# Consuming Dahlberg's Section 4 auxiliary polygon

This file records the exact finite output needed from the polygonal
approximation in Dahlberg's Section 4.  Each auxiliary vertex either has its
three defining points on the original minimal circle, or has signed Menger
curvature strictly larger than the reciprocal minimal radius.  The latter
alternative has curvature radius strictly smaller than the minimal radius,
so convex-hull containment prevents its curvature disk from containing the
auxiliary polygon.
-/

namespace Gluck.Forward


/-- A reciprocal-curvature gap is exactly the strict radius inequality used
by the minimal-disk rigidity argument. -/
theorem edgePrevCircleRadiusProfile_lt_of_signedMengerProfile_gap
    {m : ℕ} [NeZero m] {w : ZMod m → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hsimple : Gluck.Discrete.IsSimplePolygon w)
    (hpositive : PositivePolygonOrientation w)
    {i : ZMod m} (hgap : 1 / R < SignedMengerProfile w i) :
    EdgePrevCircleRadiusProfile w i < R := by
  have hρ : 0 < EdgePrevCircleRadiusProfile w i :=
    EdgePrevCircleRadiusProfile_pos hsimple i
  rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
    hsimple hpositive i] at hgap
  exact (inv_lt_inv₀ hR hρ).mp (by simpa [one_div] using hgap)




end Gluck.Forward
