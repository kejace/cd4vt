import Gluck.Forward.Discrete.Section4AuxiliaryContradiction
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Convex-hull criterion for Dahlberg's auxiliary-polygon rigidity

This file separates the final disk argument in §4 from the construction of
the auxiliary polygon. If the auxiliary polygon contains the original one in
its convex hull, then every curvature disk containing the auxiliary vertices
also contains the original vertices. Minimality of the original enclosing
disk rules out all auxiliary curvature circles of smaller radius.
-/

open Set Metric

namespace Gluck.Forward


/-- Each auxiliary curvature circle is either the original minimal enclosing
circle, or has radius strictly smaller than the original minimal radius. -/
def AuxiliaryCurvatureCircleClassification {m : ℕ}
    (w : ZMod m → ℂ) (O : ℂ) (R : ℝ) : Prop :=
  ∀ i, EdgePrevCurvatureCircleData w i = (O, R) ∨
    EdgePrevCircleRadiusProfile w i < R




end Gluck.Forward
