import Gluck.Regularity.LevelGeodesic
import Gluck.ArcChain.Final

open Gluck Gluck.SpaceForm
open scoped ContDiff

#print axioms Gluck.SpaceForm.sphere_geodesicCurvature_comp_eq
#print axioms Gluck.SpaceForm.hyperbolic_geodesicCurvature_comp_eq
#print axioms Gluck.spherical_dahlberg_converse_geodesic_of_level
#print axioms Gluck.hyperbolic_dahlberg_converse_geodesic_of_level
#print axioms Gluck.ArcChain.HasWindow.four_le
#print axioms Gluck.ArcChain.stepConverse_iff_four_le
#print axioms Gluck.ArcChain.stepConverse

/-- The positive constant spherical branch is accepted by the new level interface. -/
theorem sphere_constant_level_audit (c : ℝ) (hc : 0 < c) :
    ∃ z : ℝ → ℂ, ContDiff ℝ ∞ z ∧ IsSimpleClosed z ∧
      (∀ t, deriv z t ≠ 0) ∧ (∀ t, 0 < sphereLift (z t) 2) ∧
      sphereGeodesicCurvature (sphereLift ∘ z) = fun _ ↦ c := by
  apply spherical_dahlberg_converse_geodesic_of_level
  · intro t
    rfl
  · exact contDiff_const
  · exact ⟨c, hc, Or.inl (fun _ ↦ rfl)⟩

/-- Constant hyperbolic profiles above one are accepted by the new level interface. -/
theorem hyperbolic_constant_level_audit (c : ℝ) (hc : 1 < c) :
    ∃ z : ℝ → ℂ, ContDiff ℝ ∞ z ∧ IsSimpleClosed z ∧
      (∀ t, deriv z t ≠ 0) ∧ (∀ t, ‖z t‖ < 1) ∧
      hyperbolicGeodesicCurvature (hyperboloidLift ∘ z) = fun _ ↦ c := by
  apply hyperbolic_dahlberg_converse_geodesic_of_level
  · intro t
    rfl
  · exact contDiff_const
  · exact ⟨c, hc, Or.inl (fun _ ↦ rfl)⟩

#print axioms sphere_constant_level_audit
#print axioms hyperbolic_constant_level_audit
