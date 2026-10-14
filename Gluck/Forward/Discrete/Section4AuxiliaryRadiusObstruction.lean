/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4AuxiliaryConsumer

/-!
# Direct radius obstruction for Dahlberg's Section 4 auxiliary polygon

For the final Theorem 6 contradiction it is enough that no disk of radius
strictly below the original minimal radius contains the auxiliary vertices.
This formulation lets the circle completion carry its own finite radius
obstruction (for example three circle points spanning at least a semicircle),
without requiring it to reproduce every original boundary contact.
-/

namespace Gluck.Forward

/-- The exact finite output needed when the circle mesh itself certifies the
minimal-radius obstruction. -/
structure Section4AuxiliaryRadiusGeometry (O : ℂ) (R : ℝ) where
  m : ℕ
  hne : NeZero m
  w : ZMod m → ℂ
  four_le : 4 ≤ m
  simple : Gluck.Discrete.IsSimplePolygon w
  positive : PositivePolygonOrientation w
  nonconcyclic : ¬ Concyclic w
  radius_obstruction : ∀ C S, 0 ≤ S → PolygonInClosedDiskR2 w C S → R ≤ S
  circle_or_curvature_gap : ∀ i : ZMod m,
    (OnDiskBoundaryR2 w O R (i - 1) ∧
      OnDiskBoundaryR2 w O R i ∧
      OnDiskBoundaryR2 w O R (i + 1)) ∨
    1 / R < SignedMengerProfile w i

/-- The vertexwise circle/gap dichotomy gives the same curvature-circle
classification as in the contact-coverage formulation. -/
theorem auxiliaryCurvatureCircleClassification_of_radiusGeometry
    {O : ℂ} {R : ℝ} (hR : 0 < R)
    (aux : Section4AuxiliaryRadiusGeometry O R) :
    AuxiliaryCurvatureCircleClassification aux.w O R := by
  letI : NeZero aux.m := aux.hne
  intro i
  rcases aux.circle_or_curvature_gap i with hcircle | hgap
  · left
    exact edgePrevCurvatureCircleData_eq_of_three_boundaries_of_cross_pos
      aux.simple hR hcircle.1 hcircle.2.1 hcircle.2.2 (aux.positive i)
  · right
    exact edgePrevCircleRadiusProfile_lt_of_signedMengerProfile_gap
      hR aux.simple aux.positive hgap

/-- The direct radius obstruction rules out every nonminimal member of the
curvature-circle classification. -/
theorem containingCurvatureDisksShareCircle_of_radiusGeometry
    {O : ℂ} {R : ℝ} (hR : 0 < R)
    (aux : Section4AuxiliaryRadiusGeometry O R) :
    ContainingCurvatureDisksShareCircle aux.w := by
  letI : NeZero aux.m := aux.hne
  have hclass : AuxiliaryCurvatureCircleClassification aux.w O R :=
    auxiliaryCurvatureCircleClassification_of_radiusGeometry hR aux
  have heq (i : ZMod aux.m)
      (hcontains : EdgePrevCurvatureDiskContainsAll aux.w i) :
      EdgePrevCurvatureCircleData aux.w i = (O, R) := by
    rcases hclass i with hcircle | hradius
    · exact hcircle
    · have hminimal : R ≤ EdgePrevCircleRadiusProfile aux.w i :=
        aux.radius_obstruction
          (EdgePrevCircleCenterProfile aux.w i)
          (EdgePrevCircleRadiusProfile aux.w i)
          (EdgePrevCircleRadiusProfile_pos aux.simple i).le hcontains
      exact (not_lt_of_ge hminimal hradius).elim
  intro i j hi hj
  exact (heq i hi).trans (heq j hj).symm

/-- Any direct-radius Section 4 auxiliary geometry contradicts the
source-free containing half of Dahlberg's exact Theorem 6. -/
theorem false_of_section4AuxiliaryRadiusGeometry
    {O : ℂ} {R : ℝ} (hR : 0 < R)
    (aux : Section4AuxiliaryRadiusGeometry O R) : False := by
  letI : NeZero aux.m := aux.hne
  exact dahlbergE2_theorem6_containing_source_contradiction
    aux.four_le aux.simple aux.positive aux.nonconcyclic
      (containingCurvatureDisksShareCircle_of_radiusGeometry hR aux)

end Gluck.Forward
