/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleArc
import Gluck.Forward.Discrete.MinimalDiskContacts

/-!
# The two-contact Section 4 circle arc

When a positive minimal enclosing disk has exactly two boundary contacts,
those contacts are antipodal.  Hence either directed endpoint interval in one
angle period has length exactly `π`; in particular the direction prescribed
by the positive run has the semicircle bound required by the circle splice.
-/

namespace Gluck.Forward

open Gluck.Discrete

private theorem circlePoint_angle_sub_eq_pi_of_isDiameter_aux
    {O : ℂ} {R θB θA : ℝ} (hR : 0 < R) (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hdiam : (⟨O, R⟩ : EuclideanGeometry.Sphere ℂ).IsDiameter
      (circlePoint O R θA) (circlePoint O R θB)) :
    θA - θB = Real.pi := by
  have hformula := dist_circlePoint_eq_two_mul_abs_sin_half O R θB θA
  rw [hdiam.symm.dist_left_right, abs_of_pos hR] at hformula
  have habs : |Real.sin ((θA - θB) / 2)| = 1 := by nlinarith
  have hhalfPos : 0 < (θA - θB) / 2 := by linarith
  have hhalfLt : (θA - θB) / 2 < Real.pi := by linarith
  have hsinPos : 0 < Real.sin ((θA - θB) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalfPos hhalfLt
  have hsin : Real.sin ((θA - θB) / 2) = 1 := by
    rwa [abs_of_pos hsinPos] at habs
  have hcosHalf : Real.cos ((θA - θB) / 2) = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq ((θA - θB) / 2)]
  have hcos : Real.cos (θA - θB) = -1 := by
    have hdouble := Real.cos_two_mul ((θA - θB) / 2)
    rw [show 2 * ((θA - θB) / 2) = θA - θB by ring, hcosHalf] at hdouble
    simpa using hdouble
  obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.mp hcos
  have htwoPi : 0 < 2 * Real.pi := by positivity
  have hklo : (-1 : ℝ) < (k : ℝ) := by
    by_contra hnot
    have hkle : (k : ℝ) ≤ -1 := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_right hkle htwoPi.le
    linarith [Real.pi_pos]
  have hkhi : (k : ℝ) < 1 := by
    by_contra hnot
    have hkge : (1 : ℝ) ≤ k := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_right hkge htwoPi.le
    linarith [Real.pi_pos]
  have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
  have hkhi' : k < (1 : ℤ) := by exact_mod_cast hkhi
  have hkzero : k = 0 := by omega
  rw [hkzero, Int.cast_zero, zero_mul, add_zero] at hk
  exact hk.symm

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

private theorem endpoint_isDiameter_of_contactSet_card_eq_two_aux
    (hsimple : IsSimplePolygon v) (hΔ : MinimalEnclosingDiskR2 v O R)
    (hcard : (circleContactSet v O R).card = 2) :
    (⟨O, R⟩ : EuclideanGeometry.Sphere ℂ).IsDiameter
      (run.point run.chainStart) (run.point (run.b + 1)) := by
  let p : ZMod n := Gluck.cyclicLift run.c (run.a - 1)
  let q : ZMod n := Gluck.cyclicLift run.c (run.b + 1)
  have hp : p ∈ circleContactSet v O R := by
    simpa [p] using run.left_contact
  have hq : q ∈ circleContactSet v O R := by
    simpa [q] using run.right_contact
  have hpq : p ≠ q := run.endpointIndices_ne hsimple hΔ
  have hpairSub : ({p, q} : Finset (ZMod n)) ⊆ circleContactSet v O R := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hp
    · exact hq
  have hpairEq : ({p, q} : Finset (ZMod n)) = circleContactSet v O R := by
    apply Finset.eq_of_subset_of_card_le hpairSub
    rw [hcard, Finset.card_pair hpq]
  have hboundary : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      i = p ∨ i = q := by
    intro i hi
    have hi' : i ∈ ({p, q} : Finset (ZMod n)) := by
      rw [hpairEq]
      exact mem_circleContactSet.mpr (Metric.mem_sphere'.mp hi)
    simpa using hi'
  have hdiam :=
    isDiameter_of_minimalEnclosingDiskR2_of_boundary_subset_pair
      hΔ (Metric.mem_sphere'.mpr (mem_circleContactSet.mp hp))
        (Metric.mem_sphere'.mpr (mem_circleContactSet.mp hq)) hboundary
  simpa [Section4PositiveRunCertificate.point,
    Section4PositiveRunCertificate.chainStart, p, q] using hdiam

private theorem circleArcCertificate_of_endpoint_isDiameter_aux
    (hsimple : IsSimplePolygon v) (hΔ : MinimalEnclosingDiskR2 v O R) (hR : 0 < R)
    (hdiam : (⟨O, R⟩ : EuclideanGeometry.Sphere ℂ).IsDiameter
      (run.point run.chainStart) (run.point (run.b + 1))) :
    Nonempty (Section4CircleArcCertificate run) := by
  obtain ⟨θB, θA, hB, hA, hBA, hspan⟩ :=
    run.exists_ordered_endpointAngles_of_minimalDisk hsimple hΔ
  have hdiamAngles :
      (⟨O, R⟩ : EuclideanGeometry.Sphere ℂ).IsDiameter
        (circlePoint O R θA) (circlePoint O R θB) := by
    simpa [hA, hB] using hdiam
  have hπ : θA - θB = Real.pi :=
    circlePoint_angle_sub_eq_pi_of_isDiameter_aux hR hBA hspan hdiamAngles
  exact ⟨{
    θB := θB
    θA := θA
    right_eq := hB
    left_eq := hA
    angles_lt := hBA
    span_lt := hspan
    pi_le_span := hπ.ge }⟩

/-- If the minimal circle has exactly the two run endpoints as contacts, the
directed completion arc has angular length exactly `π`. -/
theorem circleArcCertificate_of_contactSet_card_eq_two
    (hsimple : IsSimplePolygon v) (hΔ : MinimalEnclosingDiskR2 v O R) (hR : 0 < R)
    (hcard : (circleContactSet v O R).card = 2) :
    Nonempty (Section4CircleArcCertificate run) :=
  run.circleArcCertificate_of_endpoint_isDiameter_aux hsimple hΔ hR
    (run.endpoint_isDiameter_of_contactSet_card_eq_two_aux hsimple hΔ hcard)

end Section4PositiveRunCertificate

end Gluck.Forward
