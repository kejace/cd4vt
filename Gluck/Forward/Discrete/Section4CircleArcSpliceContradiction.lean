/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleArc
import Gluck.Forward.Discrete.Section4EndpointInteriorCurvature
import Gluck.Forward.Discrete.Section4CircleSpliceOrientation
import Gluck.Forward.Discrete.Section4CircleSpliceSimple
import Gluck.Forward.Discrete.Section4CircleSpliceNonconcyclic
import Gluck.Forward.Discrete.Section4CircleSpliceAssembly

/-!
# The circle-arc splice contradiction

Local endpoint curvature gaps turn an ordered complementary circle arc into
Dahlberg's impossible auxiliary-radius geometry.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

private theorem circleSplice_leftEndpoint_cross_pos_aux
    (hR : 0 < R) (arc : Section4CircleArcCertificate run)
    {q : ℕ} (hq : 0 < q)
    (hstepPos : 0 < (arc.θA - arc.θB) / (q + 1 : ℕ))
    (hstepPi : (arc.θA - arc.θB) / (q + 1 : ℕ) < Real.pi)
    (hgap : 1 / R < SignedMengerProfile (run.circleSplice q arc.θB arc.θA) 0) :
    0 < crossR2
      (run.circleSplice q arc.θB arc.θA
        ((0 : ZMod (run.spliceVertexCount q)) - 1))
      (run.circleSplice q arc.θB arc.θA 0)
      (run.circleSplice q arc.θB arc.θA
        ((0 : ZMod (run.spliceVertexCount q)) + 1)) := by
  letI : NeZero (run.spliceVertexCount q) := ⟨(run.spliceVertexCount_pos q).ne'⟩
  obtain ⟨hprev, hself, _⟩ :=
    run.circleSplice_leftEndpoint_triple q hq arc.θB arc.θA arc.left_eq
  have hedge : run.circleSplice q arc.θB arc.θA
      ((0 : ZMod (run.spliceVertexCount q)) - 1) ≠
      run.circleSplice q arc.θB arc.θA 0 := by
    rw [zero_sub, hprev, hself, ← dist_pos]
    rw [dist_circlePoint_sub_eq_two_mul_sin_half hR hstepPos (by linarith [Real.pi_pos])]
    have hsin : 0 < Real.sin (((arc.θA - arc.θB) / (q + 1 : ℕ)) / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
    positivity
  apply crossR2_pos_of_signedMengerR2_pos hedge
  have hpos : 0 < SignedMengerProfile (run.circleSplice q arc.θB arc.θA) 0 :=
    (one_div_pos.mpr hR).trans hgap
  simpa only [SignedMengerProfile_apply] using hpos

private theorem circleSplice_rightEndpoint_cross_pos_aux
    (hΔ : MinimalEnclosingDiskR2 v O R) (hR : 0 < R)
    (arc : Section4CircleArcCertificate run) {q : ℕ} (hq : 0 < q)
    (hgap : 1 / R < SignedMengerProfile (run.circleSplice q arc.θB arc.θA)
      ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q))) :
    0 < crossR2
      (run.circleSplice q arc.θB arc.θA
        (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) - 1))
      (run.circleSplice q arc.θB arc.θA
        ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)))
      (run.circleSplice q arc.θB arc.θA
        (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) + 1)) := by
  letI : NeZero (run.spliceVertexCount q) := ⟨(run.spliceVertexCount_pos q).ne'⟩
  obtain ⟨hprev, hself, _⟩ :=
    run.circleSplice_rightEndpoint_triple q hq arc.θB arc.θA arc.right_eq
  have hedge : run.circleSplice q arc.θB arc.θA
      (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) - 1) ≠
      run.circleSplice q arc.θB arc.θA
        ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) := by
    rw [hprev, hself]
    intro heq
    have hinterior := run.internal_dist_lt hΔ run.a_le_b le_rfl
    have hboundary : dist O (run.point run.b) = R := by
      rw [heq, dist_circlePoint_center, abs_of_pos hR]
    linarith
  apply crossR2_pos_of_signedMengerR2_pos hedge
  have hpos : 0 < SignedMengerProfile (run.circleSplice q arc.θB arc.θA)
      ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) :=
    (one_div_pos.mpr hR).trans hgap
  simpa only [SignedMengerProfile_apply] using hpos

private structure CircleArcMeshData (run : Section4PositiveRunCertificate v O R)
    (arc : Section4CircleArcCertificate run) (k : ℕ) where
  step_pos : 0 < (arc.θA - arc.θB) / (2 * k + 1 + 1 : ℕ)
  step_lt_pi : (arc.θA - arc.θB) / (2 * k + 1 + 1 : ℕ) < Real.pi
  inner : run.chainInnerRadius <
    R * Real.cos (((arc.θA - arc.θB) / (2 * k + 1 + 1 : ℕ)) / 2)
  left_gap : 1 / R < SignedMengerProfile
    (run.circleSplice (2 * k + 1) arc.θB arc.θA) 0
  right_gap : 1 / R < SignedMengerProfile
    (run.circleSplice (2 * k + 1) arc.θB arc.θA)
      ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount (2 * k + 1)))

private theorem exists_auxiliaryRadiusGeometry_of_circleArcMesh_aux
    (hsimple : IsSimplePolygon v) (hΔ : MinimalEnclosingDiskR2 v O R)
    (hR : 0 < R) (arc : Section4CircleArcCertificate run) (k : ℕ)
    (mesh : CircleArcMeshData run arc k) :
    Nonempty (Section4AuxiliaryRadiusGeometry O R) := by
  let q : ℕ := 2 * k + 1
  have hq : 0 < q := by dsimp [q]; omega
  letI : NeZero (run.spliceVertexCount q) := ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hstepPos : 0 < (arc.θA - arc.θB) / (q + 1 : ℕ) := by
    simpa only [q] using mesh.step_pos
  have hstepPi : (arc.θA - arc.θB) / (q + 1 : ℕ) < Real.pi := by
    simpa only [q] using mesh.step_lt_pi
  have hleft := run.circleSplice_leftEndpoint_cross_pos_aux hR arc hq hstepPos hstepPi
    (by simpa only [q] using mesh.left_gap)
  have hright := run.circleSplice_rightEndpoint_cross_pos_aux hΔ hR arc hq
    (by simpa only [q] using mesh.right_gap)
  have hpositive := run.circleSplice_positiveOrientation_of_endpoint_cross_pos hsimple hR
    q (show 1 ≤ q from hq) arc.θB arc.θA arc.angles_lt arc.span_lt arc.right_eq
      arc.left_eq hleft hright
  have hsimpleSplice := run.circleSplice_isSimplePolygon hsimple hΔ hR (show 1 ≤ q from hq)
    arc.angles_lt arc.span_lt (by simpa only [q] using mesh.inner) arc.right_eq arc.left_eq
      hpositive
  have hnoncyclic : ¬ Concyclic (run.circleSplice q arc.θB arc.θA) := by
    simpa only [q] using run.circleSplice_oddMesh_nonconcyclic hΔ hR k arc.θB arc.θA
      arc.angles_lt arc.span_lt arc.right_eq arc.left_eq
  refine ⟨?_⟩
  apply run.auxiliaryRadiusGeometry_of_oddCircleSplice k arc.θB arc.θA hR arc.pi_le_span
    (by linarith [arc.span_lt]) arc.right_eq arc.left_eq
  · simpa only [q] using hsimpleSplice
  · simpa only [q] using hpositive
  · simpa only [q] using hnoncyclic
  · exact mesh.left_gap
  · have hcast : ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount (2 * k + 1))) =
        (run.chainLength : ZMod (run.spliceVertexCount (2 * k + 1))) - 1 := by
      rw [Nat.cast_sub (run.three_le_chainLength.trans' (by omega))]
      norm_num
    rw [← hcast]
    exact mesh.right_gap

/-- A positive run cannot admit the complementary minimal-circle arc from Section 4. -/
theorem false_of_circleArcCertificate
    (hsimple : IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hR : 0 < R)
    (arc : Section4CircleArcCertificate run) : False := by
  obtain ⟨k, _hk, hstepPos, hstepPi, hinner, hleftGap, hrightGap⟩ :=
    run.exists_oddCircleMeshAngle_supporting_innerRadius_spliceEndpointGaps
      hR hΔ (run.chainInnerRadius_lt hΔ) arc.right_eq arc.left_eq
      arc.angles_lt arc.span_lt
  let mesh : CircleArcMeshData run arc k :=
    ⟨hstepPos, hstepPi, hinner, hleftGap, hrightGap⟩
  obtain ⟨aux⟩ :=
    run.exists_auxiliaryRadiusGeometry_of_circleArcMesh_aux hsimple hΔ hR arc k mesh
  exact false_of_section4AuxiliaryRadiusGeometry hR aux

end Section4PositiveRunCertificate

end Gluck.Forward
