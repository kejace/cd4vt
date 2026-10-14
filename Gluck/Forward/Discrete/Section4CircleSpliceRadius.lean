/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleSplice
import Gluck.Forward.Discrete.CircleSemicircleRadiusObstruction

/-!
# Radius obstruction carried by an odd Section 4 circle mesh

With `2k+1` inserted circle vertices the affine mesh has `2k+2`
subintervals, so its central inserted vertex is the exact angular midpoint.
The two retained boundary endpoints and that midpoint therefore certify the
minimal radius whenever the completion arc spans at least a semicircle.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

@[simp] theorem circleMeshAngle_odd_midpoint
    (k : ℕ) (θB θA : ℝ) :
    circleMeshAngle (2 * k + 1) (k + 1) θB θA = (θB + θA) / 2 := by
  unfold circleMeshAngle
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The retained endpoints and exact midpoint of an odd mesh force every
enclosing disk for the splice to have radius at least `R`. -/
theorem circleSplice_oddMesh_radius_obstruction
    (k : ℕ) (θB θA : ℝ) (hR : 0 < R)
    (hlower : Real.pi ≤ θA - θB)
    (hupper : θA - θB < 2 * Real.pi)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA) :
    ∀ C S, 0 ≤ S →
      PolygonInClosedDiskR2
        (run.circleSplice (2 * k + 1) θB θA) C S → R ≤ S := by
  intro C S hS hcontains
  let q : ℕ := 2 * k + 1
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hkq : k < q := by dsimp [q]; omega
  have hpointB :
      run.circleSplice q θB θA
          (run.chainLength - 1 : ZMod (run.spliceVertexCount q)) =
        circlePoint O R θB := by
    rw [run.circleSplice_last_chain q θB θA, hB]
  have hpointMid :
      run.circleSplice q θB θA
          (run.chainLength + k : ZMod (run.spliceVertexCount q)) =
        circlePoint O R ((θB + θA) / 2) := by
    rw [run.circleSplice_natCast_circleMesh q θB θA hkq]
    simp [q]
  have hpointA : run.circleSplice q θB θA 0 =
      circlePoint O R θA := by
    rw [run.circleSplice_zero, hA]
  apply circlePoint_radius_le_of_semicircle_triple_inClosedDisk
    hR hS hlower hupper
  · simpa [q, hpointB] using
      hcontains
        (run.chainLength - 1 : ZMod (run.spliceVertexCount q))
  · simpa [q, hpointMid] using
      hcontains
        (run.chainLength + k : ZMod (run.spliceVertexCount q))
  · simpa [q, hpointA] using
      hcontains (0 : ZMod (run.spliceVertexCount q))

end Section4PositiveRunCertificate

end Gluck.Forward
