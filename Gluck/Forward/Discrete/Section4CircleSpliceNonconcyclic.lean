/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleSpliceRadius

/-!
# The Section 4 circle splice is not concyclic

An odd circle mesh contains the two retained boundary endpoints and its exact
angular midpoint.  These are three noncollinear points of the minimal circle,
so they determine that circle uniquely.  The retained positive run also
contains an original vertex strictly inside the minimal disk.  Consequently
the complete splice cannot lie on one circle.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- The explicit odd circle splice contains three noncollinear points of the
minimal circle and one strict interior point, hence is not concyclic. -/
theorem circleSplice_oddMesh_nonconcyclic
    (hΔ : MinimalEnclosingDiskR2 v O R) (hR : 0 < R)
    (k : ℕ) (θB θA : ℝ)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA) :
    ¬ Concyclic (run.circleSplice (2 * k + 1) θB θA) := by
  let q : ℕ := 2 * k + 1
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hkq : k < q := by
    dsimp [q]
    omega
  have hmidLeft : θB < (θB + θA) / 2 := by linarith
  have hmidRight : (θB + θA) / 2 < θA := by linarith
  have hcross : 0 < crossR2
      (circlePoint O R θB)
      (circlePoint O R ((θB + θA) / 2))
      (circlePoint O R θA) := by
    exact crossR2_circlePoint_pos_of_ordered O hR.ne'
      hmidLeft hmidRight hspan
  have hBM : circlePoint O R θB ≠
      circlePoint O R ((θB + θA) / 2) := by
    intro heq
    rw [heq] at hcross
    simp [crossR2] at hcross
  have hcircleO : CircumcircleR2
      (circlePoint O R θB)
      (circlePoint O R ((θB + θA) / 2))
      (circlePoint O R θA) O R := by
    refine ⟨hR, ?_, ?_, ?_⟩ <;>
      simp only [dist_circlePoint_center, abs_of_pos hR]
  intro hcyclic
  obtain ⟨C, S, hS, hCS⟩ := hcyclic
  have hpointB :
      run.circleSplice q θB θA
          (run.chainLength - 1 : ZMod m) = circlePoint O R θB := by
    rw [run.circleSplice_last_chain q θB θA, hB]
  have hpointMid :
      run.circleSplice q θB θA
          (run.chainLength + k : ZMod m) =
        circlePoint O R ((θB + θA) / 2) := by
    rw [run.circleSplice_natCast_circleMesh q θB θA hkq]
    simp [q]
  have hpointA : run.circleSplice q θB θA (0 : ZMod m) =
      circlePoint O R θA := by
    rw [run.circleSplice_zero, hA]
  have hcircleC : CircumcircleR2
      (circlePoint O R θB)
      (circlePoint O R ((θB + θA) / 2))
      (circlePoint O R θA) C S := by
    refine ⟨hS, ?_, ?_, ?_⟩
    · simpa [m, q, hpointB] using
        hCS (run.chainLength - 1 : ZMod m)
    · simpa [m, q, hpointMid] using
        hCS (run.chainLength + k : ZMod m)
    · simpa [m, q, hpointA] using hCS (0 : ZMod m)
  have hcircleEq : O = C ∧ R = S :=
    circumcircleR2_unique_of_noncollinear hBM hcross.ne' hcircleO hcircleC
  have honeLt : 1 < run.chainLength := run.three_le_chainLength.trans' (by omega)
  have hpointInterior :
      run.circleSplice q θB θA (1 : ZMod m) = run.point run.a := by
    calc
      run.circleSplice q θB θA (1 : ZMod m) =
          run.point (run.chainStart + 1) := by
        simpa only [m, Nat.cast_one] using
          run.circleSplice_natCast_of_lt_chain q θB θA honeLt
      _ = run.point run.a := by rw [run.chainStart_add_one]
  have hinterior : dist O (run.point run.a) < R :=
    run.internal_dist_lt hΔ (le_refl run.a) run.a_le_b
  have honCircle : dist C (run.point run.a) = S := by
    simpa [m, q, hpointInterior] using hCS (1 : ZMod m)
  rw [← hcircleEq.1, ← hcircleEq.2] at honCircle
  exact (ne_of_lt hinterior) honCircle

end Section4PositiveRunCertificate

end Gluck.Forward
