/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleSplice

/-!
# Regularity of the circle-splice endpoints in Dahlberg Section 4
-/

namespace Gluck.Forward

open Gluck.Discrete


/-- Outward unit radial at angle `θ`. -/
noncomputable def circleRadial (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I)

/-- Positively oriented unit tangent at angle `θ`. -/
noncomputable def circleTangent (θ : ℝ) : ℂ :=
  Complex.I * circleRadial θ

@[simp] theorem circleRadial_re (θ : ℝ) : (circleRadial θ).re = Real.cos θ := by
  simp [circleRadial]

@[simp] theorem circleRadial_im (θ : ℝ) : (circleRadial θ).im = Real.sin θ := by
  simp [circleRadial]

@[simp] theorem circleTangent_re (θ : ℝ) : (circleTangent θ).re = -Real.sin θ := by
  simp [circleTangent]

@[simp] theorem circleTangent_im (θ : ℝ) : (circleTangent θ).im = Real.cos θ := by
  simp [circleTangent]

@[simp] theorem norm_circleRadial (θ : ℝ) : ‖circleRadial θ‖ = 1 := by
  simp [circleRadial]


@[simp] theorem inner_circleRadial_self (θ : ℝ) :
    inner ℝ (circleRadial θ) (circleRadial θ) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_circleRadial]
  norm_num





theorem circlePoint_sub_center (O : ℂ) (R θ : ℝ) :
    circlePoint O R θ - O = (R : ℝ) • circleRadial θ := by
  apply Complex.ext <;> simp [circlePoint, circleRadial]

/-- Polarization of the power of a point relative to the parametrized circle. -/
theorem dist_center_sq_eq_dist_circlePoint_sq_add (O P : ℂ) (R θ : ℝ) :
    dist O P ^ 2 = dist (circlePoint O R θ) P ^ 2 +
      2 * R * inner ℝ (circleRadial θ) (P - circlePoint O R θ) + R ^ 2 := by
  have hdecomp : P - O =
      (P - circlePoint O R θ) + (R : ℝ) • circleRadial θ := by
    rw [← circlePoint_sub_center O R θ]
    ring
  calc
    dist O P ^ 2 = inner ℝ (P - O) (P - O) := by
      rw [real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]
    _ = inner ℝ ((P - circlePoint O R θ) + (R : ℝ) • circleRadial θ)
        ((P - circlePoint O R θ) + (R : ℝ) • circleRadial θ) := by rw [hdecomp]
    _ = inner ℝ (P - circlePoint O R θ) (P - circlePoint O R θ) +
        2 * R * inner ℝ (circleRadial θ) (P - circlePoint O R θ) + R ^ 2 := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        inner_circleRadial_self, mul_one]
      rw [real_inner_comm (P - circlePoint O R θ) (circleRadial θ)]
      ring
    _ = dist (circlePoint O R θ) P ^ 2 +
        2 * R * inner ℝ (circleRadial θ) (P - circlePoint O R θ) + R ^ 2 := by
      rw [real_inner_self_eq_norm_sq, dist_eq_norm, norm_sub_rev]

theorem endpointPredecessor_cross_eq
    (O P : ℂ) (R θ δ : ℝ) :
    crossR2 (circlePoint O R (θ - δ)) (circlePoint O R θ) P =
      R * ((1 - Real.cos δ) *
          inner ℝ (circleTangent θ) (P - circlePoint O R θ) -
        Real.sin δ * inner ℝ (circleRadial θ) (P - circlePoint O R θ)) := by
  unfold crossR2
  simp only [Complex.sub_re, Complex.sub_im, circlePoint_re, circlePoint_im]
  rw [Complex.inner, Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im, circlePoint_re, circlePoint_im,
    circleRadial_re, circleRadial_im, circleTangent_re, circleTangent_im]
  rw [Real.cos_sub, Real.sin_sub]
  ring_nf



theorem endpointSuccessor_cross_eq
    (O P : ℂ) (R θ δ : ℝ) :
    crossR2 P (circlePoint O R θ) (circlePoint O R (θ + δ)) =
      R * (-(1 - Real.cos δ) *
          inner ℝ (circleTangent θ) (P - circlePoint O R θ) -
        Real.sin δ * inner ℝ (circleRadial θ) (P - circlePoint O R θ)) := by
  calc
    crossR2 P (circlePoint O R θ) (circlePoint O R (θ + δ)) =
        -crossR2 (circlePoint O R (θ + δ)) (circlePoint O R θ) P := by
          rw [crossR2_reverse]
    _ = -crossR2 (circlePoint O R (θ - (-δ))) (circlePoint O R θ) P := by
          congr 3
          ring
    _ = -(R * ((1 - Real.cos (-δ)) *
          inner ℝ (circleTangent θ) (P - circlePoint O R θ) -
        Real.sin (-δ) * inner ℝ (circleRadial θ) (P - circlePoint O R θ))) := by
          rw [endpointPredecessor_cross_eq]
    _ = R * (-(1 - Real.cos δ) *
          inner ℝ (circleTangent θ) (P - circlePoint O R θ) -
        Real.sin δ * inner ℝ (circleRadial θ) (P - circlePoint O R θ)) := by
          rw [Real.cos_neg, Real.sin_neg]
          ring



















namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

theorem circleMeshAngle_one_eq_add_step
    (q : ℕ) (θB θA : ℝ) :
    circleMeshAngle q 1 θB θA =
      θB + (θA - θB) / (q + 1 : ℕ) := by
  have hden : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold circleMeshAngle
  push_cast
  field_simp

theorem circleMeshAngle_penultimate_eq_sub_step
    (q : ℕ) (θB θA : ℝ) :
    circleMeshAngle q q θB θA =
      θA - (θA - θB) / (q + 1 : ℕ) := by
  have hden : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold circleMeshAngle
  push_cast
  field_simp
  ring

theorem circleSplice_leftEndpoint_triple
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hA : run.point run.chainStart = circlePoint O R θA) :
    run.circleSplice q θB θA (-1) =
        circlePoint O R (θA - (θA - θB) / (q + 1 : ℕ)) ∧
      run.circleSplice q θB θA 0 = circlePoint O R θA ∧
      run.circleSplice q θB θA 1 = run.point run.a := by
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hlast : run.chainLength + (q - 1) < m := by
    dsimp [m, spliceVertexCount]
    omega
  have hprevIndex :
      ((run.chainLength + (q - 1) : ℕ) : ZMod m) = -1 := by
    have heq : run.chainLength + (q - 1) = m - 1 := by
      dsimp [m, spliceVertexCount]
      omega
    rw [heq, Nat.cast_sub (by omega : 1 ≤ m)]
    simp
  constructor
  · rw [← hprevIndex]
    have hmesh := run.circleSplice_natCast_circleMesh q θB θA
      (j := q - 1) (by omega)
    rw [show run.circleSplice q θB θA
        ((run.chainLength + (q - 1) : ℕ) : ZMod m) =
          circlePoint O R (circleMeshAngle q ((q - 1) + 1) θB θA) by
      simpa only [Nat.cast_add] using hmesh]
    congr 2
    rw [show q - 1 + 1 = q by omega,
      circleMeshAngle_penultimate_eq_sub_step]
  constructor
  · exact (run.circleSplice_zero q θB θA).trans hA
  · have hone : (1 : ℕ) < run.chainLength := by
      exact run.three_le_chainLength.trans' (by omega)
    have hpoint := run.circleSplice_natCast_of_lt_chain q θB θA hone
    simpa only [Nat.cast_one, run.chainStart_add_one] using hpoint

theorem circleSplice_rightEndpoint_triple
    (q : ℕ) (hq : 0 < q) (θB θA : ℝ)
    (hB : run.point (run.b + 1) = circlePoint O R θB) :
    run.circleSplice q θB θA
        (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) - 1) =
        run.point run.b ∧
      run.circleSplice q θB θA
        ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) =
        circlePoint O R θB ∧
      run.circleSplice q θB θA
        (((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) + 1) =
        circlePoint O R (θB + (θA - θB) / (q + 1 : ℕ)) := by
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hthree := run.three_le_chainLength
  have hlen : 1 ≤ run.chainLength := by omega
  have hprev := run.circleSplice_chain_prev q θB θA
    (t := run.chainLength - 1) (by omega) (by omega)
  have hprevPoint : run.chainStart + (run.chainLength - 1) - 1 = run.b := by
    have ha := run.a_pos
    have hab := run.a_le_b
    simp only [chainStart, chainLength]
    omega
  have hiDef :
      ((run.chainLength - 1 : ℕ) : ZMod m) =
        (run.chainLength : ZMod m) - 1 := by
    rw [Nat.cast_sub hlen]
    norm_num
  constructor
  · rw [hprev, hprevPoint]
  constructor
  · simpa [hiDef] using (run.circleSplice_last_chain q θB θA).trans hB
  · have hnextIndex :
        ((run.chainLength - 1 : ℕ) : ZMod m) + 1 =
          (run.chainLength : ZMod m) := by
      rw [hiDef]
      ring
    rw [hnextIndex]
    have hmesh := run.circleSplice_natCast_circleMesh q θB θA
      (j := 0) hq
    simpa [circleMeshAngle_one_eq_add_step] using hmesh









end Section4PositiveRunCertificate

end Gluck.Forward
