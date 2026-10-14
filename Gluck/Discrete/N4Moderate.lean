/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Convexity
import Gluck.Discrete.N4Orthogonal

/-!
# Moderate-arc realization for four vertices

The orthogonal-diagonal quadrilateral realizes the analytic Euclidean development:
its side lengths satisfy every strict moderate wall, its exterior turns sum to
`2π`, and its developed edge vectors close by unit-complex cancellation.
-/

namespace Gluck.Discrete

open scoped Real

private lemma arcsin_div_add_arcsin_div {x y h : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hh : 0 < h) (hsq : h ^ 2 = x ^ 2 + y ^ 2) :
    Real.arcsin (x / h) + Real.arcsin (y / h) = Real.pi / 2 := by
  have hxle : x / h ≤ 1 := by
    have : x < h := by nlinarith [sq_pos_of_pos hy]
    exact ((div_lt_one hh).2 this).le
  have hyroot : Real.sqrt (1 - (x / h) ^ 2) = y / h := by
    rw [div_pow]
    have hh0 : h ≠ 0 := ne_of_gt hh
    have heq : 1 - x ^ 2 / h ^ 2 = (y / h) ^ 2 := by
      field_simp [hh0]
      nlinarith
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hy hh)]
  have harccos : Real.arccos (x / h) = Real.arcsin (y / h) := by
    rw [Real.arccos_eq_arcsin (div_nonneg hx.le hh.le), hyroot]
  rw [← harccos, Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

private lemma exp_arcsin_div {x y h : ℝ} (hx : 0 < x) (hy : 0 < y) (hh : 0 < h)
    (hsq : h ^ 2 = x ^ 2 + y ^ 2) :
    Complex.exp (((Real.arcsin (x / h) : ℝ) : ℂ) * Complex.I) =
      ((y / h : ℝ) : ℂ) + ((x / h : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_arcsin]
    have hh0 : h ≠ 0 := ne_of_gt hh
    have heq : 1 - (x / h) ^ 2 = (y / h) ^ 2 := by
      field_simp [hh0]
      nlinarith
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hy hh)]
    simp
  · rw [Complex.exp_ofReal_mul_I_im]
    have hxnonneg : 0 ≤ x / h := div_nonneg hx.le hh.le
    have hxle : x / h ≤ 1 := by
      have : x < h := by nlinarith [sq_pos_of_pos hy]
      exact ((div_lt_one hh).2 this).le
    rw [Real.sin_arcsin ((by norm_num : (-1 : ℝ) ≤ 0) |>.trans hxnonneg) hxle]
    simp

private lemma zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i
  decide

set_option maxHeartbeats 800000 in
-- The explicit closure certificate normalizes four rational complex products.
theorem orthogonal_realization_data
    {k₀ k₁ k₂ k₃ a b c d A B C D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hAsq : A ^ 2 = a ^ 2 + b ^ 2) (hBsq : B ^ 2 = b ^ 2 + c ^ 2)
    (hCsq : C ^ 2 = c ^ 2 + d ^ 2) (hDsq : D ^ 2 = d ^ 2 + a ^ 2)
    (hk₀ : 2 * a / (A * D) = k₀) (hk₁ : 2 * b / (A * B) = k₁)
    (hk₂ : 2 * c / (B * C) = k₂) (hk₃ : 2 * d / (C * D) = k₃) :
    ModerateArc 0 (fourProfile k₀ k₁ k₂ k₃) (fourProfile A B C D) ∧
      closureGap (fourProfile k₀ k₁ k₂ k₃) (fourProfile A B C D) = 0 ∧
      turningSum (fourProfile k₀ k₁ k₂ k₃) (fourProfile A B C D) =
        2 * Real.pi ∧
      IsSimplePolygon
        (polygonR2 (fourProfile k₀ k₁ k₂ k₃) (fourProfile A B C D)) := by
  let ℓ : ZMod 4 → ℝ := fourProfile A B C D
  have hk₀pos : 0 < k₀ := by rw [← hk₀]; positivity
  have hk₁pos : 0 < k₁ := by rw [← hk₁]; positivity
  have hk₂pos : 0 < k₂ := by rw [← hk₂]; positivity
  have hk₃pos : 0 < k₃ := by rw [← hk₃]; positivity
  have haA : a < A := by nlinarith [sq_pos_of_pos hb]
  have hbA : b < A := by nlinarith [sq_pos_of_pos ha]
  have hbB : b < B := by nlinarith [sq_pos_of_pos hc]
  have hcB : c < B := by nlinarith [sq_pos_of_pos hb]
  have hcC : c < C := by nlinarith [sq_pos_of_pos hd]
  have hdC : d < C := by nlinarith [sq_pos_of_pos hc]
  have hdD : d < D := by nlinarith [sq_pos_of_pos ha]
  have haD : a < D := by nlinarith [sq_pos_of_pos hd]
  have hMA : ModerateArc 0 (fourProfile k₀ k₁ k₂ k₃) ℓ := by
    rw [moderateArc_zero_iff]
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · simp only [ℓ, fourProfile_zero]
      rw [abs_of_pos hk₀pos, ← hk₀]
      refine ⟨hA, ?_, ?_⟩
      · calc
          2 * a / (A * D) * (D / 2) = a / A := by field_simp
          _ < 1 := (div_lt_one hA).2 haA
      · calc
          2 * a / (A * D) * (A / 2) = a / D := by field_simp
          _ < 1 := (div_lt_one hD).2 haD
    · simp only [ℓ, fourProfile_one]
      rw [abs_of_pos hk₁pos, ← hk₁]
      refine ⟨hB, ?_, ?_⟩
      · calc
          2 * b / (A * B) * (A / 2) = b / B := by field_simp
          _ < 1 := (div_lt_one hB).2 hbB
      · calc
          2 * b / (A * B) * (B / 2) = b / A := by field_simp
          _ < 1 := (div_lt_one hA).2 hbA
    · simp only [ℓ, fourProfile_two]
      rw [abs_of_pos hk₂pos, ← hk₂]
      refine ⟨hC, ?_, ?_⟩
      · calc
          2 * c / (B * C) * (B / 2) = c / C := by field_simp
          _ < 1 := (div_lt_one hC).2 hcC
      · calc
          2 * c / (B * C) * (C / 2) = c / B := by field_simp
          _ < 1 := (div_lt_one hB).2 hcB
    · simp only [ℓ, fourProfile_three]
      rw [abs_of_pos hk₃pos, ← hk₃]
      refine ⟨hD, ?_, ?_⟩
      · calc
          2 * d / (C * D) * (C / 2) = d / D := by field_simp
          _ < 1 := (div_lt_one hD).2 hdD
      · calc
          2 * d / (C * D) * (D / 2) = d / C := by field_simp
          _ < 1 := (div_lt_one hC).2 hdC
  have hturn₀ : turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 0 =
      Real.arcsin (a / A) + Real.arcsin (a / D) := by
    norm_num [turningAngle, ℓ]
    rw [show (-1 : ZMod 4) = 3 by decide, fourProfile_three]
    rw [← hk₀]
    congr 1 <;> field_simp
  have hturn₁ : turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 1 =
      Real.arcsin (b / B) + Real.arcsin (b / A) := by
    norm_num [turningAngle, ℓ]
    rw [← hk₁]
    congr 1 <;> field_simp
  have hturn₂ : turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 2 =
      Real.arcsin (c / C) + Real.arcsin (c / B) := by
    norm_num [turningAngle, ℓ]
    rw [← hk₂]
    congr 1 <;> field_simp
  have hturn₃ : turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 3 =
      Real.arcsin (d / D) + Real.arcsin (d / C) := by
    norm_num [turningAngle, ℓ]
    rw [← hk₃]
    congr 1 <;> field_simp
  have hsideA : Real.arcsin (a / A) + Real.arcsin (b / A) = Real.pi / 2 :=
    arcsin_div_add_arcsin_div ha hb hA hAsq
  have hsideB : Real.arcsin (b / B) + Real.arcsin (c / B) = Real.pi / 2 :=
    arcsin_div_add_arcsin_div hb hc hB hBsq
  have hsideC : Real.arcsin (c / C) + Real.arcsin (d / C) = Real.pi / 2 :=
    arcsin_div_add_arcsin_div hc hd hC hCsq
  have hsideD : Real.arcsin (d / D) + Real.arcsin (a / D) = Real.pi / 2 :=
    arcsin_div_add_arcsin_div hd ha hD hDsq
  have hT : turningSum (fourProfile k₀ k₁ k₂ k₃) ℓ = 2 * Real.pi := by
    unfold turningSum
    rw [← sum_range_natCast_add (turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ) 0]
    norm_num [Finset.sum_range_succ, hturn₀, hturn₁, hturn₂, hturn₃]
    linarith
  have hrot₀ :
      Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 0 : ℂ) * Complex.I) =
        (((b / A : ℝ) : ℂ) + ((a / A : ℝ) : ℂ) * Complex.I) *
          (((d / D : ℝ) : ℂ) + ((a / D : ℝ) : ℂ) * Complex.I) := by
    rw [hturn₀]
    push_cast
    rw [add_mul, Complex.exp_add, exp_arcsin_div ha hb hA hAsq,
      exp_arcsin_div ha hd hD (by simpa [add_comm] using hDsq)]
    norm_num
  have hrot₁ :
      Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 1 : ℂ) * Complex.I) =
        (((c / B : ℝ) : ℂ) + ((b / B : ℝ) : ℂ) * Complex.I) *
          (((a / A : ℝ) : ℂ) + ((b / A : ℝ) : ℂ) * Complex.I) := by
    rw [hturn₁]
    push_cast
    rw [add_mul, Complex.exp_add, exp_arcsin_div hb hc hB hBsq,
      exp_arcsin_div hb ha hA (by simpa [add_comm] using hAsq)]
    norm_num
  have hrot₂ :
      Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 2 : ℂ) * Complex.I) =
        (((d / C : ℝ) : ℂ) + ((c / C : ℝ) : ℂ) * Complex.I) *
          (((b / B : ℝ) : ℂ) + ((c / B : ℝ) : ℂ) * Complex.I) := by
    rw [hturn₂]
    push_cast
    rw [add_mul, Complex.exp_add, exp_arcsin_div hc hd hC hCsq,
      exp_arcsin_div hc hb hB (by simpa [add_comm] using hBsq)]
    norm_num
  have hrot₃ :
      Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 3 : ℂ) * Complex.I) =
        (((a / D : ℝ) : ℂ) + ((d / D : ℝ) : ℂ) * Complex.I) *
          (((c / C : ℝ) : ℂ) + ((d / C : ℝ) : ℂ) * Complex.I) := by
    rw [hturn₃]
    push_cast
    rw [add_mul, Complex.exp_add, exp_arcsin_div hd ha hD hDsq,
      exp_arcsin_div hd hc hC (by simpa [add_comm] using hCsq)]
    norm_num
  have hhead₀ :
      Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 0 : ℂ) * Complex.I) =
        Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 0 : ℂ) *
          Complex.I) := by
    congr 1
    simp [heading]
  have hhead₁ :
      Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 1 : ℂ) * Complex.I) =
        Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 0 : ℂ) *
            Complex.I) *
          Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 1 : ℂ) *
            Complex.I) := by
    have heq : heading (fourProfile k₀ k₁ k₂ k₃) ℓ 1 =
        turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 0 +
          turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 1 := by
      norm_num [heading, Finset.sum_range_succ]
    rw [heq, ← Complex.exp_add]
    push_cast
    ring_nf
  have hhead₂ :
      Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 2 : ℂ) * Complex.I) =
        Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 0 : ℂ) *
            Complex.I) *
          Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 1 : ℂ) *
            Complex.I) *
          Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 2 : ℂ) *
            Complex.I) := by
    have heq : heading (fourProfile k₀ k₁ k₂ k₃) ℓ 2 =
        turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 0 +
            turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 1 +
          turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 2 := by
      norm_num [heading, Finset.sum_range_succ]
    rw [heq, ← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring_nf
  have hhead₃ :
      Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 3 : ℂ) * Complex.I) =
        Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 0 : ℂ) *
            Complex.I) *
          Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 1 : ℂ) *
            Complex.I) *
          Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 2 : ℂ) *
            Complex.I) *
          Complex.exp ((turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 3 : ℂ) *
            Complex.I) := by
    have heq : heading (fourProfile k₀ k₁ k₂ k₃) ℓ 3 =
        turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 0 +
              turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 1 +
            turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 2 +
          turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ℓ 3 := by
      norm_num [heading, Finset.sum_range_succ]
    rw [heq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring_nf
  let ρ : ℂ := ((a / D : ℝ) : ℂ) - ((d / D : ℝ) : ℂ) * Complex.I
  let u₀ : ℂ := -((a / A : ℝ) : ℂ) + ((b / A : ℝ) : ℂ) * Complex.I
  let v₀ : ℂ := -((a / A : ℝ) : ℂ) - ((b / A : ℝ) : ℂ) * Complex.I
  let u₁ : ℂ := -((c / B : ℝ) : ℂ) - ((b / B : ℝ) : ℂ) * Complex.I
  let v₁ : ℂ := -((c / B : ℝ) : ℂ) + ((b / B : ℝ) : ℂ) * Complex.I
  let u₂ : ℂ := ((c / C : ℝ) : ℂ) - ((d / C : ℝ) : ℂ) * Complex.I
  let v₂ : ℂ := ((c / C : ℝ) : ℂ) + ((d / C : ℝ) : ℂ) * Complex.I
  let u₃ : ℂ := ((a / D : ℝ) : ℂ) + ((d / D : ℝ) : ℂ) * Complex.I
  have hunitA : u₀ * v₀ = 1 := by
    apply Complex.ext <;>
      simp only [u₀, v₀, Complex.mul_re, Complex.mul_im, Complex.neg_re,
        Complex.neg_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im, neg_zero, mul_zero, mul_one, zero_add, sub_zero, add_zero]
    · field_simp [hA.ne']
      nlinarith [hAsq]
    · ring
  have hunitB : u₁ * v₁ = 1 := by
    apply Complex.ext <;>
      simp only [u₁, v₁, Complex.mul_re, Complex.mul_im, Complex.neg_re,
        Complex.neg_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im, neg_zero, mul_zero, mul_one, zero_add, sub_zero, add_zero]
    · field_simp [hB.ne']
      nlinarith [hBsq]
    · ring
  have hunitC : u₂ * v₂ = 1 := by
    apply Complex.ext <;>
      simp only [u₂, v₂, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im, mul_zero, mul_one, zero_add, sub_zero, add_zero]
    · field_simp [hC.ne']
      nlinarith [hCsq]
    · ring
  have hunitD : ρ * u₃ = 1 := by
    apply Complex.ext <;>
      simp only [ρ, u₃, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
        mul_zero, mul_one, zero_add, sub_zero, add_zero]
    · field_simp [hD.ne']
      nlinarith [hDsq]
    · ring
  have hfactor₀ :
      (((b / A : ℝ) : ℂ) + ((a / A : ℝ) : ℂ) * Complex.I) *
          (((d / D : ℝ) : ℂ) + ((a / D : ℝ) : ℂ) * Complex.I) = ρ * u₀ := by
    apply Complex.ext <;>
      simp only [ρ, u₀, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, neg_zero, mul_zero, mul_one, zero_add,
        sub_zero, add_zero] <;>
      field_simp [hA.ne', hD.ne'] <;> ring
  have hfactor₁ :
      (((c / B : ℝ) : ℂ) + ((b / B : ℝ) : ℂ) * Complex.I) *
          (((a / A : ℝ) : ℂ) + ((b / A : ℝ) : ℂ) * Complex.I) = v₀ * u₁ := by
    apply Complex.ext <;>
      simp only [v₀, u₁, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, neg_zero, mul_zero, mul_one, zero_add,
        sub_zero, add_zero] <;>
      field_simp [hA.ne', hB.ne'] <;> ring
  have hfactor₂ :
      (((d / C : ℝ) : ℂ) + ((c / C : ℝ) : ℂ) * Complex.I) *
          (((b / B : ℝ) : ℂ) + ((c / B : ℝ) : ℂ) * Complex.I) = v₁ * u₂ := by
    apply Complex.ext <;>
      simp only [v₁, u₂, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, neg_zero, mul_zero, mul_one, zero_add,
        sub_zero, add_zero] <;>
      field_simp [hB.ne', hC.ne'] <;> ring
  have hfactor₃ :
      (((a / D : ℝ) : ℂ) + ((d / D : ℝ) : ℂ) * Complex.I) *
          (((c / C : ℝ) : ℂ) + ((d / C : ℝ) : ℂ) * Complex.I) = v₂ * u₃ := by
    apply Complex.ext <;>
      simp only [v₂, u₃, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        zero_add, sub_zero, add_zero] <;>
      field_simp [hC.ne', hD.ne']; ring
  have hdir₀ :
      Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 0 : ℂ) * Complex.I) = ρ * u₀ := by
    rw [hhead₀, hrot₀, hfactor₀]
  have hdir₁ :
      Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 1 : ℂ) * Complex.I) = ρ * u₁ := by
    rw [hhead₁, hrot₀, hrot₁, hfactor₀, hfactor₁]
    calc
      (ρ * u₀) * (v₀ * u₁) = ρ * (u₀ * v₀) * u₁ := by ring
      _ = ρ * u₁ := by rw [hunitA, mul_one]
  have hdir₂ :
      Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 2 : ℂ) * Complex.I) = ρ * u₂ := by
    rw [hhead₂, hrot₀, hrot₁, hrot₂, hfactor₀, hfactor₁, hfactor₂]
    calc
      (ρ * u₀) * (v₀ * u₁) * (v₁ * u₂) =
          ρ * (u₀ * v₀) * (u₁ * v₁) * u₂ := by ring
      _ = ρ * u₂ := by rw [hunitA, hunitB]; ring
  have hdir₃ :
      Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 3 : ℂ) * Complex.I) = ρ * u₃ := by
    rw [hhead₃, hrot₀, hrot₁, hrot₂, hrot₃, hfactor₀, hfactor₁, hfactor₂,
      hfactor₃]
    calc
      (ρ * u₀) * (v₀ * u₁) * (v₁ * u₂) * (v₂ * u₃) =
          ρ * (u₀ * v₀) * (u₁ * v₁) * (u₂ * v₂) * u₃ := by ring
      _ = ρ * u₃ := by rw [hunitA, hunitB, hunitC]; ring
  have hedge : (A : ℂ) * u₀ + (B : ℂ) * u₁ + (C : ℂ) * u₂ + (D : ℂ) * u₃ = 0 := by
    apply Complex.ext <;>
      simp only [u₀, u₁, u₂, u₃, Complex.mul_re, Complex.mul_im, Complex.neg_re,
        Complex.neg_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re,
        Complex.zero_im, neg_zero, mul_zero, mul_one, zero_add, sub_zero, add_zero] <;>
      field_simp [hA.ne', hB.ne', hC.ne', hD.ne'] <;> ring
  have hclose : closureGap (fourProfile k₀ k₁ k₂ k₃) ℓ = 0 := by
    unfold closureGap vertexR2
    norm_num [Finset.sum_range_succ, ℓ]
    change (A : ℂ) *
            Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 0 : ℂ) * Complex.I) +
          (B : ℂ) *
            Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 1 : ℂ) * Complex.I) +
        (C : ℂ) *
          Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 2 : ℂ) * Complex.I) +
      (D : ℂ) *
        Complex.exp ((heading (fourProfile k₀ k₁ k₂ k₃) ℓ 3 : ℂ) * Complex.I) = 0
    rw [hdir₀, hdir₁, hdir₂, hdir₃]
    calc
      (A : ℂ) * (ρ * u₀) + (B : ℂ) * (ρ * u₁) + (C : ℂ) * (ρ * u₂) +
          (D : ℂ) * (ρ * u₃) = ρ * ((A : ℂ) * u₀ + (B : ℂ) * u₁ +
            (C : ℂ) * u₂ + (D : ℂ) * u₃) := by ring
      _ = 0 := by rw [hedge, mul_zero]
  refine ⟨hMA, hclose, hT,
    isSimplePolygon_of_turningPositive (by norm_num) hMA ?_ hclose hT⟩
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · exact hk₀pos
  · exact hk₁pos
  · exact hk₂pos
  · exact hk₃pos

private theorem orthogonal_middle_turn_sum_lt_pi_aux
    {k₀ k₁ k₂ k₃ a b c d A B C D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hAsq : A ^ 2 = a ^ 2 + b ^ 2) (hBsq : B ^ 2 = b ^ 2 + c ^ 2)
    (hCsq : C ^ 2 = c ^ 2 + d ^ 2)
    (hk₁ : 2 * b / (A * B) = k₁) (hk₂ : 2 * c / (B * C) = k₂)
    (hcross : b * c < a * d) :
    turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) (fourProfile A B C D) 1 +
        turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) (fourProfile A B C D) 2 <
      Real.pi := by
  have haA : a < A := by nlinarith [sq_pos_of_pos hb]
  have hcC : c < C := by nlinarith [sq_pos_of_pos hd]
  have hcross_sq : (b * c) ^ 2 < (a * d) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hcross)
      (add_pos (mul_pos hb hc) (mul_pos ha hd))]
  have hcA_lt_aC : c * A < a * C := by
    nlinarith [mul_pos hc hA, mul_pos ha hC]
  have hratio : c / C < a / A := (div_lt_div_iff₀ hC hA).2 hcA_lt_aC
  have harc_lt : Real.arcsin (c / C) < Real.arcsin (a / A) := by
    apply (Real.strictMonoOn_arcsin.lt_iff_lt
      ⟨by linarith [div_nonneg hc.le hC.le], (div_lt_one hC).2 hcC |>.le⟩
      ⟨by linarith [div_nonneg ha.le hA.le], (div_lt_one hA).2 haA |>.le⟩).2
    exact hratio
  have hsideA := arcsin_div_add_arcsin_div ha hb hA hAsq
  have hsideB := arcsin_div_add_arcsin_div hb hc hB hBsq
  have hturn₁ :
      turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) (fourProfile A B C D) 1 =
        Real.arcsin (b / B) + Real.arcsin (b / A) := by
    norm_num [turningAngle]
    rw [← hk₁]
    congr 1 <;> field_simp
  have hturn₂ :
      turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) (fourProfile A B C D) 2 =
        Real.arcsin (c / C) + Real.arcsin (c / B) := by
    norm_num [turningAngle]
    rw [← hk₂]
    congr 1 <;> field_simp
  rw [hturn₁, hturn₂]
  linarith

private theorem orthogonal_cross_lt_of_curvature_product_aux
    {k₀ k₁ k₂ k₃ A B C D a b c d : ℝ}
    (hk₀ : 0 < k₀) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hA : 0 < A) (hC : 0 < C) (hΔ : 0 < orthogonalDelta k₀ k₁ k₂ k₃)
    (hBroot : B ^ 2 = orthogonalB2 k₀ k₁ k₂ k₃)
    (hDroot : D ^ 2 = orthogonalD2 k₀ k₁ k₂ k₃)
    (haeq : a = k₀ * A * D / 2) (hbeq : b = k₁ * A * B / 2)
    (hceq : c = k₂ * B * C / 2) (hdeq : d = k₃ * C * D / 2)
    (hminor : k₀ * k₁ < k₂ * k₃) :
    b * c < a * d := by
  have hfactor :
      k₀ * k₃ * (k₂ ^ 2 - k₁ ^ 2) -
          k₁ * k₂ * (k₀ ^ 2 - k₃ ^ 2) =
        (k₂ * k₃ - k₀ * k₁) * (k₀ * k₂ + k₁ * k₃) := by
    ring
  have hscaled :
      k₁ * k₂ * (k₀ ^ 2 - k₃ ^ 2) <
        k₀ * k₃ * (k₂ ^ 2 - k₁ ^ 2) := by
    have hp := mul_pos (sub_pos.mpr hminor)
      (add_pos (mul_pos hk₀ hk₂) (mul_pos hk₁ hk₃))
    nlinarith
  have hBD :
      k₁ * k₂ * orthogonalB2 k₀ k₁ k₂ k₃ <
        k₀ * k₃ * orthogonalD2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalB2 orthogonalD2
    rw [show k₁ * k₂ * (4 * (k₀ ^ 2 - k₃ ^ 2) /
        orthogonalDelta k₀ k₁ k₂ k₃) =
      (4 * (k₁ * k₂ * (k₀ ^ 2 - k₃ ^ 2))) /
        orthogonalDelta k₀ k₁ k₂ k₃ by ring,
      show k₀ * k₃ * (4 * (k₂ ^ 2 - k₁ ^ 2) /
        orthogonalDelta k₀ k₁ k₂ k₃) =
      (4 * (k₀ * k₃ * (k₂ ^ 2 - k₁ ^ 2))) /
        orthogonalDelta k₀ k₁ k₂ k₃ by ring,
      div_lt_div_iff_of_pos_right hΔ]
    nlinarith
  rw [haeq, hbeq, hceq, hdeq, ← sub_pos]
  rw [show
    k₀ * A * D / 2 * (k₃ * C * D / 2) -
        k₁ * A * B / 2 * (k₂ * B * C / 2) =
      A * C / 4 * (k₀ * k₃ * D ^ 2 - k₁ * k₂ * B ^ 2) by ring,
    hBroot, hDroot]
  exact mul_pos (div_pos (mul_pos hA hC) (by norm_num)) (sub_pos.mpr hBD)

/-- An orthogonal-diagonal quadrilateral gives a strict moderate-arc Euclidean realization. -/
theorem realizesR2_fourProfile_of_orthogonal
    {k₀ k₁ k₂ k₃ a b c d A B C D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hAsq : A ^ 2 = a ^ 2 + b ^ 2) (hBsq : B ^ 2 = b ^ 2 + c ^ 2)
    (hCsq : C ^ 2 = c ^ 2 + d ^ 2) (hDsq : D ^ 2 = d ^ 2 + a ^ 2)
    (hk₀ : 2 * a / (A * D) = k₀) (hk₁ : 2 * b / (A * B) = k₁)
    (hk₂ : 2 * c / (B * C) = k₂) (hk₃ : 2 * d / (C * D) = k₃) :
    RealizesR2 (fourProfile k₀ k₁ k₂ k₃) := by
  exact ⟨fourProfile A B C D,
    orthogonal_realization_data ha hb hc hd hA hB hC hD hAsq hBsq hCsq hDsq
      hk₀ hk₁ hk₂ hk₃⟩

set_option maxHeartbeats 800000 in
-- The explicit square-root construction and its product factorization normalize large terms.
/-- The strict alternating chamber has an explicit orthogonal realization;
the displayed product order makes its middle two turns a minor arc. -/
theorem exists_orthogonal_realization_of_strict_alternation
    {k₀ k₁ k₂ k₃ : ℝ}
    (hk₀ : 0 < k₀) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (h₁₀ : k₁ < k₀) (h₁₂ : k₁ < k₂)
    (h₃₀ : k₃ < k₀) (h₃₂ : k₃ < k₂) :
    ∃ ell : ZMod 4 → ℝ,
      ModerateArc 0 (fourProfile k₀ k₁ k₂ k₃) ell ∧
      closureGap (fourProfile k₀ k₁ k₂ k₃) ell = 0 ∧
      turningSum (fourProfile k₀ k₁ k₂ k₃) ell = 2 * Real.pi ∧
      IsSimplePolygon (polygonR2 (fourProfile k₀ k₁ k₂ k₃) ell) ∧
      (k₀ * k₁ < k₂ * k₃ →
        turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ell 1 +
            turningAngle 0 (fourProfile k₀ k₁ k₂ k₃) ell 2 <
          Real.pi) := by
  have hprod : k₁ * k₃ < k₀ * k₂ := by
    calc
      k₁ * k₃ < k₀ * k₃ := mul_lt_mul_of_pos_right h₁₀ hk₃
      _ < k₀ * k₂ := mul_lt_mul_of_pos_left h₃₂ hk₀
  have hΔ : 0 < orthogonalDelta k₀ k₁ k₂ k₃ := by
    have hfac : orthogonalDelta k₀ k₁ k₂ k₃ =
        (k₀ * k₂ - k₁ * k₃) * (k₀ * k₂ + k₁ * k₃) := by
      unfold orthogonalDelta
      ring
    rw [hfac]
    exact mul_pos (sub_pos.mpr hprod) (add_pos (mul_pos hk₀ hk₂) (mul_pos hk₁ hk₃))
  have hs₂₃ : 0 < k₂ ^ 2 - k₃ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₃₂) (add_pos hk₂ hk₃)]
  have hs₀₃ : 0 < k₀ ^ 2 - k₃ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₃₀) (add_pos hk₀ hk₃)]
  have hs₀₁ : 0 < k₀ ^ 2 - k₁ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₁₀) (add_pos hk₀ hk₁)]
  have hs₂₁ : 0 < k₂ ^ 2 - k₁ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₁₂) (add_pos hk₂ hk₁)]
  have hA2 : 0 < orthogonalA2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalA2
    exact div_pos (mul_pos (by norm_num) hs₂₃) hΔ
  have hB2 : 0 < orthogonalB2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalB2
    exact div_pos (mul_pos (by norm_num) hs₀₃) hΔ
  have hC2 : 0 < orthogonalC2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalC2
    exact div_pos (mul_pos (by norm_num) hs₀₁) hΔ
  have hD2 : 0 < orthogonalD2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalD2
    exact div_pos (mul_pos (by norm_num) hs₂₁) hΔ
  let A := Real.sqrt (orthogonalA2 k₀ k₁ k₂ k₃)
  let B := Real.sqrt (orthogonalB2 k₀ k₁ k₂ k₃)
  let C := Real.sqrt (orthogonalC2 k₀ k₁ k₂ k₃)
  let D := Real.sqrt (orthogonalD2 k₀ k₁ k₂ k₃)
  have hA : 0 < A := by exact Real.sqrt_pos.2 hA2
  have hB : 0 < B := by exact Real.sqrt_pos.2 hB2
  have hC : 0 < C := by exact Real.sqrt_pos.2 hC2
  have hD : 0 < D := by exact Real.sqrt_pos.2 hD2
  have hAroot : A ^ 2 = orthogonalA2 k₀ k₁ k₂ k₃ := by
    exact Real.sq_sqrt hA2.le
  have hBroot : B ^ 2 = orthogonalB2 k₀ k₁ k₂ k₃ := by
    exact Real.sq_sqrt hB2.le
  have hCroot : C ^ 2 = orthogonalC2 k₀ k₁ k₂ k₃ := by
    exact Real.sq_sqrt hC2.le
  have hDroot : D ^ 2 = orthogonalD2 k₀ k₁ k₂ k₃ := by
    exact Real.sq_sqrt hD2.le
  let a := k₀ * A * D / 2
  let b := k₁ * A * B / 2
  let c := k₂ * B * C / 2
  let d := k₃ * C * D / 2
  have ha : 0 < a := by exact div_pos (mul_pos (mul_pos hk₀ hA) hD) (by norm_num)
  have hb : 0 < b := by exact div_pos (mul_pos (mul_pos hk₁ hA) hB) (by norm_num)
  have hc : 0 < c := by exact div_pos (mul_pos (mul_pos hk₂ hB) hC) (by norm_num)
  have hd : 0 < d := by exact div_pos (mul_pos (mul_pos hk₃ hC) hD) (by norm_num)
  have hasq : a ^ 2 = k₀ ^ 2 * orthogonalA2 k₀ k₁ k₂ k₃ *
      orthogonalD2 k₀ k₁ k₂ k₃ / 4 := by
    dsimp [a]
    rw [div_pow, mul_pow, mul_pow, hAroot, hDroot]
    norm_num
  have hbsq : b ^ 2 = k₁ ^ 2 * orthogonalA2 k₀ k₁ k₂ k₃ *
      orthogonalB2 k₀ k₁ k₂ k₃ / 4 := by
    dsimp [b]
    rw [div_pow, mul_pow, mul_pow, hAroot, hBroot]
    norm_num
  have hcsq : c ^ 2 = k₂ ^ 2 * orthogonalB2 k₀ k₁ k₂ k₃ *
      orthogonalC2 k₀ k₁ k₂ k₃ / 4 := by
    dsimp [c]
    rw [div_pow, mul_pow, mul_pow, hBroot, hCroot]
    norm_num
  have hdsq : d ^ 2 = k₃ ^ 2 * orthogonalC2 k₀ k₁ k₂ k₃ *
      orthogonalD2 k₀ k₁ k₂ k₃ / 4 := by
    dsimp [d]
    rw [div_pow, mul_pow, mul_pow, hCroot, hDroot]
    norm_num
  have hAsq : A ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hAroot, hasq, hbsq]
    exact orthogonalA2_identity hΔ.ne'
  have hBsq : B ^ 2 = b ^ 2 + c ^ 2 := by
    rw [hBroot, hbsq, hcsq]
    exact orthogonalB2_identity hΔ.ne'
  have hCsq : C ^ 2 = c ^ 2 + d ^ 2 := by
    rw [hCroot, hcsq, hdsq]
    exact orthogonalC2_identity hΔ.ne'
  have hDsq : D ^ 2 = d ^ 2 + a ^ 2 := by
    rw [hDroot, hdsq, hasq]
    exact orthogonalD2_identity hΔ.ne'
  have hk₀eq : 2 * a / (A * D) = k₀ := by
    dsimp [a]
    field_simp [hA.ne', hD.ne']
  have hk₁eq : 2 * b / (A * B) = k₁ := by
    dsimp [b]
    field_simp [hA.ne', hB.ne']
  have hk₂eq : 2 * c / (B * C) = k₂ := by
    dsimp [c]
    field_simp [hB.ne', hC.ne']
  have hk₃eq : 2 * d / (C * D) = k₃ := by
    dsimp [d]
    field_simp [hC.ne', hD.ne']
  have hdata := orthogonal_realization_data ha hb hc hd hA hB hC hD
    hAsq hBsq hCsq hDsq hk₀eq hk₁eq hk₂eq hk₃eq
  refine ⟨fourProfile A B C D, hdata.1, hdata.2.1, hdata.2.2.1,
    hdata.2.2.2, ?_⟩
  intro hminor
  apply orthogonal_middle_turn_sum_lt_pi_aux ha hb hc hd hA hB hC hAsq hBsq hCsq
    hk₁eq hk₂eq
  exact orthogonal_cross_lt_of_curvature_product_aux hk₀ hk₁ hk₂ hk₃ hA hC hΔ
    hBroot hDroot rfl rfl rfl rfl hminor

/-- **The four-vertex orthogonal-diagonal construction.**  If vertices `0,2`
carry the two strictly larger curvatures and vertices `1,3` the two strictly
smaller ones, the prescribed profile is realized by an explicit simple
orthogonal-diagonal quadrilateral. -/
theorem realizesR2_fourProfile_of_strictAlternation
    {k₀ k₁ k₂ k₃ : ℝ}
    (hk₀ : 0 < k₀) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (h₁₀ : k₁ < k₀) (h₁₂ : k₁ < k₂)
    (h₃₀ : k₃ < k₀) (h₃₂ : k₃ < k₂) :
    RealizesR2 (fourProfile k₀ k₁ k₂ k₃) := by
  obtain ⟨ell, hmoderate, hclose, hturn, hsimple, _⟩ :=
    exists_orthogonal_realization_of_strict_alternation
      hk₀ hk₁ hk₂ hk₃ h₁₀ h₁₂ h₃₀ h₃₂
  exact ⟨ell, hmoderate, hclose, hturn, hsimple⟩

/-- A positive four-point profile alternating strictly across a level has a
strict moderate-arc Euclidean realization. -/
theorem realizesR2_zmod4_of_alternating_level {k : ZMod 4 → ℝ} {q : ℝ}
    (hk : ∀ i, 0 < k i) (h₀ : q < k 0) (h₁ : k 1 < q)
    (h₂ : q < k 2) (h₃ : k 3 < q) : RealizesR2 k := by
  have hprofile : k = fourProfile (k 0) (k 1) (k 2) (k 3) := by
    funext i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp
  rw [hprofile]
  exact realizesR2_fourProfile_of_strictAlternation (hk 0) (hk 1) (hk 2) (hk 3)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- Rotating the labels of a positive four-point moderate-arc realization by
one place preserves Euclidean realizability. -/
theorem realizesR2_comp_add_one_zmod4 {k : ZMod 4 → ℝ}
    (hk : ∀ i, 0 < k i) (h : RealizesR2 k) :
    RealizesR2 (fun i ↦ k (i + 1)) := by
  obtain ⟨ℓ, hMA, hE, hT, _hsimple⟩ := h
  let k' : ZMod 4 → ℝ := fun i ↦ k (i + 1)
  let ℓ' : ZMod 4 → ℝ := fun i ↦ ℓ (i + 1)
  have hMA' : ModerateArc 0 k' ℓ' := by
    rw [moderateArc_zero_iff] at hMA ⊢
    intro i
    convert hMA (i + 1) using 1
    all_goals simp only [k', ℓ', sub_eq_add_neg]
    all_goals ring_nf
  have hturn (i : ZMod 4) :
      turningAngle 0 k' ℓ' i = turningAngle 0 k ℓ (i + 1) := by
    simp only [turningAngle, tK_zero, k', ℓ', sub_eq_add_neg]
    congr 2
    ring_nf
  have hT' : turningSum k' ℓ' = 2 * Real.pi := by
    unfold turningSum
    simp_rw [hturn]
    rw [show (∑ i : ZMod 4, turningAngle 0 k ℓ (i + 1)) = turningSum k ℓ by
      unfold turningSum
      exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod 4)) _ _ (fun _ ↦ rfl)]
    exact hT
  have hE' : closureGap k' ℓ' = 0 := by
    let θ : ZMod 4 → ℝ := turningAngle 0 k ℓ
    have hhead₀ : heading k ℓ 0 = θ 0 := by simp [heading, θ]
    have hhead₁ : heading k ℓ 1 = θ 0 + θ 1 := by
      norm_num [heading, Finset.sum_range_succ, θ]
    have hhead₂ : heading k ℓ 2 = θ 0 + θ 1 + θ 2 := by
      norm_num [heading, Finset.sum_range_succ, θ]
    have hhead₃ : heading k ℓ 3 = 2 * Real.pi := by
      have hsum := hT
      unfold turningSum at hsum
      rw [← sum_range_natCast_add (turningAngle 0 k ℓ) 0] at hsum
      norm_num [Finset.sum_range_succ, heading, θ] at hsum ⊢
      linarith
    have hhead₀' : heading k' ℓ' 0 = θ 1 := by
      simp [heading, hturn, θ]
    have hhead₁' : heading k' ℓ' 1 = θ 1 + θ 2 := by
      norm_num [heading, Finset.sum_range_succ, hturn, θ]
    have hhead₂' : heading k' ℓ' 2 = θ 1 + θ 2 + θ 3 := by
      norm_num [heading, Finset.sum_range_succ, hturn, θ]
    have hhead₃' : heading k' ℓ' 3 = 2 * Real.pi := by
      have hsum := hT'
      unfold turningSum at hsum
      rw [← sum_range_natCast_add (turningAngle 0 k' ℓ') 0] at hsum
      norm_num [Finset.sum_range_succ, heading] at hsum ⊢
      linarith
    let E : ℝ → ℂ := fun x ↦ Complex.exp ((x : ℂ) * Complex.I)
    have hmul (x y : ℝ) : E x * E y = E (x + y) := by
      simp only [E, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hone : E (2 * Real.pi) = 1 := by
      change Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1
      convert Complex.exp_two_pi_mul_I using 1
      all_goals push_cast
      all_goals ring_nf
    have hE₀ := hE
    unfold closureGap vertexR2 at hE₀ ⊢
    norm_num [Finset.sum_range_succ, ℓ'] at hE₀ ⊢
    change (ℓ 0 : ℂ) * E (heading k ℓ 0) +
          (ℓ 1 : ℂ) * E (heading k ℓ 1) +
        (ℓ 2 : ℂ) * E (heading k ℓ 2) +
      (ℓ 3 : ℂ) * E (heading k ℓ 3) = 0 at hE₀
    change (ℓ 1 : ℂ) * E (heading k' ℓ' 0) +
          (ℓ 2 : ℂ) * E (heading k' ℓ' 1) +
        (ℓ 3 : ℂ) * E (heading k' ℓ' 2) +
      (ℓ 0 : ℂ) * E (heading k' ℓ' 3) = 0
    rw [hhead₀, hhead₁, hhead₂, hhead₃, hone] at hE₀
    rw [hhead₀', hhead₁', hhead₂', hhead₃', hone]
    apply (mul_left_cancel₀
      (Complex.exp_ne_zero (((θ 0 : ℝ) : ℂ) * Complex.I)))
    change E (θ 0) *
        ((ℓ 1 : ℂ) * E (θ 1) +
          (ℓ 2 : ℂ) * E (θ 1 + θ 2) +
          (ℓ 3 : ℂ) * E (θ 1 + θ 2 + θ 3) +
          (ℓ 0 : ℂ) * 1) = E (θ 0) * 0
    have hsum : θ 0 + θ 1 + θ 2 + θ 3 = 2 * Real.pi := by
      norm_num [heading, Finset.sum_range_succ, θ] at hhead₃ ⊢
      linarith
    rw [mul_zero]
    calc
      E (θ 0) *
          ((ℓ 1 : ℂ) * E (θ 1) +
            (ℓ 2 : ℂ) * E (θ 1 + θ 2) +
            (ℓ 3 : ℂ) * E (θ 1 + θ 2 + θ 3) +
            (ℓ 0 : ℂ) * 1) =
          (ℓ 1 : ℂ) * (E (θ 0) * E (θ 1)) +
            (ℓ 2 : ℂ) * (E (θ 0) * E (θ 1 + θ 2)) +
            (ℓ 3 : ℂ) * (E (θ 0) * E (θ 1 + θ 2 + θ 3)) +
            (ℓ 0 : ℂ) * E (θ 0) := by ring
      _ = (ℓ 1 : ℂ) * E (θ 0 + θ 1) +
            (ℓ 2 : ℂ) * E (θ 0 + (θ 1 + θ 2)) +
            (ℓ 3 : ℂ) * E (θ 0 + (θ 1 + θ 2 + θ 3)) +
            (ℓ 0 : ℂ) * E (θ 0) := by rw [hmul, hmul, hmul]
      _ = (ℓ 0 : ℂ) * E (θ 0) +
            (ℓ 1 : ℂ) * E (θ 0 + θ 1) +
            (ℓ 2 : ℂ) * E (θ 0 + θ 1 + θ 2) +
            (ℓ 3 : ℂ) * 1 := by
        rw [show θ 0 + (θ 1 + θ 2) = θ 0 + θ 1 + θ 2 by ring,
          show θ 0 + (θ 1 + θ 2 + θ 3) = 2 * Real.pi by linarith,
          hone]
        ring
      _ = 0 := hE₀
  refine ⟨ℓ', hMA', hE', hT',
    isSimplePolygon_of_turningPositive (by norm_num) hMA' ?_ hE' hT'⟩
  intro i
  exact hk (i + 1)

/-- Cyclic reindexing preserves positive four-point moderate-arc Euclidean
realizability. -/
theorem realizesR2_comp_add_zmod4 {k : ZMod 4 → ℝ}
    (hk : ∀ i, 0 < k i) (h : RealizesR2 k) (a : ZMod 4) :
    RealizesR2 (fun i ↦ k (i + a)) := by
  have h₁ : RealizesR2 (fun i ↦ k (i + 1)) :=
    realizesR2_comp_add_one_zmod4 hk h
  have h₂ : RealizesR2 (fun i ↦ k (i + 2)) := by
    have hshift := realizesR2_comp_add_one_zmod4 (fun i ↦ hk (i + 1)) h₁
    convert hshift using 1
    funext i
    congr 1
    ring
  have h₃ : RealizesR2 (fun i ↦ k (i + 3)) := by
    have hshift := realizesR2_comp_add_one_zmod4 (fun i ↦ hk (i + 2)) h₂
    convert hshift using 1
    funext i
    congr 1
    ring
  rcases zmod4_cases a with rfl | rfl | rfl | rfl
  · convert h using 1
    funext i
    congr 1
    simp
  · exact h₁
  · exact h₂
  · exact h₃

end Gluck.Discrete
