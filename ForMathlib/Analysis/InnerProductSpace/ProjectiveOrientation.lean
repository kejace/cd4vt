module

public import ForMathlib.Analysis.InnerProductSpace.ProjectiveBall
public import Mathlib.Analysis.Complex.Basic

/-!
# Orientation of projective ball normalization in the plane

The area multiplier is positive precisely on the affine region of positive
projective denominators. These identities make orientation preservation explicit.
-/

@[expose] public section

open scoped InnerProductSpace

namespace ProjectiveBall

/-- The standard oriented area form on the complex plane. -/
def area (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

lemma area_numerator (a u v : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) :
    area (numerator a σ u) (numerator a σ v) =
      σ * (area u v + area a (u - v)) := by
  have ha : σ ^ 2 + (a.re ^ 2 + a.im ^ 2) = 1 := by
    simpa only [Complex.sq_norm, Complex.normSq_apply, ← pow_two] using hsq
  simp only [area, numerator, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, Complex.sub_re, Complex.sub_im, Complex.inner, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, smul_eq_mul]
  field_simp
  linear_combination σ * (1 + σ) * (u.re * v.im - u.im * v.re) * ha

/-- The affine homogeneous determinant of the projective map. -/
lemma denominator_area_numerator (a x y z : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) :
    denominator a x * area (numerator a σ y) (numerator a σ z) -
        denominator a y * area (numerator a σ x) (numerator a σ z) +
        denominator a z * area (numerator a σ x) (numerator a σ y) =
      σ ^ 3 * area (y - x) (z - x) := by
  have ha : σ ^ 2 + (a.re ^ 2 + a.im ^ 2) = 1 := by
    simpa only [Complex.sq_norm, Complex.normSq_apply, ← pow_two] using hsq
  rw [area_numerator a y z hσ hsq, area_numerator a x z hσ hsq,
    area_numerator a x y hσ hsq]
  simp only [area, denominator, Complex.sub_re, Complex.sub_im, Complex.inner,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  linear_combination -σ * ((y.re - x.re) * (z.im - x.im) -
    (y.im - x.im) * (z.re - x.re)) * ha

/-- Signed triangle area is multiplied by a positive factor on the positive
projective chart. The formula itself only needs nonzero denominators. -/
theorem area_transform_sub (a x y z : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) (hx : denominator a x ≠ 0)
    (hy : denominator a y ≠ 0) (hz : denominator a z ≠ 0) :
    area (transform a σ y - transform a σ x) (transform a σ z - transform a σ x) =
      σ ^ 3 * area (y - x) (z - x) /
        (denominator a x * denominator a y * denominator a z) := by
  have h := denominator_area_numerator a x y z hσ hsq
  simp only [transform, area, Complex.sub_re, Complex.sub_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]
  field_simp [hx, hy, hz]
  simp only [area, Complex.sub_re, Complex.sub_im] at h
  linear_combination denominator a x * h

/-- Every triangle keeps its strict orientation in the positive projective chart. -/
theorem area_transform_sub_pos_iff (a x y z : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) (hx : 0 < denominator a x)
    (hy : 0 < denominator a y) (hz : 0 < denominator a z) :
    0 < area (transform a σ y - transform a σ x)
      (transform a σ z - transform a σ x) ↔ 0 < area (y - x) (z - x) := by
  rw [area_transform_sub a x y z hσ hsq hx.ne' hy.ne' hz.ne',
    div_pos_iff_of_pos_right (mul_pos (mul_pos hx hy) hz),
    mul_pos_iff_of_pos_left (pow_pos hσ 3)]

/-- The radial signed area formula, useful for transported tangent normals. -/
theorem area_transform (a u v : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) :
    area (transform a σ u) (transform a σ v) =
      σ * (area u v + area a (u - v)) / (denominator a u * denominator a v) := by
  have h := area_numerator a u v hσ hsq
  simp only [transform, area, Complex.smul_re, Complex.smul_im, smul_eq_mul,
    Complex.sub_re, Complex.sub_im]
  simp only [area, Complex.sub_re, Complex.sub_im] at h
  rw [div_eq_mul_inv, mul_inv_rev]
  linear_combination (denominator a u)⁻¹ * (denominator a v)⁻¹ * h

end ProjectiveBall
