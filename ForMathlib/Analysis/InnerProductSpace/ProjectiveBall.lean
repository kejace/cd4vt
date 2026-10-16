/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic

/-!
# An explicit projective normalization of the unit ball

These are projective maps in the affine Klein model. They are not conformal
Möbius transformations. Keeping the positive square-root parameter explicit
makes the algebra independent of square-root simplification.
-/

@[expose] public section

open scoped InnerProductSpace

namespace ProjectiveBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine denominator of the projective map. -/
def denominator (a x : E) : ℝ := 1 - ⟪a, x⟫_ℝ

/-- The affine numerator of the projective map. -/
noncomputable def numerator (a : E) (σ : ℝ) (x : E) : E :=
  σ • x + (⟪a, x⟫_ℝ / (1 + σ) - 1) • a

/-- Projective ball normalization with square-root parameter `σ`. -/
noncomputable def transform (a : E) (σ : ℝ) (x : E) : E :=
  (denominator a x)⁻¹ • numerator a σ x

/-- The Lorentz bilinear identity underlying preservation of the unit sphere
and of its tangent supporting hyperplanes. -/
theorem numerator_inner_sub (a x y : E) {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) :
    ⟪numerator a σ x, numerator a σ y⟫_ℝ - denominator a x * denominator a y =
      σ ^ 2 * (⟪x, y⟫_ℝ - 1) := by
  have ha : ⟪a, a⟫_ℝ = 1 - σ ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    linarith
  simp only [numerator, denominator, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm a x, ha]
  field_simp
  ring

/-- The normalized bilinear identity preserves tangent hyperplanes to the unit sphere. -/
theorem one_sub_inner_transform (a x y : E) {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1)
    (hx : denominator a x ≠ 0) (hy : denominator a y ≠ 0) :
    1 - ⟪transform a σ x, transform a σ y⟫_ℝ =
      σ ^ 2 * (1 - ⟪x, y⟫_ℝ) / (denominator a x * denominator a y) := by
  have h := numerator_inner_sub a x y hσ hsq
  simp only [transform, real_inner_smul_left, real_inner_smul_right]
  field_simp
  nlinarith only [h]

/-- A parameter in the open unit ball has a positive denominator on the closed unit ball. -/
theorem denominator_pos_of_norm_le_one {a x : E} (ha : ‖a‖ < 1) (hx : ‖x‖ ≤ 1) :
    0 < denominator a x := by
  have h := real_inner_le_norm a x
  dsimp [denominator]
  nlinarith [norm_nonneg a, norm_nonneg x]

/-- Unit tangent normals remain unit after projective normalization. -/
theorem norm_transform_eq_one {a u : E} {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1)
    (hu : ‖u‖ = 1) (hden : denominator a u ≠ 0) :
    ‖transform a σ u‖ = 1 := by
  have h := one_sub_inner_transform a u u hσ hsq hden hden
  simp only [real_inner_self_eq_norm_sq, hu, one_pow, sub_self, mul_zero, zero_div] at h
  nlinarith [norm_nonneg (transform a σ u)]

/-- A tangent supporting equation is preserved wherever both denominators are nonzero. -/
theorem inner_transform_eq_one {a u x : E} {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1)
    (hu : denominator a u ≠ 0) (hx : denominator a x ≠ 0)
    (htangent : ⟪u, x⟫_ℝ = 1) :
    ⟪transform a σ u, transform a σ x⟫_ℝ = 1 := by
  have h := one_sub_inner_transform a u x hσ hsq hu hx
  rw [htangent, sub_self, mul_zero, zero_div] at h
  linarith

/-- Positive projective denominators preserve the strict inside of a supporting hyperplane. -/
theorem inner_transform_lt_one_iff {a u x : E} {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1)
    (hu : 0 < denominator a u) (hx : 0 < denominator a x) :
    ⟪transform a σ u, transform a σ x⟫_ℝ < 1 ↔ ⟪u, x⟫_ℝ < 1 := by
  rw [← sub_pos, one_sub_inner_transform a u x hσ hsq hu.ne' hx.ne',
    div_pos_iff_of_pos_right (mul_pos hu hx),
    mul_pos_iff_of_pos_left (sq_pos_of_pos hσ), sub_pos]

/-- The component in the parameter direction simplifies using the Lorentz relation. -/
theorem inner_numerator (a x : E) {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) :
    ⟪a, numerator a σ x⟫_ℝ = ⟪a, x⟫_ℝ - ‖a‖ ^ 2 := by
  have ha : ‖a‖ ^ 2 = 1 - σ ^ 2 := by linarith
  simp only [numerator, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ha]
  field_simp
  ring

/-- The inverse parameter has a nonzero denominator at every defined image. -/
theorem denominator_neg_transform (a x : E) {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) (hx : denominator a x ≠ 0) :
    denominator (-a) (transform a σ x) = σ ^ 2 / denominator a x := by
  have hi := inner_numerator a x hσ hsq
  simp only [denominator, transform, inner_neg_left, real_inner_smul_right, hi,
    sub_neg_eq_add]
  field_simp [show 1 - ⟪a, x⟫_ℝ ≠ 0 from hx]
  linarith

/-- The parameter-direction component of a transformed point. -/
theorem inner_transform (a x : E) {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) :
    ⟪a, transform a σ x⟫_ℝ = (⟪a, x⟫_ℝ - ‖a‖ ^ 2) / denominator a x := by
  simp only [transform, real_inner_smul_right, inner_numerator a x hσ hsq,
    div_eq_mul_inv, mul_comm]

/-- The inverse numerator is a scalar multiple of the original point. -/
theorem numerator_neg_transform (a x : E) {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) (hx : denominator a x ≠ 0) :
    numerator (-a) σ (transform a σ x) = (σ ^ 2 / denominator a x) • x := by
  rw [numerator, inner_neg_left, inner_transform a x hσ hsq, transform, numerator]
  match_scalars
  · ring
  · have ha : ‖a‖ ^ 2 = 1 - σ ^ 2 := by linarith
    rw [ha]
    field_simp
    dsimp [denominator]
    ring

/-- Negating the parameter inverts the projective normalization on its affine domain. -/
theorem transform_neg_transform (a x : E) {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) (hx : denominator a x ≠ 0) :
    transform (-a) σ (transform a σ x) = x := by
  rw [transform, denominator_neg_transform a x hσ hsq hx,
    numerator_neg_transform a x hσ hsq hx, smul_smul,
    inv_mul_cancel₀ (div_ne_zero (pow_ne_zero 2 hσ.ne') hx), one_smul]

/-- The map is injective wherever its affine denominator is nonzero. -/
theorem transform_injOn (a : E) {σ : ℝ}
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) :
    Set.InjOn (transform a σ) {x | denominator a x ≠ 0} := by
  intro x hx y hy h
  have hi := congrArg (transform (-a) σ) h
  simpa only [transform_neg_transform a x hσ hsq hx,
    transform_neg_transform a y hσ hsq hy] using hi

end ProjectiveBall
