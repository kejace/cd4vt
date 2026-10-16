/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace, Codex
-/
module

public import Gluck.Discrete.Convexity

/-!
# Positive similarity invariance of Euclidean realization

Multiplying every prescribed curvature by a positive scalar and dividing every
edge length by the same scalar preserves all Euclidean turning angles.  The
resulting development is the original polygon scaled by the reciprocal scalar,
so closure and total turning are unchanged.  For positive curvature profiles,
the existing positive-turning simplicity theorem then supplies simplicity.
-/

@[expose] public section

namespace Gluck.Discrete

variable {n : ℕ}

/-- Simultaneously scaling curvatures and inversely scaling lengths leaves each
Euclidean turning angle unchanged. -/
theorem turningAngle_scale_curvature_length
    {s : ℝ} (hs : s ≠ 0) (κ ℓ : ZMod n → ℝ) (i : ZMod n) :
    turningAngle 0 (fun j ↦ s * κ j) (fun j ↦ ℓ j / s) i =
      turningAngle 0 κ ℓ i := by
  simp only [turningAngle, tK_zero]
  congr 1 <;> field_simp

/-- Every heading is unchanged by the same positive similarity scaling. -/
theorem heading_scale_curvature_length
    {s : ℝ} (hs : s ≠ 0) (κ ℓ : ZMod n → ℝ) (j : ℕ) :
    heading (fun i ↦ s * κ i) (fun i ↦ ℓ i / s) j =
      heading κ ℓ j := by
  unfold heading
  apply Finset.sum_congr rfl
  intro i _hi
  exact turningAngle_scale_curvature_length hs κ ℓ i

/-- The developed vertices are scaled by the reciprocal curvature factor. -/
theorem vertexR2_scale_curvature_length
    {s : ℝ} (hs : s ≠ 0) (κ ℓ : ZMod n → ℝ) (k : ℕ) :
    vertexR2 (fun i ↦ s * κ i) (fun i ↦ ℓ i / s) k =
      ((1 / s : ℝ) : ℂ) * vertexR2 κ ℓ k := by
  unfold vertexR2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [heading_scale_curvature_length hs]
  push_cast
  field_simp

/-- Closure scales linearly under a positive similarity. -/
theorem closureGap_scale_curvature_length
    {s : ℝ} (hs : s ≠ 0) (κ ℓ : ZMod n → ℝ) :
    closureGap (fun i ↦ s * κ i) (fun i ↦ ℓ i / s) =
      ((1 / s : ℝ) : ℂ) * closureGap κ ℓ := by
  exact vertexR2_scale_curvature_length hs κ ℓ n

/-- Total turning is unchanged by a positive similarity. -/
theorem turningSum_scale_curvature_length [NeZero n]
    {s : ℝ} (hs : s ≠ 0) (κ ℓ : ZMod n → ℝ) :
    turningSum (fun i ↦ s * κ i) (fun i ↦ ℓ i / s) =
      turningSum κ ℓ := by
  unfold turningSum
  apply Finset.sum_congr rfl
  intro i _hi
  exact turningAngle_scale_curvature_length hs κ ℓ i

/-- The strict Euclidean moderate-arc domain is similarity-invariant. -/
theorem moderateArc_scale_curvature_length
    {s : ℝ} (hs : 0 < s) {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) :
    ModerateArc 0 (fun i ↦ s * κ i) (fun i ↦ ℓ i / s) := by
  rw [moderateArc_zero_iff] at h ⊢
  intro i
  have hi := h i
  refine ⟨div_pos hi.1 hs, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hs]
    convert hi.2.1 using 1
    all_goals field_simp
  · rw [abs_mul, abs_of_pos hs]
    convert hi.2.2 using 1
    all_goals field_simp

/-- A positive Euclidean curvature profile remains realizable after multiplying
all curvatures by the same positive scalar. -/
theorem realizesR2_scale_of_pos [NeZero n]
    (hn : 3 ≤ n) {s : ℝ} (hs : 0 < s) {κ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (hreal : RealizesR2 κ) :
    RealizesR2 (fun i ↦ s * κ i) := by
  obtain ⟨ℓ, hMA, hE, hT, _hsimple⟩ := hreal
  let ℓs : ZMod n → ℝ := fun i ↦ ℓ i / s
  have hMAs : ModerateArc 0 (fun i ↦ s * κ i) ℓs := by
    exact moderateArc_scale_curvature_length hs hMA
  have hEs : closureGap (fun i ↦ s * κ i) ℓs = 0 := by
    rw [closureGap_scale_curvature_length hs.ne' κ ℓ, hE, mul_zero]
  have hTs : turningSum (fun i ↦ s * κ i) ℓs = 2 * Real.pi := by
    rw [turningSum_scale_curvature_length hs.ne' κ ℓ, hT]
  have hκs : ∀ i, 0 < s * κ i := fun i ↦ mul_pos hs (hκ i)
  exact ⟨ℓs, hMAs, hEs, hTs,
    isSimplePolygon_of_turningPositive hn hMAs hκs hEs hTs⟩

end Gluck.Discrete
