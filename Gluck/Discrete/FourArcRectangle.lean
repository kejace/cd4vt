/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Winding

/-!
# A four-arc parameterization of rectangle boundaries

This file gives a canonical counterclockwise parameterization of an
axis-aligned rectangle, based at the midpoint of its right face.  The four
faces occupy exactly the arcs cut at `1/8`, `3/8`, `5/8`, and `7/8`, matching
the four-half-plane winding lemmas used by the tilted open-cap socket.
-/

@[expose] public section

namespace Gluck.Discrete

/-- Horizontal coordinate of the standard counterclockwise square boundary
loop, based at the midpoint of the right face. -/
def fourArcSquareX (t : unitInterval) : ℝ :=
  max (-1) (min 1 (|8 * (t : ℝ) - 4| - 2))

/-- Vertical coordinate of the standard counterclockwise square boundary
loop, based at the midpoint of the right face. -/
def fourArcSquareY (t : unitInterval) : ℝ :=
  max (-1) (min 1 (max (2 - |8 * (t : ℝ) - 2|) (8 * (t : ℝ) - 8)))

lemma continuous_fourArcSquareX : Continuous fourArcSquareX := by
  unfold fourArcSquareX
  fun_prop

lemma continuous_fourArcSquareY : Continuous fourArcSquareY := by
  unfold fourArcSquareY
  fun_prop

lemma fourArcSquareX_mem_Icc (t : unitInterval) :
    fourArcSquareX t ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma fourArcSquareY_mem_Icc (t : unitInterval) :
    fourArcSquareY t ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma fourArcSquareX_eq_one_of_right {t : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 8 ∨ 7 / 8 ≤ (t : ℝ)) :
    fourArcSquareX t = 1 := by
  rcases ht with ht | ht
  · unfold fourArcSquareX
    rw [abs_of_nonpos (by linarith [t.2.1])]
    rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
  · unfold fourArcSquareX
    rw [abs_of_nonneg (by linarith)]
    rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

lemma fourArcSquareY_eq_one_of_top {t : unitInterval}
    (hl : 1 / 8 ≤ (t : ℝ)) (hr : (t : ℝ) ≤ 3 / 8) :
    fourArcSquareY t = 1 := by
  have habs : |8 * (t : ℝ) - 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hinner :
      max (2 - |8 * (t : ℝ) - 2|) (8 * (t : ℝ) - 8) =
        2 - |8 * (t : ℝ) - 2| :=
    max_eq_left (by linarith)
  unfold fourArcSquareY
  rw [hinner, min_eq_left (by linarith), max_eq_right (by norm_num)]

lemma fourArcSquareY_eq_eight_mul_of_initial_right {t : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 8) :
    fourArcSquareY t = 8 * (t : ℝ) := by
  unfold fourArcSquareY
  rw [abs_of_nonpos (by linarith)]
  rw [show 2 - -(8 * (t : ℝ) - 2) = 8 * (t : ℝ) by ring]
  have hinner : max (8 * (t : ℝ)) (8 * (t : ℝ) - 8) =
      8 * (t : ℝ) := max_eq_left (by linarith)
  rw [hinner, min_eq_right (by linarith),
    max_eq_right (by linarith [t.property.1])]

lemma fourArcSquareY_eq_eight_mul_sub_eight_of_terminal_right
    {t : unitInterval} (ht : 7 / 8 ≤ (t : ℝ)) :
    fourArcSquareY t = 8 * (t : ℝ) - 8 := by
  unfold fourArcSquareY
  rw [abs_of_nonneg (by linarith)]
  rw [show 2 - (8 * (t : ℝ) - 2) = 4 - 8 * (t : ℝ) by ring]
  have hinner : max (4 - 8 * (t : ℝ)) (8 * (t : ℝ) - 8) =
      8 * (t : ℝ) - 8 := max_eq_right (by linarith)
  rw [hinner, min_eq_right (by linarith [t.property.2]),
    max_eq_right (by linarith)]

lemma fourArcSquareX_eq_neg_one_of_left {t : unitInterval}
    (hl : 3 / 8 ≤ (t : ℝ)) (hr : (t : ℝ) ≤ 5 / 8) :
    fourArcSquareX t = -1 := by
  have habs : |8 * (t : ℝ) - 4| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  unfold fourArcSquareX
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

lemma fourArcSquareY_eq_neg_one_of_bottom {t : unitInterval}
    (hl : 5 / 8 ≤ (t : ℝ)) (hr : (t : ℝ) ≤ 7 / 8) :
    fourArcSquareY t = -1 := by
  unfold fourArcSquareY
  rw [abs_of_nonneg (by linarith)]
  have hinner :
      max (2 - (8 * (t : ℝ) - 2)) (8 * (t : ℝ) - 8) ≤ -1 :=
    max_le (by linarith) (by linarith)
  rw [min_eq_right (hinner.trans (by norm_num)), max_eq_left hinner]

/-- The square-boundary ordinate stays above the bottom edge on the open
right arc. -/
lemma neg_one_lt_fourArcSquareY_of_right {t : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 8 ∨ 7 / 8 < (t : ℝ)) :
    -1 < fourArcSquareY t := by
  rcases ht with ht | ht
  · unfold fourArcSquareY
    rw [abs_of_nonpos (by linarith)]
    rw [show 2 - -(8 * (t : ℝ) - 2) = 8 * (t : ℝ) by ring]
    have hinner : max (8 * (t : ℝ)) (8 * (t : ℝ) - 8) = 8 * (t : ℝ) :=
      max_eq_left (by linarith)
    rw [hinner, min_eq_right (by linarith), max_eq_right (by linarith [t.2.1])]
    norm_num at ht ⊢
    linarith [t.2.1]
  · unfold fourArcSquareY
    rw [abs_of_nonneg (by linarith)]
    rw [show 2 - (8 * (t : ℝ) - 2) = 4 - 8 * (t : ℝ) by ring]
    have hinner : max (4 - 8 * (t : ℝ)) (8 * (t : ℝ) - 8) =
        8 * (t : ℝ) - 8 := max_eq_right (by linarith)
    rw [hinner, min_eq_right (by linarith [t.2.2]), max_eq_right (by linarith)]
    norm_num at ht ⊢
    linarith

/-- The square-boundary abscissa stays right of the left edge on the open
top arc. -/
lemma neg_one_lt_fourArcSquareX_of_top {t : unitInterval}
    (ht0 : 1 / 8 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 3 / 8) :
    -1 < fourArcSquareX t := by
  unfold fourArcSquareX
  rw [abs_of_nonpos (by linarith)]
  rw [show -(8 * (t : ℝ) - 4) - 2 = 2 - 8 * (t : ℝ) by ring,
    min_eq_right (by linarith), max_eq_right (by linarith)]
  norm_num at ht1 ⊢
  linarith

/-- The square-boundary ordinate stays below the top edge on the open
left arc. -/
lemma fourArcSquareY_lt_one_of_left {t : unitInterval}
    (ht0 : 3 / 8 < (t : ℝ)) (ht1 : (t : ℝ) ≤ 5 / 8) :
    fourArcSquareY t < 1 := by
  unfold fourArcSquareY
  rw [abs_of_nonneg (by linarith)]
  rw [show 2 - (8 * (t : ℝ) - 2) = 4 - 8 * (t : ℝ) by ring]
  have hinner : max (4 - 8 * (t : ℝ)) (8 * (t : ℝ) - 8) =
      4 - 8 * (t : ℝ) := max_eq_left (by linarith)
  rw [hinner, min_eq_right (by linarith), max_eq_right (by linarith)]
  norm_num at ht0 ⊢
  linarith

/-- The square-boundary abscissa stays left of the right edge on the open
bottom arc. -/
lemma fourArcSquareX_lt_one_of_bottom {t : unitInterval}
    (ht0 : 5 / 8 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 7 / 8) :
    fourArcSquareX t < 1 := by
  unfold fourArcSquareX
  rw [abs_of_nonneg (by linarith)]
  rw [show 8 * (t : ℝ) - 4 - 2 = 8 * (t : ℝ) - 6 by ring,
    min_eq_right (by linarith), max_eq_right (by linarith)]
  norm_num at ht1 ⊢
  linarith

@[simp] lemma fourArcSquareX_zero : fourArcSquareX 0 = 1 := by
  norm_num [fourArcSquareX]

@[simp] lemma fourArcSquareX_one : fourArcSquareX 1 = 1 := by
  norm_num [fourArcSquareX]

@[simp] lemma fourArcSquareY_zero : fourArcSquareY 0 = 0 := by
  norm_num [fourArcSquareY]

@[simp] lemma fourArcSquareY_one : fourArcSquareY 1 = 0 := by
  norm_num [fourArcSquareY]

/-- Canonical counterclockwise boundary loop of an axis-aligned rectangle,
based at the midpoint of its right face. -/
noncomputable def fourArcRectangleBoundary
    (u₁ u₂ v₁ v₂ : ℝ) : C(unitInterval, ℝ × ℝ) :=
  ⟨fun t ↦
      ((u₁ + u₂) / 2 + (u₂ - u₁) / 2 * fourArcSquareX t,
        (v₁ + v₂) / 2 + (v₂ - v₁) / 2 * fourArcSquareY t),
    (continuous_const.add
      (continuous_const.mul continuous_fourArcSquareX)).prodMk
      (continuous_const.add
        (continuous_const.mul continuous_fourArcSquareY))⟩

@[simp] lemma fourArcRectangleBoundary_zero_eq_one
    (u₁ u₂ v₁ v₂ : ℝ) :
    fourArcRectangleBoundary u₁ u₂ v₁ v₂ 0 =
      fourArcRectangleBoundary u₁ u₂ v₁ v₂ 1 := by
  simp [fourArcRectangleBoundary]

lemma fourArcRectangleBoundary_fst_eq_right
    (u₁ u₂ v₁ v₂ : ℝ) {t : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 8 ∨ 7 / 8 ≤ (t : ℝ)) :
    (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t).1 = u₂ := by
  simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk]
  rw [fourArcSquareX_eq_one_of_right ht]
  ring

lemma fourArcRectangleBoundary_snd_eq_top
    (u₁ u₂ v₁ v₂ : ℝ) {t : unitInterval}
    (hl : 1 / 8 ≤ (t : ℝ)) (hr : (t : ℝ) ≤ 3 / 8) :
    (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t).2 = v₂ := by
  simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk]
  rw [fourArcSquareY_eq_one_of_top hl hr]
  ring

lemma fourArcRectangleBoundary_fst_eq_left
    (u₁ u₂ v₁ v₂ : ℝ) {t : unitInterval}
    (hl : 3 / 8 ≤ (t : ℝ)) (hr : (t : ℝ) ≤ 5 / 8) :
    (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t).1 = u₁ := by
  simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk]
  rw [fourArcSquareX_eq_neg_one_of_left hl hr]
  ring

lemma fourArcRectangleBoundary_snd_eq_bottom
    (u₁ u₂ v₁ v₂ : ℝ) {t : unitInterval}
    (hl : 5 / 8 ≤ (t : ℝ)) (hr : (t : ℝ) ≤ 7 / 8) :
    (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t).2 = v₁ := by
  simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk]
  rw [fourArcSquareY_eq_neg_one_of_bottom hl hr]
  ring

/-- A nondegenerate rectangle boundary stays strictly above its bottom edge
on the open right arc. -/
lemma fourArcRectangleBoundary_snd_gt_bottom_of_right
    {u₁ u₂ v₁ v₂ : ℝ} (hv : v₁ < v₂) {t : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 8 ∨ 7 / 8 < (t : ℝ)) :
    v₁ < (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t).2 := by
  have hy := neg_one_lt_fourArcSquareY_of_right ht
  have hprod : 0 < (v₂ - v₁) * (1 + fourArcSquareY t) :=
    mul_pos (sub_pos.mpr hv) (by linarith)
  simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk]
  nlinarith

/-- A nondegenerate rectangle boundary stays strictly right of its left edge
on the open top arc. -/
lemma fourArcRectangleBoundary_fst_gt_left_of_top
    {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ < u₂) {t : unitInterval}
    (ht0 : 1 / 8 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 3 / 8) :
    u₁ < (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t).1 := by
  have hx := neg_one_lt_fourArcSquareX_of_top ht0 ht1
  have hprod : 0 < (u₂ - u₁) * (1 + fourArcSquareX t) :=
    mul_pos (sub_pos.mpr hu) (by linarith)
  simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk]
  nlinarith

/-- A nondegenerate rectangle boundary stays strictly below its top edge
on the open left arc. -/
lemma fourArcRectangleBoundary_snd_lt_top_of_left
    {u₁ u₂ v₁ v₂ : ℝ} (hv : v₁ < v₂) {t : unitInterval}
    (ht0 : 3 / 8 < (t : ℝ)) (ht1 : (t : ℝ) ≤ 5 / 8) :
    (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t).2 < v₂ := by
  have hy := fourArcSquareY_lt_one_of_left ht0 ht1
  have hprod : 0 < (v₂ - v₁) * (1 - fourArcSquareY t) :=
    mul_pos (sub_pos.mpr hv) (by linarith)
  simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk]
  nlinarith

/-- A nondegenerate rectangle boundary stays strictly left of its right edge
on the open bottom arc. -/
lemma fourArcRectangleBoundary_fst_lt_right_of_bottom
    {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ < u₂) {t : unitInterval}
    (ht0 : 5 / 8 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 7 / 8) :
    (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t).1 < u₂ := by
  have hx := fourArcSquareX_lt_one_of_bottom ht0 ht1
  have hprod : 0 < (u₂ - u₁) * (1 - fourArcSquareX t) :=
    mul_pos (sub_pos.mpr hu) (by linarith)
  simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk]
  nlinarith

/-- The canonical rectangle boundary loop stays in the closed rectangle. -/
theorem fourArcRectangleBoundary_mem
    {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂)
    (t : unitInterval) :
    fourArcRectangleBoundary u₁ u₂ v₁ v₂ t ∈
      Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂ := by
  have hx := fourArcSquareX_mem_Icc t
  have hy := fourArcSquareY_mem_Icc t
  have hdu : 0 ≤ u₂ - u₁ := sub_nonneg.mpr hu
  have hdv : 0 ≤ v₂ - v₁ := sub_nonneg.mpr hv
  have hxlo : 0 ≤ (u₂ - u₁) * (1 + fourArcSquareX t) :=
    mul_nonneg hdu (by linarith [hx.1])
  have hxhi : 0 ≤ (u₂ - u₁) * (1 - fourArcSquareX t) :=
    mul_nonneg hdu (by linarith [hx.2])
  have hylo : 0 ≤ (v₂ - v₁) * (1 + fourArcSquareY t) :=
    mul_nonneg hdv (by linarith [hy.1])
  have hyhi : 0 ≤ (v₂ - v₁) * (1 - fourArcSquareY t) :=
    mul_nonneg hdv (by linarith [hy.2])
  constructor
  · constructor <;>
      simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk] <;>
      nlinarith
  · constructor <;>
      simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk] <;>
      nlinarith

lemma fourArcUnitBoundary_eq_initial_right {t : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 8) :
    fourArcRectangleBoundary 0 1 0 1 t =
      (1, 1 / 2 + 4 * (t : ℝ)) := by
  apply Prod.ext
  · exact fourArcRectangleBoundary_fst_eq_right 0 1 0 1 (Or.inl ht)
  · simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk]
    rw [fourArcSquareY_eq_eight_mul_of_initial_right ht]
    ring

lemma fourArcUnitBoundary_eq_terminal_right {t : unitInterval}
    (ht : 7 / 8 ≤ (t : ℝ)) :
    fourArcRectangleBoundary 0 1 0 1 t =
      (1, 4 * (t : ℝ) - 7 / 2) := by
  apply Prod.ext
  · exact fourArcRectangleBoundary_fst_eq_right 0 1 0 1 (Or.inr ht)
  · simp only [fourArcRectangleBoundary, ContinuousMap.coe_mk]
    rw [fourArcSquareY_eq_eight_mul_sub_eight_of_terminal_right ht]
    ring

/-- A monotone clock which traverses its first half on the initial right arc
of `fourArcRectangleBoundary`, pauses on the top, left, and bottom arcs, and
traverses its second half on the terminal right arc. -/
noncomputable def fourArcRightLoopTimeR (t : unitInterval) : ℝ :=
  min (1 / 2 : ℝ) (4 * (t : ℝ)) +
    max 0 (4 * (t : ℝ) - 7 / 2)

lemma continuous_fourArcRightLoopTimeR :
    Continuous fourArcRightLoopTimeR := by
  unfold fourArcRightLoopTimeR
  fun_prop

lemma fourArcRightLoopTimeR_mem (t : unitInterval) :
    fourArcRightLoopTimeR t ∈ Set.Icc (0 : ℝ) 1 := by
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  have hfirst0 : 0 ≤ min (1 / 2 : ℝ) (4 * (t : ℝ)) :=
    le_min (by norm_num) (mul_nonneg (by norm_num) ht0)
  have hsecond0 : 0 ≤ max 0 (4 * (t : ℝ) - 7 / 2) :=
    le_max_left _ _
  have hfirst1 : min (1 / 2 : ℝ) (4 * (t : ℝ)) ≤ 1 / 2 :=
    min_le_left _ _
  have hsecond1 : max 0 (4 * (t : ℝ) - 7 / 2) ≤ 1 / 2 :=
    max_le (by norm_num) (by linarith)
  constructor
  · change 0 ≤ min (1 / 2 : ℝ) (4 * (t : ℝ)) +
        max 0 (4 * (t : ℝ) - 7 / 2)
    exact add_nonneg hfirst0 hsecond0
  · change min (1 / 2 : ℝ) (4 * (t : ℝ)) +
        max 0 (4 * (t : ℝ) - 7 / 2) ≤ 1
    linarith

/-- `fourArcRightLoopTimeR` as a continuous self-map of the unit interval. -/
noncomputable def fourArcRightLoopTime : C(unitInterval, unitInterval) :=
  ⟨fun t ↦ ⟨fourArcRightLoopTimeR t, fourArcRightLoopTimeR_mem t⟩,
    continuous_fourArcRightLoopTimeR.subtype_mk _⟩

@[simp] lemma fourArcRightLoopTime_zero : fourArcRightLoopTime 0 = 0 := by
  ext
  norm_num [fourArcRightLoopTime, fourArcRightLoopTimeR]

@[simp] lemma fourArcRightLoopTime_one : fourArcRightLoopTime 1 = 1 := by
  ext
  norm_num [fourArcRightLoopTime, fourArcRightLoopTimeR]

lemma fourArcRightLoopTimeR_of_initial_right {t : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 8) : fourArcRightLoopTimeR t = 4 * (t : ℝ) := by
  unfold fourArcRightLoopTimeR
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  ring

lemma fourArcRightLoopTimeR_of_paused {t : unitInterval}
    (ht0 : 1 / 8 ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 7 / 8) :
    fourArcRightLoopTimeR t = 1 / 2 := by
  unfold fourArcRightLoopTimeR
  rw [min_eq_left (by linarith), max_eq_left (by linarith)]
  ring

lemma fourArcRightLoopTimeR_of_terminal_right {t : unitInterval}
    (ht : 7 / 8 ≤ (t : ℝ)) : fourArcRightLoopTimeR t = 4 * (t : ℝ) - 3 := by
  unfold fourArcRightLoopTimeR
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  ring

/-- The forward half-rotation clock, clamped only to make it a globally
defined self-map of the unit interval. -/
noncomputable def halfRotateForwardTime : C(unitInterval, unitInterval) :=
  ⟨fun t ↦ Set.projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) + 1 / 2),
    continuous_projIcc.comp (continuous_subtype_val.add continuous_const)⟩

/-- The backward half-rotation clock, likewise globally clamped. -/
noncomputable def halfRotateBackwardTime : C(unitInterval, unitInterval) :=
  ⟨fun t ↦ Set.projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) - 1 / 2),
    continuous_projIcc.comp (continuous_subtype_val.sub continuous_const)⟩

@[simp] lemma halfRotateForwardTime_zero :
    halfRotateForwardTime 0 = (⟨1 / 2, by norm_num⟩ : unitInterval) := by
  change Set.projIcc (0 : ℝ) 1 zero_le_one (0 + 1 / 2) = _
  rw [Set.projIcc_of_mem zero_le_one
    (by norm_num : (0 + 1 / 2 : ℝ) ∈ Set.Icc 0 1)]
  norm_num

@[simp] lemma halfRotateForwardTime_half :
    halfRotateForwardTime (⟨1 / 2, by norm_num⟩ : unitInterval) = 1 := by
  change Set.projIcc (0 : ℝ) 1 zero_le_one (1 / 2 + 1 / 2) = _
  rw [Set.projIcc_of_mem zero_le_one
    (by norm_num : (1 / 2 + 1 / 2 : ℝ) ∈ Set.Icc 0 1)]
  norm_num

@[simp] lemma halfRotateBackwardTime_half :
    halfRotateBackwardTime (⟨1 / 2, by norm_num⟩ : unitInterval) = 0 := by
  change Set.projIcc (0 : ℝ) 1 zero_le_one (1 / 2 - 1 / 2) = _
  rw [Set.projIcc_of_mem zero_le_one
    (by norm_num : (1 / 2 - 1 / 2 : ℝ) ∈ Set.Icc 0 1)]
  norm_num

@[simp] lemma halfRotateBackwardTime_one :
    halfRotateBackwardTime 1 = (⟨1 / 2, by norm_num⟩ : unitInterval) := by
  change Set.projIcc (0 : ℝ) 1 zero_le_one (1 - 1 / 2) = _
  rw [Set.projIcc_of_mem zero_le_one
    (by norm_num : (1 - 1 / 2 : ℝ) ∈ Set.Icc 0 1)]
  norm_num

/-- Rotate the basepoint of a loop by half a turn.  The two formulas meet
because the supplied continuous map has equal endpoint values. -/
noncomputable def halfRotateLoop
    {α : Type*} [TopologicalSpace α]
    (gamma : C(unitInterval, α)) (hloop : gamma 0 = gamma 1) :
    C(unitInterval, α) :=
  ⟨fun t ↦ if (1 / 2 : ℝ) ≤ (t : ℝ) then
      gamma (halfRotateBackwardTime t)
    else gamma (halfRotateForwardTime t), by
      apply continuous_if_le continuous_const continuous_subtype_val
        (gamma.continuous.comp halfRotateBackwardTime.continuous).continuousOn
        (gamma.continuous.comp halfRotateForwardTime.continuous).continuousOn
      intro t ht
      have ht' : t = (⟨1 / 2, by norm_num⟩ : unitInterval) :=
        Subtype.ext ht.symm
      subst t
      change gamma (halfRotateBackwardTime ⟨1 / 2, by norm_num⟩) =
        gamma (halfRotateForwardTime ⟨1 / 2, by norm_num⟩)
      rw [halfRotateForwardTime_half, halfRotateBackwardTime_half]
      exact hloop⟩

@[simp] lemma halfRotateLoop_zero
    {α : Type*} [TopologicalSpace α]
    (gamma : C(unitInterval, α)) (hloop : gamma 0 = gamma 1) :
    halfRotateLoop gamma hloop 0 = gamma ⟨1 / 2, by norm_num⟩ := by
  rw [halfRotateLoop]
  simp only [ContinuousMap.coe_mk]
  rw [if_neg (by norm_num), halfRotateForwardTime_zero]

@[simp] lemma halfRotateLoop_one
    {α : Type*} [TopologicalSpace α]
    (gamma : C(unitInterval, α)) (hloop : gamma 0 = gamma 1) :
    halfRotateLoop gamma hloop 1 = gamma ⟨1 / 2, by norm_num⟩ := by
  rw [halfRotateLoop]
  simp only [ContinuousMap.coe_mk]
  rw [if_pos (by norm_num), halfRotateBackwardTime_one]

lemma halfRotateLoop_proj_initial_right
    {α : Type*} [TopologicalSpace α]
    (gamma : C(unitInterval, α)) (hloop : gamma 0 = gamma 1)
    {t : unitInterval} (ht : (t : ℝ) ≤ 1 / 8) :
    halfRotateLoop gamma hloop
        (Set.projIcc (0 : ℝ) 1 zero_le_one
          (1 / 2 + 4 * (t : ℝ))) =
      gamma (fourArcRightLoopTime t) := by
  have hv : 1 / 2 + 4 * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [t.property.1]
  let v : unitInterval :=
    ⟨1 / 2 + 4 * (t : ℝ), hv⟩
  have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one
      (1 / 2 + 4 * (t : ℝ)) = v :=
    Set.projIcc_of_mem zero_le_one hv
  rw [hproj, halfRotateLoop]
  simp only [ContinuousMap.coe_mk]
  rw [if_pos (by dsimp only [v]; linarith [t.property.1])]
  have hw : (v : ℝ) - 1 / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [v]
    constructor <;> linarith [t.property.1]
  have hback : halfRotateBackwardTime v =
      (⟨(v : ℝ) - 1 / 2, hw⟩ : unitInterval) := by
    change Set.projIcc (0 : ℝ) 1 zero_le_one ((v : ℝ) - 1 / 2) = _
    exact Set.projIcc_of_mem zero_le_one hw
  rw [hback]
  apply congrArg gamma
  ext
  change (v : ℝ) - 1 / 2 = fourArcRightLoopTimeR t
  rw [fourArcRightLoopTimeR_of_initial_right ht]
  dsimp only [v]
  ring

lemma halfRotateLoop_proj_terminal_right
    {α : Type*} [TopologicalSpace α]
    (gamma : C(unitInterval, α)) (hloop : gamma 0 = gamma 1)
    {t : unitInterval} (ht : 7 / 8 ≤ (t : ℝ)) :
    halfRotateLoop gamma hloop
        (Set.projIcc (0 : ℝ) 1 zero_le_one
          (4 * (t : ℝ) - 7 / 2)) =
      gamma (fourArcRightLoopTime t) := by
  by_cases ht1 : t = 1
  · subst t
    rw [show Set.projIcc (0 : ℝ) 1 zero_le_one
        (4 * ((1 : unitInterval) : ℝ) - 7 / 2) =
          (⟨1 / 2, by norm_num⟩ : unitInterval) by
      change Set.projIcc (0 : ℝ) 1 zero_le_one (4 * 1 - 7 / 2) = _
      rw [Set.projIcc_of_mem zero_le_one
        (by norm_num : (4 * 1 - 7 / 2 : ℝ) ∈ Set.Icc 0 1)]
      norm_num,
      fourArcRightLoopTime_one]
    rw [halfRotateLoop]
    simp only [ContinuousMap.coe_mk]
    rw [if_pos (by norm_num), halfRotateBackwardTime_half]
    exact hloop
  · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
      intro h
      apply ht1
      exact Subtype.ext h)
    have hv : 4 * (t : ℝ) - 7 / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith
    let v : unitInterval := ⟨4 * (t : ℝ) - 7 / 2, hv⟩
    have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one
        (4 * (t : ℝ) - 7 / 2) = v :=
      Set.projIcc_of_mem zero_le_one hv
    rw [hproj, halfRotateLoop]
    simp only [ContinuousMap.coe_mk]
    rw [if_neg (by dsimp only [v]; linarith)]
    have hw : (v : ℝ) + 1 / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp only [v]
      constructor <;> linarith
    have hforward : halfRotateForwardTime v =
        (⟨(v : ℝ) + 1 / 2, hw⟩ : unitInterval) := by
      change Set.projIcc (0 : ℝ) 1 zero_le_one ((v : ℝ) + 1 / 2) = _
      exact Set.projIcc_of_mem zero_le_one hw
    rw [hforward]
    apply congrArg gamma
    ext
    change (v : ℝ) + 1 / 2 = fourArcRightLoopTimeR t
    rw [fourArcRightLoopTimeR_of_terminal_right ht]
    dsimp only [v]
    ring

/-- Cone a loop from its half-rotated basepoint across the unit square.  On
the canonical square boundary, three faces collapse to the basepoint and the
right face carries the loop. -/
noncomputable def fourArcLoopConeField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gamma : C(unitInterval, E)) (hloop : gamma 0 = gamma 1)
    (z : ℝ × ℝ) : E :=
  let rotated := halfRotateLoop gamma hloop
  (1 - z.1) • rotated 0 + z.1 •
    rotated (Set.projIcc (0 : ℝ) 1 zero_le_one z.2)

lemma continuous_fourArcLoopConeField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gamma : C(unitInterval, E)) (hloop : gamma 0 = gamma 1) :
    Continuous (fourArcLoopConeField gamma hloop) := by
  let rotated := halfRotateLoop gamma hloop
  let v : C(ℝ × ℝ, unitInterval) :=
    ⟨fun z ↦ Set.projIcc (0 : ℝ) 1 zero_le_one z.2,
      continuous_projIcc.comp continuous_snd⟩
  have hs : Continuous fun z : ℝ × ℝ ↦ z.1 := continuous_fst
  have hrotated : Continuous fun z : ℝ × ℝ ↦ rotated (v z) :=
    rotated.continuous.comp v.continuous
  exact ((continuous_const.sub hs).smul continuous_const).add
    (hs.smul hrotated) |>.congr fun z ↦ by
      rfl

/-- The canonical boundary of the loop cone is precisely the original loop
with the three non-right arcs represented by the stuttering clock. -/
theorem fourArcLoopConeField_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gamma : C(unitInterval, E)) (hloop : gamma 0 = gamma 1)
    (t : unitInterval) :
    fourArcLoopConeField gamma hloop
        (fourArcRectangleBoundary 0 1 0 1 t) =
      gamma (fourArcRightLoopTime t) := by
  by_cases h₁ : (t : ℝ) ≤ 1 / 8
  · rw [fourArcUnitBoundary_eq_initial_right h₁]
    simpa only [fourArcLoopConeField, Prod.fst, Prod.snd,
      sub_self, zero_smul, one_smul, zero_add] using
        halfRotateLoop_proj_initial_right gamma hloop h₁
  · have h₁' : 1 / 8 ≤ (t : ℝ) := (lt_of_not_ge h₁).le
    by_cases h₃ : (t : ℝ) ≤ 3 / 8
    · have hy := fourArcRectangleBoundary_snd_eq_top 0 1 0 1 h₁' h₃
      have htime := fourArcRightLoopTimeR_of_paused h₁'
        (h₃.trans (by norm_num : (3 / 8 : ℝ) ≤ 7 / 8))
      change (1 - (fourArcRectangleBoundary 0 1 0 1 t).1) •
          halfRotateLoop gamma hloop 0 +
          (fourArcRectangleBoundary 0 1 0 1 t).1 •
            halfRotateLoop gamma hloop
              (Set.projIcc (0 : ℝ) 1 zero_le_one
                (fourArcRectangleBoundary 0 1 0 1 t).2) =
        gamma (fourArcRightLoopTime t)
      rw [hy]
      have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one 1 =
          (1 : unitInterval) := by
        exact Set.projIcc_of_mem zero_le_one (by norm_num)
      rw [hproj, halfRotateLoop_zero, halfRotateLoop_one]
      rw [show fourArcRightLoopTime t =
          (⟨1 / 2, by norm_num⟩ : unitInterval) by
        ext
        exact htime]
      rw [← add_smul]
      simp
    · have h₃' : 3 / 8 ≤ (t : ℝ) := (lt_of_not_ge h₃).le
      by_cases h₅ : (t : ℝ) ≤ 5 / 8
      · have hx := fourArcRectangleBoundary_fst_eq_left 0 1 0 1 h₃' h₅
        have htime := fourArcRightLoopTimeR_of_paused
          (h₁') (h₅.trans (by norm_num : (5 / 8 : ℝ) ≤ 7 / 8))
        change (1 - (fourArcRectangleBoundary 0 1 0 1 t).1) •
            halfRotateLoop gamma hloop 0 +
            (fourArcRectangleBoundary 0 1 0 1 t).1 •
              halfRotateLoop gamma hloop
                (Set.projIcc (0 : ℝ) 1 zero_le_one
                  (fourArcRectangleBoundary 0 1 0 1 t).2) =
          gamma (fourArcRightLoopTime t)
        rw [hx]
        rw [show fourArcRightLoopTime t =
            (⟨1 / 2, by norm_num⟩ : unitInterval) by
          ext
          exact htime]
        simp
      · have h₅' : 5 / 8 ≤ (t : ℝ) := (lt_of_not_ge h₅).le
        by_cases h₇ : (t : ℝ) ≤ 7 / 8
        · have hy := fourArcRectangleBoundary_snd_eq_bottom 0 1 0 1 h₅' h₇
          have htime := fourArcRightLoopTimeR_of_paused h₁' h₇
          change (1 - (fourArcRectangleBoundary 0 1 0 1 t).1) •
              halfRotateLoop gamma hloop 0 +
              (fourArcRectangleBoundary 0 1 0 1 t).1 •
                halfRotateLoop gamma hloop
                  (Set.projIcc (0 : ℝ) 1 zero_le_one
                    (fourArcRectangleBoundary 0 1 0 1 t).2) =
            gamma (fourArcRightLoopTime t)
          rw [hy]
          have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one 0 =
              (0 : unitInterval) := by
            exact Set.projIcc_of_mem zero_le_one (by norm_num)
          rw [hproj]
          rw [show fourArcRightLoopTime t =
              (⟨1 / 2, by norm_num⟩ : unitInterval) by
            ext
            exact htime]
          rw [halfRotateLoop_zero, ← add_smul]
          simp
        · have h₇' : 7 / 8 ≤ (t : ℝ) := (lt_of_not_ge h₇).le
          rw [fourArcUnitBoundary_eq_terminal_right h₇']
          simpa only [fourArcLoopConeField, Prod.fst, Prod.snd,
            sub_self, zero_smul, one_smul, zero_add] using
              halfRotateLoop_proj_terminal_right gamma hloop h₇'

private lemma midpoint_combo_mem_Icc_aux {a b x s : ℝ}
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b) (hs : s ∈ Set.Icc 0 1) :
    (1 - s) * ((a + b) / 2) + s * x ∈ Set.Icc a b := by
  have hm : (a + b) / 2 ∈ Set.Icc a b := by constructor <;> linarith
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hm.1),
      mul_nonneg hs.1 (sub_nonneg.mpr hx.1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hm.2),
      mul_nonneg hs.1 (sub_nonneg.mpr hx.2)]

private lemma midpoint_combo_mem_Ioo_aux {a b x s : ℝ}
    (hab : a < b) (hx : x ∈ Set.Icc a b) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 - s) * ((a + b) / 2) + s * x ∈ Set.Ioo a b := by
  have hm : (a + b) / 2 ∈ Set.Ioo a b := by constructor <;> linarith
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hm.1),
      mul_nonneg hs0 (sub_nonneg.mpr hx.1)]
  · nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hm.2),
      mul_nonneg hs0 (sub_nonneg.mpr hx.2)]

noncomputable def fourArcRectangleRadialAux
    (u₁ u₂ v₁ v₂ : ℝ) : C(unitInterval × unitInterval, ℝ × ℝ) :=
  ⟨fun st ↦
      ((1 - (st.1 : ℝ)) * ((u₁ + u₂) / 2) +
          (st.1 : ℝ) * (fourArcRectangleBoundary u₁ u₂ v₁ v₂ st.2).1,
        (1 - (st.1 : ℝ)) * ((v₁ + v₂) / 2) +
          (st.1 : ℝ) * (fourArcRectangleBoundary u₁ u₂ v₁ v₂ st.2).2),
    by
      have hs : Continuous fun st : unitInterval × unitInterval ↦ (st.1 : ℝ) :=
        continuous_subtype_val.comp continuous_fst
      have hb : Continuous fun st : unitInterval × unitInterval ↦
          fourArcRectangleBoundary u₁ u₂ v₁ v₂ st.2 :=
        (fourArcRectangleBoundary u₁ u₂ v₁ v₂).continuous.comp continuous_snd
      exact (((continuous_const.sub hs).mul continuous_const).add
        (hs.mul (continuous_fst.comp hb))).prodMk <|
          ((continuous_const.sub hs).mul continuous_const).add
            (hs.mul (continuous_snd.comp hb))⟩

lemma four_arc_rectangle_radial_mem_aux
    {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂)
    (st : unitInterval × unitInterval) :
    fourArcRectangleRadialAux u₁ u₂ v₁ v₂ st ∈
      Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂ := by
  have hb := fourArcRectangleBoundary_mem hu hv st.2
  exact ⟨midpoint_combo_mem_Icc_aux hu hb.1 st.1.2,
    midpoint_combo_mem_Icc_aux hv hb.2 st.1.2⟩

private lemma four_arc_rectangle_radial_mem_interior_aux
    {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ < u₂) (hv : v₁ < v₂)
    {s t : unitInterval} (hs : (s : ℝ) < 1) :
    fourArcRectangleRadialAux u₁ u₂ v₁ v₂ (s, t) ∈
      Set.Ioo u₁ u₂ ×ˢ Set.Ioo v₁ v₂ := by
  have hb := fourArcRectangleBoundary_mem hu.le hv.le t
  exact ⟨midpoint_combo_mem_Ioo_aux hu hb.1 s.2.1 hs,
    midpoint_combo_mem_Ioo_aux hv hb.2 s.2.1 hs⟩

private lemma four_arc_rectangle_radial_zero_aux
    (u₁ u₂ v₁ v₂ : ℝ) (t : unitInterval) :
    fourArcRectangleRadialAux u₁ u₂ v₁ v₂ (0, t) =
      ((u₁ + u₂) / 2, (v₁ + v₂) / 2) := by
  simp [fourArcRectangleRadialAux]

private lemma four_arc_rectangle_radial_one_aux
    (u₁ u₂ v₁ v₂ : ℝ) (t : unitInterval) :
    fourArcRectangleRadialAux u₁ u₂ v₁ v₂ (1, t) =
      fourArcRectangleBoundary u₁ u₂ v₁ v₂ t := by
  simp [fourArcRectangleRadialAux]

private lemma four_arc_rectangle_radial_loop_aux
    (u₁ u₂ v₁ v₂ : ℝ) (s : unitInterval) :
    fourArcRectangleRadialAux u₁ u₂ v₁ v₂ (s, 0) =
      fourArcRectangleRadialAux u₁ u₂ v₁ v₂ (s, 1) := by
  simp [fourArcRectangleRadialAux]

private lemma zero_time_pos_aux
    {ε₀ : ℝ} {g : ℝ × unitInterval → ℂ}
    (hzero : ∀ t, g (0, t) ≠ 0) {p : ℝ × unitInterval}
    (hp : p.1 ∈ Set.Icc 0 ε₀) (hpg : g p = 0) :
    0 < p.1 := by
  rcases eq_or_lt_of_le hp.1 with h | h
  · have hpzero : p = (0, p.2) := Prod.ext h.symm rfl
    rw [hpzero] at hpg
    exact (hzero p.2 hpg).elim
  · exact h

private lemma exists_pos_boundary_collar_aux
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) {g : ℝ × unitInterval → ℂ}
    (hg : ContinuousOn g (Set.Icc 0 ε₀ ×ˢ Set.univ))
    (hzero : ∀ t, g (0, t) ≠ 0) :
    ∃ η, 0 < η ∧ η ≤ ε₀ ∧ ∀ ε ∈ Set.Ico 0 η, ∀ t, g (ε, t) ≠ 0 := by
  let K : Set (ℝ × unitInterval) := Set.Icc 0 ε₀ ×ˢ Set.univ
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_univ
  let S : Set (ℝ × unitInterval) := K ∩ g ⁻¹' {0}
  have hSclosed : IsClosed S :=
    hg.preimage_isClosed_of_isClosed hKcomp.isClosed isClosed_singleton
  have hScomp : IsCompact S :=
    hKcomp.of_isClosed_subset hSclosed Set.inter_subset_left
  rcases S.eq_empty_or_nonempty with hemp | hne
  · refine ⟨ε₀, hε₀, le_rfl, fun ε hε t hvanish ↦ ?_⟩
    have hmem : (ε, t) ∈ S := by
      exact ⟨⟨⟨hε.1, hε.2.le⟩, Set.mem_univ _⟩, by simpa using hvanish⟩
    rw [hemp] at hmem
    exact hmem
  · obtain ⟨p₀, hp₀S, hmin⟩ :=
      hScomp.exists_isMinOn hne continuous_fst.continuousOn
    have hp₀K : p₀ ∈ K := hp₀S.1
    have hp₀g : g p₀ = 0 := by simpa using hp₀S.2
    have hη := zero_time_pos_aux hzero hp₀K.1 hp₀g
    refine ⟨p₀.1, hη, hp₀K.1.2, fun ε hε t hvanish ↦ ?_⟩
    have hmem : (ε, t) ∈ S := by
      exact ⟨⟨⟨hε.1, hε.2.le.trans hp₀K.1.2⟩, Set.mem_univ _⟩,
        by simpa using hvanish⟩
    exact absurd (hmin hmem) (not_le.mpr hε.2)

section ZeroLocalization

open Set

/-- Zeros of a continuous compact family remain in every open strict
sublevel that contains all zeros of its initial slice. -/
theorem exists_pos_forall_lt_zero_localized_near_initial
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T1Space Y] [Zero Y]
    {K : Set X} (hK : IsCompact K)
    {ε₀ a : ℝ} (hε₀ : 0 < ε₀)
    {measure : X → ℝ} {Phi : ℝ × X → Y}
    (hmeasure : ContinuousOn measure K)
    (hPhi : ContinuousOn Phi (Icc 0 ε₀ ×ˢ K))
    (hinitial : ∀ x ∈ K, Phi (0, x) = 0 → measure x < a) :
    ∃ eta, 0 < eta ∧ eta ≤ ε₀ ∧
      ∀ ε ∈ Ico 0 eta, ∀ x ∈ K, Phi (ε, x) = 0 → measure x < a := by
  let Q : Set (ℝ × X) := Icc 0 ε₀ ×ˢ K
  have hQcomp : IsCompact Q := isCompact_Icc.prod hK
  let Z : Set (ℝ × X) := Q ∩ Phi ⁻¹' {0}
  have hZclosed : IsClosed Z :=
    hPhi.preimage_isClosed_of_isClosed hQcomp.isClosed isClosed_singleton
  have hZcomp : IsCompact Z :=
    hQcomp.of_isClosed_subset hZclosed inter_subset_left
  have hmeasureQ : ContinuousOn (fun p : ℝ × X ↦ measure p.2) Q :=
    hmeasure.comp continuous_snd.continuousOn (fun p hp ↦ hp.2)
  have hmeasureZ : ContinuousOn (fun p : ℝ × X ↦ measure p.2) Z :=
    hmeasureQ.mono inter_subset_left
  let S : Set (ℝ × X) := Z ∩ (fun p ↦ measure p.2) ⁻¹' Ici a
  have hSclosed : IsClosed S :=
    hmeasureZ.preimage_isClosed_of_isClosed hZclosed isClosed_Ici
  have hScomp : IsCompact S :=
    hZcomp.of_isClosed_subset hSclosed inter_subset_left
  rcases S.eq_empty_or_nonempty with hemp | hne
  · refine ⟨ε₀, hε₀, le_rfl, fun ε hε x hx hzero ↦ ?_⟩
    by_contra hnot
    rw [not_lt] at hnot
    have hp : (ε, x) ∈ S := by
      refine ⟨⟨⟨⟨hε.1, hε.2.le⟩, hx⟩, ?_⟩, hnot⟩
      simpa using hzero
    rw [hemp] at hp
    exact hp
  · obtain ⟨p₀, hp₀S, hmin⟩ :=
      hScomp.exists_isMinOn hne continuous_fst.continuousOn
    have hp₀Q : p₀ ∈ Q := hp₀S.1.1
    have hp₀Phi : Phi p₀ = 0 := by simpa using hp₀S.1.2
    have hp₀Measure : a ≤ measure p₀.2 := hp₀S.2
    have hp₀Pos : 0 < p₀.1 := by
      rcases eq_or_lt_of_le hp₀Q.1.1 with hzero | hpos
      · have hgood : measure p₀.2 < a := by
          apply hinitial p₀.2 hp₀Q.2
          simpa [hzero] using hp₀Phi
        exact (not_lt_of_ge hp₀Measure hgood).elim
      · exact hpos
    refine ⟨p₀.1, hp₀Pos, hp₀Q.1.2, fun ε hε x hx hzero ↦ ?_⟩
    by_contra hnot
    rw [not_lt] at hnot
    have hp : (ε, x) ∈ S := by
      refine ⟨⟨⟨⟨hε.1, hε.2.le.trans hp₀Q.1.2⟩, hx⟩, ?_⟩, hnot⟩
      simpa using hzero
    exact (not_le.mpr hε.2) (hmin hp)

/-- If a continuous safety margin is positive at every zero of a continuous
map on a compact set, then it has one positive lower bound on a sufficiently
small norm sublevel of that map. -/
theorem exists_pos_uniform_lower_bound_near_compact_zero_set
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    {K : Set X} (hK : IsCompact K) {F : X → E} {margin : X → ℝ}
    (hF : ContinuousOn F K) (hmargin : ContinuousOn margin K)
    (hzero : ∀ x ∈ K, F x = 0 → 0 < margin x) :
    ∃ mu, 0 < mu ∧ ∃ delta, 0 < delta ∧
      ∀ x ∈ K, ‖F x‖ ≤ mu → delta ≤ margin x := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, zero_lt_one, 1, zero_lt_one, fun x hx ↦ ?_⟩
    rw [hemp] at hx
    exact hx.elim
  · let measure : X → ℝ := fun x ↦ ‖F x‖ + max (margin x) 0
    have hmeasure : ContinuousOn measure K := by
      exact (continuous_norm.comp_continuousOn hF).add
        (continuous_max.comp_continuousOn
          (hmargin.prodMk continuousOn_const))
    obtain ⟨x₀, hx₀, hmin⟩ :=
      hK.exists_isMinOn hne hmeasure
    have hmeasurePos : 0 < measure x₀ := by
      by_cases hFzero : F x₀ = 0
      · have hsafe := hzero x₀ hx₀ hFzero
        simp [measure, hFzero, max_eq_left hsafe.le, hsafe]
      · exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hFzero)
          (le_max_right _ _)
    refine ⟨measure x₀ / 2, half_pos hmeasurePos,
      measure x₀ / 2, half_pos hmeasurePos, fun x hx hnorm ↦ ?_⟩
    have hmax : measure x₀ / 2 ≤ max (margin x) 0 := by
      have hleast := hmin hx
      change measure x₀ ≤ measure x at hleast
      dsimp only [measure] at hleast
      have hnormNonneg : 0 ≤ ‖F x‖ := norm_nonneg _
      linarith
    have hmaxPos : 0 < max (margin x) 0 :=
      (half_pos hmeasurePos).trans_le hmax
    have hmarginPos : 0 < margin x :=
      (lt_max_iff.mp hmaxPos).resolve_right (lt_irrefl 0)
    rwa [max_eq_left hmarginPos.le] at hmax

/-- A positive lower bound on one compact slice of a continuous family
persists uniformly for all nearby parameter values in a compact domain. -/
theorem exists_pos_uniform_lower_bound_near_compact_slice
    {P X : Type*} [MetricSpace P] [TopologicalSpace X] [T2Space X]
    {C : Set P} (hC : IsCompact C) {K : Set X} (hK : IsCompact K)
    {p₀ : P} {margin : P × X → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hmargin : ContinuousOn margin (C ×ˢ K))
    (hbase : ∀ x ∈ K, delta ≤ margin (p₀, x)) :
    ∃ eta, 0 < eta ∧ ∀ p ∈ C, dist p p₀ < eta →
      ∀ x ∈ K, delta / 2 ≤ margin (p, x) := by
  let Q : Set (P × X) := C ×ˢ K
  have hQcomp : IsCompact Q := hC.prod hK
  let B : Set (P × X) := Q ∩ margin ⁻¹' Iic (delta / 2)
  have hBclosed : IsClosed B :=
    hmargin.preimage_isClosed_of_isClosed hQcomp.isClosed isClosed_Iic
  have hBcomp : IsCompact B :=
    hQcomp.of_isClosed_subset hBclosed inter_subset_left
  rcases B.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, zero_lt_one, fun p hp _ x hx ↦ ?_⟩
    by_contra hnot
    have hbad : (p, x) ∈ B := by
      exact ⟨⟨hp, hx⟩, by simpa using not_le.mp hnot |>.le⟩
    rw [hemp] at hbad
    exact hbad.elim
  · let separation : P × X → ℝ := fun y ↦ dist y.1 p₀
    have hseparation : Continuous separation :=
      continuous_dist.comp (continuous_fst.prodMk continuous_const)
    obtain ⟨y₀, hy₀, hmin⟩ :=
      hBcomp.exists_isMinOn hne hseparation.continuousOn
    have heta : 0 < separation y₀ := by
      by_contra hnot
      have hzero : separation y₀ = 0 :=
        le_antisymm (not_lt.mp hnot) dist_nonneg
      have hyEq : y₀.1 = p₀ := dist_eq_zero.mp hzero
      have hsafe := hbase y₀.2 hy₀.1.2
      have hbad : margin y₀ ≤ delta / 2 := hy₀.2
      rw [show y₀ = (p₀, y₀.2) from Prod.ext hyEq rfl] at hbad
      linarith
    refine ⟨separation y₀, heta, fun p hp hpnear x hx ↦ ?_⟩
    by_contra hnot
    have hbad : (p, x) ∈ B := by
      exact ⟨⟨hp, hx⟩, by simpa using not_le.mp hnot |>.le⟩
    exact (not_le.mpr hpnear) (hmin hbad)

/-- A continuous margin that is positive on the zero slice over a compact
set remains uniformly positive for all sufficiently small nonnegative
parameters. -/
theorem exists_pos_uniform_positive_near_compact_slice
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    {margin : ℝ × X → ℝ}
    (hmargin : ContinuousOn margin (Icc 0 ε₀ ×ˢ K))
    (hbase : ∀ x ∈ K, 0 < margin (0, x)) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧
      ∀ ε ∈ Icc 0 ε₁, ∀ x ∈ K, 0 < margin (ε, x) := by
  have hbaseCont : ContinuousOn (fun x ↦ margin (0, x)) K :=
    hmargin.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx ↦ ⟨⟨le_rfl, hε₀.le⟩, hx⟩)
  obtain ⟨dummy, hdummy, delta, hdelta, hbaseBoundRaw⟩ :=
    exists_pos_uniform_lower_bound_near_compact_zero_set
      (E := ℝ) hK (F := fun _ : X ↦ (0 : ℝ)) continuousOn_const
      hbaseCont (fun x hx _ ↦ hbase x hx)
  have hbaseBound : ∀ x ∈ K, delta ≤ margin (0, x) := by
    intro x hx
    exact hbaseBoundRaw x hx (by simpa using hdummy.le)
  obtain ⟨eta, heta, hnear⟩ :=
    exists_pos_uniform_lower_bound_near_compact_slice
      (p₀ := (0 : ℝ)) isCompact_Icc hK hdelta hmargin hbaseBound
  refine ⟨min ε₀ (eta / 2), lt_min hε₀ (half_pos heta),
    min_le_left _ _, fun ε hε x hx ↦ ?_⟩
  have hεC : ε ∈ Icc 0 ε₀ :=
    ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hεNear : dist ε 0 < eta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hε.1]
    exact hε.2.trans_lt <|
      (min_le_right ε₀ (eta / 2)).trans_lt (half_lt_self heta)
  exact (half_pos hdelta).trans_le (hnear ε hεC hεNear x hx)

end ZeroLocalization

private lemma exists_four_arc_boundary_ne_collar_aux
    {u₁ u₂ v₁ v₂ ε₀ : ℝ} (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) (hε₀ : 0 < ε₀)
    {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (hΦ : ContinuousOn Φ
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂)))
    (hzero : ∀ t, Φ (0, fourArcRectangleBoundary u₁ u₂ v₁ v₂ t) ≠ 0) :
    ∃ η, 0 < η ∧ η ≤ ε₀ ∧ ∀ ε ∈ Set.Ico 0 η, ∀ t,
      Φ (ε, fourArcRectangleBoundary u₁ u₂ v₁ v₂ t) ≠ 0 := by
  let g : ℝ × unitInterval → ℂ := fun p ↦
    Φ (p.1, fourArcRectangleBoundary u₁ u₂ v₁ v₂ p.2)
  have hg : ContinuousOn g (Set.Icc 0 ε₀ ×ˢ Set.univ) := by
    apply hΦ.comp
      (continuous_fst.prodMk
        ((fourArcRectangleBoundary u₁ u₂ v₁ v₂).continuous.comp
          continuous_snd)).continuousOn
    exact fun p hp ↦ ⟨hp.1, fourArcRectangleBoundary_mem hu hv p.2⟩
  have hzero' : ∀ t, g (0, t) ≠ 0 := by simpa only [g] using hzero
  simpa only [g] using exists_pos_boundary_collar_aux hε₀ hg hzero'

/-- Restrict a map continuous on a closed rectangle to its canonical
four-arc boundary loop. -/
noncomputable def fourArcRectangleBoundaryMap
    {α : Type*} [TopologicalSpace α] {u₁ u₂ v₁ v₂ : ℝ}
    (F : ℝ × ℝ → α) (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂)
    (hF : ContinuousOn F (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂)) :
    C(unitInterval, α) :=
  ⟨fun t ↦ F (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t),
    hF.comp_continuous (fourArcRectangleBoundary u₁ u₂ v₁ v₂).continuous
      (fourArcRectangleBoundary_mem hu hv)⟩

@[simp] lemma fourArcRectangleBoundaryMap_apply
    {α : Type*} [TopologicalSpace α] {u₁ u₂ v₁ v₂ : ℝ}
    (F : ℝ × ℝ → α) (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂)
    (hF : ContinuousOn F (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂))
    (t : unitInterval) :
    fourArcRectangleBoundaryMap F hu hv hF t =
      F (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t) := rfl

theorem fourArcRectangleBoundaryMap_zero_eq_one
    {α : Type*} [TopologicalSpace α] {u₁ u₂ v₁ v₂ : ℝ}
    (F : ℝ × ℝ → α) (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂)
    (hF : ContinuousOn F (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂)) :
    fourArcRectangleBoundaryMap F hu hv hF 0 =
      fourArcRectangleBoundaryMap F hu hv hF 1 := by
  simp [fourArcRectangleBoundaryMap]

/-- A zero-free continuous family on a rectangle boundary preserves the
winding number of its endpoint loops. -/
theorem windingNumberC_eq_of_fourArcRectangleBoundary_family
    {u₁ u₂ v₁ v₂ ε ε₀ : ℝ} (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂)
    (hε0 : 0 ≤ ε) (hεε₀ : ε ≤ ε₀)
    {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (hΦ : ContinuousOn Φ
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂)))
    (hbd : ∀ δ ∈ Set.Icc 0 ε, ∀ t,
      Φ (δ, fourArcRectangleBoundary u₁ u₂ v₁ v₂ t) ≠ 0)
    (gamma₀ gamma₁ : C(unitInterval, ℂ))
    (hgamma₀ : ∀ t, gamma₀ t ≠ 0) (hgamma₁ : ∀ t, gamma₁ t ≠ 0)
    (hzero : ∀ t, gamma₀ t =
      Φ (0, fourArcRectangleBoundary u₁ u₂ v₁ v₂ t))
    (hone : ∀ t, gamma₁ t =
      Φ (ε, fourArcRectangleBoundary u₁ u₂ v₁ v₂ t)) :
    Gluck.windingNumberC gamma₀ hgamma₀ =
      Gluck.windingNumberC gamma₁ hgamma₁ := by
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun st ↦ Φ ((st.1 : ℝ) * ε,
        fourArcRectangleBoundary u₁ u₂ v₁ v₂ st.2),
      hΦ.comp_continuous
        (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk
          ((fourArcRectangleBoundary u₁ u₂ v₁ v₂).continuous.comp continuous_snd))
        (fun st ↦ ⟨⟨mul_nonneg st.1.2.1 hε0,
          (mul_le_of_le_one_left hε0 st.1.2.2).trans hεε₀⟩,
            fourArcRectangleBoundary_mem hu hv st.2⟩)⟩
  have hH : ∀ st, H st ≠ 0 := fun st ↦ hbd _ ⟨mul_nonneg st.1.2.1 hε0,
    mul_le_of_le_one_left hε0 st.1.2.2⟩ st.2
  apply Gluck.windingNumberC_eq_of_homotopy gamma₀ gamma₁ hgamma₀ hgamma₁ H hH
  · intro t
    simpa only [H, ContinuousMap.coe_mk, Set.Icc.coe_zero, zero_mul] using
      (hzero t).symm
  · intro t
    simpa only [H, ContinuousMap.coe_mk, Set.Icc.coe_one, one_mul] using
      (hone t).symm
  · intro s
    change Φ ((s : ℝ) * ε, fourArcRectangleBoundary u₁ u₂ v₁ v₂ 0) =
      Φ ((s : ℝ) * ε, fourArcRectangleBoundary u₁ u₂ v₁ v₂ 1)
    rw [fourArcRectangleBoundary_zero_eq_one]

/-- Stuttering a loop on three rectangle arcs while traversing its two
halves on the initial and terminal right arcs preserves winding. -/
theorem windingNumberC_comp_fourArcRightLoopTime
    (gamma : C(unitInterval, ℂ)) (hgamma : ∀ t, gamma t ≠ 0)
    (hloop : gamma 0 = gamma 1) :
    Gluck.windingNumberC gamma hgamma =
      Gluck.windingNumberC (gamma.comp fourArcRightLoopTime)
        (fun t ↦ hgamma (fourArcRightLoopTime t)) := by
  let q : C(unitInterval × unitInterval, unitInterval) :=
    ⟨fun st ↦
      ⟨(1 - (st.1 : ℝ)) * (st.2 : ℝ) +
          (st.1 : ℝ) * (fourArcRightLoopTime st.2 : ℝ), by
        have hmem : AffineMap.lineMap (st.2 : ℝ)
            (fourArcRightLoopTime st.2 : ℝ) (st.1 : ℝ) ∈
              Set.Icc (0 : ℝ) 1 :=
          (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).lineMap_mem
            st.2.property (fourArcRightLoopTime st.2).property st.1.property
        simpa only [AffineMap.lineMap_apply_module, smul_eq_mul] using hmem⟩,
      by
        apply Continuous.subtype_mk
        have hs : Continuous fun st : unitInterval × unitInterval ↦
            (st.1 : ℝ) := continuous_subtype_val.comp continuous_fst
        have ht : Continuous fun st : unitInterval × unitInterval ↦
            (st.2 : ℝ) := continuous_subtype_val.comp continuous_snd
        have hclock : Continuous fun st : unitInterval × unitInterval ↦
            (fourArcRightLoopTime st.2 : ℝ) :=
          continuous_subtype_val.comp
            (fourArcRightLoopTime.continuous.comp continuous_snd)
        exact ((continuous_const.sub hs).mul ht).add (hs.mul hclock)⟩
  let H : C(unitInterval × unitInterval, ℂ) := gamma.comp q
  have hH : ∀ st, H st ≠ 0 := fun st ↦ hgamma (q st)
  apply Gluck.windingNumberC_eq_of_homotopy gamma
    (gamma.comp fourArcRightLoopTime) hgamma
    (fun t ↦ hgamma (fourArcRightLoopTime t)) H hH
  · intro t
    change gamma (q (0, t)) = gamma t
    rw [show q (0, t) = t by
      ext
      simp [q]]
  · intro t
    change gamma (q (1, t)) = gamma (fourArcRightLoopTime t)
    rw [show q (1, t) = fourArcRightLoopTime t by
      ext
      simp [q]]
  · intro s
    change gamma (q (s, 0)) = gamma (q (s, 1))
    have hq0 : q (s, 0) = 0 := by
      ext
      simp [q]
    have hq1 : q (s, 1) = 1 := by
      ext
      simp [q]
    rw [hq0, hq1, hloop]

noncomputable def fourArcRectangleRadialMapAux
    {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂)
    (F : ℝ × ℝ → ℂ)
    (hF : ContinuousOn F (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂)) :
    C(unitInterval × unitInterval, ℂ) :=
  ⟨fun st ↦ F (fourArcRectangleRadialAux u₁ u₂ v₁ v₂ st),
    hF.comp_continuous (fourArcRectangleRadialAux u₁ u₂ v₁ v₂).continuous
      (four_arc_rectangle_radial_mem_aux hu hv)⟩

private lemma four_arc_rectangle_radial_map_ne_zero_aux
    {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ < u₂) (hv : v₁ < v₂)
    {F : ℝ × ℝ → ℂ}
    (hF : ContinuousOn F (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂))
    {gamma : C(unitInterval, ℂ)} (hgamma : ∀ t, gamma t ≠ 0)
    (hgammaEq : ∀ t, gamma t =
      F (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t))
    (hnot : ∀ z ∈ Set.Ioo u₁ u₂ ×ˢ Set.Ioo v₁ v₂, F z ≠ 0) :
    ∀ st, fourArcRectangleRadialMapAux hu.le hv.le F hF st ≠ 0 := by
  intro st
  change F (fourArcRectangleRadialAux u₁ u₂ v₁ v₂ st) ≠ 0
  by_cases hs : (st.1 : ℝ) < 1
  · exact hnot _ (four_arc_rectangle_radial_mem_interior_aux hu hv hs)
  · have hs1 : st.1 = (1 : unitInterval) := Subtype.ext <|
      le_antisymm st.1.2.2 (le_of_not_gt hs)
    rw [show st = ((1 : unitInterval), st.2) from Prod.ext hs1 rfl,
      four_arc_rectangle_radial_one_aux, ← hgammaEq]
    exact hgamma _

private lemma windingNumberC_eq_zero_of_no_interior_zero_aux
    {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ < u₂) (hv : v₁ < v₂)
    {F : ℝ × ℝ → ℂ}
    (hF : ContinuousOn F (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂))
    (gamma : C(unitInterval, ℂ)) (hgamma : ∀ t, gamma t ≠ 0)
    (hgammaEq : ∀ t, gamma t =
      F (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t))
    (hnot : ∀ z ∈ Set.Ioo u₁ u₂ ×ˢ Set.Ioo v₁ v₂, F z ≠ 0) :
    Gluck.windingNumberC gamma hgamma = 0 := by
  let c : ℝ × ℝ := ((u₁ + u₂) / 2, (v₁ + v₂) / 2)
  have hc : c ∈ Set.Ioo u₁ u₂ ×ˢ Set.Ioo v₁ v₂ := by
    exact ⟨⟨by dsimp only [c]; linarith, by dsimp only [c]; linarith⟩,
      ⟨by dsimp only [c]; linarith, by dsimp only [c]; linarith⟩⟩
  have hcne : F c ≠ 0 := hnot c hc
  let gamma₀ : C(unitInterval, ℂ) := ContinuousMap.const _ (F c)
  let H := fourArcRectangleRadialMapAux hu.le hv.le F hF
  have hhom := Gluck.windingNumberC_eq_of_homotopy gamma₀ gamma
    (fun _ ↦ hcne) hgamma H
    (four_arc_rectangle_radial_map_ne_zero_aux hu hv hF hgamma hgammaEq hnot)
    (fun t ↦ by
      change F (fourArcRectangleRadialAux u₁ u₂ v₁ v₂ (0, t)) = F c
      rw [four_arc_rectangle_radial_zero_aux])
    (fun t ↦ by
      change F (fourArcRectangleRadialAux u₁ u₂ v₁ v₂ (1, t)) = gamma t
      rw [four_arc_rectangle_radial_one_aux]
      exact (hgammaEq t).symm)
    (fun s ↦ by
      change F (fourArcRectangleRadialAux u₁ u₂ v₁ v₂ (s, 0)) =
        F (fourArcRectangleRadialAux u₁ u₂ v₁ v₂ (s, 1))
      rw [four_arc_rectangle_radial_loop_aux])
  have hconst : Gluck.windingNumberC gamma₀ (fun _ ↦ hcne) = 0 := by
    simpa only [gamma₀] using Gluck.windingNumberC_const (F c) hcne
  exact hhom.symm ▸ hconst

/-- Nonzero winding of the canonical rectangle boundary loop forces a zero
strictly inside the rectangle. -/
theorem exists_zero_of_fourArcRectangleBoundary_winding
    {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ < u₂) (hv : v₁ < v₂)
    {F : ℝ × ℝ → ℂ}
    (hF : ContinuousOn F (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂))
    (gamma : C(unitInterval, ℂ)) (hgamma : ∀ t, gamma t ≠ 0)
    (hgammaEq : ∀ t, gamma t =
      F (fourArcRectangleBoundary u₁ u₂ v₁ v₂ t))
    (hwind : Gluck.windingNumberC gamma hgamma ≠ 0) :
    ∃ z ∈ Set.Ioo u₁ u₂ ×ˢ Set.Ioo v₁ v₂, F z = 0 := by
  by_contra hnot
  push Not at hnot
  exact hwind (windingNumberC_eq_zero_of_no_interior_zero_aux
    hu hv hF gamma hgamma hgammaEq hnot)

/-- A jointly continuous perturbation of a nonzero-winding rectangle loop
has an interior zero on every sufficiently small positive slice. -/
theorem exists_pos_forall_lt_exists_zero_of_fourArcRectangleBoundary_winding
    {u₁ u₂ v₁ v₂ ε₀ : ℝ} (hu : u₁ < u₂) (hv : v₁ < v₂) (hε₀ : 0 < ε₀)
    {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (hΦ : ContinuousOn Φ
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂)))
    (gamma : C(unitInterval, ℂ)) (hgamma : ∀ t, gamma t ≠ 0)
    (hgammaEq : ∀ t, gamma t =
      Φ (0, fourArcRectangleBoundary u₁ u₂ v₁ v₂ t))
    (hwind : Gluck.windingNumberC gamma hgamma ≠ 0) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Set.Ioo 0 ε₁,
      ∃ z ∈ Set.Ioo u₁ u₂ ×ˢ Set.Ioo v₁ v₂, Φ (ε, z) = 0 := by
  obtain ⟨ε₁, hε₁, hε₁ε₀, hboundary⟩ :=
    exists_four_arc_boundary_ne_collar_aux hu.le hv.le hε₀ hΦ
      (fun t ↦ by rw [← hgammaEq t]; exact hgamma t)
  refine ⟨ε₁, hε₁, hε₁ε₀, fun ε hε ↦ ?_⟩
  have hslice : ContinuousOn (fun z ↦ Φ (ε, z))
      (Set.Icc u₁ u₂ ×ˢ Set.Icc v₁ v₂) := by
    apply hΦ.comp (continuous_const.prodMk continuous_id).continuousOn
    exact fun _ hz ↦ ⟨⟨hε.1.le, hε.2.le.trans hε₁ε₀⟩, hz⟩
  let gammaε := fourArcRectangleBoundaryMap (fun z ↦ Φ (ε, z)) hu.le hv.le hslice
  have hgammaε : ∀ t, gammaε t ≠ 0 :=
    fun t ↦ hboundary ε ⟨hε.1.le, hε.2⟩ t
  have hwindEq := windingNumberC_eq_of_fourArcRectangleBoundary_family hu.le hv.le
    hε.1.le (hε.2.le.trans hε₁ε₀) hΦ
    (fun δ hδ t ↦ hboundary δ ⟨hδ.1, hδ.2.trans_lt hε.2⟩ t)
    gamma gammaε hgamma hgammaε hgammaEq (fun _ ↦ rfl)
  have hwindε : Gluck.windingNumberC gammaε hgammaε ≠ 0 := by
    rwa [← hwindEq]
  exact exists_zero_of_fourArcRectangleBoundary_winding hu hv hslice
    gammaε hgammaε (fun _ ↦ rfl) hwindε

end Gluck.Discrete
