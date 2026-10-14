/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Winding

/-!
# Winding from crossed four-arc signs

This file computes the winding of a loop whose four consecutive arcs lie in
the lower, left, right, and upper open half-planes, with the two crossed
coordinate-axis corners retained explicitly.
-/

namespace Gluck.Discrete

private noncomputable def crossedFourArcPhase (t : unitInterval) : ℝ :=
  9 * Real.pi / 8 + Real.pi * (t : ℝ) +
    2 * Real.pi * max 0 (min ((t : ℝ) - 3 / 8) (1 / 2))

private lemma continuous_crossed_four_arc_phase_aux : Continuous crossedFourArcPhase := by
  unfold crossedFourArcPhase
  fun_prop

private lemma crossed_four_arc_phase_of_le_three_eighths_aux
    {t : unitInterval} (ht : (t : ℝ) ≤ 3 / 8) :
    crossedFourArcPhase t = 9 * Real.pi / 8 + Real.pi * (t : ℝ) := by
  rw [crossedFourArcPhase, min_eq_left (by linarith), max_eq_left (by linarith)]
  ring

private lemma crossed_four_arc_phase_of_mem_middle_aux
    {t : unitInterval} (ht0 : 3 / 8 ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 7 / 8) :
    crossedFourArcPhase t = 3 * Real.pi / 8 + 3 * Real.pi * (t : ℝ) := by
  rw [crossedFourArcPhase, min_eq_left (by linarith), max_eq_right (by linarith)]
  ring

private lemma crossed_four_arc_phase_of_seven_eighths_le_aux
    {t : unitInterval} (ht : 7 / 8 ≤ (t : ℝ)) :
    crossedFourArcPhase t = 17 * Real.pi / 8 + Real.pi * (t : ℝ) := by
  rw [crossedFourArcPhase, min_eq_right (by linarith), max_eq_right (by norm_num)]
  ring

private noncomputable def crossedFourArcModel : C(unitInterval, ℂ) :=
  ⟨fun t ↦ Complex.exp ((crossedFourArcPhase t : ℂ) * Complex.I), by
    apply Complex.continuous_exp.comp
    exact (Complex.continuous_ofReal.comp continuous_crossed_four_arc_phase_aux).mul
      continuous_const⟩

private lemma crossed_four_arc_model_re_aux (t : unitInterval) :
    (crossedFourArcModel t).re = Real.cos (crossedFourArcPhase t) := by
  rw [crossedFourArcModel, ContinuousMap.coe_mk, Complex.exp_ofReal_mul_I_re]

private lemma crossed_four_arc_model_im_aux (t : unitInterval) :
    (crossedFourArcModel t).im = Real.sin (crossedFourArcPhase t) := by
  rw [crossedFourArcModel, ContinuousMap.coe_mk, Complex.exp_ofReal_mul_I_im]

private lemma crossed_four_arc_model_right_first_aux
    {t : unitInterval} (ht : (t : ℝ) ≤ 1 / 8) :
    (crossedFourArcModel t).im < 0 := by
  rw [crossed_four_arc_model_im_aux,
    crossed_four_arc_phase_of_le_three_eighths_aux (by linarith)]
  rw [show 9 * Real.pi / 8 + Real.pi * (t : ℝ) =
    (9 * Real.pi / 8 + Real.pi * (t : ℝ) - 2 * Real.pi) + 2 * Real.pi by ring,
    Real.sin_add_two_pi]
  have hmul : 0 ≤ Real.pi * (t : ℝ) := mul_nonneg Real.pi_pos.le t.2.1
  exact Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos, hmul])
    (by nlinarith [Real.pi_pos])

private lemma crossed_four_arc_model_right_last_aux
    {t : unitInterval} (ht : 7 / 8 < (t : ℝ)) :
    (crossedFourArcModel t).im < 0 := by
  rw [crossed_four_arc_model_im_aux,
    crossed_four_arc_phase_of_seven_eighths_le_aux ht.le]
  rw [show 17 * Real.pi / 8 + Real.pi * (t : ℝ) =
    ((17 * Real.pi / 8 + Real.pi * (t : ℝ) - 4 * Real.pi) + 2 * Real.pi) +
      2 * Real.pi by ring, Real.sin_add_two_pi, Real.sin_add_two_pi]
  have hmul : Real.pi * (t : ℝ) ≤ Real.pi :=
    by simpa using mul_le_mul_of_nonneg_left t.2.2 Real.pi_pos.le
  exact Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos, hmul])

private lemma crossed_four_arc_model_top_aux
    {t : unitInterval} (ht0 : 1 / 8 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 3 / 8) :
    (crossedFourArcModel t).re < 0 := by
  rw [crossed_four_arc_model_re_aux,
    crossed_four_arc_phase_of_le_three_eighths_aux ht1.le]
  exact Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])

private lemma crossed_four_arc_model_left_aux
    {t : unitInterval} (ht0 : 3 / 8 < (t : ℝ)) (ht1 : (t : ℝ) ≤ 5 / 8) :
    0 < (crossedFourArcModel t).re := by
  rw [crossed_four_arc_model_re_aux,
    crossed_four_arc_phase_of_mem_middle_aux ht0.le (by linarith)]
  rw [show 3 * Real.pi / 8 + 3 * Real.pi * (t : ℝ) =
    (3 * Real.pi / 8 + 3 * Real.pi * (t : ℝ) - 2 * Real.pi) +
      2 * Real.pi by ring, Real.cos_add_two_pi]
  exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos],
    by nlinarith [Real.pi_pos]⟩

private lemma crossed_four_arc_model_bottom_aux
    {t : unitInterval} (ht0 : 5 / 8 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 7 / 8) :
    0 < (crossedFourArcModel t).im := by
  rw [crossed_four_arc_model_im_aux,
    crossed_four_arc_phase_of_mem_middle_aux (by linarith) ht1.le]
  rw [show 3 * Real.pi / 8 + 3 * Real.pi * (t : ℝ) =
    (3 * Real.pi / 8 + 3 * Real.pi * (t : ℝ) - 2 * Real.pi) +
      2 * Real.pi by ring, Real.sin_add_two_pi]
  exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])

private lemma crossed_four_arc_model_top_left_aux :
    (crossedFourArcModel ⟨(3 : ℝ) / 8, by norm_num⟩).im < 0 := by
  rw [crossed_four_arc_model_im_aux,
    crossed_four_arc_phase_of_le_three_eighths_aux (by norm_num)]
  rw [show 9 * Real.pi / 8 + Real.pi * ((⟨(3 : ℝ) / 8, by norm_num⟩ :
      unitInterval) : ℝ) = -(Real.pi / 2) + 2 * Real.pi by norm_num; ring,
    Real.sin_add_two_pi, Real.sin_neg, Real.sin_pi_div_two]
  norm_num

private lemma crossed_four_arc_model_bottom_right_aux :
    (crossedFourArcModel ⟨(7 : ℝ) / 8, by norm_num⟩).re < 0 := by
  rw [crossed_four_arc_model_re_aux,
    crossed_four_arc_phase_of_seven_eighths_le_aux (by norm_num)]
  rw [show 17 * Real.pi / 8 + Real.pi * ((⟨(7 : ℝ) / 8, by norm_num⟩ :
      unitInterval) : ℝ) = Real.pi + 2 * Real.pi by norm_num; ring,
    Real.cos_add_two_pi, Real.cos_pi]
  norm_num

private lemma crossed_four_arc_phase_zero_aux :
    crossedFourArcPhase 0 = 9 * Real.pi / 8 := by
  rw [crossed_four_arc_phase_of_le_three_eighths_aux (by norm_num)]
  norm_num

private lemma crossed_four_arc_phase_one_aux :
    crossedFourArcPhase 1 = 25 * Real.pi / 8 := by
  rw [crossed_four_arc_phase_of_seven_eighths_le_aux (by norm_num)]
  rw [Set.Icc.coe_one]
  ring

private lemma crossed_four_arc_model_ne_aux (t : unitInterval) :
    crossedFourArcModel t ≠ 0 :=
  Complex.exp_ne_zero _

private lemma crossed_four_arc_model_loop_aux :
    crossedFourArcModel 0 = crossedFourArcModel 1 := by
  change Complex.exp ((crossedFourArcPhase 0 : ℂ) * Complex.I) =
    Complex.exp ((crossedFourArcPhase 1 : ℂ) * Complex.I)
  rw [crossed_four_arc_phase_zero_aux, crossed_four_arc_phase_one_aux]
  rw [show (((25 * Real.pi / 8 : ℝ) : ℂ) * Complex.I) =
    (((9 * Real.pi / 8 : ℝ) : ℂ) * Complex.I) +
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add]
  have hexp : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    convert Complex.exp_two_pi_mul_I using 1
    push_cast
    ring
  rw [hexp, mul_one]

private noncomputable def crossedFourArcHomotopyPhase
    (st : unitInterval × unitInterval) : ℝ :=
  (1 - (st.1 : ℝ)) * (2 * Real.pi * (st.2 : ℝ)) +
    (st.1 : ℝ) * crossedFourArcPhase st.2

private lemma continuous_crossed_four_arc_homotopy_phase_aux :
    Continuous crossedFourArcHomotopyPhase := by
  unfold crossedFourArcHomotopyPhase
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_const.mul (continuous_subtype_val.comp continuous_snd)) |>.add <|
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_crossed_four_arc_phase_aux.comp continuous_snd)

private noncomputable def crossedFourArcModelHomotopy :
    C(unitInterval × unitInterval, ℂ) :=
  ⟨fun st ↦ Complex.exp ((crossedFourArcHomotopyPhase st : ℂ) * Complex.I),
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        continuous_crossed_four_arc_homotopy_phase_aux).mul continuous_const)⟩

private lemma crossed_four_arc_model_homotopy_zero_aux (t : unitInterval) :
    crossedFourArcModelHomotopy (0, t) = Gluck.linearLoop (1 : ℂ) 0 t := by
  simp [crossedFourArcModelHomotopy, crossedFourArcHomotopyPhase,
    Gluck.linearLoop_apply]

private lemma crossed_four_arc_model_homotopy_one_aux (t : unitInterval) :
    crossedFourArcModelHomotopy (1, t) = crossedFourArcModel t := by
  simp [crossedFourArcModelHomotopy, crossedFourArcHomotopyPhase,
    crossedFourArcModel]

private lemma crossed_four_arc_model_homotopy_loop_aux (s : unitInterval) :
    crossedFourArcModelHomotopy (s, 0) = crossedFourArcModelHomotopy (s, 1) := by
  change Complex.exp (((crossedFourArcHomotopyPhase (s, 0) : ℝ) : ℂ) * Complex.I) =
    Complex.exp (((crossedFourArcHomotopyPhase (s, 1) : ℝ) : ℂ) * Complex.I)
  have hphase : crossedFourArcHomotopyPhase (s, 1) =
      crossedFourArcHomotopyPhase (s, 0) + 2 * Real.pi := by
    rw [crossedFourArcHomotopyPhase, crossedFourArcHomotopyPhase,
      Set.Icc.coe_zero, Set.Icc.coe_one, crossed_four_arc_phase_zero_aux,
      crossed_four_arc_phase_one_aux]
    ring
  rw [hphase]
  rw [show (((crossedFourArcHomotopyPhase (s, 0) + 2 * Real.pi : ℝ) : ℂ) *
      Complex.I) =
    ((crossedFourArcHomotopyPhase (s, 0) : ℂ) * Complex.I) +
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_add]
  have hexp : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    convert Complex.exp_two_pi_mul_I using 1
    push_cast
    ring
  rw [hexp, mul_one]

private lemma crossed_four_arc_model_winding_aux :
    Gluck.windingNumberC crossedFourArcModel crossed_four_arc_model_ne_aux = 1 := by
  have hgamma₀ : ∀ t, Gluck.linearLoop (1 : ℂ) 0 t ≠ 0 :=
    Gluck.linearLoop_ne_zero (1 : ℂ) 0 (by norm_num)
  have hhom := Gluck.windingNumberC_eq_of_homotopy
    (Gluck.linearLoop (1 : ℂ) 0) crossedFourArcModel hgamma₀
    crossed_four_arc_model_ne_aux crossedFourArcModelHomotopy
    (fun _ ↦ Complex.exp_ne_zero _) crossed_four_arc_model_homotopy_zero_aux
    crossed_four_arc_model_homotopy_one_aux crossed_four_arc_model_homotopy_loop_aux
  have hlinear := Gluck.windingNumberC_linearLoop (1 : ℂ) 0 (by norm_num)
  rw [if_pos (by norm_num)] at hlinear
  exact hhom.symm.trans hlinear

/-- The crossed four-arc signs and the two coordinate-axis corner signs
exclude zero from the entire loop. -/
theorem ne_zero_of_crossed_fourArcs
    (gamma : C(unitInterval, ℂ))
    (hright : ∀ t : unitInterval,
      ((t : ℝ) ≤ 1 / 8 ∨ 7 / 8 < (t : ℝ)) → (gamma t).im < 0)
    (htop : ∀ t : unitInterval,
      1 / 8 ≤ (t : ℝ) → (t : ℝ) < 3 / 8 → (gamma t).re < 0)
    (hleft : ∀ t : unitInterval,
      3 / 8 < (t : ℝ) → (t : ℝ) ≤ 5 / 8 → 0 < (gamma t).re)
    (hbottom : ∀ t : unitInterval,
      5 / 8 ≤ (t : ℝ) → (t : ℝ) < 7 / 8 → 0 < (gamma t).im)
    (htopLeft : ∀ t : unitInterval, (t : ℝ) = 3 / 8 → (gamma t).im < 0)
    (hbottomRight : ∀ t : unitInterval, (t : ℝ) = 7 / 8 → (gamma t).re < 0) :
    ∀ t, gamma t ≠ 0 := by
  intro t hzero
  have hre : (gamma t).re = 0 := by simpa using congrArg Complex.re hzero
  have him : (gamma t).im = 0 := by simpa using congrArg Complex.im hzero
  by_cases h1 : (t : ℝ) ≤ 1 / 8
  · linarith [hright t (Or.inl h1)]
  by_cases h3 : (t : ℝ) < 3 / 8
  · linarith [htop t (by linarith) h3]
  by_cases he3 : (t : ℝ) = 3 / 8
  · linarith [htopLeft t he3]
  have ht3 : 3 / 8 < (t : ℝ) :=
    lt_of_le_of_ne (le_of_not_gt h3) (Ne.symm he3)
  by_cases h5 : (t : ℝ) ≤ 5 / 8
  · linarith [hleft t ht3 h5]
  by_cases h7 : (t : ℝ) < 7 / 8
  · linarith [hbottom t (by linarith) h7]
  by_cases he7 : (t : ℝ) = 7 / 8
  · linarith [hbottomRight t he7]
  · have ht7 : 7 / 8 < (t : ℝ) :=
      lt_of_le_of_ne (le_of_not_gt h7) (Ne.symm he7)
    linarith [hright t (Or.inr ht7)]

private lemma unit_interval_convex_pos_aux
    (s : unitInterval) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < (1 - (s : ℝ)) * a + (s : ℝ) * b := by
  rcases le_total (s : ℝ) (1 / 2) with hs | hs
  · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) ha)
      (mul_nonneg s.2.1 hb.le)
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr s.2.2) ha.le) (mul_pos (by linarith) hb)

private lemma crossed_four_arc_line_re_aux
    (gamma : C(unitInterval, ℂ)) (s t : unitInterval) :
    (crossedFourArcModel t + (s : ℝ) •
      (gamma t - crossedFourArcModel t)).re =
      (1 - (s : ℝ)) * (crossedFourArcModel t).re + (s : ℝ) * (gamma t).re := by
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma crossed_four_arc_line_im_aux
    (gamma : C(unitInterval, ℂ)) (s t : unitInterval) :
    (crossedFourArcModel t + (s : ℝ) •
      (gamma t - crossedFourArcModel t)).im =
      (1 - (s : ℝ)) * (crossedFourArcModel t).im + (s : ℝ) * (gamma t).im := by
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma crossed_four_arc_line_homotopy_ne_aux
    (gamma : C(unitInterval, ℂ))
    (hright : ∀ t : unitInterval,
      ((t : ℝ) ≤ 1 / 8 ∨ 7 / 8 < (t : ℝ)) → (gamma t).im < 0)
    (htop : ∀ t : unitInterval,
      1 / 8 ≤ (t : ℝ) → (t : ℝ) < 3 / 8 → (gamma t).re < 0)
    (hleft : ∀ t : unitInterval,
      3 / 8 < (t : ℝ) → (t : ℝ) ≤ 5 / 8 → 0 < (gamma t).re)
    (hbottom : ∀ t : unitInterval,
      5 / 8 ≤ (t : ℝ) → (t : ℝ) < 7 / 8 → 0 < (gamma t).im)
    (htopLeft : ∀ t : unitInterval, (t : ℝ) = 3 / 8 → (gamma t).im < 0)
    (hbottomRight : ∀ t : unitInterval, (t : ℝ) = 7 / 8 → (gamma t).re < 0)
    (s t : unitInterval) :
    crossedFourArcModel t + (s : ℝ) • (gamma t - crossedFourArcModel t) ≠ 0 := by
  intro hzero
  have hzre : _ = (0 : ℝ) := congrArg Complex.re hzero
  have hzim : _ = (0 : ℝ) := congrArg Complex.im hzero
  rw [crossed_four_arc_line_re_aux] at hzre
  rw [crossed_four_arc_line_im_aux] at hzim
  by_cases h1 : (t : ℝ) ≤ 1 / 8
  · nlinarith [unit_interval_convex_pos_aux s
      (neg_pos.mpr (crossed_four_arc_model_right_first_aux h1))
      (neg_pos.mpr (hright t (Or.inl h1)))]
  by_cases h3 : (t : ℝ) < 3 / 8
  · nlinarith [unit_interval_convex_pos_aux s
      (neg_pos.mpr (crossed_four_arc_model_top_aux (by linarith) h3))
      (neg_pos.mpr (htop t (by linarith) h3))]
  by_cases he3 : (t : ℝ) = 3 / 8
  · have htEq : t = ⟨(3 : ℝ) / 8, by norm_num⟩ := Subtype.ext he3
    have hmodel : (crossedFourArcModel t).im < 0 := by
      rw [htEq]
      exact crossed_four_arc_model_top_left_aux
    nlinarith [unit_interval_convex_pos_aux s (neg_pos.mpr hmodel)
      (neg_pos.mpr (htopLeft t he3))]
  have ht3 : 3 / 8 < (t : ℝ) :=
    lt_of_le_of_ne (le_of_not_gt h3) (Ne.symm he3)
  by_cases h5 : (t : ℝ) ≤ 5 / 8
  · nlinarith [unit_interval_convex_pos_aux s
      (crossed_four_arc_model_left_aux ht3 h5)
      (hleft t ht3 h5)]
  by_cases h7 : (t : ℝ) < 7 / 8
  · nlinarith [unit_interval_convex_pos_aux s
      (crossed_four_arc_model_bottom_aux (by linarith) h7)
      (hbottom t (by linarith) h7)]
  by_cases he7 : (t : ℝ) = 7 / 8
  · have htEq : t = ⟨(7 : ℝ) / 8, by norm_num⟩ := Subtype.ext he7
    have hmodel : (crossedFourArcModel t).re < 0 := by
      rw [htEq]
      exact crossed_four_arc_model_bottom_right_aux
    nlinarith [unit_interval_convex_pos_aux s (neg_pos.mpr hmodel)
      (neg_pos.mpr (hbottomRight t he7))]
  · have ht7 : 7 / 8 < (t : ℝ) :=
      lt_of_le_of_ne (le_of_not_gt h7) (Ne.symm he7)
    nlinarith [unit_interval_convex_pos_aux s
      (neg_pos.mpr (crossed_four_arc_model_right_last_aux ht7))
      (neg_pos.mpr (hright t (Or.inr ht7)))]

/-- A loop with the crossed four-arc signs has winding number one. -/
theorem windingNumberC_eq_one_of_crossed_fourArcs
    (gamma : C(unitInterval, ℂ)) (hgamma : ∀ t, gamma t ≠ 0)
    (hloop : gamma 0 = gamma 1)
    (hright : ∀ t : unitInterval,
      ((t : ℝ) ≤ 1 / 8 ∨ 7 / 8 < (t : ℝ)) → (gamma t).im < 0)
    (htop : ∀ t : unitInterval,
      1 / 8 ≤ (t : ℝ) → (t : ℝ) < 3 / 8 → (gamma t).re < 0)
    (hleft : ∀ t : unitInterval,
      3 / 8 < (t : ℝ) → (t : ℝ) ≤ 5 / 8 → 0 < (gamma t).re)
    (hbottom : ∀ t : unitInterval,
      5 / 8 ≤ (t : ℝ) → (t : ℝ) < 7 / 8 → 0 < (gamma t).im)
    (htopLeft : ∀ t : unitInterval, (t : ℝ) = 3 / 8 → (gamma t).im < 0)
    (hbottomRight : ∀ t : unitInterval, (t : ℝ) = 7 / 8 → (gamma t).re < 0) :
    Gluck.windingNumberC gamma hgamma = 1 := by
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun st ↦ crossedFourArcModel st.2 +
      (st.1 : ℝ) • (gamma st.2 - crossedFourArcModel st.2), by fun_prop⟩
  have hH : ∀ st, H st ≠ 0 := fun st ↦ crossed_four_arc_line_homotopy_ne_aux
    gamma hright htop hleft hbottom htopLeft hbottomRight st.1 st.2
  have hzero : ∀ t, H (0, t) = crossedFourArcModel t := by
    intro t
    simp [H]
  have hone : ∀ t, H (1, t) = gamma t := by
    intro t
    simp [H]
  have hHloop : ∀ s, H (s, 0) = H (s, 1) := by
    intro s
    simp only [H, ContinuousMap.coe_mk]
    rw [crossed_four_arc_model_loop_aux, hloop]
  have hwind := Gluck.windingNumberC_eq_of_homotopy crossedFourArcModel gamma
    crossed_four_arc_model_ne_aux hgamma H hH hzero hone hHloop
  exact hwind ▸ crossed_four_arc_model_winding_aux

end Gluck.Discrete
