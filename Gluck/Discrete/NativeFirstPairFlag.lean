/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!+# Branch-safe consequences of the original native first-pair flag

The input is the original principal-arcsine inequality. Its branch guard,
squared failure bound, and strict `p*q > 1` are conclusions rather than
additional assumptions. The stronger separation is needed when the flag
itself is an equality.
-/

namespace Gluck.Discrete.NativeOppositePure

open Set

noncomputable def firstPairSigma (h l : ℝ) : ℝ :=
  √((1 - l ^ 2) / (h ^ 2 - l ^ 2))

noncomputable def firstPairFlag (p q h l : ℝ) : ℝ :=
  Real.arcsin p + Real.arcsin (q * firstPairSigma h l) -
    Real.arcsin (firstPairSigma h l) - Real.pi / 2

/-- A general principal-angle flag forces its own missing branch guard
and an unsquared positive lower bound. -/
theorem arcsin_flag_guard_and_bound {p q s : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s) (hs1 : s < 1)
    (hqs : q * s < 1)
    (hflag : 0 ≤ Real.arcsin p + Real.arcsin (q * s) -
      Real.arcsin s - Real.pi / 2) :
    s < p ∧ √(1 - p ^ 2) * √(1 - s ^ 2) ≤ (q - p) * s := by
  have hP0 := Real.arcsin_pos.2 hp
  have hP1 := Real.arcsin_lt_pi_div_two.2 hp1
  have hS0 := Real.arcsin_pos.2 hs
  have hS1 := Real.arcsin_lt_pi_div_two.2 hs1
  have hQ1 := Real.arcsin_lt_pi_div_two.2 hqs
  have hPS : Real.arcsin s < Real.arcsin p := by linarith
  have hsp : s < p := by
    by_contra h
    have := Real.arcsin_le_arcsin (le_of_not_gt h)
    linarith
  refine ⟨hsp, ?_⟩
  have hleft : Real.pi / 2 - Real.arcsin p + Real.arcsin s ∈
      Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hright : Real.arcsin (q * s) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_le_arcsin _, (Real.arcsin_le_pi_div_two _)⟩
  have hsin := Real.monotoneOn_sin hleft hright (by linarith)
  have hqs0 : 0 < q * s := by
    have : 0 < Real.arcsin (q * s) := by linarith
    exact Real.arcsin_pos.mp this
  rw [Real.sin_add, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
    Real.sin_arcsin (by linarith : -1 ≤ p) hp1.le,
    Real.sin_arcsin (by linarith : -1 ≤ s) hs1.le,
    Real.sin_arcsin (by linarith : -1 ≤ q * s) hqs.le,
    Real.cos_arcsin, Real.cos_arcsin] at hsin
  nlinarith

theorem arcsin_flag_one_lt_mul {p q s : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s) (hs1 : s < 1)
    (hqs : q * s < 1)
    (hflag : 0 ≤ Real.arcsin p + Real.arcsin (q * s) -
      Real.arcsin s - Real.pi / 2) : 1 < p * q := by
  obtain ⟨hsp, hbound⟩ := arcsin_flag_guard_and_bound hp hp1 hs hs1 hqs hflag
  have hpRad : 0 < 1 - p ^ 2 := by nlinarith
  have hsRad : 0 < 1 - s ^ 2 := by nlinarith
  have hr : 0 < √(1 - p ^ 2) := Real.sqrt_pos.2 hpRad
  have hc : 0 < √(1 - s ^ 2) := Real.sqrt_pos.2 hsRad
  have hr2 := Real.sq_sqrt hpRad.le
  have hc2 := Real.sq_sqrt hsRad.le
  have hcomp : √(1 - p ^ 2) * s < p * √(1 - s ^ 2) := by
    have hsq : (√(1 - p ^ 2) * s) ^ 2 < (p * √(1 - s ^ 2)) ^ 2 := by
      nlinarith [congrArg (fun v : ℝ => v * s ^ 2) hr2,
        congrArg (fun v : ℝ => p ^ 2 * v) hc2]
    exact (sq_lt_sq₀ (mul_pos hr hs).le (mul_pos hp hc).le).mp hsq
  have hstep := mul_lt_mul_of_pos_left hcomp hr
  have hscale := mul_le_mul_of_nonneg_left hbound hp.le
  have hmul : s < p * q * s := by
    nlinarith [congrArg (fun v : ℝ => v * s) hr2]
  exact (mul_lt_mul_iff_left₀ hs).mp (by simpa [mul_comm, mul_left_comm] using hmul)

theorem firstPairSigma_data {h l : ℝ} (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1) :
    0 < firstPairSigma h l ∧ firstPairSigma h l < 1 ∧
      (firstPairSigma h l) ^ 2 * (h ^ 2 - l ^ 2) = 1 - l ^ 2 ∧
      h * firstPairSigma h l < 1 := by
  have hnum : 0 < 1 - l ^ 2 := by nlinarith
  have hden : 0 < h ^ 2 - l ^ 2 := by nlinarith
  have hs : 0 < firstPairSigma h l := Real.sqrt_pos.2 (div_pos hnum hden)
  have hs2 : (firstPairSigma h l) ^ 2 = (1 - l ^ 2) / (h ^ 2 - l ^ 2) :=
    Real.sq_sqrt (div_pos hnum hden).le
  have hid : (firstPairSigma h l) ^ 2 * (h ^ 2 - l ^ 2) = 1 - l ^ 2 := by
    rw [hs2]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  have hhs : h * firstPairSigma h l < 1 := by
    have hidentity : (1 - (h * firstPairSigma h l) ^ 2) * (h ^ 2 - l ^ 2) =
        l ^ 2 * (h ^ 2 - 1) := by
      nlinarith [congrArg (fun v : ℝ => h ^ 2 * v) hid]
    have hpos : 0 < l ^ 2 * (h ^ 2 - 1) := mul_pos (sq_pos_of_pos hl) (by nlinarith)
    have hsq : 0 < 1 - (h * firstPairSigma h l) ^ 2 :=
      pos_of_mul_pos_left (hidentity.symm ▸ hpos) hden.le
    nlinarith [mul_pos (show 0 < h by linarith) hs]
  refine ⟨hs, ?_, hid, hhs⟩
  nlinarith

theorem firstPairFlag_guard_and_bound {p q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hq : 1 < q) (hqh : q < h) (hflag : 0 ≤ firstPairFlag p q h l) :
    firstPairSigma h l < p ∧
      √(1 - p ^ 2) * √(1 - (firstPairSigma h l) ^ 2) ≤
        (q - p) * firstPairSigma h l := by
  obtain ⟨hs, hs1, _hsq, hhs⟩ := firstPairSigma_data (h := h) (by linarith) hl hl1
  exact arcsin_flag_guard_and_bound hp hp1 hs hs1
    ((mul_lt_mul_of_pos_right hqh hs).trans hhs) hflag

/-- The squared first-pair inequality follows from the original flag,
with its principal branch retained throughout the proof. -/
theorem firstPairFlag_square_bound {p q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hq : 1 < q) (hqh : q < h) (hflag : 0 ≤ firstPairFlag p q h l) :
    (1 - p ^ 2) * (h ^ 2 - 1) ≤ (1 - l ^ 2) * (q - p) ^ 2 := by
  obtain ⟨hs, _hs1, hsig, _hwall⟩ := firstPairSigma_data (h := h) (by linarith) hl hl1
  obtain ⟨_hguard, hbound⟩ := firstPairFlag_guard_and_bound hp hp1 hl hl1 hq hqh hflag
  have hpRad : 0 ≤ 1 - p ^ 2 := by nlinarith
  have hsRad : 0 ≤ 1 - (firstPairSigma h l) ^ 2 := by nlinarith
  have hr2 := Real.sq_sqrt hpRad
  have hc2 := Real.sq_sqrt hsRad
  have hright : 0 ≤ (q - p) * firstPairSigma h l :=
    mul_nonneg (by linarith) hs.le
  have hsq := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hright).mpr hbound
  have hpoly : (1 - p ^ 2) * (1 - (firstPairSigma h l) ^ 2) ≤
      (q - p) ^ 2 * (firstPairSigma h l) ^ 2 := by
    simpa only [mul_pow, hr2, hc2] using hsq
  have hden : 0 < h ^ 2 - l ^ 2 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hpoly hden.le
  nlinarith [congrArg (fun v : ℝ => (q - p) ^ 2 * v) hsig,
    congrArg (fun v : ℝ => (1 - p ^ 2) * v) hsig]

theorem firstPairFlag_one_lt_mul {p q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hq : 1 < q) (hqh : q < h) (hflag : 0 ≤ firstPairFlag p q h l) :
    1 < p * q := by
  obtain ⟨hs, hs1, _hsq, hhs⟩ := firstPairSigma_data (h := h) (by linarith) hl hl1
  exact arcsin_flag_one_lt_mul hp hp1 hs hs1
    ((mul_lt_mul_of_pos_right hqh hs).trans hhs) hflag

/-- Strict separation remains available even when the original flag is
an equality, since the next actual high reading is strictly larger. -/
theorem firstPairFlag_strong_separation {p q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hq : 1 < q) (hqh : q < h) (hflag : 0 ≤ firstPairFlag p q h l) :
    l * (q - p) < p * q - 1 := by
  have hpq := firstPairFlag_one_lt_mul hp hp1 hl hl1 hq hqh hflag
  have hbound := firstPairFlag_square_bound hp hp1 hl hl1 hq hqh hflag
  have hU : 0 < 1 - p ^ 2 := by nlinarith
  have hH : 0 < h ^ 2 - q ^ 2 := by nlinarith
  have hgap := mul_pos hU hH
  have hsq : (l * (q - p)) ^ 2 < (p * q - 1) ^ 2 := by nlinarith
  exact (sq_lt_sq₀ (mul_nonneg hl.le (by linarith)) (by linarith)).mp hsq

/-- Only the side with the larger neighbor can carry a failed flag. -/
theorem firstPairFlag_low_order {p q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hq : 1 < q) (hqh : q < h) (hflag : 0 ≤ firstPairFlag p q h l) : l < p := by
  have hsep := firstPairFlag_strong_separation hp hp1 hl hl1 hq hqh hflag
  have hpl : p * l < 1 := by nlinarith
  by_contra h
  have hple : p ≤ l := le_of_not_gt h
  have hprod := mul_nonneg (show 0 ≤ q by linarith) (sub_nonneg.mpr hple)
  nlinarith

theorem firstPairFlag_threshold_lt_q {p q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hq : 1 < q) (hqh : q < h) (hflag : 0 ≤ firstPairFlag p q h l) :
    (1 - p * l) / (p - l) < q := by
  have hlp := firstPairFlag_low_order hp hp1 hl hl1 hq hqh hflag
  have hsep := firstPairFlag_strong_separation hp hp1 hl hl1 hq hqh hflag
  apply (div_lt_iff₀ (sub_pos.mpr hlp)).mpr
  nlinarith

/-- Producer-facing package derived solely from the original principal
flag and the actual endpoint ordering. -/
theorem firstPairFlag_consequences {p q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hq : 1 < q) (hqh : q < h) (hflag : 0 ≤ firstPairFlag p q h l) :
    (1 - p ^ 2) * (h ^ 2 - 1) ≤ (1 - l ^ 2) * (q - p) ^ 2 ∧
      1 < p * q ∧ l * (q - p) < p * q - 1 ∧ l < p :=
  ⟨firstPairFlag_square_bound hp hp1 hl hl1 hq hqh hflag,
    firstPairFlag_one_lt_mul hp hp1 hl hl1 hq hqh hflag,
    firstPairFlag_strong_separation hp hp1 hl hl1 hq hqh hflag,
    firstPairFlag_low_order hp hp1 hl hl1 hq hqh hflag⟩

end Gluck.Discrete.NativeOppositePure
