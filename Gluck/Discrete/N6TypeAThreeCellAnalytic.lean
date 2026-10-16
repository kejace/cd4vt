/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.N6TypeAThreeCell
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Inverse-sine corner estimates in the Type-A three-cell selector

This file proves the upper-left `R`-cell corner sign in the exact normalized
failure regime of `research/notes/TYPE_A_THREE_CELL_ORTHOGONAL_COVER.md`. The proof treats
the two regimes `h * l ≤ 1` and `1 < h * l` and includes the exact threshold
identity used in the latter. It also proves that a nonnegative bottom-right
corner residual forces the sharp critical lower bound on `t`, and transfers
that bound to the scalar `M` wall.
-/

@[expose] public section

namespace Gluck.Discrete.N6TypeAThreeCell

open Set

/-- For `1 < h`, the difference `arcsin (h*x) - arcsin x` is strictly
increasing throughout its physical interval. -/
theorem strictMonoOn_arcsin_mul_sub_arcsin {h : ℝ} (hh : 1 < h) :
    StrictMonoOn (fun x ↦ Real.arcsin (h * x) - Real.arcsin x) (Icc 0 (1 / h)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    have hh0 : 0 < h := lt_trans zero_lt_one hh
    have hhx1 : h * x < 1 := by
      have := (lt_div_iff₀ hh0).1 hx.2
      nlinarith
    have hx1 : x < 1 := hx.2.trans ((div_lt_one hh0).2 hh)
    have hhx0 : 0 < h * x := mul_pos hh0 hx.1
    have hd₁ := (Real.hasDerivAt_arcsin (by nlinarith) (by nlinarith)).comp x
      (hasDerivAt_const_mul h)
    have hd₂ := Real.hasDerivAt_arcsin (by nlinarith) (by nlinarith : x ≠ 1)
    have hd := hd₁.sub hd₂
    change 0 < deriv ((Real.arcsin ∘ fun y ↦ h * y) - Real.arcsin) x
    rw [hd.deriv]
    have hA : 0 < √(1 - (h * x) ^ 2) := Real.sqrt_pos.2 <|
      sub_pos.mpr ((sq_lt_one_iff₀ hhx0.le).2 hhx1)
    have hB : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 <|
      sub_pos.mpr ((sq_lt_one_iff₀ hx.1.le).2 hx1)
    have hxlt : x < h * x := by
      nlinarith [mul_pos (sub_pos.mpr hh) hx.1]
    have hsq : x ^ 2 < (h * x) ^ 2 := (sq_lt_sq₀ hx.1.le hhx0.le).2 hxlt
    have hAB : √(1 - (h * x) ^ 2) < √(1 - x ^ 2) :=
      Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
    have hinv : 1 / √(1 - x ^ 2) < 1 / √(1 - (h * x) ^ 2) :=
      one_div_lt_one_div_of_lt hA hAB
    have hscale :
        1 / √(1 - (h * x) ^ 2) < 1 / √(1 - (h * x) ^ 2) * h := by
      simpa using mul_lt_mul_of_pos_left hh (one_div_pos.mpr hA)
    exact sub_pos.mpr (hinv.trans hscale)

/-- The upper-left Type-A `R`-cell corner is negative in the `h*l ≤ 1` branch. -/
theorem r_corner_residual_neg_of_mul_le_one {h l rho : ℝ}
    (hh : 1 < h) (hrho0 : 0 ≤ rho) (hrho : rho < 1 / h) (hhl : h * l ≤ 1) :
    Real.arcsin (h * rho) + Real.arcsin l - Real.arcsin rho - Real.pi / 2 < 0 := by
  have hh0 : 0 < h := lt_trans zero_lt_one hh
  have hl : l ≤ 1 / h := by
    rw [le_div_iff₀ hh0]
    simpa [mul_comm] using hhl
  have hinv0 : 0 ≤ 1 / h := one_div_nonneg.mpr hh0.le
  have hdiff := strictMonoOn_arcsin_mul_sub_arcsin hh
    ⟨hrho0, hrho.le⟩ ⟨hinv0, le_rfl⟩ hrho
  dsimp only at hdiff
  rw [show h * (1 / h) = 1 by field_simp, Real.arcsin_one] at hdiff
  exact lt_of_lt_of_le (by linarith : _ < Real.arcsin l - Real.arcsin (1 / h))
    (sub_nonpos.mpr (Real.arcsin_le_arcsin hl))

private lemma arcsin_mul_sub_arcsin_eq_arccos_aux {h l rho : ℝ}
    (hh : 1 ≤ h) (hrho0 : 0 ≤ rho) (hhrho : h * rho ≤ 1)
    (hcos : √(1 - (h * rho) ^ 2) * √(1 - rho ^ 2) + h * rho ^ 2 = l) :
    Real.arcsin (h * rho) - Real.arcsin rho = Real.arccos l := by
  have harg0 : 0 ≤ h * rho := mul_nonneg (zero_le_one.trans hh) hrho0
  have hrhoArg : rho ≤ h * rho := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) hrho0]
  have hrho1 : rho ≤ 1 := hrhoArg.trans hhrho
  have hA0 : 0 ≤ Real.arcsin (h * rho) - Real.arcsin rho :=
    sub_nonneg.mpr (Real.arcsin_le_arcsin hrhoArg)
  have hasinRho0 : 0 ≤ Real.arcsin rho := Real.arcsin_nonneg.2 hrho0
  have hApi : Real.arcsin (h * rho) - Real.arcsin rho ≤ Real.pi := by
    nlinarith [Real.arcsin_le_pi_div_two (h * rho), Real.pi_pos]
  have hcosA : Real.cos (Real.arcsin (h * rho) - Real.arcsin rho) = l := by
    rw [Real.cos_sub, Real.cos_arcsin, Real.cos_arcsin]
    rw [Real.sin_arcsin (by linarith) hhrho, Real.sin_arcsin (by linarith) hrho1]
    simpa [pow_two, mul_assoc] using hcos
  exact (Real.arccos_eq_of_eq_cos hA0 hApi hcosA.symm).symm

private lemma r_corner_threshold_bounds_aux {h l rho d : ℝ}
    (hh : 1 < h) (hl0 : 0 < l) (hl1 : l < 1) (hhl : 1 < h * l)
    (hd : d = h ^ 2 + 1 - 2 * h * l)
    (hrhosq : rho ^ 2 * d = 1 - l ^ 2) :
    0 < d ∧ 0 < 1 - (h * rho) ^ 2 ∧ 0 < 1 - rho ^ 2 := by
  have hlSq : l ^ 2 < 1 := (sq_lt_one_iff₀ hl0.le).2 hl1
  have hdpos : 0 < d := by
    rw [hd]
    nlinarith [sq_nonneg (h - l)]
  have hidH : d * (1 - (h * rho) ^ 2) = (h * l - 1) ^ 2 := by
    rw [hd] at hrhosq ⊢
    nlinarith
  have hidRho : d * (1 - rho ^ 2) = (h - l) ^ 2 := by
    rw [hd] at hrhosq ⊢
    nlinarith
  have hHinside : 0 < 1 - (h * rho) ^ 2 := by
    apply pos_of_mul_pos_left (b := d)
    · have : 0 < d * (1 - (h * rho) ^ 2) := by
        rw [hidH]
        positivity
      simpa [mul_comm] using this
    · exact hdpos.le
  have hRhoInside : 0 < 1 - rho ^ 2 := by
    apply pos_of_mul_pos_left (b := d)
    · have : 0 < d * (1 - rho ^ 2) := by
        rw [hidRho]
        exact sq_pos_of_pos (by linarith)
      simpa [mul_comm] using this
    · exact hdpos.le
  exact ⟨hdpos, hHinside, hRhoInside⟩

private lemma r_corner_threshold_cosine_aux {h l rho d : ℝ}
    (hh : 1 < h) (hl0 : 0 < l) (hl1 : l < 1) (hhl : 1 < h * l)
    (hd : d = h ^ 2 + 1 - 2 * h * l)
    (hrhosq : rho ^ 2 * d = 1 - l ^ 2) :
    √(1 - (h * rho) ^ 2) * √(1 - rho ^ 2) + h * rho ^ 2 = l := by
  obtain ⟨hdpos, hHinside, hRhoInside⟩ :=
    r_corner_threshold_bounds_aux hh hl0 hl1 hhl hd hrhosq
  have hidH : d * (1 - (h * rho) ^ 2) = (h * l - 1) ^ 2 := by
    rw [hd] at hrhosq ⊢
    nlinarith
  have hidRho : d * (1 - rho ^ 2) = (h - l) ^ 2 := by
    rw [hd] at hrhosq ⊢
    nlinarith
  have hsqrtHsq :
      (√(1 - (h * rho) ^ 2) * √d) ^ 2 = (h * l - 1) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hHinside.le, Real.sq_sqrt hdpos.le]
    simpa [mul_comm] using hidH
  have hsqrtH : √(1 - (h * rho) ^ 2) * √d = h * l - 1 :=
    (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by linarith)).1 hsqrtHsq
  have hsqrtRhoSq : (√(1 - rho ^ 2) * √d) ^ 2 = (h - l) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hRhoInside.le, Real.sq_sqrt hdpos.le]
    simpa [mul_comm] using hidRho
  have hsqrtRho : √(1 - rho ^ 2) * √d = h - l :=
    (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by linarith)).1 hsqrtRhoSq
  have hABscaled :
      (√(1 - (h * rho) ^ 2) * √(1 - rho ^ 2)) * d =
        (h * l - 1) * (h - l) := by
    calc
      (√(1 - (h * rho) ^ 2) * √(1 - rho ^ 2)) * d =
          (√(1 - (h * rho) ^ 2) * √(1 - rho ^ 2)) * (√d) ^ 2 := by
            rw [Real.sq_sqrt hdpos.le]
      _ = (√(1 - (h * rho) ^ 2) * √d) * (√(1 - rho ^ 2) * √d) := by ring
      _ = (h * l - 1) * (h - l) := by rw [hsqrtH, hsqrtRho]
  have hcosScaled :
      (√(1 - (h * rho) ^ 2) * √(1 - rho ^ 2) + h * rho ^ 2) * d =
        l * d := by
    rw [add_mul, hABscaled, show h * rho ^ 2 * d = h * (rho ^ 2 * d) by ring,
      hrhosq, hd]
    ring
  exact mul_right_cancel₀ hdpos.ne' hcosScaled

/-- At the exact `h*l > 1` threshold, the upper-left `R`-corner residual vanishes. -/
theorem r_corner_residual_eq_zero_at_threshold {h l rho d : ℝ}
    (hh : 1 < h) (hl0 : 0 < l) (hl1 : l < 1) (hhl : 1 < h * l)
    (hd : d = h ^ 2 + 1 - 2 * h * l) (hrho : 0 < rho)
    (hrhosq : rho ^ 2 * d = 1 - l ^ 2) :
    Real.arcsin (h * rho) + Real.arcsin l - Real.arcsin rho - Real.pi / 2 = 0 := by
  obtain ⟨_hdpos, hHinside, _hRhoInside⟩ :=
    r_corner_threshold_bounds_aux hh hl0 hl1 hhl hd hrhosq
  have harg1 : h * rho < 1 :=
    (sq_lt_one_iff₀ (mul_pos (lt_trans zero_lt_one hh) hrho).le).1 (sub_pos.mp hHinside)
  have hcos := r_corner_threshold_cosine_aux hh hl0 hl1 hhl hd hrhosq
  have hdiff := arcsin_mul_sub_arcsin_eq_arccos_aux hh.le hrho.le harg1.le hcos
  rw [Real.arccos_eq_pi_div_two_sub_arcsin] at hdiff
  linarith

/-- The exact `h*l > 1` threshold lies strictly inside the physical interval. -/
theorem r_corner_threshold_lt_inv {h l rho d : ℝ}
    (hh : 1 < h) (hl0 : 0 < l) (hl1 : l < 1) (hhl : 1 < h * l)
    (hd : d = h ^ 2 + 1 - 2 * h * l) (hrho : 0 < rho)
    (hrhosq : rho ^ 2 * d = 1 - l ^ 2) :
    rho < 1 / h := by
  obtain ⟨_hdpos, hinside, _hRhoInside⟩ :=
    r_corner_threshold_bounds_aux hh hl0 hl1 hhl hd hrhosq
  have hh0 : 0 < h := lt_trans zero_lt_one hh
  have harg1 : h * rho < 1 :=
    (sq_lt_one_iff₀ (mul_pos hh0 hrho).le).1 (sub_pos.mp hinside)
  rw [lt_div_iff₀ hh0]
  nlinarith

/-- The upper-left Type-A `R`-cell corner is negative in the `1 < h*l` branch. -/
theorem r_corner_residual_neg_of_one_lt_mul {h l rho rho0 d : ℝ}
    (hh : 1 < h) (hl0 : 0 < l) (hl1 : l < 1) (hhl : 1 < h * l)
    (hrho0 : 0 ≤ rho) (hrho : rho < rho0)
    (hd : d = h ^ 2 + 1 - 2 * h * l) (hrho0pos : 0 < rho0)
    (hrho0sq : rho0 ^ 2 * d = 1 - l ^ 2) :
    Real.arcsin (h * rho) + Real.arcsin l - Real.arcsin rho - Real.pi / 2 < 0 := by
  have hrho0Upper := r_corner_threshold_lt_inv hh hl0 hl1 hhl hd hrho0pos hrho0sq
  have hzero :=
    r_corner_residual_eq_zero_at_threshold hh hl0 hl1 hhl hd hrho0pos hrho0sq
  have hdiff := strictMonoOn_arcsin_mul_sub_arcsin hh
    ⟨hrho0, (hrho.trans hrho0Upper).le⟩ ⟨hrho0pos.le, hrho0Upper.le⟩ hrho
  dsimp only at hdiff
  linarith

private lemma rho_lt_of_scaled_denominator_aux {rho rho0 r d e L : ℝ}
    (hrho0 : 0 ≤ rho) (hrho0pos : 0 < rho0) (hd : 0 < d) (he : 0 < e)
    (hrhoSq : rho ^ 2 * e = r ^ 2) (hrho0Sq : rho0 ^ 2 * d = L)
    (hscaled : r ^ 2 * d < L * e) :
    rho < rho0 := by
  have hsqScaled : rho ^ 2 * (e * d) < rho0 ^ 2 * (e * d) := by
    calc
      rho ^ 2 * (e * d) = (rho ^ 2 * e) * d := by ring
      _ = r ^ 2 * d := by rw [hrhoSq]
      _ < L * e := hscaled
      _ = (rho0 ^ 2 * d) * e := by rw [hrho0Sq]
      _ = rho0 ^ 2 * (e * d) := by ring
  have hsq := lt_of_mul_lt_mul_right hsqScaled (mul_pos he hd).le
  exact (sq_lt_sq₀ hrho0 hrho0pos.le).1 hsq

private lemma r_corner_rho_lt_inv_aux {p q h r a rho : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hh : 1 < h)
    (hqcrit : p + r * a ≤ q)
    (hwall : h ^ 2 * r ^ 2 + p ^ 2 < (p + r * a) ^ 2)
    (hrho : 0 < rho) (hrhoSq : rho ^ 2 * (q ^ 2 - p ^ 2) = r ^ 2) :
    rho < 1 / h := by
  have hqc0 : 0 < p + r * a := by positivity
  have hq0 : 0 < q := hqc0.trans_le hqcrit
  have hqSq : (p + r * a) ^ 2 ≤ q ^ 2 :=
    (sq_le_sq₀ hqc0.le hq0.le).2 hqcrit
  have hden : 0 < q ^ 2 - p ^ 2 := by nlinarith
  have hbound : h ^ 2 * r ^ 2 < q ^ 2 - p ^ 2 := by nlinarith
  have hscaled :
      (h * rho) ^ 2 * (q ^ 2 - p ^ 2) < 1 * (q ^ 2 - p ^ 2) := by
    calc
      (h * rho) ^ 2 * (q ^ 2 - p ^ 2) =
          h ^ 2 * (rho ^ 2 * (q ^ 2 - p ^ 2)) := by ring
      _ = h ^ 2 * r ^ 2 := by rw [hrhoSq]
      _ < q ^ 2 - p ^ 2 := hbound
      _ = 1 * (q ^ 2 - p ^ 2) := by ring
  have hsquare : (h * rho) ^ 2 < 1 := lt_of_mul_lt_mul_right hscaled hden.le
  have harg0 : 0 < h * rho := mul_pos (lt_trans zero_lt_one hh) hrho
  have harg1 : h * rho < 1 := (sq_lt_one_iff₀ harg0.le).1 hsquare
  rw [lt_div_iff₀ (lt_trans zero_lt_one hh)]
  nlinarith

private lemma critical_scaled_threshold_aux {p h l r a d : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hl : 0 < l) (hl1 : l < 1)
    (hhl : 1 < h * l) (hd : d = h ^ 2 + 1 - 2 * h * l)
    (haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1) :
    r ^ 2 * d < (1 - l ^ 2) * ((p + r * a) ^ 2 - p ^ 2) := by
  have hLa : (1 - l ^ 2) * a ^ 2 = h ^ 2 - 1 := by
    simpa [mul_comm] using haeq
  have hid :
      (1 - l ^ 2) * ((p + r * a) ^ 2 - p ^ 2) - r ^ 2 * d =
        2 * (1 - l ^ 2) * p * r * a + 2 * r ^ 2 * (h * l - 1) := by
    calc
      (1 - l ^ 2) * ((p + r * a) ^ 2 - p ^ 2) - r ^ 2 * d =
          2 * (1 - l ^ 2) * p * r * a +
            r ^ 2 * ((1 - l ^ 2) * a ^ 2 - d) := by ring
      _ = 2 * (1 - l ^ 2) * p * r * a + 2 * r ^ 2 * (h * l - 1) := by
        rw [hLa, hd]
        ring
  rw [← sub_pos, hid]
  have hlSq : l ^ 2 < 1 := (sq_lt_one_iff₀ hl.le).2 hl1
  have hfirst : 0 < 2 * (1 - l ^ 2) * p * r * a := by positivity
  have hsecond : 0 < 2 * r ^ 2 * (h * l - 1) := by positivity
  linarith

private lemma exists_r_corner_threshold_gt_rho_aux {p q h l r a rho : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hl : 0 < l)
    (hl1 : l < 1) (hhl : 1 < h * l)
    (haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1)
    (hqcrit : p + r * a ≤ q) (hrho : 0 < rho)
    (hrhoSq : rho ^ 2 * (q ^ 2 - p ^ 2) = r ^ 2) :
    ∃ d rho0, d = h ^ 2 + 1 - 2 * h * l ∧ 0 < rho0 ∧
      rho0 ^ 2 * d = 1 - l ^ 2 ∧ rho < rho0 := by
  have hqc0 : 0 < p + r * a := by positivity
  have hq0 : 0 < q := hqc0.trans_le hqcrit
  have hqSq : (p + r * a) ^ 2 ≤ q ^ 2 :=
    (sq_le_sq₀ hqc0.le hq0.le).2 hqcrit
  have hden : 0 < q ^ 2 - p ^ 2 := by nlinarith
  let d := h ^ 2 + 1 - 2 * h * l
  have hlSq : l ^ 2 < 1 := (sq_lt_one_iff₀ hl.le).2 hl1
  have hdpos : 0 < d := by
    dsimp only [d]
    nlinarith [sq_nonneg (h - l)]
  let rho0 := √((1 - l ^ 2) / d)
  have hquot : 0 < (1 - l ^ 2) / d := div_pos (sub_pos.mpr hlSq) hdpos
  have hrho0pos : 0 < rho0 := by
    dsimp only [rho0]
    exact Real.sqrt_pos.2 hquot
  have hrho0Sq : rho0 ^ 2 * d = 1 - l ^ 2 := by
    dsimp only [rho0]
    rw [Real.sq_sqrt hquot.le]
    field_simp
  have hcritical := critical_scaled_threshold_aux hp hr ha hl hl1 hhl rfl haeq
  have hdenLe : (p + r * a) ^ 2 - p ^ 2 ≤ q ^ 2 - p ^ 2 := by linarith
  have hscaled : r ^ 2 * d < (1 - l ^ 2) * (q ^ 2 - p ^ 2) :=
    hcritical.trans_le (mul_le_mul_of_nonneg_left hdenLe (sub_pos.mpr hlSq).le)
  have hrhoLt := rho_lt_of_scaled_denominator_aux hrho.le hrho0pos hdpos hden
    hrhoSq hrho0Sq hscaled
  exact ⟨d, rho0, rfl, hrho0pos, hrho0Sq, hrhoLt⟩

/-- Failure of the scalar `X` test forces the upper-left Type-A `R`-cell
corner residual to be strictly negative. -/
theorem r_corner_residual_neg_of_failure {p q h l r a s rho : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hs : 0 < s) (hsp : s < p)
    (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1)
    (hseq : s ^ 2 * (1 + a ^ 2) = 1)
    (hqcrit : p + r * a ≤ q) (hrho : 0 < rho)
    (hrhoSq : rho ^ 2 * (q ^ 2 - p ^ 2) = r ^ 2) :
    Real.arcsin (h * rho) + Real.arcsin l - Real.arcsin rho - Real.pi / 2 < 0 := by
  have hwall := critical_hWall_pos hp hr ha hs hsp hh hl hl1 hrsq haeq hseq
  by_cases hhl : h * l ≤ 1
  · have hrhoInv := r_corner_rho_lt_inv_aux hp hr ha hh hqcrit hwall hrho hrhoSq
    exact r_corner_residual_neg_of_mul_le_one hh hrho.le hrhoInv hhl
  · have hhl' : 1 < h * l := lt_of_not_ge hhl
    obtain ⟨d, rho0, hd, hrho0, hrho0Sq, hrhoLt⟩ :=
      exists_r_corner_threshold_gt_rho_aux hp hr ha hl hl1 hhl' haeq hqcrit
        hrho hrhoSq
    exact r_corner_residual_neg_of_one_lt_mul hh hl hl1 hhl' hrho.le hrhoLt
      hd hrho0 hrho0Sq

/-! ## The complementary bottom-right corner -/

/-- A nonnegative bottom-right `R`-corner residual forces `sigma < p`.
Only the strict physical upper bound on the other inverse-sine argument is
needed for this first part of equation (21). -/
theorem sigma_lt_p_of_r_corner_residual_nonneg {p t sigma : ℝ}
    (htsigma1 : t * sigma < 1)
    (hB :
      0 ≤ Real.arcsin p + Real.arcsin (t * sigma) -
        Real.pi / 2 - Real.arcsin sigma) :
    sigma < p := by
  by_contra hnot
  have hpSigma : p ≤ sigma := le_of_not_gt hnot
  have hangle := Real.arcsin_le_arcsin hpSigma
  have htAngle : Real.arcsin (t * sigma) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.2 htsigma1
  linarith

private lemma raw_critical_tc_le_of_r_corner_residual_nonneg {p t sigma : ℝ}
    (hp1 : p < 1) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (htsigma : 0 ≤ t * sigma) (htsigma1 : t * sigma < 1)
    (hB :
      0 ≤ Real.arcsin p + Real.arcsin (t * sigma) -
        Real.pi / 2 - Real.arcsin sigma) :
    p + √(1 - p ^ 2) * (√(1 - sigma ^ 2) / sigma) ≤ t := by
  have hsigmaP := sigma_lt_p_of_r_corner_residual_nonneg htsigma1 hB
  have hpAngle : Real.arcsin p < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.2 hp1
  have hsigmaAngle : 0 < Real.arcsin sigma := Real.arcsin_pos.2 hsigma
  have hangleStrict : Real.arcsin sigma < Real.arcsin p :=
    Real.arcsin_lt_arcsin (by linarith) hsigmaP hp1.le
  have hdeltaMem :
      Real.pi / 2 + Real.arcsin sigma - Real.arcsin p ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have htsigmaMem : t * sigma ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith
  have hdelta :
      Real.pi / 2 + Real.arcsin sigma - Real.arcsin p ≤
        Real.arcsin (t * sigma) := by
    linarith
  have hsin := (Real.le_arcsin_iff_sin_le hdeltaMem htsigmaMem).1 hdelta
  have hsinIdentity :
      Real.sin (Real.pi / 2 + Real.arcsin sigma - Real.arcsin p) =
        √(1 - p ^ 2) * √(1 - sigma ^ 2) + p * sigma := by
    rw [show Real.pi / 2 + Real.arcsin sigma - Real.arcsin p =
      Real.pi / 2 - (Real.arcsin p - Real.arcsin sigma) by ring]
    rw [Real.sin_pi_div_two_sub, Real.cos_sub, Real.cos_arcsin,
      Real.cos_arcsin, Real.sin_arcsin (by linarith) hp1.le,
      Real.sin_arcsin (by linarith) hsigma1.le]
  rw [hsinIdentity] at hsin
  have hproduct :
      √(1 - p ^ 2) * √(1 - sigma ^ 2) ≤ (t - p) * sigma := by
    nlinarith
  have hquotient :
      √(1 - p ^ 2) * √(1 - sigma ^ 2) / sigma ≤ t - p :=
    (div_le_iff₀ hsigma).2 hproduct
  calc
    p + √(1 - p ^ 2) * (√(1 - sigma ^ 2) / sigma) =
        p + √(1 - p ^ 2) * √(1 - sigma ^ 2) / sigma := by ring
    _ ≤ t := by linarith

/-- A nonnegative bottom-right `R`-corner residual forces the sharp
normalized bound `p + r * (z / x) ≤ t`, where `r`, `x`, and `z` are the
positive square roots of `1-p^2`, `1-l^2`, and `q^2-1`. This is equation
(21) of the Type-A three-cell cover. -/
theorem critical_tc_le_of_r_corner_residual_nonneg
    {p q l t sigma r x z : ℝ}
    (hp1 : p < 1) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (htsigma : 0 ≤ t * sigma) (htsigma1 : t * sigma < 1)
    (hr : 0 < r) (hx : 0 < x) (hz : 0 < z)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (hxsq : x ^ 2 = 1 - l ^ 2)
    (hzsq : z ^ 2 = q ^ 2 - 1)
    (hsigmaSq : sigma ^ 2 * (q ^ 2 - l ^ 2) = 1 - l ^ 2)
    (hB :
      0 ≤ Real.arcsin p + Real.arcsin (t * sigma) -
        Real.pi / 2 - Real.arcsin sigma) :
    p + r * (z / x) ≤ t := by
  have hraw := raw_critical_tc_le_of_r_corner_residual_nonneg hp1 hsigma
    hsigma1 htsigma htsigma1 hB
  have hrSqrt : √(1 - p ^ 2) = r := by
    rw [← hrsq, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hsigmaInside : 0 ≤ 1 - sigma ^ 2 := by
    nlinarith [sq_nonneg sigma]
  have hsquareIdentity :
      x ^ 2 * (1 - sigma ^ 2) = (sigma * z) ^ 2 := by
    rw [hxsq, mul_pow, hzsq]
    nlinarith [hsigmaSq]
  have hrootSquare :
      (x * √(1 - sigma ^ 2)) ^ 2 = (sigma * z) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hsigmaInside]
    exact hsquareIdentity
  have hrootIdentity : x * √(1 - sigma ^ 2) = sigma * z :=
    (sq_eq_sq₀ (by positivity) (by positivity)).1 hrootSquare
  have hratio : √(1 - sigma ^ 2) / sigma = z / x := by
    apply (div_eq_div_iff hsigma.ne' hx.ne').2
    simpa [mul_comm] using hrootIdentity
  rwa [hrSqrt, hratio] at hraw

/-- The complete complementary-sign transfer into the scalar `M` cell:
a nonnegative bottom-right `R`-corner residual puts `t` strictly above the
normalized inward `h` wall. This composes equations (21) and (28). -/
theorem fallback_core_lt_t_of_r_corner_residual_nonneg
    {p p0 q t sigma r0 r x a zc z h l : ℝ}
    (hp0def : p0 = (1 + h * l) / (h + l))
    (hp0p : p0 ≤ p) (hp1 : p < 1)
    (hr0 : 0 < r0) (hr : 0 < r) (hx : 0 < x)
    (ha : 0 < a) (hzc : 0 < zc) (hz : 0 < z)
    (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (htsigma : 0 ≤ t * sigma) (htsigma1 : t * sigma < 1)
    (hcircle : p0 ^ 2 + r0 ^ 2 = 1)
    (hp0critical : p0 + r0 * a = h)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (hxsq : x ^ 2 = 1 - l ^ 2)
    (hax : x ^ 2 * a ^ 2 = h ^ 2 - 1)
    (hzcSq : zc ^ 2 = (p + r * a) ^ 2 - 1)
    (hzSq : z ^ 2 = q ^ 2 - 1)
    (hsigmaSq : sigma ^ 2 * (q ^ 2 - l ^ 2) = 1 - l ^ 2)
    (hwall : h ^ 2 * r ^ 2 + p ^ 2 < (p + r * a) ^ 2)
    (hqcrit : p + r * a ≤ q)
    (hB :
      0 ≤ Real.arcsin p + Real.arcsin (t * sigma) -
        Real.pi / 2 - Real.arcsin sigma) :
    (h ^ 2 * r ^ 2 + p ^ 2 * l ^ 2) / h < t := by
  have hcoreCritical := critical_tc_gt_fallbackCore hp0def hp0p hp1.le hr0
    hr hx ha hzc hh hl hl1 hcircle hp0critical hrsq hax hzcSq hwall
  have hcriticalQ := critical_tc_le_of_r_corner_residual_nonneg hp1 hsigma
    hsigma1 htsigma htsigma1 hr hx hz hrsq hxsq hzSq hsigmaSq hB
  have hqc0 : 0 < p + r * a := by nlinarith [mul_pos hr ha]
  have hq0 : 0 < q := hqc0.trans_le hqcrit
  have hqSq : (p + r * a) ^ 2 ≤ q ^ 2 :=
    (sq_le_sq₀ hqc0.le hq0.le).2 hqcrit
  have hzcLe : zc ≤ z := by
    apply (sq_le_sq₀ hzc.le hz.le).1
    rw [hzcSq, hzSq]
    linarith
  have hcriticalMono : p + r * (zc / x) ≤ p + r * (z / x) := by
    simpa [add_comm] using
      add_le_add_left
        (mul_le_mul_of_nonneg_left
          ((div_le_div_iff_of_pos_right hx).2 hzcLe) hr.le) p
  exact hcoreCritical.trans_le (hcriticalMono.trans hcriticalQ)

end Gluck.Discrete.N6TypeAThreeCell
