import Gluck.Discrete.NativeOppositePureDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The pure-one wall of the native first-pair construction

The convention is: `α, β` are the pure-one half-angles, and `γ, δ`
are the pure-`q` half-angles. This file constructs the acute `δ` chart
on `α = π / 2`. It does not yet assert the global realization theorem.
-/

namespace Gluck.Discrete.NativeOppositePure

open scoped Real

noncomputable def wallN (p t q γ : ℝ) : ℝ :=
  Real.sqrt (1 - p ^ 2) * Real.sqrt (q ^ 2 - t ^ 2 * Real.sin γ ^ 2) +
    (1 - p * t) * Real.sin γ

noncomputable def wallD (p t q γ : ℝ) : ℝ :=
  p * Real.sqrt (q ^ 2 - t ^ 2 * Real.sin γ ^ 2) +
    t * Real.sqrt (1 - p ^ 2) * Real.sin γ - Real.cos γ

noncomputable def wallDelta (p t q γ : ℝ) : ℝ :=
  Real.arctan (wallN p t q γ / wallD p t q γ)

noncomputable def wallBeta (p t q γ : ℝ) : ℝ :=
  Real.pi - wallDelta p t q γ - Real.arcsin p -
    Real.arcsin ((t / q) * Real.sin γ)

private lemma wall_q_pos {p q : ℝ} (hp : 0 < p) (hpq : 1 < p * q) : 0 < q :=
  pos_of_mul_pos_right (lt_trans zero_lt_one hpq) hp.le

private lemma wall_one_lt_q {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpq : 1 < p * q) : 1 < q := by
  have hq := wall_q_pos hp hpq
  calc
    1 < p * q := hpq
    _ < 1 * q := mul_lt_mul_of_pos_right hp1 hq
    _ = q := one_mul q

lemma wall_radicand_pos {p t q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q) (γ : ℝ) :
    0 < q ^ 2 - t ^ 2 * Real.sin γ ^ 2 := by
  have hq := wall_one_lt_q hp hp1 hpq
  have htq : t < q := (mul_lt_mul_iff_right₀ hp).mp (hpt.trans hpq)
  have hs : Real.sin γ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq γ, sq_nonneg (Real.cos γ)]
  have hm : t ^ 2 * Real.sin γ ^ 2 ≤ t ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg t) hs
  have hsq : t ^ 2 < q ^ 2 := by nlinarith
  linarith

lemma wallN_pos {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) : 0 < wallN p t q γ := by
  have hU : 0 < 1 - p ^ 2 := by nlinarith
  have hR := wall_radicand_pos hp hp1 ht hpt hpq γ
  have hs : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0
    (hγ1.trans (by linarith [Real.pi_pos]))
  exact add_pos_of_pos_of_nonneg
    (mul_pos (Real.sqrt_pos.2 hU) (Real.sqrt_pos.2 hR))
    (mul_nonneg (sub_pos.mpr hpt).le hs)

lemma wallD_pos {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) : 0 < wallD p t q γ := by
  have hR := wall_radicand_pos hp hp1 ht hpt hpq γ
  have hs : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0
    (hγ1.trans (by linarith [Real.pi_pos]))
  have hpq2 : 1 < p ^ 2 * q ^ 2 := by nlinarith [sq_nonneg (p * q - 1)]
  have hpt2 : p ^ 2 * t ^ 2 < 1 := by nlinarith [mul_pos hp ht]
  have hgap : Real.cos γ ^ 2 <
      (p * Real.sqrt (q ^ 2 - t ^ 2 * Real.sin γ ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hR.le]
    nlinarith [Real.sin_sq_add_cos_sq γ,
      mul_nonneg (show 0 ≤ 1 - p ^ 2 * t ^ 2 by linarith) (sq_nonneg (Real.sin γ))]
  have hlead : Real.cos γ < p * Real.sqrt (q ^ 2 - t ^ 2 * Real.sin γ ^ 2) := by
    have hh := mul_pos hp (Real.sqrt_pos.2 hR)
    nlinarith
  have hrest : 0 ≤ t * Real.sqrt (1 - p ^ 2) * Real.sin γ := by positivity
  unfold wallD
  linarith

lemma wallDelta_pos {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) : 0 < wallDelta p t q γ := by
  exact Real.arctan_pos.2 (div_pos (wallN_pos hp hp1 ht hpt hpq hγ0 hγ1)
    (wallD_pos hp hp1 ht hpt hpq hγ0 hγ1))

lemma wallDelta_lt_pi_div_two (p t q γ : ℝ) : wallDelta p t q γ < Real.pi / 2 :=
  Real.arctan_lt_pi_div_two _

@[simp] lemma wallN_zero {p t q : ℝ} (hq : 0 ≤ q) :
    wallN p t q 0 = q * Real.sqrt (1 - p ^ 2) := by
  simp [wallN, Real.sqrt_sq hq, mul_comm]

@[simp] lemma wallD_zero {p t q : ℝ} (hq : 0 ≤ q) :
    wallD p t q 0 = p * q - 1 := by
  simp [wallD, Real.sqrt_sq hq]

lemma wall_initial_norm (p q : ℝ) :
    (p * q - 1) ^ 2 + q ^ 2 * (1 - p ^ 2) = q ^ 2 - 2 * p * q + 1 := by
  ring

private lemma sqrt_one_add_div_sq {n d : ℝ} (hd : 0 < d) :
    Real.sqrt (1 + (n / d) ^ 2) = Real.sqrt (n ^ 2 + d ^ 2) / d := by
  have heq : 1 + (n / d) ^ 2 = (n ^ 2 + d ^ 2) / d ^ 2 := by
    field_simp
    ring
  rw [heq, Real.sqrt_div (by positivity), Real.sqrt_sq hd.le]

lemma sin_arctan_div_pos {n d : ℝ} (hd : 0 < d) :
    Real.sin (Real.arctan (n / d)) = n / Real.sqrt (n ^ 2 + d ^ 2) := by
  rw [Real.sin_arctan, sqrt_one_add_div_sq hd, div_div_eq_mul_div,
    div_mul_cancel₀ _ hd.ne']

lemma cos_arctan_div_pos {n d : ℝ} (hd : 0 < d) :
    Real.cos (Real.arctan (n / d)) = d / Real.sqrt (n ^ 2 + d ^ 2) := by
  rw [Real.cos_arctan, sqrt_one_add_div_sq hd, one_div_div]

lemma wall_initial_norm_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < q ^ 2 - 2 * p * q + 1 := by
  nlinarith [sq_nonneg (q - p)]

lemma sin_wallDelta_zero {p t q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpq : 1 < p * q) :
    Real.sin (wallDelta p t q 0) =
      q * Real.sqrt (1 - p ^ 2) / Real.sqrt (q ^ 2 - 2 * p * q + 1) := by
  have hq := wall_q_pos hp hpq
  have hU : 0 ≤ 1 - p ^ 2 := by nlinarith
  have hnorm : (q * Real.sqrt (1 - p ^ 2)) ^ 2 + (p * q - 1) ^ 2 =
      q ^ 2 - 2 * p * q + 1 := by
    rw [mul_pow, Real.sq_sqrt hU]
    ring
  unfold wallDelta
  rw [wallN_zero hq.le, wallD_zero hq.le,
    sin_arctan_div_pos (sub_pos.mpr hpq), hnorm]

lemma cos_wallDelta_zero {p t q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpq : 1 < p * q) :
    Real.cos (wallDelta p t q 0) =
      (p * q - 1) / Real.sqrt (q ^ 2 - 2 * p * q + 1) := by
  have hq := wall_q_pos hp hpq
  have hU : 0 ≤ 1 - p ^ 2 := by nlinarith
  have hnorm : (q * Real.sqrt (1 - p ^ 2)) ^ 2 + (p * q - 1) ^ 2 =
      q ^ 2 - 2 * p * q + 1 := by
    rw [mul_pow, Real.sq_sqrt hU]
    ring
  unfold wallDelta
  rw [wallN_zero hq.le, wallD_zero hq.le,
    cos_arctan_div_pos (sub_pos.mpr hpq), hnorm]

lemma sin_wallBeta_zero {p t q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpq : 1 < p * q) :
    Real.sin (wallBeta p t q 0) =
      (q - p) / Real.sqrt (q ^ 2 - 2 * p * q + 1) := by
  have hU : 0 ≤ 1 - p ^ 2 := by nlinarith
  have hZ := Real.sqrt_pos.2 (wall_initial_norm_pos (q := q) hp hp1)
  have hb : wallBeta p t q 0 = Real.pi - (wallDelta p t q 0 + Real.arcsin p) := by
    simp only [wallBeta, Real.sin_zero, mul_zero, Real.arcsin_zero, sub_zero]
    ring
  rw [hb, Real.sin_pi_sub, Real.sin_add, Real.cos_arcsin,
    Real.sin_arcsin (by linarith) hp1.le,
    sin_wallDelta_zero hp hp1 hpq, cos_wallDelta_zero hp hp1 hpq]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  congr 1
  linear_combination q * Real.sq_sqrt hU

lemma cos_wallBeta_zero {p t q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpq : 1 < p * q) :
    Real.cos (wallBeta p t q 0) =
      Real.sqrt (1 - p ^ 2) / Real.sqrt (q ^ 2 - 2 * p * q + 1) := by
  have hZ := Real.sqrt_pos.2 (wall_initial_norm_pos (q := q) hp hp1)
  have hb : wallBeta p t q 0 = Real.pi - (wallDelta p t q 0 + Real.arcsin p) := by
    simp only [wallBeta, Real.sin_zero, mul_zero, Real.arcsin_zero, sub_zero]
    ring
  rw [hb, Real.cos_pi_sub, Real.cos_add, Real.cos_arcsin,
    Real.sin_arcsin (by linarith) hp1.le,
    sin_wallDelta_zero hp hp1 hpq, cos_wallDelta_zero hp hp1 hpq]
  field_simp
  ring

lemma wall_initial_hwall {p t q h l : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpq : 1 < p * q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hflag : (1 - p ^ 2) * (h ^ 2 - 1) ≤ (1 - l ^ 2) * (q - p) ^ 2) :
    (h / q) * Real.sin (wallDelta p t q 0) < 1 := by
  have hq := wall_q_pos hp hpq
  have hU : 0 < 1 - p ^ 2 := by nlinarith
  have hL : 0 < 1 - l ^ 2 := by nlinarith
  have hH : 0 < h ^ 2 - 1 := by nlinarith
  have hmargin : 0 < (1 - l ^ 2) *
      (q ^ 2 - 2 * p * q + 1 - h ^ 2 * (1 - p ^ 2)) := by
    calc
      _ = ((1 - l ^ 2) * (q - p) ^ 2 - (1 - p ^ 2) * (h ^ 2 - 1)) +
          l ^ 2 * (1 - p ^ 2) * (h ^ 2 - 1) := by ring
      _ > 0 := add_pos_of_nonneg_of_pos (sub_nonneg.mpr hflag) (by positivity)
  have hgap := pos_of_mul_pos_right hmargin hL.le
  have hZ := Real.sqrt_pos.2 (wall_initial_norm_pos (q := q) hp hp1)
  have hlt : h * Real.sqrt (1 - p ^ 2) < Real.sqrt (q ^ 2 - 2 * p * q + 1) := by
    have hsU := Real.sq_sqrt hU.le
    have hsZ := Real.sq_sqrt (wall_initial_norm_pos (q := q) hp hp1).le
    have hprod : 0 ≤ h * Real.sqrt (1 - p ^ 2) := by positivity
    nlinarith
  rw [sin_wallDelta_zero hp hp1 hpq]
  have heq : h / q * (q * Real.sqrt (1 - p ^ 2) /
      Real.sqrt (q ^ 2 - 2 * p * q + 1)) =
      h * Real.sqrt (1 - p ^ 2) / Real.sqrt (q ^ 2 - 2 * p * q + 1) := by
    field_simp
  rw [heq]
  exact (div_lt_one hZ).2 hlt

lemma arcsin_add_arcsin_le_half_pi {x y : ℝ} (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) :
    Real.arcsin x + Real.arcsin y ≤ Real.pi / 2 := by
  have hxroot : x ≤ Real.sqrt (1 - y ^ 2) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hmono := Real.monotone_arcsin hxroot
  rw [← Real.arccos_eq_arcsin hy, Real.arccos_eq_pi_div_two_sub_arcsin] at hmono
  linarith

lemma wall_initial_high_nonpos {p t q h l : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpq : 1 < p * q) (hh : 0 < h) (hl : 0 < l)
    (hflag : (1 - p ^ 2) * (h ^ 2 - 1) ≤ (1 - l ^ 2) * (q - p) ^ 2) :
    seamHigh q h l (Real.pi / 2) (wallBeta p t q 0) 0 (wallDelta p t q 0) ≤ 0 := by
  have hq := wall_q_pos hp hpq
  have hq1 := wall_one_lt_q hp hp1 hpq
  have hqp : 0 < q - p := by linarith
  have hU : 0 ≤ 1 - p ^ 2 := by nlinarith
  have hZ := wall_initial_norm_pos (q := q) hp hp1
  have hsZ := Real.sqrt_pos.2 hZ
  have hx : 0 ≤ h * Real.sqrt (1 - p ^ 2) / Real.sqrt (q ^ 2 - 2 * p * q + 1) :=
    by positivity
  have hy : 0 ≤ l * (q - p) / Real.sqrt (q ^ 2 - 2 * p * q + 1) := by positivity
  have hsq : (h * Real.sqrt (1 - p ^ 2) / Real.sqrt (q ^ 2 - 2 * p * q + 1)) ^ 2 +
      (l * (q - p) / Real.sqrt (q ^ 2 - 2 * p * q + 1)) ^ 2 ≤ 1 := by
    rw [div_pow, div_pow, ← add_div, Real.sq_sqrt hZ.le]
    apply (div_le_one hZ).2
    rw [mul_pow, Real.sq_sqrt hU]
    nlinarith [hflag]
  have hangle := arcsin_add_arcsin_le_half_pi hx hy hsq
  have hxEq : h / q * Real.sin (wallDelta p t q 0) =
      h * Real.sqrt (1 - p ^ 2) / Real.sqrt (q ^ 2 - 2 * p * q + 1) := by
    rw [sin_wallDelta_zero hp hp1 hpq]
    field_simp
  have hyEq : l * Real.sin (wallBeta p t q 0) =
      l * (q - p) / Real.sqrt (q ^ 2 - 2 * p * q + 1) := by
    rw [sin_wallBeta_zero hp hp1 hpq, mul_div_assoc]
  unfold seamHigh highTurn angleAtom
  rw [hxEq, hyEq]
  linarith

private lemma wall_arcsin_arg_mem {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    (t / q) * Real.sin γ ∈ Set.Icc (-1 : ℝ) 1 := by
  have hq := wall_q_pos hp hpq
  have hq1 := wall_one_lt_q hp hp1 hpq
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hγ0
    (hγ1.trans (by linarith [Real.pi_pos]))
  have htq : t < q := (mul_lt_mul_iff_right₀ hp).mp (hpt.trans hpq)
  have hr : 0 < t / q := div_pos ht hq
  have hr1 : t / q < 1 := (div_lt_one hq).2 htq
  constructor
  · have : 0 ≤ (t / q) * Real.sin γ := mul_nonneg hr.le hs
    linarith
  · calc
      (t / q) * Real.sin γ ≤ (t / q) * 1 :=
        mul_le_mul_of_nonneg_left (Real.sin_le_one γ) hr.le
      _ ≤ 1 := by simpa using hr1.le

private lemma wall_sqrt_ratio {p t q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q) (γ : ℝ) :
    Real.sqrt (1 - ((t / q) * Real.sin γ) ^ 2) =
      Real.sqrt (q ^ 2 - t ^ 2 * Real.sin γ ^ 2) / q := by
  have hq := wall_q_pos hp hpq
  have hR := wall_radicand_pos hp hp1 ht hpt hpq γ
  have heq : 1 - ((t / q) * Real.sin γ) ^ 2 =
      (q ^ 2 - t ^ 2 * Real.sin γ ^ 2) / q ^ 2 := by
    field_simp
  rw [heq, Real.sqrt_div hR.le, Real.sqrt_sq hq.le]

lemma wallD_eq_trig {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    wallD p t q γ = q * Real.sin (lowTurn p t q (Real.pi / 2) γ) - Real.cos γ := by
  have hq := wall_q_pos hp hpq
  have ha := wall_arcsin_arg_mem hp hp1 ht hpt hpq hγ0 hγ1
  unfold lowTurn angleAtom wallD
  rw [Real.sin_pi_div_two, mul_one, Real.sin_add,
    Real.sin_arcsin (by linarith) hp1.le, Real.cos_arcsin, Real.cos_arcsin,
    Real.sin_arcsin ha.1 ha.2, wall_sqrt_ratio hp hp1 ht hpt hpq]
  field_simp

lemma wallN_eq_trig {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    wallN p t q γ = q * Real.cos (lowTurn p t q (Real.pi / 2) γ) + Real.sin γ := by
  have hq := wall_q_pos hp hpq
  have ha := wall_arcsin_arg_mem hp hp1 ht hpt hpq hγ0 hγ1
  unfold lowTurn angleAtom wallN
  rw [Real.sin_pi_div_two, mul_one, Real.cos_add,
    Real.sin_arcsin (by linarith) hp1.le, Real.cos_arcsin, Real.cos_arcsin,
    Real.sin_arcsin ha.1 ha.2, wall_sqrt_ratio hp hp1 ht hpt hpq]
  field_simp
  ring

lemma wall_seamLow (p t q γ : ℝ) :
    seamLow p t q (Real.pi / 2) (wallBeta p t q γ) γ (wallDelta p t q γ) = 0 := by
  simp only [seamLow, lowTurn, angleAtom, wallBeta, Real.sin_pi_div_two, mul_one]
  ring

lemma wall_chord {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    chord q (Real.pi / 2) (wallBeta p t q γ) γ (wallDelta p t q γ) = 0 := by
  have hq := wall_q_pos hp hpq
  have hD := wallD_pos hp hp1 ht hpt hpq hγ0 hγ1
  have hlow : wallBeta p t q γ = Real.pi -
      (wallDelta p t q γ + lowTurn p t q (Real.pi / 2) γ) := by
    simp only [wallBeta, lowTurn, angleAtom, Real.sin_pi_div_two, mul_one]
    ring
  have hzero : wallD p t q γ * Real.sin (wallDelta p t q γ) -
      wallN p t q γ * Real.cos (wallDelta p t q γ) = 0 := by
    unfold wallDelta
    rw [sin_arctan_div_pos hD, cos_arctan_div_pos hD]
    ring
  rw [wallD_eq_trig hp hp1 ht hpt hpq hγ0 hγ1,
    wallN_eq_trig hp hp1 ht hpt hpq hγ0 hγ1] at hzero
  unfold chord
  rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  simp only [one_mul, zero_mul, add_zero]
  rw [hlow, Real.cos_pi_sub, Real.cos_add, Real.sin_add]
  apply mul_left_cancel₀ hq.ne'
  field_simp
  nlinarith

lemma continuous_wallN (p t q : ℝ) : Continuous (wallN p t q) := by
  unfold wallN
  fun_prop

lemma continuous_wallD (p t q : ℝ) : Continuous (wallD p t q) := by
  unfold wallD
  fun_prop

lemma continuousOn_wallDelta {p t q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q) :
    ContinuousOn (wallDelta p t q) (Set.Icc 0 (Real.pi / 2)) := by
  unfold wallDelta
  apply Real.continuous_arctan.comp_continuousOn
  exact (continuous_wallN p t q).continuousOn.div (continuous_wallD p t q).continuousOn
    (fun γ hγ => (wallD_pos hp hp1 ht hpt hpq hγ.1 hγ.2).ne')

lemma continuousOn_wallBeta {p t q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q) :
    ContinuousOn (wallBeta p t q) (Set.Icc 0 (Real.pi / 2)) := by
  have hδ := continuousOn_wallDelta hp hp1 ht hpt hpq
  unfold wallBeta
  fun_prop

lemma wallBeta_zero_pos {p t q : ℝ} (hp1 : p < 1) :
    0 < wallBeta p t q 0 := by
  have hδ := wallDelta_lt_pi_div_two p t q 0
  have hp := Real.arcsin_lt_pi_div_two.2 hp1
  simp only [wallBeta, Real.sin_zero, mul_zero, Real.arcsin_zero, sub_zero]
  linarith

lemma wallBeta_ne_zero {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) : wallBeta p t q γ ≠ 0 := by
  intro hb
  have hc := wall_chord hp hp1 ht hpt hpq hγ0 hγ1
  have hq := wall_q_pos hp hpq
  have hq1 := wall_one_lt_q hp hp1 hpq
  unfold chord at hc
  rw [hb, add_zero, Real.sin_pi_div_two] at hc
  have he : Real.sin (γ + wallDelta p t q γ) = q := by
    apply (div_eq_one_iff_eq hq.ne').1
    linarith
  have hs := Real.sin_le_one (γ + wallDelta p t q γ)
  linarith

lemma wallBeta_pos {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) : 0 < wallBeta p t q γ := by
  by_contra hb
  have hbn : wallBeta p t q γ ≤ 0 := le_of_not_gt hb
  have hcont : ContinuousOn (wallBeta p t q) (Set.Icc 0 γ) :=
    (continuousOn_wallBeta hp hp1 ht hpt hpq).mono
      (fun _ hx => ⟨hx.1, hx.2.trans hγ1⟩)
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc' hγ0 hcont
    (show 0 ∈ Set.Icc (wallBeta p t q γ) (wallBeta p t q 0) from
      ⟨hbn, (wallBeta_zero_pos (t := t) (q := q) hp1).le⟩)
  exact wallBeta_ne_zero hp hp1 ht hpt hpq hx.1 (hx.2.trans hγ1) he

lemma wallBeta_lt_pi_div_two {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) : wallBeta p t q γ < Real.pi / 2 := by
  have hδ0 := wallDelta_pos hp hp1 ht hpt hpq hγ0 hγ1
  have hδ1 := wallDelta_lt_pi_div_two p t q γ
  have hq := wall_q_pos hp hpq
  have hsγ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0
    (hγ1.trans (by linarith [Real.pi_pos]))
  have hpangle := Real.arcsin_pos.2 hp
  have htangle : 0 ≤ Real.arcsin ((t / q) * Real.sin γ) :=
    Real.arcsin_nonneg.2 (mul_nonneg (div_pos ht hq).le hsγ)
  have hbpi : wallBeta p t q γ < Real.pi := by
    unfold wallBeta
    linarith
  have hs : 0 < Real.sin (γ + wallDelta p t q γ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc := wall_chord hp hp1 ht hpt hpq hγ0 hγ1
  unfold chord at hc
  rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two] at hc
  simp only [one_mul, zero_mul, add_zero] at hc
  have hcos : 0 < Real.cos (wallBeta p t q γ) := by
    have := div_pos hs hq
    linarith
  by_contra hb
  have := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt hb)
    (show wallBeta p t q γ ≤ Real.pi + Real.pi / 2 by linarith [Real.pi_pos])
  linarith

/-- A continuous path reaches a positive residual before its first physical wall. -/
lemma exists_positive_before_first_wall {f g : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hf : ContinuousOn f (Set.Icc 0 b)) (hg : ContinuousOn g (Set.Icc 0 b))
    (hf0 : f 0 < 1) (hgb : 0 < g b)
    (hwall : ∀ x ∈ Set.Icc 0 b, f x = 1 → 0 < g x) :
    ∃ c ∈ Set.Ioo 0 b, (∀ x ∈ Set.Icc 0 c, f x < 1) ∧ 0 < g c := by
  have hex : ∃ e, 0 < e ∧ e ≤ b ∧
      (∀ x ∈ Set.Ico 0 e, f x < 1) ∧ 0 < g e := by
    let s := Set.Icc 0 b ∩ f ⁻¹' ({1} : Set ℝ)
    have hsclosed : IsClosed s :=
      hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hscompact : IsCompact s :=
      isCompact_Icc.of_isClosed_subset hsclosed Set.inter_subset_left
    by_cases hs : s.Nonempty
    · obtain ⟨e, he⟩ := hscompact.exists_isLeast hs
      have heb : e ∈ Set.Icc 0 b := he.1.1
      have hfe : f e = 1 := he.1.2
      have he0 : 0 < e := by
        by_contra hh
        have hez : e = 0 := le_antisymm (le_of_not_gt hh) heb.1
        rw [hez] at hfe
        linarith
      refine ⟨e, he0, heb.2, ?_, hwall e heb hfe⟩
      intro x hx
      by_contra hh
      have hfx : 1 ≤ f x := le_of_not_gt hh
      have hcont : ContinuousOn f (Set.Icc 0 x) :=
        hf.mono (fun _ hy => ⟨hy.1, hy.2.trans (hx.2.le.trans heb.2)⟩)
      obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc hx.1 hcont
        (show 1 ∈ Set.Icc (f 0) (f x) from ⟨hf0.le, hfx⟩)
      have hes : e ≤ z := he.2 ⟨⟨hz.1, hz.2.trans (hx.2.le.trans heb.2)⟩, hfz⟩
      linarith [hz.2, hx.2]
    · refine ⟨b, hb, le_rfl, ?_, hgb⟩
      intro x hx
      by_contra hh
      have hfx : 1 ≤ f x := le_of_not_gt hh
      have hcont : ContinuousOn f (Set.Icc 0 x) :=
        hf.mono (fun _ hy => ⟨hy.1, hy.2.trans hx.2.le⟩)
      obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc hx.1 hcont
        (show 1 ∈ Set.Icc (f 0) (f x) from ⟨hf0.le, hfx⟩)
      exact hs ⟨z, ⟨⟨hz.1, hz.2.trans hx.2.le⟩, hfz⟩⟩
  obtain ⟨e, he0, heb, hpre, hge⟩ := hex
  obtain ⟨d, hd, hnear⟩ := Metric.continuousWithinAt_iff.1
    (hg e ⟨he0.le, heb⟩) (g e) hge
  obtain ⟨c, hc0, hce⟩ := exists_between
    (show max 0 (e - d) < e from max_lt_iff.2 ⟨he0, by linarith⟩)
  have hcpos : 0 < c := lt_of_le_of_lt (le_max_left _ _) hc0
  have hcb : c < b := hce.trans_le heb
  have hcd : dist c e < d := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.2 hce)]
    have : e - d < c := lt_of_le_of_lt (le_max_right _ _) hc0
    linarith
  have hgc := hnear ⟨hcpos.le, hcb.le⟩ hcd
  rw [Real.dist_eq, abs_lt] at hgc
  refine ⟨c, ⟨hcpos, hcb⟩, ?_, ?_⟩
  · intro x hx
    exact hpre x ⟨hx.1, hx.2.trans_lt hce⟩
  · linarith [hgc.1]

lemma continuousOn_wall_hargument {p t q h : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q) :
    ContinuousOn (fun γ => (h / q) * Real.sin (wallDelta p t q γ))
      (Set.Icc 0 (Real.pi / 2)) := by
  have hδ := continuousOn_wallDelta hp hp1 ht hpt hpq
  fun_prop

lemma continuousOn_wall_high {p t q h l : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q) :
    ContinuousOn (fun γ => seamHigh q h l (Real.pi / 2)
      (wallBeta p t q γ) γ (wallDelta p t q γ)) (Set.Icc 0 (Real.pi / 2)) := by
  have hδ := continuousOn_wallDelta hp hp1 ht hpt hpq
  have hβ := continuousOn_wallBeta hp hp1 ht hpt hpq
  unfold seamHigh highTurn angleAtom
  fun_prop

lemma wall_high_pos_at_hwall {p t q h l γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q) (hl : 0 < l)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2)
    (hwall : (h / q) * Real.sin (wallDelta p t q γ) = 1) :
    0 < seamHigh q h l (Real.pi / 2) (wallBeta p t q γ) γ (wallDelta p t q γ) := by
  have hβ0 := wallBeta_pos hp hp1 ht hpt hpq hγ0 hγ1
  have hβ1 := wallBeta_lt_pi_div_two hp hp1 ht hpt hpq hγ0 hγ1
  have hsβ := Real.sin_pos_of_pos_of_lt_pi hβ0 (by linarith [Real.pi_pos])
  have hlangle := Real.arcsin_pos.2 (mul_pos hl hsβ)
  unfold seamHigh highTurn angleAtom
  rw [hwall, Real.arcsin_one]
  linarith

lemma wall_high_pos_at_right {p t q h l : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q) (hh : 0 < h) (hl : 0 < l) :
    0 < seamHigh q h l (Real.pi / 2) (wallBeta p t q (Real.pi / 2))
      (Real.pi / 2) (wallDelta p t q (Real.pi / 2)) := by
  have hq := wall_q_pos hp hpq
  have hπ : 0 ≤ Real.pi / 2 := (by linarith [Real.pi_pos])
  have hβ0 := wallBeta_pos hp hp1 ht hpt hpq hπ le_rfl
  have hβ1 := wallBeta_lt_pi_div_two hp hp1 ht hpt hpq hπ le_rfl
  have hδ0 := wallDelta_pos hp hp1 ht hpt hpq hπ le_rfl
  have hδ1 := wallDelta_lt_pi_div_two p t q (Real.pi / 2)
  have hsβ := Real.sin_pos_of_pos_of_lt_pi hβ0 (by linarith [Real.pi_pos])
  have hsδ := Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith [Real.pi_pos])
  have hlangle := Real.arcsin_pos.2 (mul_pos hl hsβ)
  have hhangle := Real.arcsin_pos.2 (mul_pos (div_pos hh hq) hsδ)
  unfold seamHigh highTurn angleAtom
  linarith

/-- A strictly physical wall-chart segment ends with positive high-seam residual. -/
lemma exists_wall_positive_endpoint {p t q h l : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q) (hh : 0 < h) (hl : 0 < l)
    (hinit : (h / q) * Real.sin (wallDelta p t q 0) < 1) :
    ∃ γhi ∈ Set.Ioo 0 (Real.pi / 2),
      (∀ γ ∈ Set.Icc 0 γhi, (h / q) * Real.sin (wallDelta p t q γ) < 1) ∧
      0 < seamHigh q h l (Real.pi / 2) (wallBeta p t q γhi) γhi
        (wallDelta p t q γhi) := by
  exact exists_positive_before_first_wall (by linarith [Real.pi_pos])
    (continuousOn_wall_hargument hp hp1 ht hpt hpq)
    (continuousOn_wall_high hp hp1 ht hpt hpq) hinit
    (wall_high_pos_at_right hp hp1 ht hpt hpq hh hl)
    (fun γ hγ => wall_high_pos_at_hwall hp hp1 ht hpt hpq hl hγ.1 hγ.2)

end Gluck.Discrete.NativeOppositePure
