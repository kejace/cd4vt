import Mathlib.Tactic

/-!
# Exact polynomial exclusion in the one-sided projective chamber

Here `p,q,B,r` are projective parameters from the orthogonal-core rank
reduction, not the curvature parameters of the native slot controller.
The polynomials are the two quadratics in equation (21) of
`research/notes/TOP_TWO_MIXED_ORTHOGONAL_RANK_RESULT.md`. This file proves their sign
on the forced interval; the native rank-to-interval reduction is separate.
-/

namespace Gluck.Discrete.NativeIncidentProjective

def polyA (p q r : ℝ) : ℝ :=
  (2 * p ^ 3) * r ^ 2 + (-3 * p ^ 3 + p ^ 2 * q + p ^ 2 + p * q) * r +
    (p ^ 3 - p ^ 2 * q - p ^ 2 + q ^ 2)

def polyD (p q r : ℝ) : ℝ :=
  (2 * p ^ 2 + 2 * p * q - 2 * p) * r ^ 2 +
    (-p ^ 2 - p * q + 3 * p - q) * r + (-p + q)

def polyC (p q B r : ℝ) : ℝ := B * p * polyD p q r + q * polyA p q r

private theorem quadratic_neg_between {a b c lo hi x : ℝ}
    (ha : 0 ≤ a) (hlo : lo < x) (hhi : x < hi)
    (hflo : a * lo ^ 2 + b * lo + c < 0)
    (hfhi : a * hi ^ 2 + b * hi + c < 0) : a * x ^ 2 + b * x + c < 0 := by
  have hw : 0 < hi - lo := sub_pos.mpr (hlo.trans hhi)
  have hl : 0 < x - lo := sub_pos.mpr hlo
  have hh : 0 < hi - x := sub_pos.mpr hhi
  have hsum : (hi - x) * (a * lo ^ 2 + b * lo + c) +
      (x - lo) * (a * hi ^ 2 + b * hi + c) < 0 :=
    add_neg (mul_neg_of_pos_of_neg hh hflo) (mul_neg_of_pos_of_neg hl hfhi)
  have hcorr : 0 ≤ a * (x - lo) * (hi - x) * (hi - lo) := by positivity
  have hid : (hi - lo) * (a * x ^ 2 + b * x + c) =
      (hi - x) * (a * lo ^ 2 + b * lo + c) +
        (x - lo) * (a * hi ^ 2 + b * hi + c) -
          a * (x - lo) * (hi - x) * (hi - lo) := by ring
  have hprod : (hi - lo) * (a * x ^ 2 + b * x + c) < 0 := by
    rw [hid]
    linarith
  exact neg_of_mul_neg_right hprod hw.le

theorem polyA_at_left {p q : ℝ} (hp : p ≠ 0) :
    polyA p q ((p - q) / p) = -p * q * (p - q) := by
  unfold polyA
  field_simp
  ring

theorem polyA_at_outer_right {p q : ℝ} (hp : p ≠ 0) (hp1 : p + 1 ≠ 0) :
    polyA p q ((p ^ 2 - q) / (p * (p + 1))) =
      -p * (p + q) * (p ^ 2 - 2 * q + 1) / (p + 1) ^ 2 := by
  unfold polyA
  field_simp
  ring

theorem polyD_at_left {p q : ℝ} (hp : p ≠ 0) :
    polyD p q ((p - q) / p) = (p - q) * (p ^ 2 - p * q - 2 * q ^ 2 + q) / p := by
  unfold polyD
  field_simp
  ring

theorem polyD_at_right {p q : ℝ} (hden : p + 2 * q - 1 ≠ 0) :
    polyD p q ((q - 1) / (p + 2 * q - 1)) =
      -q * (p + q) * (p ^ 2 - 2 * q + 1) / (p + 2 * q - 1) ^ 2 := by
  unfold polyD
  field_simp
  ring

/-- Both quadratics are strictly negative on the interval forced by
physical projective collinearity. No numerical certificate is used. -/
theorem polyA_neg_and_polyD_neg_of_interval {p q r : ℝ}
    (hq : 1 < q) (hqp : q < p)
    (hlo : (p - q) / p < r) (hhi : r < (q - 1) / (p + 2 * q - 1)) :
    polyA p q r < 0 ∧ polyD p q r < 0 := by
  have hq0 : 0 < q := by linarith
  have hp : 0 < p := by linarith
  have hp1 : 0 < p + 1 := by linarith
  have hden : 0 < p + 2 * q - 1 := by linarith
  have hgap : 0 < p ^ 2 - 2 * q + 1 := by nlinarith
  have hpq : 0 < p + q := by linarith
  have hcross := (div_lt_div_iff₀ hp hden).mp (hlo.trans hhi)
  have hbound : p ^ 2 - 2 * q ^ 2 + q < 0 := by nlinarith
  have hright : (q - 1) / (p + 2 * q - 1) < (p ^ 2 - q) / (p * (p + 1)) := by
    apply (div_lt_div_iff₀ hden (mul_pos hp hp1)).mpr
    nlinarith [mul_pos hpq hgap]
  have hAleft : polyA p q ((p - q) / p) < 0 := by
    rw [polyA_at_left hp.ne']
    have := mul_pos (mul_pos hp hq0) (sub_pos.mpr hqp)
    nlinarith
  have hAright : polyA p q ((p ^ 2 - q) / (p * (p + 1))) < 0 := by
    rw [polyA_at_outer_right hp.ne' hp1.ne']
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hp) hpq) hgap)
      (sq_pos_of_pos hp1)
  have hDleft : polyD p q ((p - q) / p) < 0 := by
    rw [polyD_at_left hp.ne']
    have hinner : p ^ 2 - p * q - 2 * q ^ 2 + q < 0 := by
      nlinarith [mul_pos hp hq0]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sub_pos.mpr hqp) hinner) hp
  have hDright : polyD p q ((q - 1) / (p + 2 * q - 1)) < 0 := by
    rw [polyD_at_right hden.ne']
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hq0) hpq) hgap)
      (sq_pos_of_pos hden)
  constructor
  · exact quadratic_neg_between (by positivity : 0 ≤ 2 * p ^ 3)
      hlo (hhi.trans hright) hAleft hAright
  · have hcoeff : 0 ≤ 2 * p ^ 2 + 2 * p * q - 2 * p := by
      have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hp)
        (show 0 < p + q - 1 by linarith)
      nlinarith
    exact quadratic_neg_between hcoeff hlo hhi hDleft hDright

/-- The remaining resultant factor is strictly negative throughout the
physical projective interval, excluding the one-sided algebraic branch. -/
theorem polyC_neg_of_interval {p q B r : ℝ} (hq : 1 < q) (hqp : q < p) (hB : 0 < B)
    (hlo : (p - q) / p < r) (hhi : r < (q - 1) / (p + 2 * q - 1)) :
    polyC p q B r < 0 := by
  obtain ⟨hA, hD⟩ := polyA_neg_and_polyD_neg_of_interval hq hqp hlo hhi
  exact add_neg (mul_neg_of_pos_of_neg (mul_pos hB (by linarith)) hD)
    (mul_neg_of_pos_of_neg (by linarith) hA)

end Gluck.Discrete.NativeIncidentProjective
