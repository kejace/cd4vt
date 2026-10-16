/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.N6MonotoneResidue

/-!
# Semialgebraic core of the ordinary type-A three-cell selector

This file formalizes the algebraic inequalities behind
`research/notes/TYPE_A_THREE_CELL_ORTHOGONAL_COVER.md`.  It deliberately stops before the
analytic orthogonal-anchor, winding, and dormant-gap opening arguments.

The main results are:

* `xFailure_forces_feasibleInterval`: failure of the scalar `X` cell forces
  the normalized low value past the exact threshold `(1 + h * l) / (h + l)`;
* `critical_hWall_pos`: the same failure inequalities make the entire `R`
  rectangle lie inside the actual `h` wall;
* `quadratic_pos_on_feasibleInterval`: the endpoint argument used to transfer
  the complementary `R` sign to the scalar `M` cell.
-/

@[expose] public section

namespace Gluck.Discrete
namespace N6TypeAThreeCell

/-! ## Exact failure factorization -/

/-- The polynomial factorization which isolates the feasible component of
the failed scalar `X` test. -/
lemma xFailure_factorization (p h l : ℝ) :
    (1 - l ^ 2) * (h - p) ^ 2 - (1 - p ^ 2) * (h ^ 2 - 1) =
      ((h + l) * p - (1 + h * l)) *
        ((h - l) * p + (h * l - 1)) := by
  ring

/-- Above the sharp scalar threshold `s`, the second factor in
`xFailure_factorization` is positive. -/
lemma xFailure_secondFactor_pos {p h l s : ℝ}
    (hp : 0 < p) (hs : 0 < s) (hsp : s < p)
    (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hsq : s ^ 2 * (h ^ 2 - l ^ 2) = 1 - l ^ 2) :
    0 < (h - l) * p + (h * l - 1) := by
  have hhl : 0 < h - l := by linarith
  by_cases hprod : 1 ≤ h * l
  · have : 0 < (h - l) * p := mul_pos hhl hp
    linarith
  · have hprod' : h * l < 1 := lt_of_not_ge hprod
    have hl_sq : l ^ 2 < 1 := by nlinarith
    have hright : 0 < 1 - h * l := sub_pos.mpr hprod'
    have hleft : 0 < (h - l) * s := mul_pos hhl hs
    by_contra hnot
    have hle : (h - l) * p ≤ 1 - h * l := by linarith
    have hlt : (h - l) * s < 1 - h * l :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_left hsp hhl) hle
    have hsq_lt : ((h - l) * s) ^ 2 < (1 - h * l) ^ 2 :=
      (sq_lt_sq₀ hleft.le hright.le).2 hlt
    have hden : 0 < h ^ 2 - l ^ 2 := by nlinarith
    have hscaled :
        (1 - l ^ 2) * (h - l) ^ 2 <
          (1 - h * l) ^ 2 * (h ^ 2 - l ^ 2) := by
      calc
        (1 - l ^ 2) * (h - l) ^ 2 =
            ((h - l) * s) ^ 2 * (h ^ 2 - l ^ 2) := by
              rw [mul_pow]
              nlinarith
        _ < (1 - h * l) ^ 2 * (h ^ 2 - l ^ 2) :=
          mul_lt_mul_of_pos_right hsq_lt hden
    have hfactor :
        (1 - l ^ 2) * (h - l) ^ 2 -
            (1 - h * l) ^ 2 * (h ^ 2 - l ^ 2) =
          l * (h - 1) * (h + 1) * (h - l) *
            (2 - h * l - l ^ 2) := by
      ring
    have hlast : 0 < 2 - h * l - l ^ 2 := by linarith
    have hpositive :
        0 < l * (h - 1) * (h + 1) * (h - l) *
          (2 - h * l - l ^ 2) := by positivity
    nlinarith [hfactor]

/-- If the critical scalar value lies strictly below `h`, scalar failure is
possible only on the component `p > (1 + h*l)/(h+l)`.  The variables `r`,
`x`, `a`, and `s` record the positive square roots used in the normalized
orthogonal formulas. -/
theorem xFailure_forces_feasibleInterval {p h l r x a s : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hx : 0 < x) (ha : 0 < a) (hs : 0 < s)
    (hsp : s < p) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hrsq : r ^ 2 = 1 - p ^ 2) (hxsq : x ^ 2 = 1 - l ^ 2)
    (hax : x ^ 2 * a ^ 2 = h ^ 2 - 1)
    (hsq : s ^ 2 * (h ^ 2 - l ^ 2) = 1 - l ^ 2)
    (hcritical : p + r * a < h) :
    (1 + h * l) / (h + l) < p := by
  have hgap : r * a < h - p := by linarith
  have hgap_pos : 0 < h - p := lt_of_lt_of_le (mul_pos hr ha) hgap.le
  have hsq_lt : (r * a) ^ 2 < (h - p) ^ 2 :=
    (sq_lt_sq₀ (mul_pos hr ha).le hgap_pos.le).2 hgap
  have hscaled :
      r ^ 2 * (h ^ 2 - 1) < x ^ 2 * (h - p) ^ 2 := by
    calc
      r ^ 2 * (h ^ 2 - 1) = x ^ 2 * (r * a) ^ 2 := by
        rw [← hax]
        ring
      _ < x ^ 2 * (h - p) ^ 2 :=
        mul_lt_mul_of_pos_left hsq_lt (sq_pos_of_pos hx)
  have hsecond : 0 < (h - l) * p + (h * l - 1) :=
    xFailure_secondFactor_pos hp hs hsp hh hl hl1 hsq
  have hproduct :
      0 < ((h + l) * p - (1 + h * l)) *
        ((h - l) * p + (h * l - 1)) := by
    rw [← xFailure_factorization]
    rw [← hxsq, ← hrsq]
    linarith
  have hfirst : 0 < (h + l) * p - (1 + h * l) :=
    pos_of_mul_pos_left hproduct hsecond.le
  have hden : 0 < h + l := by linarith
  rw [div_lt_iff₀ hden]
  linarith

/-! ## The whole `R` rectangle is physical -/

/-- The actual `t`-wall margin for the `R` profile `(1,u,q,v)`. -/
lemma tWall_margin_identity (q u v t : ℝ) :
    q ^ 2 - u ^ 2 * v ^ 2 - t ^ 2 * (1 - v ^ 2) =
      q ^ 2 - t ^ 2 + v ^ 2 * (t ^ 2 - u ^ 2) := by
  ring

/-- The actual `h`-wall margin for the `R` profile `(1,u,q,v)`. -/
lemma hWall_margin_identity (q u v h : ℝ) :
    q ^ 2 - u ^ 2 * v ^ 2 - h ^ 2 * (1 - u ^ 2) =
      q ^ 2 - h ^ 2 + u ^ 2 * (h ^ 2 - v ^ 2) := by
  ring

/-- The exact critical-value expansion at the minimum of the `h` wall. -/
lemma critical_hWall_identity (p h r a : ℝ) :
    (p + r * a) ^ 2 - (h ^ 2 * r ^ 2 + p ^ 2) =
      r ^ 2 * (a ^ 2 - h ^ 2) + 2 * p * r * a := by
  ring

/-- Above the sharp scalar threshold, the critical value is already beyond
the minimum actual `h` wall of the entire `R` rectangle. -/
theorem critical_hWall_pos {p h l r a s : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hs : 0 < s)
    (hsp : s < p) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1)
    (hseq : s ^ 2 * (1 + a ^ 2) = 1) :
    h ^ 2 * r ^ 2 + p ^ 2 < (p + r * a) ^ 2 := by
  have hl_sq : l ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hl.le zero_le_one).2 hl1
  have hx : 0 < 1 - l ^ 2 := sub_pos.mpr hl_sq
  have hh_sq : 0 < h ^ 2 - 1 := by nlinarith
  have hbase_product :
      (a ^ 2 - h ^ 2 + 2) * (1 - l ^ 2) =
        (1 - l ^ 2) + l ^ 2 * (h ^ 2 - 1) := by
    nlinarith
  have hbase_rhs : 0 < (1 - l ^ 2) + l ^ 2 * (h ^ 2 - 1) := by
    positivity
  have hbase_product_pos :
      0 < (a ^ 2 - h ^ 2 + 2) * (1 - l ^ 2) := by
    rw [hbase_product]
    exact hbase_rhs
  have hbase : 0 < a ^ 2 - h ^ 2 + 2 := by
    exact pos_of_mul_pos_left hbase_product_pos hx.le
  have hs_sq_lt : s ^ 2 < p ^ 2 :=
    (sq_lt_sq₀ hs.le hp.le).2 hsp
  have ha1 : 0 < 1 + a ^ 2 := by positivity
  have hp_scale : 1 < p ^ 2 * (1 + a ^ 2) := by
    calc
      1 = s ^ 2 * (1 + a ^ 2) := hseq.symm
      _ < p ^ 2 * (1 + a ^ 2) :=
        mul_lt_mul_of_pos_right hs_sq_lt ha1
  have hpa_sq : r ^ 2 < (p * a) ^ 2 := by
    rw [hrsq]
    nlinarith
  have hpa : r < p * a :=
    (sq_lt_sq₀ hr.le (mul_pos hp ha).le).1 hpa_sq
  have hcross : 2 * r ^ 2 < 2 * p * r * a := by
    have := mul_lt_mul_of_pos_left hpa (show 0 < 2 * r by positivity)
    nlinarith
  have hscaled_base : 0 < r ^ 2 * (a ^ 2 - h ^ 2 + 2) := by
    positivity
  rw [← sub_pos, critical_hWall_identity]
  nlinarith

/-- The sharp scalar failure threshold is strictly above the normalized
value `1`.  This closes the nonadjacent equality case `Q=A`: it necessarily
belongs to the successful `X` branch. -/
lemma one_lt_criticalValue {p r a s : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hs : 0 < s)
    (hsp : s < p) (hrsq : r ^ 2 = 1 - p ^ 2)
    (hseq : s ^ 2 * (1 + a ^ 2) = 1) :
    1 < p + r * a := by
  have hs_sq_lt : s ^ 2 < p ^ 2 :=
    (sq_lt_sq₀ hs.le hp.le).2 hsp
  have ha1 : 0 < 1 + a ^ 2 := by positivity
  have hp_scale : 1 < p ^ 2 * (1 + a ^ 2) := by
    calc
      1 = s ^ 2 * (1 + a ^ 2) := hseq.symm
      _ < p ^ 2 * (1 + a ^ 2) :=
        mul_lt_mul_of_pos_right hs_sq_lt ha1
  have hpa_sq : r ^ 2 < (p * a) ^ 2 := by
    rw [hrsq]
    nlinarith
  have hpa : r < p * a :=
    (sq_lt_sq₀ hr.le (mul_pos hp ha).le).1 hpa_sq
  have hp1 : p < 1 := by
    have hr_sq : 0 < r ^ 2 := sq_pos_of_pos hr
    nlinarith
  have hra : 0 < r * a := mul_pos hr ha
  have hmul : r ^ 2 < r * p * a := by
    have := mul_lt_mul_of_pos_left hpa hr
    nlinarith
  have hstep : (1 - p) * (1 + p) < (r * a) * (1 + p) := by
    calc
      (1 - p) * (1 + p) = r ^ 2 := by nlinarith
      _ < r * p * a := hmul
      _ < (r * a) * (1 + p) := by
        have := mul_lt_mul_of_pos_left (show p < 1 + p by linarith) hra
        nlinarith
  have hgap : 1 - p < r * a :=
    lt_of_mul_lt_mul_right hstep (show 0 ≤ 1 + p by linarith)
  linarith

/-- Algebraic form of the first strict inequality in
`t_c(q_c) > p + r^2*a`: a positive square root `z` of `q_c^2-1`, divided by
`x=sqrt(1-l^2)`, lies beyond `r*a`. -/
lemma critical_tc_gt {p h r x a z : ℝ}
    (hr : 0 < r) (hx : 0 < x) (ha : 0 < a) (hz : 0 < z)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (hax : x ^ 2 * a ^ 2 = h ^ 2 - 1)
    (hzsq : z ^ 2 = (p + r * a) ^ 2 - 1)
    (hwall : h ^ 2 * r ^ 2 + p ^ 2 < (p + r * a) ^ 2) :
    p + r ^ 2 * a < p + r * (z / x) := by
  have hz_bound : r ^ 2 * (h ^ 2 - 1) < z ^ 2 := by
    rw [hzsq]
    nlinarith
  have hsquare : (r * a * x) ^ 2 < z ^ 2 := by
    calc
      (r * a * x) ^ 2 = r ^ 2 * (h ^ 2 - 1) := by
        rw [← hax]
        ring
      _ < z ^ 2 := hz_bound
  have hroot : r * a * x < z := by
    apply (sq_lt_sq₀ (by positivity) hz.le).1
    exact hsquare
  have hdiv : r * a < z / x := (lt_div_iff₀ hx).2 (by nlinarith)
  have hmul := mul_lt_mul_of_pos_left hdiv hr
  nlinarith

/-! ## Scalar fallback transfer -/

/-- A quadratic of the form `A+p-C*p^2` which is positive at both ends of
`[p0,1]` stays positive throughout.  The proof separates the concave case
`C>=0` from the increasing case `C<0`, exactly as in the type-A selector. -/
lemma quadratic_pos_on_feasibleInterval {A C p0 p : ℝ}
    (hp0 : 0 ≤ p0) (hp0p : p0 ≤ p) (hp1 : p ≤ 1)
    (hleft : 0 < A + p0 - C * p0 ^ 2)
    (hright : 0 < A + 1 - C) :
    0 < A + p - C * p ^ 2 := by
  by_cases hC : 0 ≤ C
  · by_cases hslope : 0 ≤ 1 - C * (p + p0)
    · have hmul : 0 ≤ (p - p0) * (1 - C * (p + p0)) :=
        mul_nonneg (sub_nonneg.mpr hp0p) hslope
      have hid :
          A + p - C * p ^ 2 - (A + p0 - C * p0 ^ 2) =
            (p - p0) * (1 - C * (p + p0)) := by
        ring
      linarith
    · have hslope' : 1 - C * (p + 1) < 0 := by
        have hp01 : p0 ≤ 1 := hp0p.trans hp1
        have hmul_le := mul_le_mul_of_nonneg_left
          (add_le_add_left hp01 p) hC
        linarith
      have hmul : 0 ≤ (p - 1) * (1 - C * (p + 1)) :=
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hp1) hslope'.le
      have hid :
          A + p - C * p ^ 2 - (A + 1 - C) =
            (p - 1) * (1 - C * (p + 1)) := by
        ring
      linarith
  · have hC' : C < 0 := lt_of_not_ge hC
    have hsum : 0 ≤ p + p0 := by linarith
    have hslope : 0 < 1 - C * (p + p0) := by
      have : C * (p + p0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC'.le hsum
      linarith
    have hmul : 0 ≤ (p - p0) * (1 - C * (p + p0)) :=
      mul_nonneg (sub_nonneg.mpr hp0p) hslope.le
    have hid :
        A + p - C * p ^ 2 - (A + p0 - C * p0 ^ 2) =
          (p - p0) * (1 - C * (p + p0)) := by
      ring
    linarith

/-- The normalized scalar fallback is exactly the quadratic used above. -/
lemma fallback_quadratic_identity (p h l a : ℝ) :
    p + (1 - p ^ 2) * a -
        (h ^ 2 * (1 - p ^ 2) + p ^ 2 * l ^ 2) / h =
      (a - h) + p - (a - h + l ^ 2 / h) * p ^ 2 := by
  by_cases hh : h = 0
  · simp [hh]
    ring
  · field_simp
    ring

/-- The exact positive numerator which puts the lower fallback endpoint
above `l^2/h`. -/
lemma fallback_p0_numerator_identity (h l : ℝ) :
    h * (1 + h * l) - l ^ 2 * (h + l) =
      h * (1 - l ^ 2) + l * (h ^ 2 - l ^ 2) := by
  ring

/-- The exact feasible endpoint lies strictly above `l^2/h`. -/
lemma fallback_lsq_div_lt_p0 {h l : ℝ}
    (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1) :
    l ^ 2 / h < (1 + h * l) / (h + l) := by
  have hh0 : 0 < h := lt_trans zero_lt_one hh
  have hden : 0 < h + l := add_pos hh0 hl
  have hl_sq : l ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hl.le zero_le_one).2 hl1
  have hhl_sq : l ^ 2 < h ^ 2 := by nlinarith
  rw [div_lt_div_iff₀ hh0 hden]
  have hid := fallback_p0_numerator_identity h l
  have hright : 0 < h * (1 - l ^ 2) + l * (h ^ 2 - l ^ 2) := by
    positivity
  nlinarith

/-- Algebraic value of the fallback quadratic at the exact feasible
endpoint.  Only the circle and critical-value relations are needed for this
identity. -/
lemma fallback_lowerEndpoint_identity {p0 r0 h l a : ℝ}
    (hh : h ≠ 0) (hrden : 1 + r0 ≠ 0)
    (hcircle : p0 ^ 2 + r0 ^ 2 = 1)
    (hcritical : p0 + r0 * a = h) :
    (a - h) + p0 - (a - h + l ^ 2 / h) * p0 ^ 2 =
      p0 ^ 2 * ((p0 + h * r0) / (1 + r0) - l ^ 2 / h) := by
  field_simp [hh, hrden]
  linear_combination
    -h * (p0 + r0 * a + a - h) * hcircle +
      r0 * h * (r0 + 1) * hcritical

/-- Positivity of the lower endpoint in the scalar `M` fallback. -/
lemma fallback_lowerEndpoint_pos {p0 r0 h l a : ℝ}
    (hp0def : p0 = (1 + h * l) / (h + l))
    (hr0 : 0 < r0) (ha : 0 < a)
    (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hcircle : p0 ^ 2 + r0 ^ 2 = 1)
    (hcritical : p0 + r0 * a = h) :
    0 < (a - h) + p0 - (a - h + l ^ 2 / h) * p0 ^ 2 := by
  have hh0 : 0 < h := lt_trans zero_lt_one hh
  have hden : 0 < h + l := add_pos hh0 hl
  have hp0 : 0 < p0 := by
    rw [hp0def]
    positivity
  have hp0lt : l ^ 2 / h < p0 := by
    rw [hp0def]
    exact fallback_lsq_div_lt_p0 hh hl hl1
  have hp0h : p0 < h := by nlinarith [mul_pos hr0 ha]
  have hrden : 0 < 1 + r0 := by linarith
  have havg : p0 < (p0 + h * r0) / (1 + r0) := by
    rw [lt_div_iff₀ hrden]
    nlinarith [mul_pos hr0 (sub_pos.mpr hp0h)]
  have hbracket :
      0 < (p0 + h * r0) / (1 + r0) - l ^ 2 / h := by
    linarith
  rw [fallback_lowerEndpoint_identity hh0.ne' hrden.ne' hcircle hcritical]
  exact mul_pos (sq_pos_of_pos hp0) hbracket

/-- Positivity of the upper endpoint in the scalar `M` fallback. -/
lemma fallback_upperEndpoint_pos {h l : ℝ}
    (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1) :
    0 < 1 - l ^ 2 / h := by
  have hh0 : 0 < h := lt_trans zero_lt_one hh
  have hl_sq : l ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hl.le zero_le_one).2 hl1
  rw [sub_pos, div_lt_iff₀ hh0]
  nlinarith

/-- The strict scalar face-transfer inequality on the full feasible interval
`[p0,1]`.  This is equation (24)--(27) of the three-cell cover. -/
theorem fallback_faceTransfer_pos {p p0 r0 h l a : ℝ}
    (hp0def : p0 = (1 + h * l) / (h + l))
    (hp0p : p0 ≤ p) (hp1 : p ≤ 1)
    (hr0 : 0 < r0) (ha : 0 < a)
    (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hcircle : p0 ^ 2 + r0 ^ 2 = 1)
    (hcritical : p0 + r0 * a = h) :
    0 < (a - h) + p - (a - h + l ^ 2 / h) * p ^ 2 := by
  have hh0 : 0 < h := lt_trans zero_lt_one hh
  have hden : 0 < h + l := add_pos hh0 hl
  have hp0 : 0 ≤ p0 := by
    rw [hp0def]
    positivity
  apply quadratic_pos_on_feasibleInterval hp0 hp0p hp1
  · exact fallback_lowerEndpoint_pos hp0def hr0 ha hh hl hl1
      hcircle hcritical
  · have hu := fallback_upperEndpoint_pos hh hl hl1
    convert hu using 1
    ring

/-- Geometric form of `fallback_faceTransfer_pos`: the critical scalar
quantity `p+(1-p^2)*a` lies strictly above the squared `M` wall divided by
`h`. -/
theorem fallback_coreMargin_pos {p p0 r0 h l a : ℝ}
    (hp0def : p0 = (1 + h * l) / (h + l))
    (hp0p : p0 ≤ p) (hp1 : p ≤ 1)
    (hr0 : 0 < r0) (ha : 0 < a)
    (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hcircle : p0 ^ 2 + r0 ^ 2 = 1)
    (hcritical : p0 + r0 * a = h) :
    (h ^ 2 * (1 - p ^ 2) + p ^ 2 * l ^ 2) / h <
      p + (1 - p ^ 2) * a := by
  have hf := fallback_faceTransfer_pos hp0def hp0p hp1 hr0 ha hh hl hl1
    hcircle hcritical
  rw [← fallback_quadratic_identity] at hf
  exact sub_pos.mp hf

/-- The complete strict comparison in equation (28), up to the final
positive correction which makes `T_wall` smaller than the displayed left
side. -/
theorem critical_tc_gt_fallbackCore {p p0 r0 h l r x a z : ℝ}
    (hp0def : p0 = (1 + h * l) / (h + l))
    (hp0p : p0 ≤ p) (hp1 : p ≤ 1)
    (hr0 : 0 < r0) (hr : 0 < r) (hx : 0 < x)
    (ha : 0 < a) (hz : 0 < z)
    (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hcircle : p0 ^ 2 + r0 ^ 2 = 1)
    (hp0critical : p0 + r0 * a = h)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (hax : x ^ 2 * a ^ 2 = h ^ 2 - 1)
    (hzsq : z ^ 2 = (p + r * a) ^ 2 - 1)
    (hwall : h ^ 2 * r ^ 2 + p ^ 2 < (p + r * a) ^ 2) :
    (h ^ 2 * r ^ 2 + p ^ 2 * l ^ 2) / h < p + r * (z / x) := by
  have hcore := fallback_coreMargin_pos hp0def hp0p hp1 hr0 ha hh hl hl1
    hcircle hp0critical
  rw [← hrsq] at hcore
  exact hcore.trans (critical_tc_gt hr hx ha hz hrsq hax hzsq hwall)

end N6TypeAThreeCell
end Gluck.Discrete
