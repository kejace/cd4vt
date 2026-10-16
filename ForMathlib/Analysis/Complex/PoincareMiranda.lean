/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import ForMathlib.Analysis.Complex.WindingNumber

/-!
# The Poincaré–Miranda theorem in the plane

This file proves the two-dimensional **Poincaré–Miranda theorem** (conjectured by Poincaré in
1883, proved equivalent to the Brouwer fixed-point theorem by Miranda in 1940), the planar
generalisation of the intermediate value theorem: a continuous map
`G = (G₁, G₂) : [a₁, a₂] × [b₁, b₂] → ℝ × ℝ` whose first component is `≤ 0` on the left face
and `≥ 0` on the right face, and whose second component is `≤ 0` on the bottom face and `≥ 0`
on the top face, has a zero in the rectangle.

## Main results

* `poincare_miranda`: the Poincaré–Miranda theorem in the plane, in the literature-standard
  weak-inequality form (degenerate rectangles are allowed).
* `exists_fixedPoint_prod_Icc`: the **Brouwer fixed-point theorem** for a plane rectangle,
  derived as the classical corollary.

## Proof outline

For a nondegenerate rectangle and strict face signs (`poincare_miranda_of_lt`), identify
`ℝ × ℝ ≅ ℂ` and pull `G` back to the closed unit disk through the radial disk-to-square chart
`z ↦ (‖z‖ / max |re z| |im z|) • z` followed by the affine chart of the rectangle.  The four
strict sign faces keep the resulting `F : ℂ → ℂ` away from `0` on the unit circle and force
its boundary loop to thread the four open half-planes `{re > 0}`, `{im > 0}`, `{re < 0}`,
`{im < 0}` in the cyclic order of the standard circle loop, so the "dog-on-a-leash" Rouché
theorem (`Complex.windingNumberAt_eq_of_norm_sub_lt`) gives the boundary loop winding number
`1` about `0`, and the existence property of the planar degree
(`Complex.exists_eq_of_windingNumberAt_ne_zero`) produces a zero of `F` in the open disk.
The general weak-inequality form follows by a vanishing linear perturbation (which has
strict face signs for every step) and compactness; degenerate rectangles reduce to the
1-dimensional intermediate value theorem.

## Naming

The theorem is universally cited as "the Poincaré–Miranda theorem", so — following the
precedent of `ZMod.wilsons_lemma` and `legendreSym.quadratic_reciprocity` — it is named after
the result rather than after the shape of its statement.  Its 1-dimensional instance is
Bolzano's intermediate value theorem, `intermediate_value_Icc`; an eventual `n`-dimensional
version can take the `poincare_miranda` name for `Fin n → ℝ` and keep this statement as the
planar special case.

## References

* [H. Poincaré, *Sur certaines solutions particulières du problème des trois corps*,
  C. R. Acad. Sci. Paris **97** (1883), 251–252]
* [C. Miranda, *Un'osservazione su un teorema di Brouwer*,
  Boll. Un. Mat. Ital. (2) **3** (1940), 5–7]
* [W. Kulpa, *The Poincaré-Miranda theorem*, Amer. Math. Monthly **104** (1997), 545–550]

## Tags

Poincare-Miranda, Miranda, intermediate value theorem, winding number, degree, Brouwer,
fixed point
-/

@[expose] public section

open scoped Real unitInterval
open Complex Metric

/-! ### Rouché feeders: two points of a common open half-plane -/

/-- Two points whose real parts have the same strict sign satisfy the strict triangle
inequality `‖d - c‖ < ‖c‖ + ‖d‖`: the segment from `c` to `d` stays inside the half-plane,
away from `0`. -/
private theorem norm_sub_lt_add_of_mul_re_pos {c d : ℂ} (h : 0 < c.re * d.re) :
    ‖d - c‖ < ‖c‖ + ‖d‖ := by
  have him : -(c.im * d.im) ≤ ‖c‖ * ‖d‖ :=
    calc -(c.im * d.im) ≤ |c.im * d.im| := neg_le_abs _
      _ = |c.im| * |d.im| := abs_mul _ _
      _ ≤ ‖c‖ * ‖d‖ := by
          gcongr
          exacts [Complex.abs_im_le_norm c, Complex.abs_im_le_norm d]
  have e1 : ‖d - c‖ ^ 2 = (d.re - c.re) ^ 2 + (d.im - c.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  have e2 : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e3 : ‖d‖ ^ 2 = d.re ^ 2 + d.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  nlinarith [h, him, e1, e2, e3]

/-- Two points whose imaginary parts have the same strict sign satisfy the strict triangle
inequality `‖d - c‖ < ‖c‖ + ‖d‖`.  Multiplication by `I` reduces this to the real-part
version. -/
private theorem norm_sub_lt_add_of_mul_im_pos {c d : ℂ} (h : 0 < c.im * d.im) :
    ‖d - c‖ < ‖c‖ + ‖d‖ := by
  have := norm_sub_lt_add_of_mul_re_pos (c := Complex.I * c) (d := Complex.I * d)
    (by simpa using h)
  simpa [← mul_sub, norm_mul] using this

/-! ### Four-arc winding -/

private theorem circleMap_zero_one_re (θ : ℝ) : (circleMap 0 1 θ).re = Real.cos θ := by
  simp only [circleMap, Complex.ofReal_one, one_mul, zero_add, Complex.exp_ofReal_mul_I_re]

private theorem circleMap_zero_one_im (θ : ℝ) : (circleMap 0 1 θ).im = Real.sin θ := by
  simp only [circleMap, Complex.ofReal_one, one_mul, zero_add, Complex.exp_ofReal_mul_I_im]

/-- **Four-arc winding.**  A nowhere-zero loop `γ` whose four quarter-mark arcs (split at
`1/8, 3/8, 5/8, 7/8`) lie successively in the open half-planes `{re > 0}` (right arc,
wrapping through `t = 0`), `{im > 0}` (top), `{re < 0}` (left) and `{im < 0}` (bottom) — the
cyclic order that four sign-definite rectangle faces impose — winds exactly once about `0`.
On each arc, `γ` shares an open half-plane with the standard circle loop, so the
"dog-on-a-leash" Rouché theorem compares `γ` with the standard loop. -/
private theorem windingNumberAt_eq_one_of_fourArcs (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (hloop : γ 0 = γ 1)
    (harcR : ∀ t : I, ((t : ℝ) ≤ 1 / 8 ∨ 7 / 8 ≤ (t : ℝ)) → 0 < (γ t).re)
    (harcT : ∀ t : I, 1 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 3 / 8 → 0 < (γ t).im)
    (harcL : ∀ t : I, 3 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 5 / 8 → (γ t).re < 0)
    (harcB : ∀ t : I, 5 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 7 / 8 → (γ t).im < 0) :
    windingNumberAt 0 γ hγ = 1 := by
  have hpi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  set sl : C(I, ℂ) := circleLoop id 0 1 continuous_id.continuousOn
  have hsl : ∀ t : I, sl t = circleMap 0 1 (2 * π * (t : ℝ)) := fun _ ↦ rfl
  have hslR : ∀ t : I, ((t : ℝ) ≤ 1 / 8 ∨ 7 / 8 ≤ (t : ℝ)) → 0 < (sl t).re := by
    intro t ht
    rw [hsl t, circleMap_zero_one_re]
    have h0t := t.2.1
    have h1t := t.2.2
    rcases ht with ht | ht
    · apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [h2pi, hpi]
    · rw [show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring,
        Real.cos_add_two_pi]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [h2pi, hpi]
  have hslT : ∀ t : I, 1 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 3 / 8 → 0 < (sl t).im := by
    intro t hl hr
    rw [hsl t, circleMap_zero_one_im]
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith [h2pi, hpi]
  have hslL : ∀ t : I, 3 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 5 / 8 → (sl t).re < 0 := by
    intro t hl hr
    rw [hsl t, circleMap_zero_one_re]
    apply Real.cos_neg_of_pi_div_two_lt_of_lt <;> nlinarith [h2pi, hpi]
  have hslB : ∀ t : I, 5 / 8 ≤ (t : ℝ) → (t : ℝ) ≤ 7 / 8 → (sl t).im < 0 := by
    intro t hl hr
    rw [hsl t, circleMap_zero_one_im,
      show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring,
      Real.sin_add_two_pi]
    apply Real.sin_neg_of_neg_of_neg_pi_lt <;> nlinarith [h2pi, hpi]
  have hslloop : sl 0 = sl 1 := by
    rw [hsl 0, hsl 1, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one]
    simpa using (periodic_circleMap 0 1 0).symm
  have hpert : ∀ t : I, ‖γ t - sl t‖ < ‖sl t - 0‖ + ‖γ t - 0‖ := by
    intro t
    simp only [sub_zero]
    rcases le_or_gt (t : ℝ) (1 / 8) with h1 | h1
    · exact norm_sub_lt_add_of_mul_re_pos (mul_pos (hslR t (Or.inl h1)) (harcR t (Or.inl h1)))
    · rcases le_or_gt (t : ℝ) (3 / 8) with h2 | h2
      · exact norm_sub_lt_add_of_mul_im_pos (mul_pos (hslT t h1.le h2) (harcT t h1.le h2))
      · rcases le_or_gt (t : ℝ) (5 / 8) with h3 | h3
        · exact norm_sub_lt_add_of_mul_re_pos
            (mul_pos_of_neg_of_neg (hslL t h2.le h3) (harcL t h2.le h3))
        · rcases le_or_gt (t : ℝ) (7 / 8) with h4 | h4
          · exact norm_sub_lt_add_of_mul_im_pos
              (mul_pos_of_neg_of_neg (hslB t h3.le h4) (harcB t h3.le h4))
          · exact norm_sub_lt_add_of_mul_re_pos
              (mul_pos (hslR t (Or.inr h4.le)) (harcR t (Or.inr h4.le)))
  have hkey := windingNumberAt_eq_of_norm_sub_lt 0 sl γ hslloop hloop hpert
  exact hkey.symm.trans (windingNumberAt_circleLoop_id 0 one_pos)

/-! ### The radial disk-to-square chart -/

/-- Scaling denominator of the radial disk-to-square chart: `‖z‖_∞ = max |re z| |im z|`. -/
noncomputable def sqDen (z : ℂ) : ℝ := max |z.re| |z.im|

private theorem sqDen_continuous : Continuous sqDen :=
  (continuous_abs.comp Complex.continuous_re).max (continuous_abs.comp Complex.continuous_im)

private theorem sqDen_pos {z : ℂ} (hz : z ≠ 0) : 0 < sqDen z := by
  rw [sqDen]
  rcases eq_or_ne z.re 0 with hr | hr
  · have hi : z.im ≠ 0 := fun hi ↦ hz (Complex.ext hr hi)
    exact lt_of_lt_of_le (abs_pos.2 hi) (le_max_right _ _)
  · exact lt_of_lt_of_le (abs_pos.2 hr) (le_max_left _ _)

/-- The radial disk-to-square chart `z ↦ (‖z‖ / ‖z‖_∞) • z`, mapping the closed unit disk
onto the closed square `[-1, 1]²` (radially) and the unit circle onto the square's boundary.
(Junk value `0` at `z = 0`, which is also its continuous value there.) -/
noncomputable def squareChart (z : ℂ) : ℂ := (‖z‖ / sqDen z) • z

private theorem squareChart_norm_le (z : ℂ) : ‖squareChart z‖ ≤ 2 * ‖z‖ := by
  by_cases hz : z = 0
  · subst hz; simp [squareChart]
  · have hden : 0 < sqDen z := sqDen_pos hz
    have hz1 : ‖z‖ ≤ |z.re| + |z.im| := by
      conv_lhs => rw [← Complex.re_add_im z]
      calc ‖(z.re : ℂ) + z.im * Complex.I‖
          ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs]
    have hz2 : ‖z‖ ≤ 2 * sqDen z := by
      rw [sqDen]
      have h1 := le_max_left |z.re| |z.im|
      have h2 := le_max_right |z.re| |z.im|
      linarith
    rw [squareChart, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg z),
      abs_of_pos hden, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [norm_nonneg z, hz2]

private theorem squareChart_continuous : Continuous squareChart := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : squareChart 0 = 0 := by simp [squareChart]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (fun x ↦ squareChart_norm_le x) ?_
    simpa using (continuous_norm.tendsto (0 : ℂ)).const_mul (2 : ℝ)
  · have hden : sqDen z ≠ 0 := (sqDen_pos hz).ne'
    exact (continuous_norm.continuousAt.div sqDen_continuous.continuousAt hden).smul
      continuousAt_id

private theorem squareChart_re (z : ℂ) : (squareChart z).re = (‖z‖ / sqDen z) * z.re := by
  rw [squareChart, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem squareChart_im (z : ℂ) : (squareChart z).im = (‖z‖ / sqDen z) * z.im := by
  rw [squareChart, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem squareChart_re_le (z : ℂ) : |(squareChart z).re| ≤ ‖z‖ := by
  by_cases hz : z = 0
  · subst hz; simp [squareChart]
  · have hden : 0 < sqDen z := sqDen_pos hz
    rw [squareChart_re, abs_mul, abs_div, abs_of_nonneg (norm_nonneg z), abs_of_pos hden,
      div_mul_eq_mul_div, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg z)

private theorem squareChart_im_le (z : ℂ) : |(squareChart z).im| ≤ ‖z‖ := by
  by_cases hz : z = 0
  · subst hz; simp [squareChart]
  · have hden : 0 < sqDen z := sqDen_pos hz
    rw [squareChart_im, abs_mul, abs_div, abs_of_nonneg (norm_nonneg z), abs_of_pos hden,
      div_mul_eq_mul_div, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg z)

/-- On the unit circle, `squareChart` lands on the boundary of the square: whichever
coordinate dominates has absolute value `1` there. -/
private theorem squareChart_re_eq_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.im| ≤ |z.re|)
    (hpos : 0 < z.re) : (squareChart z).re = 1 := by
  have hden_eq : sqDen z = z.re := by rw [sqDen, max_eq_left hle, abs_of_pos hpos]
  rw [squareChart_re, hzn, hden_eq, one_div_mul_cancel hpos.ne']

private theorem squareChart_re_eq_neg_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.im| ≤ |z.re|)
    (hneg : z.re < 0) : (squareChart z).re = -1 := by
  have hden_eq : sqDen z = -z.re := by rw [sqDen, max_eq_left hle, abs_of_neg hneg]
  rw [squareChart_re, hzn, hden_eq, div_mul_eq_mul_div, one_mul, div_neg, div_self hneg.ne]

private theorem squareChart_im_eq_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.re| ≤ |z.im|)
    (hpos : 0 < z.im) : (squareChart z).im = 1 := by
  have hden_eq : sqDen z = z.im := by rw [sqDen, max_eq_right hle, abs_of_pos hpos]
  rw [squareChart_im, hzn, hden_eq, one_div_mul_cancel hpos.ne']

private theorem squareChart_im_eq_neg_one {z : ℂ} (hzn : ‖z‖ = 1) (hle : |z.re| ≤ |z.im|)
    (hneg : z.im < 0) : (squareChart z).im = -1 := by
  have hden_eq : sqDen z = -z.im := by rw [sqDen, max_eq_right hle, abs_of_neg hneg]
  rw [squareChart_im, hzn, hden_eq, div_mul_eq_mul_div, one_mul, div_neg, div_self hneg.ne]

/-- `cos 2x ≥ 0` forces `|sin x| ≤ |cos x|` (equivalently `sin² x ≤ cos² x`). -/
private theorem abs_sin_le_abs_cos_of_cos_two_mul_nonneg {x : ℝ} (h : 0 ≤ Real.cos (2 * x)) :
    |Real.sin x| ≤ |Real.cos x| := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sin_sq_add_cos_sq x, Real.cos_two_mul x, h]

/-- `cos 2x ≤ 0` forces `|cos x| ≤ |sin x|` (equivalently `cos² x ≤ sin² x`). -/
private theorem abs_cos_le_abs_sin_of_cos_two_mul_nonpos {x : ℝ} (h : Real.cos (2 * x) ≤ 0) :
    |Real.cos x| ≤ |Real.sin x| := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sin_sq_add_cos_sq x, Real.cos_two_mul x, h]

/-! ### The strict, nondegenerate case -/

/-- **Poincaré–Miranda on a rectangle, strict form.**  Same as `poincare_miranda` but with a
nondegenerate rectangle (`a₁ < a₂`, `b₁ < b₂`) and *strictly* sign-definite opposite faces.
This is the form proven by the winding argument; the weak form reduces to it by a vanishing
perturbation and compactness. -/
private theorem poincare_miranda_of_lt {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ < a₂) (hb : b₁ < b₂)
    (G : ℝ × ℝ → ℝ × ℝ)
    (hG : ContinuousOn G (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hleft : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 < 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂, 0 < (G (a₂, y)).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 < 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂, 0 < (G (x, b₂)).2) :
    ∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, G p = 0 := by
  have haffineX : ∀ u : ℝ, |u| ≤ 1 → (a₁ + a₂) / 2 + (a₂ - a₁) / 2 * u ∈ Set.Icc a₁ a₂ := by
    intro u hu
    obtain ⟨h1, h2⟩ := abs_le.1 hu
    constructor <;> nlinarith [ha, h1, h2]
  have haffineY : ∀ v : ℝ, |v| ≤ 1 → (b₁ + b₂) / 2 + (b₂ - b₁) / 2 * v ∈ Set.Icc b₁ b₂ := by
    intro v hv
    obtain ⟨h1, h2⟩ := abs_le.1 hv
    constructor <;> nlinarith [hb, h1, h2]
  set Φ : ℂ → ℝ × ℝ := fun z ↦
    ((a₁ + a₂) / 2 + (a₂ - a₁) / 2 * (squareChart z).re,
     (b₁ + b₂) / 2 + (b₂ - b₁) / 2 * (squareChart z).im) with hΦ
  have hΦcont : Continuous Φ := by
    rw [hΦ]
    exact (continuous_const.add (continuous_const.mul
        (Complex.continuous_re.comp squareChart_continuous))).prodMk
      (continuous_const.add (continuous_const.mul
        (Complex.continuous_im.comp squareChart_continuous)))
  have hΦmem : ∀ z ∈ closedBall (0 : ℂ) 1, Φ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂ := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
    exact Set.mk_mem_prod (haffineX _ (le_trans (squareChart_re_le z) hzn))
      (haffineY _ (le_trans (squareChart_im_le z) hzn))
  have hΦxmem : ∀ z ∈ closedBall (0 : ℂ) 1, (Φ z).1 ∈ Set.Icc a₁ a₂ :=
    fun z hz ↦ (Set.mem_prod.1 (hΦmem z hz)).1
  have hΦymem : ∀ z ∈ closedBall (0 : ℂ) 1, (Φ z).2 ∈ Set.Icc b₁ b₂ :=
    fun z hz ↦ (Set.mem_prod.1 (hΦmem z hz)).2
  set F : ℂ → ℂ := fun z ↦ ((G (Φ z)).1 : ℂ) + ((G (Φ z)).2 : ℂ) * Complex.I with hFdef
  have hFre : ∀ z, (F z).re = (G (Φ z)).1 := by intro z; rw [hFdef]; simp
  have hFim : ∀ z, (F z).im = (G (Φ z)).2 := by intro z; rw [hFdef]; simp
  have hGΦ : ContinuousOn (fun z ↦ G (Φ z)) (closedBall 0 1) :=
    hG.comp hΦcont.continuousOn hΦmem
  have hF : ContinuousOn F (closedBall 0 1) := by
    rw [hFdef]
    exact (Complex.continuous_ofReal.comp_continuousOn
        (continuous_fst.comp_continuousOn hGΦ)).add
      ((Complex.continuous_ofReal.comp_continuousOn
        (continuous_snd.comp_continuousOn hGΦ)).mul continuousOn_const)
  have hface_r_pos : ∀ z, (squareChart z).re = 1 → (Φ z).2 ∈ Set.Icc b₁ b₂ →
      0 < (G (Φ z)).1 := by
    intro z hsc hy
    have hx : (Φ z).1 = a₂ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = (a₂, (Φ z).2) := Prod.ext hx rfl
    rw [heq]; exact hright _ hy
  have hface_r_neg : ∀ z, (squareChart z).re = -1 → (Φ z).2 ∈ Set.Icc b₁ b₂ →
      (G (Φ z)).1 < 0 := by
    intro z hsc hy
    have hx : (Φ z).1 = a₁ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = (a₁, (Φ z).2) := Prod.ext hx rfl
    rw [heq]; exact hleft _ hy
  have hface_t_pos : ∀ z, (squareChart z).im = 1 → (Φ z).1 ∈ Set.Icc a₁ a₂ →
      0 < (G (Φ z)).2 := by
    intro z hsc hx
    have hy : (Φ z).2 = b₂ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = ((Φ z).1, b₂) := Prod.ext rfl hy
    rw [heq]; exact htop _ hx
  have hface_b_neg : ∀ z, (squareChart z).im = -1 → (Φ z).1 ∈ Set.Icc a₁ a₂ →
      (G (Φ z)).2 < 0 := by
    intro z hsc hx
    have hy : (Φ z).2 = b₁ := by rw [hΦ]; dsimp only; rw [hsc]; ring
    have heq : Φ z = ((Φ z).1, b₁) := Prod.ext rfl hy
    rw [heq]; exact hbot _ hx
  have hbd : ∀ z ∈ sphere (0 : ℂ) 1, F z ≠ 0 := by
    intro z hz
    have hzn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hzn
    have hzcb : z ∈ closedBall (0 : ℂ) 1 := by
      simp [mem_closedBall, dist_zero_right, hzn]
    intro hFz
    have hA : (G (Φ z)).1 = 0 := by rw [← hFre z, hFz, Complex.zero_re]
    have hB : (G (Φ z)).2 = 0 := by rw [← hFim z, hFz, Complex.zero_im]
    rcases le_total |z.im| |z.re| with hle | hle
    · have hre0 : z.re ≠ 0 := by
        intro h; rw [h, abs_zero] at hle
        exact hz0 (Complex.ext h (abs_nonpos_iff.1 hle))
      rcases lt_or_gt_of_ne hre0 with hneg | hpos
      · have := hface_r_neg z (squareChart_re_eq_neg_one hzn hle hneg) (hΦymem z hzcb)
        linarith
      · have := hface_r_pos z (squareChart_re_eq_one hzn hle hpos) (hΦymem z hzcb)
        linarith
    · have him0 : z.im ≠ 0 := by
        intro h; rw [h, abs_zero] at hle
        exact hz0 (Complex.ext (abs_nonpos_iff.1 hle) h)
      rcases lt_or_gt_of_ne him0 with hneg | hpos
      · have := hface_b_neg z (squareChart_im_eq_neg_one hzn hle hneg) (hΦxmem z hzcb)
        linarith
      · have := hface_t_pos z (squareChart_im_eq_one hzn hle hpos) (hΦxmem z hzcb)
        linarith
  have hFs : ContinuousOn F (sphere (0 : ℂ) |(1 : ℝ)|) :=
    hF.mono (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall (abs_of_pos one_pos).le))
  have hbd' : ∀ z ∈ sphere (0 : ℂ) |(1 : ℝ)|, F z ≠ 0 := fun z hz ↦
    hbd z (mem_sphere.2 ((mem_sphere.1 hz).trans (abs_of_pos one_pos)))
  have hwind : windingNumberAt 0 (circleLoop F 0 1 hFs)
      (circleLoop_ne F 0 1 0 hFs hbd') ≠ 0 := by
    have hpi := Real.pi_pos
    have h2pi : (0 : ℝ) < 2 * π := by positivity
    have hbl : ∀ t : I, circleLoop F 0 1 hFs t = F (circleMap 0 1 (2 * π * (t : ℝ))) :=
      fun _ ↦ rfl
    have hwtn : ∀ t : I, ‖circleMap 0 1 (2 * π * (t : ℝ))‖ = 1 := by
      intro t; rw [norm_circleMap_zero, abs_one]
    have hwtcb : ∀ t : I, circleMap 0 1 (2 * π * (t : ℝ)) ∈ closedBall (0 : ℂ) 1 := by
      intro t
      rw [mem_closedBall, dist_zero_right, norm_circleMap_zero]
      exact abs_one.le
    have hw1 : windingNumberAt 0 (circleLoop F 0 1 hFs)
        (circleLoop_ne F 0 1 0 hFs hbd') = 1 := by
      apply windingNumberAt_eq_one_of_fourArcs
      · rw [hbl 0, hbl 1, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one]
        exact congrArg F (by simpa using (periodic_circleMap 0 1 0).symm)
      · intro t ht
        rw [hbl t, hFre]
        refine hface_r_pos _ ?_ (hΦymem _ (hwtcb t))
        apply squareChart_re_eq_one (hwtn t)
        · rw [circleMap_zero_one_re, circleMap_zero_one_im]
          apply abs_sin_le_abs_cos_of_cos_two_mul_nonneg
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring]
          rcases ht with h | h
          · exact Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr
              ⟨by nlinarith [hpi, h2pi, t.2.1], by nlinarith [hpi, h2pi, h]⟩)
          · rw [show 4 * π * (t : ℝ) = (4 * π * (t : ℝ) - 4 * π) + 2 * π + 2 * π by ring,
              Real.cos_add_two_pi, Real.cos_add_two_pi]
            exact Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr
              ⟨by nlinarith [hpi, h2pi, h], by nlinarith [hpi, h2pi, t.2.2]⟩)
        · rw [circleMap_zero_one_re]
          rcases ht with h | h
          · exact Real.cos_pos_of_mem_Ioo (Set.mem_Ioo.mpr
              ⟨by nlinarith [hpi, h2pi, t.2.1], by nlinarith [hpi, h2pi, h]⟩)
          · rw [show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring,
              Real.cos_add_two_pi]
            exact Real.cos_pos_of_mem_Ioo (Set.mem_Ioo.mpr
              ⟨by nlinarith [hpi, h2pi, h], by nlinarith [hpi, h2pi, t.2.2]⟩)
      · intro t hl hr
        rw [hbl t, hFim]
        refine hface_t_pos _ ?_ (hΦxmem _ (hwtcb t))
        apply squareChart_im_eq_one (hwtn t)
        · rw [circleMap_zero_one_re, circleMap_zero_one_im]
          apply abs_cos_le_abs_sin_of_cos_two_mul_nonpos
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring]
          have hp : (0 : ℝ) ≤ Real.cos (4 * π * (t : ℝ) + π) := by
            rw [show 4 * π * (t : ℝ) + π = (4 * π * (t : ℝ) - π) + 2 * π by ring,
              Real.cos_add_two_pi]
            exact Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr
              ⟨by nlinarith [hpi, h2pi, hl], by nlinarith [hpi, h2pi, hr]⟩)
          have hcp := Real.cos_add_pi (4 * π * (t : ℝ))
          linarith
        · rw [circleMap_zero_one_im]
          exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hpi, h2pi, hl])
            (by nlinarith [hpi, h2pi, hr])
      · intro t hl hr
        rw [hbl t, hFre]
        refine hface_r_neg _ ?_ (hΦymem _ (hwtcb t))
        apply squareChart_re_eq_neg_one (hwtn t)
        · rw [circleMap_zero_one_re, circleMap_zero_one_im]
          apply abs_sin_le_abs_cos_of_cos_two_mul_nonneg
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring,
            show 4 * π * (t : ℝ) = (4 * π * (t : ℝ) - 2 * π) + 2 * π by ring,
            Real.cos_add_two_pi]
          exact Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr
            ⟨by nlinarith [hpi, h2pi, hl], by nlinarith [hpi, h2pi, hr]⟩)
        · rw [circleMap_zero_one_re]
          exact Real.cos_neg_of_pi_div_two_lt_of_lt
            (by nlinarith [hpi, h2pi, hl]) (by nlinarith [hpi, h2pi, hr])
      · intro t hl hr
        rw [hbl t, hFim]
        refine hface_b_neg _ ?_ (hΦxmem _ (hwtcb t))
        apply squareChart_im_eq_neg_one (hwtn t)
        · rw [circleMap_zero_one_re, circleMap_zero_one_im]
          apply abs_cos_le_abs_sin_of_cos_two_mul_nonpos
          rw [show (2 : ℝ) * (2 * π * (t : ℝ)) = 4 * π * (t : ℝ) by ring]
          have hp : (0 : ℝ) ≤ Real.cos (4 * π * (t : ℝ) + π) := by
            rw [show 4 * π * (t : ℝ) + π = (4 * π * (t : ℝ) - 3 * π) + 2 * π + 2 * π by
                ring,
              Real.cos_add_two_pi, Real.cos_add_two_pi]
            exact Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr
              ⟨by nlinarith [hpi, h2pi, hl], by nlinarith [hpi, h2pi, hr]⟩)
          have hcp := Real.cos_add_pi (4 * π * (t : ℝ))
          linarith
        · rw [circleMap_zero_one_im,
            show 2 * π * (t : ℝ) = (2 * π * (t : ℝ) - 2 * π) + 2 * π by ring,
            Real.sin_add_two_pi]
          exact Real.sin_neg_of_neg_of_neg_pi_lt
            (by nlinarith [hpi, h2pi, hr]) (by nlinarith [hpi, h2pi, hl])
    rw [hw1]
    exact one_ne_zero
  obtain ⟨z₀, hz₀ball, hz₀⟩ :=
    exists_eq_of_windingNumberAt_ne_zero F 0 one_pos 0 hF hbd hwind
  have hz₀cb : z₀ ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz₀ball
  refine ⟨Φ z₀, hΦmem z₀ hz₀cb, ?_⟩
  have hA : (G (Φ z₀)).1 = 0 := by rw [← hFre z₀, hz₀, Complex.zero_re]
  have hB : (G (Φ z₀)).2 = 0 := by rw [← hFim z₀, hz₀, Complex.zero_im]
  exact Prod.ext hA hB

/-! ### The Poincaré–Miranda theorem -/

/-- **The Poincaré–Miranda theorem** in the plane — the two-dimensional intermediate value
theorem.  A continuous map `G = (G₁, G₂) : [a₁, a₂] × [b₁, b₂] → ℝ × ℝ` with each component
sign-definite on the pair of opposite faces it controls — `G₁ ≤ 0` on the left face
`{a₁} × [b₁, b₂]` and `G₁ ≥ 0` on the right face `{a₂} × [b₁, b₂]`; `G₂ ≤ 0` on the bottom
face `[a₁, a₂] × {b₁}` and `G₂ ≥ 0` on the top face `[a₁, a₂] × {b₂}` — has a zero in the
rectangle.

The weak face inequalities are the literature-standard form of the theorem (Kulpa, *The
Poincaré-Miranda theorem*, Amer. Math. Monthly 104 (1997), 545–550); consequently the zero
may lie on the boundary of the rectangle.  Degenerate rectangles (`a₁ = a₂` or `b₁ = b₂`)
are allowed.  The 1-dimensional analogue is `intermediate_value_Icc`; the Brouwer fixed-point
theorem for a rectangle follows as the corollary `exists_fixedPoint_prod_Icc`. -/
theorem poincare_miranda {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (G : ℝ × ℝ → ℝ × ℝ)
    (hG : ContinuousOn G (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hleft : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 ≤ 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂, 0 ≤ (G (a₂, y)).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 ≤ 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂, 0 ≤ (G (x, b₂)).2) :
    ∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, G p = 0 := by
  rcases ha.eq_or_lt with hae | halt
  · have hxmem : a₁ ∈ Set.Icc a₁ a₂ := ⟨le_rfl, ha⟩
    have hg1 : ∀ y ∈ Set.Icc b₁ b₂, (G (a₁, y)).1 = 0 := by
      intro y hy
      have h1 := hleft y hy
      have h2 := hright y hy
      rw [← hae] at h2
      linarith
    have hfcont : ContinuousOn (fun y ↦ G (a₁, y)) (Set.Icc b₁ b₂) :=
      hG.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun y hy ↦ Set.mk_mem_prod hxmem hy)
    have hcont : ContinuousOn (fun y ↦ (G (a₁, y)).2) (Set.Icc b₁ b₂) :=
      continuous_snd.comp_continuousOn hfcont
    have hmem : (0 : ℝ) ∈
        Set.Icc ((fun y ↦ (G (a₁, y)).2) b₁) ((fun y ↦ (G (a₁, y)).2) b₂) :=
      ⟨hbot a₁ hxmem, htop a₁ hxmem⟩
    obtain ⟨y₀, hy₀mem, hy₀⟩ := intermediate_value_Icc hb hcont hmem
    exact ⟨(a₁, y₀), Set.mk_mem_prod hxmem hy₀mem, Prod.ext (hg1 y₀ hy₀mem) hy₀⟩
  rcases hb.eq_or_lt with hbe | hblt
  · have hymem : b₁ ∈ Set.Icc b₁ b₂ := ⟨le_rfl, hb⟩
    have hg2 : ∀ x ∈ Set.Icc a₁ a₂, (G (x, b₁)).2 = 0 := by
      intro x hx
      have h1 := hbot x hx
      have h2 := htop x hx
      rw [← hbe] at h2
      linarith
    have hfcont : ContinuousOn (fun x ↦ G (x, b₁)) (Set.Icc a₁ a₂) :=
      hG.comp ((continuous_id.prodMk continuous_const).continuousOn)
        (fun x hx ↦ Set.mk_mem_prod hx hymem)
    have hcont : ContinuousOn (fun x ↦ (G (x, b₁)).1) (Set.Icc a₁ a₂) :=
      continuous_fst.comp_continuousOn hfcont
    have hmem : (0 : ℝ) ∈
        Set.Icc ((fun x ↦ (G (x, b₁)).1) a₁) ((fun x ↦ (G (x, b₁)).1) a₂) :=
      ⟨hleft b₁ hymem, hright b₁ hymem⟩
    obtain ⟨x₀, hx₀mem, hx₀⟩ := intermediate_value_Icc ha hcont hmem
    exact ⟨(x₀, b₁), Set.mk_mem_prod hx₀mem hymem, Prod.ext hx₀ (hg2 x₀ hx₀mem)⟩
  set K : Set (ℝ × ℝ) := Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  set cx : ℝ := (a₁ + a₂) / 2 with hcx
  set cy : ℝ := (b₁ + b₂) / 2 with hcy
  set w : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 - cx, p.2 - cy) with hw
  have hwcont : Continuous w := by fun_prop
  set Gn : ℕ → ℝ × ℝ → ℝ × ℝ := fun n p ↦ G p + (1 / ((n : ℝ) + 1)) • w p with hGn
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n ↦ by positivity
  have hzero : ∀ n : ℕ, ∃ p ∈ K, Gn n p = 0 := by
    intro n
    apply poincare_miranda_of_lt halt hblt (Gn n)
    · exact hG.add (Continuous.continuousOn (by fun_prop))
    · intro y hy
      have hGl := hleft y hy
      have he : (Gn n (a₁, y)).1 = (G (a₁, y)).1 + (1 / ((n : ℝ) + 1)) * (a₁ - cx) := by
        simp [hGn, hw]
      rw [he]
      have : (1 / ((n : ℝ) + 1)) * (a₁ - cx) < 0 :=
        mul_neg_of_pos_of_neg (hpos n) (by rw [hcx]; linarith)
      linarith
    · intro y hy
      have hGr := hright y hy
      have he : (Gn n (a₂, y)).1 = (G (a₂, y)).1 + (1 / ((n : ℝ) + 1)) * (a₂ - cx) := by
        simp [hGn, hw]
      rw [he]
      have : (0 : ℝ) < (1 / ((n : ℝ) + 1)) * (a₂ - cx) :=
        mul_pos (hpos n) (by rw [hcx]; linarith)
      linarith
    · intro x hx
      have hGb := hbot x hx
      have he : (Gn n (x, b₁)).2 = (G (x, b₁)).2 + (1 / ((n : ℝ) + 1)) * (b₁ - cy) := by
        simp [hGn, hw]
      rw [he]
      have : (1 / ((n : ℝ) + 1)) * (b₁ - cy) < 0 :=
        mul_neg_of_pos_of_neg (hpos n) (by rw [hcy]; linarith)
      linarith
    · intro x hx
      have hGt := htop x hx
      have he : (Gn n (x, b₂)).2 = (G (x, b₂)).2 + (1 / ((n : ℝ) + 1)) * (b₂ - cy) := by
        simp [hGn, hw]
      rw [he]
      have : (0 : ℝ) < (1 / ((n : ℝ) + 1)) * (b₂ - cy) :=
        mul_pos (hpos n) (by rw [hcy]; linarith)
      linarith
  choose p hpK hpz using hzero
  obtain ⟨q, hqK, φ, hφ, hlim⟩ := hKcomp.tendsto_subseq hpK
  refine ⟨q, hqK, ?_⟩
  have hGq : Filter.Tendsto (fun k ↦ G (p (φ k))) Filter.atTop (nhds (G q)) := by
    have hcw : ContinuousWithinAt G K q := hG q hqK
    have hin : Filter.Tendsto (fun k ↦ p (φ k)) Filter.atTop (nhdsWithin q K) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hlim, Filter.Eventually.of_forall (fun k ↦ hpK (φ k))⟩
    exact (hcw.tendsto).comp hin
  have hpert : Filter.Tendsto (fun k ↦ (1 / ((φ k : ℝ) + 1)) • w (p (φ k)))
      Filter.atTop (nhds (0 : ℝ × ℝ)) := by
    have h0 : Filter.Tendsto (fun k ↦ 1 / ((φ k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hwlim : Filter.Tendsto (fun k ↦ w (p (φ k))) Filter.atTop (nhds (w q)) :=
      (hwcont.tendsto q).comp hlim
    simpa using h0.smul hwlim
  have heq : Filter.Tendsto (fun k ↦ G (p (φ k))) Filter.atTop (nhds (0 : ℝ × ℝ)) := by
    have hcancel : ∀ k, G (p (φ k)) = -((1 / ((φ k : ℝ) + 1)) • w (p (φ k))) := by
      intro k
      have h := hpz (φ k)
      simp only [hGn] at h
      exact eq_neg_of_add_eq_zero_left h
    have hneg : Filter.Tendsto (fun k ↦ -((1 / ((φ k : ℝ) + 1)) • w (p (φ k))))
        Filter.atTop (nhds (0 : ℝ × ℝ)) := by simpa using hpert.neg
    exact hneg.congr (fun k ↦ (hcancel k).symm)
  exact tendsto_nhds_unique hGq heq

/-! ### The Brouwer fixed-point theorem for a rectangle -/

-- TODO(PR): consider renaming to `exists_isFixedPt_Icc_prod_Icc` and stating the conclusion
-- via `Function.IsFixedPt`, matching mathlib's fixed-point vocabulary.
/-- **The Brouwer fixed-point theorem for a plane rectangle.**  A continuous self-map of a
closed rectangle `[a₁, a₂] × [b₁, b₂]` (possibly degenerate) has a fixed point.  This is the
classical corollary of the Poincaré–Miranda theorem, applied to `G p = p - f p`. -/
theorem exists_fixedPoint_prod_Icc {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (f : ℝ × ℝ → ℝ × ℝ) (hf : ContinuousOn f (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hmaps : Set.MapsTo f (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)
      (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)) :
    ∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, f p = p := by
  obtain ⟨p, hp, hzero⟩ := poincare_miranda ha hb (fun p ↦ p - f p)
    (continuousOn_id.sub hf)
    (fun y hy ↦ sub_nonpos.2 (hmaps (Set.mk_mem_prod ⟨le_rfl, ha⟩ hy)).1.1)
    (fun y hy ↦ sub_nonneg.2 (hmaps (Set.mk_mem_prod ⟨ha, le_rfl⟩ hy)).1.2)
    (fun x hx ↦ sub_nonpos.2 (hmaps (Set.mk_mem_prod hx ⟨le_rfl, hb⟩)).2.1)
    (fun x hx ↦ sub_nonneg.2 (hmaps (Set.mk_mem_prod hx ⟨hb, le_rfl⟩)).2.2)
  exact ⟨p, hp, (sub_eq_zero.1 hzero).symm⟩
