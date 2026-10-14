/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import ForMathlib.Analysis.Complex.ConeWinding
import Mathlib.Analysis.Normed.Module.Convex

/-!
# A zero-existence principle on a diamond

Four consecutive boundary arcs are tested in four different open half-planes.
The coordinate swap gives a model with winding minus one.
-/

open scoped unitInterval

namespace Complex

/-- The closed diamond, measured in the coordinate one-norm. -/
def diamond (r : ℝ) : Set ℂ := {z | |z.re| + |z.im| ≤ r}

/-- The diamond is convex. -/
theorem convex_diamond (r : ℝ) : Convex ℝ (diamond r) := by
  have hre : ConvexOn ℝ Set.univ (fun z : ℂ ↦ |z.re|) := by
    simpa [Function.comp_def, Real.norm_eq_abs] using
      (convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set ℝ))).comp_linearMap Complex.reLm
  have him : ConvexOn ℝ Set.univ (fun z : ℂ ↦ |z.im|) := by
    simpa [Function.comp_def, Real.norm_eq_abs] using
      (convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set ℝ))).comp_linearMap Complex.imLm
  simpa [diamond] using (hre.add him).convex_le r

private noncomputable def circlePhase : C(I, ℝ) :=
  ⟨fun t ↦ 2 * Real.pi * (t : ℝ), by fun_prop⟩

private noncomputable def unitLoop : C(I, ℂ) := phaseCurve circlePhase

private theorem norm_unitLoop (t : I) : ‖unitLoop t‖ = 1 :=
  norm_exp_ofReal_mul_I _

private theorem l1_unitLoop_pos (t : I) : 0 < |(unitLoop t).re| + |(unitLoop t).im| := by
  have h := norm_le_abs_re_add_abs_im (unitLoop t)
  linarith [norm_unitLoop t]

/-- Radial projection of the unit circle onto the boundary of the diamond of radius `r`. -/
noncomputable def diamondBoundary (r : ℝ) : C(I, ℂ) :=
  ⟨fun t ↦ (r / (|(unitLoop t).re| + |(unitLoop t).im|)) • unitLoop t, by
    exact (continuous_const.div ((Complex.continuous_re.comp unitLoop.continuous).abs.add
      (Complex.continuous_im.comp unitLoop.continuous).abs)
      (fun t ↦ (l1_unitLoop_pos t).ne')).smul unitLoop.continuous⟩

/-- Every boundary point has the prescribed coordinate one-norm. -/
theorem diamondBoundary_mem {r : ℝ} (hr : 0 ≤ r) (t : I) :
    |(diamondBoundary r t).re| + |(diamondBoundary r t).im| = r := by
  simp only [diamondBoundary, ContinuousMap.coe_mk, smul_re, smul_im, smul_eq_mul,
    abs_mul, abs_of_nonneg (div_nonneg hr (l1_unitLoop_pos t).le)]
  rw [← mul_add, div_mul_cancel₀ _ (l1_unitLoop_pos t).ne']

private theorem unitLoop_closed : unitLoop 0 = unitLoop 1 := by
  simp [unitLoop, phaseCurve, circlePhase, exp_two_pi_mul_I]

/-- The radial boundary parametrization is a closed loop. -/
theorem diamondBoundary_closed (r : ℝ) : diamondBoundary r 0 = diamondBoundary r 1 := by
  simp only [diamondBoundary, ContinuousMap.coe_mk, unitLoop_closed]

private noncomputable def reversedPhase : C(I, ℝ) :=
  ⟨fun t ↦ Real.pi / 2 - 2 * Real.pi * (t : ℝ), by fun_prop⟩

private theorem reversedPhase_eq_swap (t : I) :
    phaseCurve reversedPhase t = Complex.I * star (unitLoop t) := by
  apply Complex.ext
  all_goals simp only [phaseCurve, unitLoop, ContinuousMap.coe_mk, mul_re, mul_im,
    I_re, I_im, star_def, conj_re, conj_im, zero_mul, one_mul, zero_sub, zero_add,
    neg_neg, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  all_goals simp [reversedPhase, circlePhase, Real.cos_sub, Real.sin_sub]

private theorem reversedPhase_winding :
    windingNumberAt 0 (phaseCurve reversedPhase) (phaseCurve_ne_zero reversedPhase) = -1 := by
  rw [windingNumberAt_phaseCurve]
  norm_num [reversedPhase, Real.pi_ne_zero]

/-- The four boundary arcs have the coordinate signs of a reflected unit-circle loop. -/
structure DiamondSigns (F : ℂ → ℂ) (r : ℝ) : Prop where
  top : ∀ z, |z.re| + |z.im| = r → |z.re| ≤ z.im → 0 < (F z).re
  left : ∀ z, |z.re| + |z.im| = r → |z.im| ≤ -z.re → (F z).im < 0
  bottom : ∀ z, |z.re| + |z.im| = r → |z.re| ≤ -z.im → (F z).re < 0
  right : ∀ z, |z.re| + |z.im| = r → |z.im| ≤ z.re → 0 < (F z).im

private theorem common_halfPlane_of_diamondSigns {F : ℂ → ℂ} {r a : ℝ} {z v : ℂ}
    (hr : 0 < r) (ha : 0 < a) (hbd : |z.re| + |z.im| = r)
    (hre : z.re = a * v.im) (him : z.im = a * v.re) (hF : DiamondSigns F r) :
    ∃ L : ℂ →ₗ[ℝ] ℝ, 0 < L (F z) ∧ 0 < L v := by
  rcases le_total |z.re| |z.im| with hvertical | hhorizontal
  · rcases le_total 0 z.im with hpos | hneg
    · refine ⟨Complex.reLm, hF.top z hbd ?_, ?_⟩
      · simpa [abs_of_nonneg hpos] using hvertical
      · change 0 < v.re
        nlinarith [abs_of_nonneg hpos]
    · refine ⟨-Complex.reLm, neg_pos.mpr (hF.bottom z hbd ?_), ?_⟩
      · simpa [abs_of_nonpos hneg] using hvertical
      · change 0 < -v.re
        nlinarith [abs_of_nonpos hneg]
  · rcases le_total 0 z.re with hpos | hneg
    · refine ⟨Complex.imLm, hF.right z hbd ?_, ?_⟩
      · simpa [abs_of_nonneg hpos] using hhorizontal
      · change 0 < v.im
        nlinarith [abs_of_nonneg hpos]
    · refine ⟨-Complex.imLm, neg_pos.mpr (hF.left z hbd ?_), ?_⟩
      · simpa [abs_of_nonpos hneg] using hhorizontal
      · change 0 < -v.im
        nlinarith [abs_of_nonpos hneg]

private theorem diamondSigns_boundaryCone {F : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hF : DiamondSigns F r) (t : I) :
    ∃ L : ℂ →ₗ[ℝ] ℝ, 0 < L (F (diamondBoundary r t)) ∧
      0 < L (phaseCurve reversedPhase t) := by
  refine common_halfPlane_of_diamondSigns hr (div_pos hr (l1_unitLoop_pos t))
    (diamondBoundary_mem hr.le t) ?_ ?_ hF
  all_goals simp only [diamondBoundary, ContinuousMap.coe_mk, smul_re, smul_im,
    smul_eq_mul, reversedPhase_eq_swap, mul_re, mul_im, I_re, I_im, star_def,
    conj_re, conj_im, zero_mul, one_mul, zero_add, zero_sub, neg_neg]

/-- A continuous field with the four reflected boundary signs has a zero in the diamond. -/
theorem exists_zero_of_diamondSigns {r : ℝ} (hr : 0 < r) (F : ℂ → ℂ)
    (hF : ContinuousOn F (diamond r)) (hsigns : DiamondSigns F r) :
    ∃ z ∈ diamond r, F z = 0 := by
  have hmem : ∀ t, diamondBoundary r t ∈ diamond r :=
    fun t ↦ (diamondBoundary_mem hr.le t).le
  let γ : C(I, ℂ) :=
    ⟨F ∘ diamondBoundary r, hF.comp_continuous (diamondBoundary r).continuous hmem⟩
  have hcone : ∀ t, ∃ L : ℂ →ₗ[ℝ] ℝ, 0 < L (γ t) ∧
      0 < L (phaseCurve reversedPhase t) := diamondSigns_boundaryCone hr hsigns
  have hne : ∀ t, γ t ≠ 0 := by
    intro t ht
    obtain ⟨L, hL, -⟩ := hcone t
    simp [ht] at hL
  have hmodel : phaseCurve reversedPhase 0 = phaseCurve reversedPhase 1 := by
    rw [reversedPhase_eq_swap, reversedPhase_eq_swap, unitLoop_closed]
  have hw := windingNumberAt_eq_of_common_halfPlane γ (phaseCurve reversedPhase)
    hne (phaseCurve_ne_zero reversedPhase) (congrArg F (diamondBoundary_closed r))
    hmodel hcone
  refine exists_zero_of_windingNumberAt_ne_zero_on_convex (convex_diamond r) 0
    (by simpa [diamond] using hr.le) F hF (diamondBoundary r) hmem
    (diamondBoundary_closed r) hne ?_
  exact (hw.trans reversedPhase_winding).trans_ne (neg_ne_zero.mpr one_ne_zero)

end Complex
