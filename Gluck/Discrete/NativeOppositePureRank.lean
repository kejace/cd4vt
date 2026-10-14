/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.NativeOppositePureDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!+# Derivative core of the native opposite-pure controller

The low-curvature angle defects have strictly positive derivatives, as
does the high-curvature angle excess on its original physical domain.
These signs give the mixed-split determinant without an orthogonality
assumption. The branch comparison retains both possible second-cap turns.
-/

namespace Gluck.Discrete.NativeOppositePure

open Set

/-- Derivative of the principal endpoint atom `arcsin (a * sin z)`. -/
noncomputable def angleSlope (a z : ℝ) : ℝ :=
  a * Real.cos z / √(1 - (a * Real.sin z) ^ 2)

private theorem sin_pos_of_acute {z : ℝ}
    (hz : 0 < z) (hz' : z < Real.pi / 2) : 0 < Real.sin z :=
  Real.sin_pos_of_pos_of_lt_pi hz (by linarith [Real.pi_pos])

private theorem cos_pos_of_acute {z : ℝ}
    (hz : 0 < z) (hz' : z < Real.pi / 2) : 0 < Real.cos z :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hz'⟩

theorem endpoint_arg_lt_one {a z : ℝ}
    (_ha : 0 < a) (ha1 : a < 1) (hz : 0 < z) (hz' : z < Real.pi / 2) :
    a * Real.sin z < 1 := by
  have hs := sin_pos_of_acute hz hz'
  have hmul : a * Real.sin z < Real.sin z := by nlinarith
  exact hmul.trans_le (Real.sin_le_one z)

theorem endpoint_radicand_pos {a z : ℝ}
    (ha : 0 < a) (hz : 0 < z) (hz' : z < Real.pi / 2)
    (hwall : a * Real.sin z < 1) :
    0 < 1 - (a * Real.sin z) ^ 2 := by
  have harg : 0 < a * Real.sin z := mul_pos ha (sin_pos_of_acute hz hz')
  nlinarith

theorem hasDerivAt_endpointAtom {a z : ℝ}
    (ha : 0 < a) (hz : 0 < z) (hz' : z < Real.pi / 2)
    (hwall : a * Real.sin z < 1) :
    HasDerivAt (fun x : ℝ => Real.arcsin (a * Real.sin x)) (angleSlope a z) z := by
  have harg : 0 < a * Real.sin z := mul_pos ha (sin_pos_of_acute hz hz')
  have hd := (Real.hasDerivAt_arcsin (by linarith : a * Real.sin z ≠ -1)
    (ne_of_lt hwall)).comp z ((Real.hasDerivAt_sin z).const_mul a)
  simpa only [angleSlope, Function.comp_def, div_eq_mul_inv, one_mul,
    mul_comm, mul_left_comm, mul_assoc] using hd

theorem angleSlope_pos {a z : ℝ}
    (ha : 0 < a) (hz : 0 < z) (hz' : z < Real.pi / 2)
    (hwall : a * Real.sin z < 1) : 0 < angleSlope a z := by
  exact div_pos (mul_pos ha (cos_pos_of_acute hz hz'))
    (Real.sqrt_pos.2 (endpoint_radicand_pos ha hz hz' hwall))

theorem angleSlope_lt_one {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : 0 < z) (hz' : z < Real.pi / 2) :
    angleSlope a z < 1 := by
  have hwall := endpoint_arg_lt_one ha ha1 hz hz'
  have hrad := endpoint_radicand_pos ha hz hz' hwall
  have hsqrt := Real.sqrt_pos.2 hrad
  have hsquare := Real.sq_sqrt hrad.le
  have hnum : 0 < a * Real.cos z := mul_pos ha (cos_pos_of_acute hz hz')
  have htrig := Real.sin_sq_add_cos_sq z
  have ha2 : a ^ 2 < 1 := by nlinarith
  have hdiff : (a * Real.cos z) ^ 2 < 1 - (a * Real.sin z) ^ 2 := by
    nlinarith [congrArg (fun v : ℝ => a ^ 2 * v) htrig]
  have hlt : a * Real.cos z < √(1 - (a * Real.sin z) ^ 2) := by
    nlinarith
  exact (div_lt_one hsqrt).2 hlt

theorem one_lt_angleSlope {a z : ℝ}
    (ha1 : 1 < a) (hz : 0 < z) (hz' : z < Real.pi / 2)
    (hwall : a * Real.sin z < 1) : 1 < angleSlope a z := by
  have ha : 0 < a := by linarith
  have hrad := endpoint_radicand_pos ha hz hz' hwall
  have hsqrt := Real.sqrt_pos.2 hrad
  have hsquare := Real.sq_sqrt hrad.le
  have hnum : 0 < a * Real.cos z := mul_pos ha (cos_pos_of_acute hz hz')
  have htrig := Real.sin_sq_add_cos_sq z
  have ha2 : 1 < a ^ 2 := by nlinarith
  have hdiff : 1 - (a * Real.sin z) ^ 2 < (a * Real.cos z) ^ 2 := by
    nlinarith [congrArg (fun v : ℝ => a ^ 2 * v) htrig]
  have hlt : √(1 - (a * Real.sin z) ^ 2) < a * Real.cos z := by
    nlinarith
  exact (one_lt_div hsqrt).2 hlt

theorem hasDerivAt_lowDefect {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : 0 < z) (hz' : z < Real.pi / 2) :
    HasDerivAt (fun x : ℝ => x - Real.arcsin (a * Real.sin x))
      (1 - angleSlope a z) z := by
  exact (hasDerivAt_id z).sub
    (hasDerivAt_endpointAtom ha hz hz' (endpoint_arg_lt_one ha ha1 hz hz'))

theorem lowDefect_derivative_pos {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : 0 < z) (hz' : z < Real.pi / 2) :
    0 < 1 - angleSlope a z := sub_pos.2 (angleSlope_lt_one ha ha1 hz hz')

theorem hasDerivAt_highExcess {a z : ℝ}
    (ha1 : 1 < a) (hz : 0 < z) (hz' : z < Real.pi / 2)
    (hwall : a * Real.sin z < 1) :
    HasDerivAt (fun x : ℝ => Real.arcsin (a * Real.sin x) - x)
      (angleSlope a z - 1) z := by
  exact (hasDerivAt_endpointAtom (by linarith) hz hz' hwall).sub (hasDerivAt_id z)

theorem highExcess_derivative_pos {a z : ℝ}
    (ha1 : 1 < a) (hz : 0 < z) (hz' : z < Real.pi / 2)
    (hwall : a * Real.sin z < 1) :
    0 < angleSlope a z - 1 := sub_pos.2 (one_lt_angleSlope ha1 hz hz' hwall)

theorem hasDerivAt_angleAtom {a z : ℝ}
    (ha : 0 < a) (hz : 0 < z) (hz' : z < Real.pi / 2)
    (hwall : a * Real.sin z < 1) :
    HasDerivAt (angleAtom a) (angleSlope a z) z :=
  hasDerivAt_endpointAtom ha hz hz' hwall

theorem hasDerivAt_angleDefect {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : 0 < z) (hz' : z < Real.pi / 2) :
    HasDerivAt (angleDefect a) (1 - angleSlope a z) z :=
  hasDerivAt_lowDefect ha ha1 hz hz'

theorem hasDerivAt_angleExcess {a z : ℝ}
    (ha1 : 1 < a) (hz : 0 < z) (hz' : z < Real.pi / 2)
    (hwall : a * Real.sin z < 1) :
    HasDerivAt (angleExcess a) (angleSlope a z - 1) z :=
  hasDerivAt_highExcess ha1 hz hz' hwall

theorem endpointAtom_lt_angle {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : 0 < z) (hz' : z < Real.pi / 2) :
    Real.arcsin (a * Real.sin z) < z := by
  have harg : 0 < a * Real.sin z := mul_pos ha (sin_pos_of_acute hz hz')
  have hlt : a * Real.sin z < Real.sin z := by
    nlinarith [sin_pos_of_acute hz hz']
  have h := Real.arcsin_lt_arcsin (by linarith : -1 ≤ a * Real.sin z)
    hlt (Real.sin_le_one z)
  rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) hz'.le] at h

/-- A positive total seam defect and the unequal cap radii force the
first pure turn to be obtuse, without restricting the second turn. -/
theorem pi_div_two_lt_first_sum {S T q : ℝ}
    (hS : 0 < S) (hS' : S < Real.pi) (_hT : 0 < T) (hT' : T < Real.pi)
    (hsum : Real.pi < S + T) (hq : 1 < q)
    (hchord : Real.sin S = Real.sin T / q) : Real.pi / 2 < S := by
  by_contra h
  have hS2 : S ≤ Real.pi / 2 := le_of_not_gt h
  have hsin := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ Real.pi - T by linarith [Real.pi_pos]) hS2
    (show Real.pi - T < S by linarith)
  rw [Real.sin_pi_sub] at hsin
  have hpos := Real.sin_pos_of_pos_of_lt_pi hS hS'
  have hq0 : q ≠ 0 := by linarith
  have heq : Real.sin S * q = Real.sin T := (eq_div_iff hq0).mp hchord
  nlinarith

theorem cos_first_sum_neg {S T q : ℝ}
    (hS : 0 < S) (hS' : S < Real.pi) (hT : 0 < T) (hT' : T < Real.pi)
    (hsum : Real.pi < S + T) (hq : 1 < q)
    (hchord : Real.sin S = Real.sin T / q) : Real.cos S < 0 := by
  exact Real.cos_neg_of_pi_div_two_lt_of_lt
    (pi_div_two_lt_first_sum hS hS' hT hT' hsum hq hchord)
    (by linarith [Real.pi_pos])

theorem angle_sums_gt_pi_of_seamLow_zero {p t q α β γ δ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q) (hq : 0 < q)
    (hα : α ∈ Ioo 0 (Real.pi / 2)) (hγ : γ ∈ Ioo 0 (Real.pi / 2))
    (hlow : seamLow p t q α β γ δ = 0) :
    Real.pi < (α + β) + (γ + δ) := by
  have hpa := endpointAtom_lt_angle hp hp1 hα.1 hα.2
  have htg := endpointAtom_lt_angle (div_pos ht hq) ((div_lt_one hq).2 htq)
    hγ.1 hγ.2
  unfold seamLow lowTurn angleAtom at hlow
  linarith

theorem cos_first_sum_neg_of_root {p t q h α β γ δ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q) (hq : 1 < q)
    (hangles : StrictAngles q h α β γ δ)
    (hlow : seamLow p t q α β γ δ = 0) (hchord : chord q α β γ δ = 0) :
    Real.cos (α + β) < 0 := by
  rcases hangles with ⟨hα, hβ, hγ, hδ, _hwall⟩
  apply cos_first_sum_neg (q := q)
    (by linarith [hα.1, hβ.1]) (by linarith [hα.2, hβ.2])
    (by linarith [hγ.1, hδ.1]) (by linarith [hγ.2, hδ.2])
    (angle_sums_gt_pi_of_seamLow_zero hp hp1 ht htq (by linarith) hα hγ hlow) hq
  exact sub_eq_zero.mp hchord

/-- The split Jacobian is invertible with a strictly positive determinant. -/
theorem split_det_pos {A B C G : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hG : 0 < G) :
    0 < Matrix.det !![-A, -C; B, -G] := by
  rw [Matrix.det_fin_two_of]
  nlinarith [mul_pos hA hG, mul_pos hB hC]

/-- In coordinates `(S, α, γ)` at fixed `T`, this is the controller minor. -/
theorem controller_minor_neg {R A B C G : ℝ}
    (hR : R < 0) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hG : 0 < G) :
    Matrix.det !![R, 0, 0; 1, -A, -C; 1 - B, B, -G] < 0 := by
  have hpos : 0 < A * G + B * C := add_pos (mul_pos hA hG) (mul_pos hB hC)
  have hdet : Matrix.det !![R, 0, 0; 1, -A, -C; 1 - B, B, -G] =
      R * (A * G + B * C) := by
    simp [Matrix.det_fin_three]
    ring
  rw [hdet]
  exact mul_neg_of_neg_of_pos hR hpos

/-- The three split-coordinate derivative columns `(S, α, γ)` at fixed `T`. -/
noncomputable def splitControllerMinor (p t q h l α β γ δ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos (α + β), 0, 0;
    1, -(1 - angleSlope p α), -(1 - angleSlope (t / q) γ);
    1 - (1 - angleSlope l β), 1 - angleSlope l β, -(angleSlope (h / q) δ - 1)]

/-- The exact split-coordinate minor is strictly negative at every strict
root, without choosing an acute or obtuse second-cap branch. -/
theorem splitControllerMinor_det_neg {p t q h l α β γ δ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hqh : q < h)
    (hangles : StrictAngles q h α β γ δ)
    (hlow : seamLow p t q α β γ δ = 0) (hchord : chord q α β γ δ = 0) :
    Matrix.det (splitControllerMinor p t q h l α β γ δ) < 0 := by
  have hq0 : 0 < q := by linarith
  have hcos := cos_first_sum_neg_of_root hp hp1 ht htq hq hangles hlow hchord
  rcases hangles with ⟨hα, hβ, hγ, hδ, hwall⟩
  exact controller_minor_neg hcos
    (lowDefect_derivative_pos hp hp1 hα.1 hα.2)
    (lowDefect_derivative_pos hl hl1 hβ.1 hβ.2)
    (lowDefect_derivative_pos (div_pos ht hq0) ((div_lt_one hq0).2 htq) hγ.1 hγ.2)
    (highExcess_derivative_pos ((one_lt_div hq0).2 hqh) hδ.1 hδ.2 hwall)

theorem splitControllerMinor_det_ne_zero {p t q h l α β γ δ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hqh : q < h)
    (hangles : StrictAngles q h α β γ δ)
    (hlow : seamLow p t q α β γ δ = 0) (hchord : chord q α β γ δ = 0) :
    Matrix.det (splitControllerMinor p t q h l α β γ δ) ≠ 0 :=
  ne_of_lt (splitControllerMinor_det_neg hp hp1 hl hl1 ht htq hq hqh hangles hlow hchord)

/-- The three-variable chart fixes the second pure turn `T` and uses
coordinates `(S, α, γ)`, with `β=S-α` and `δ=T-γ`. -/
noncomputable def splitController (p t q h l T : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![chord q (x 1) (x 0 - x 1) (x 2) (T - x 2),
    seamLow p t q (x 1) (x 0 - x 1) (x 2) (T - x 2),
    seamHigh q h l (x 1) (x 0 - x 1) (x 2) (T - x 2)]

/-- The differential written with its positive defect coefficients. -/
noncomputable def splitDifferential (R A B C G : ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![
    R • ContinuousLinearMap.proj 0,
    ContinuousLinearMap.proj 0 - A • ContinuousLinearMap.proj 1 -
      C • ContinuousLinearMap.proj 2,
    (1 - B) • ContinuousLinearMap.proj 0 + B • ContinuousLinearMap.proj 1 -
      G • ContinuousLinearMap.proj 2]

theorem splitDifferential_apply (R A B C G : ℝ) (v : Fin 3 → ℝ) :
    splitDifferential R A B C G v =
      ![R * v 0, v 0 - A * v 1 - C * v 2,
        (1 - B) * v 0 + B * v 1 - G * v 2] := by
  ext i
  fin_cases i <;> simp [splitDifferential]

/-- Explicit inversion of the triangular-plus-two-split differential. -/
theorem splitDifferential_surjective {R A B C G : ℝ}
    (hR : R ≠ 0) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hG : 0 < G) :
    Function.Surjective (splitDifferential R A B C G) := by
  have hD : A * G + B * C ≠ 0 := ne_of_gt (add_pos (mul_pos hA hG) (mul_pos hB hC))
  intro y
  let u := y 0 / R
  let v := y 1 - u
  let w := y 2 - (1 - B) * u
  refine ⟨![u, (C * w - G * v) / (A * G + B * C),
    (-A * w - B * v) / (A * G + B * C)], ?_⟩
  rw [splitDifferential_apply]
  ext i
  fin_cases i <;> simp [u, v, w]
  all_goals field_simp
  all_goals nlinarith

theorem hasFDerivAt_splitController {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 0 < q) (hqh : q < h)
    (hangles : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2)) :
    HasFDerivAt (splitController p t q h l T)
      (splitDifferential (Real.cos (x 0))
        (1 - angleSlope p (x 1)) (1 - angleSlope l (x 0 - x 1))
        (1 - angleSlope (t / q) (x 2)) (angleSlope (h / q) (T - x 2) - 1)) x := by
  rcases hangles with ⟨hα, hβ, hγ, hδ, hwall⟩
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 x
  have hpD := (hasDerivAt_angleDefect hp hp1 hα.1 hα.2).comp_hasFDerivAt x h1
  have htD := (hasDerivAt_angleDefect (div_pos ht hq) ((div_lt_one hq).2 htq)
    hγ.1 hγ.2).comp_hasFDerivAt x h2
  have hlD := (hasDerivAt_angleDefect hl hl1 hβ.1 hβ.2).comp_hasFDerivAt x (h0.sub h1)
  have hhD := (hasDerivAt_angleExcess ((one_lt_div hq).2 hqh)
    hδ.1 hδ.2 hwall).comp_hasFDerivAt x (h2.const_sub T)
  have hM := ((Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0).sub_const (Real.sin T / q)
  have hLow := (((h0.add_const T).sub_const Real.pi).sub hpD).sub htD
  have hHigh := (((h0.add_const T).sub_const Real.pi).sub hlD).add hhD
  unfold splitDifferential
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert hM using 1 <;> simp [splitController, chord]
  · convert hLow using 1
    · ext y
      simp [splitController, seamLow, lowTurn, angleDefect, Function.comp_def]
      ring
    · simp
  · convert hHigh using 1
    · ext y
      simp [splitController, seamHigh, highTurn, angleDefect, angleExcess, Function.comp_def]
      ring
    · ext v
      simp
      ring

/-- Surjectivity of the derivative of the actual three-variable seam/chord
chart, not merely nonvanishing of an unattached symbolic determinant. -/
theorem fderiv_splitController_surjective {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hqh : q < h)
    (hangles : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2))
    (hlow : seamLow p t q (x 1) (x 0 - x 1) (x 2) (T - x 2) = 0)
    (hchord : chord q (x 1) (x 0 - x 1) (x 2) (T - x 2) = 0) :
    Function.Surjective (fderiv ℝ (splitController p t q h l T) x) := by
  have hq0 : 0 < q := by linarith
  rw [(hasFDerivAt_splitController hp hp1 hl hl1 ht htq hq0 hqh hangles).fderiv]
  have hcos := cos_first_sum_neg_of_root hp hp1 ht htq hq hangles hlow hchord
  have hcos' : Real.cos (x 0) < 0 := by simpa using hcos
  rcases hangles with ⟨hα, hβ, hγ, hδ, hwall⟩
  exact splitDifferential_surjective (ne_of_lt hcos')
    (lowDefect_derivative_pos hp hp1 hα.1 hα.2)
    (lowDefect_derivative_pos hl hl1 hβ.1 hβ.2)
    (lowDefect_derivative_pos (div_pos ht hq0) ((div_lt_one hq0).2 htq) hγ.1 hγ.2)
    (highExcess_derivative_pos ((one_lt_div hq0).2 hqh) hδ.1 hδ.2 hwall)

end Gluck.Discrete.NativeOppositePure
