/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.MonotoneRunTrace
public import Gluck.Discrete.TangentChord
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The orthogonal residual controller

The three residual turns of a closed four-edge core determine its literal
total-turn and closure defects. This file identifies their exact nonlinear
controller and proves that the residual origin is a locally isolated zero
whenever the first and last core edges are transverse.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Gluck.Discrete

/-- The literal closure defect written in the two active residual turns. -/
noncomputable def orthogonalResidualClosure (e0 e3 : ℂ) (r1 r3 : ℝ) : ℂ :=
  (1 - unitPhase r1) * e0 +
    unitPhase r1 * (unitPhase r3 - 1) * e3

/-- The closure defect obtained by developing all four core edges. -/
noncomputable def orthogonalResidualDevelopedClosure
    (e0 e1 e2 e3 : ℂ) (r1 r3 : ℝ) : ℂ :=
  e0 + unitPhase r1 * (e1 + e2) + unitPhase (r1 + r3) * e3

/-- The derivative-completed secant slope of the real unit-phase path at
the phase origin. -/
noncomputable def unitPhaseSlope (t : ℝ) : ℂ :=
  dslope unitPhase 0 t

/-- The derivative-completed unit-phase slope is continuous. -/
@[fun_prop] theorem continuous_unitPhaseSlope : Continuous unitPhaseSlope := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · subst t
    exact continuousAt_dslope_same.mpr (hasDerivAt_unitPhase 0).differentiableAt
  · exact (continuousAt_dslope_of_ne ht).mpr (hasDerivAt_unitPhase t).continuousAt

/-- The unit-phase slope at the origin is `i`. -/
@[simp] theorem unitPhaseSlope_zero : unitPhaseSlope 0 = Complex.I := by
  rw [unitPhaseSlope, dslope_same, (hasDerivAt_unitPhase 0).deriv]
  simp [unitPhase]

/-- The derivative-completed secant slope factors the unit-phase increment. -/
theorem unit_phase_sub_one_eq_mul_slope (t : ℝ) :
    unitPhase t - 1 = (t : ℂ) * unitPhaseSlope t := by
  have h := sub_smul_dslope (fun x : ℝ ↦ unitPhase x) 0 t
  change (t - 0) • unitPhaseSlope t = unitPhase t - unitPhase 0 at h
  simpa [unitPhase] using h.symm

/-- The first edge of a positively oriented coordinate-axis orthogonal
quadrilateral with positive half-diagonals `a,b`. -/
def orthogonalQuadFirstEdge (a b : ℝ) : ℂ :=
  (b : ℂ) * Complex.I - a

/-- The last edge of a positively oriented coordinate-axis orthogonal
quadrilateral with positive half-diagonals `a,d`. -/
def orthogonalQuadLastEdge (a d : ℝ) : ℂ :=
  (a : ℂ) + (d : ℂ) * Complex.I

/-- The retained edges of an orthogonal quadrilateral have negative cross
product in the positive cyclic orientation. -/
theorem crossR2_orthogonal_quad_first_last
    (a b d : ℝ) :
    crossR2 0 (orthogonalQuadFirstEdge a b) (orthogonalQuadLastEdge a d) =
      -a * (b + d) := by
  simp [crossR2, orthogonalQuadFirstEdge, orthogonalQuadLastEdge, Complex.mul_re,
    Complex.mul_im]
  ring

/-- Positive orthogonal half-diagonals make the retained edge pair
transverse. -/
theorem crossR2_orthogonal_quad_first_last_ne_zero
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    crossR2 0 (orthogonalQuadFirstEdge a b) (orthogonalQuadLastEdge a d) ≠ 0 := by
  rw [crossR2_orthogonal_quad_first_last]
  exact mul_ne_zero (neg_ne_zero.mpr ha.ne') (ne_of_gt (add_pos hb hd))

/-- A closed core turns the developed closure formula into the factored
two-edge residual formula. -/
theorem orthogonal_residual_developed_closure_eq
    {e0 e1 e2 e3 : ℂ} (hclose : e0 + e1 + e2 + e3 = 0) (r1 r3 : ℝ) :
    orthogonalResidualDevelopedClosure e0 e1 e2 e3 r1 r3 =
      orthogonalResidualClosure e0 e3 r1 r3 := by
  rw [orthogonalResidualDevelopedClosure, orthogonalResidualClosure, unitPhase_add]
  linear_combination unitPhase r1 * hclose

/-- The exact closure defect factors through the two residual coordinates. -/
theorem orthogonal_residual_closure_factorization (e0 e3 : ℂ) (r1 r3 : ℝ) :
    orthogonalResidualClosure e0 e3 r1 r3 =
      (r1 : ℂ) * (-unitPhaseSlope r1 * e0) +
        (r3 : ℂ) * (unitPhase r1 * unitPhaseSlope r3 * e3) := by
  rw [orthogonalResidualClosure, show 1 - unitPhase r1 =
    -(unitPhase r1 - 1) by ring, unit_phase_sub_one_eq_mul_slope,
    unit_phase_sub_one_eq_mul_slope]
  ring

/-- The actual controller in coordinates `(r0,r1,r3)`: total-turn defect
together with literal developed closure. -/
noncomputable def orthogonalResidualController
    (e0 e3 : ℂ) (r : ℝ × (ℝ × ℝ)) : ℝ × ℂ :=
  (r.1 + r.2.1 + r.2.2, orthogonalResidualClosure e0 e3 r.2.1 r.2.2)

@[simp] theorem orthogonal_residual_controller_zero (e0 e3 : ℂ) :
    orthogonalResidualController e0 e3 0 = 0 := by
  simp [orthogonalResidualController, orthogonalResidualClosure, unitPhase]

/-- The joint controller with the two retained core edges as parameters. -/
noncomputable def orthogonalResidualControllerVarying
    (p : (ℂ × ℂ) × (ℝ × (ℝ × ℝ))) : ℝ × ℂ :=
  orthogonalResidualController p.1.1 p.1.2 p.2

@[simp] theorem orthogonal_residual_controller_varying_zero (e : ℂ × ℂ) :
    orthogonalResidualControllerVarying (e, 0) = 0 :=
  orthogonal_residual_controller_zero e.1 e.2

/-- The joint edge-and-residual controller is continuously differentiable. -/
theorem contDiff_orthogonalResidualControllerVarying :
    ContDiff ℝ 1 orthogonalResidualControllerVarying := by
  have hr1 : ContDiff ℝ 1
      (fun p : (ℂ × ℂ) × (ℝ × (ℝ × ℝ)) ↦ p.2.2.1) := by
    fun_prop
  have hr3 : ContDiff ℝ 1
      (fun p : (ℂ × ℂ) × (ℝ × (ℝ × ℝ)) ↦ p.2.2.2) := by
    fun_prop
  have hr1C : ContDiff ℝ 1
      (fun p : (ℂ × ℂ) × (ℝ × (ℝ × ℝ)) ↦ (p.2.2.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr1
  have hr3C : ContDiff ℝ 1
      (fun p : (ℂ × ℂ) × (ℝ × (ℝ × ℝ)) ↦ (p.2.2.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr3
  unfold orthogonalResidualControllerVarying orthogonalResidualController
    orthogonalResidualClosure unitPhase
  fun_prop

/-- The real derivative of the residual controller at the origin. -/
noncomputable def orthogonalResidualFDeriv (e0 e3 : ℂ) :
    (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × ℂ) :=
  let residual := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)
  let r1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp residual
  let r3 := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp residual
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) + r1 + r3).prod
    (((-Complex.I * e0) • Complex.ofRealCLM).comp r1 +
      ((Complex.I * e3) • Complex.ofRealCLM).comp r3)

/-- The residual-controller derivative has the three displayed columns. -/
@[simp] theorem orthogonal_residual_fderiv_apply (e0 e3 : ℂ) (w : ℝ × (ℝ × ℝ)) :
    orthogonalResidualFDeriv e0 e3 w =
      (w.1 + w.2.1 + w.2.2,
        (w.2.1 : ℂ) * (-Complex.I * e0) + (w.2.2 : ℂ) * (Complex.I * e3)) := by
  simp [orthogonalResidualFDeriv]
  ring

/-- The oriented planar minor of the controller derivative is the negative
cross product of the two retained core edges. -/
theorem orthogonal_residual_planar_jacobian_eq (e0 e3 : ℂ) :
    (-Complex.I * e0).re * (Complex.I * e3).im -
        (-Complex.I * e0).im * (Complex.I * e3).re =
      -crossR2 0 e0 e3 := by
  simp [crossR2, Complex.mul_re, Complex.mul_im]

/-- The controller derivative in source order `(r0,r1,r3)` and target order
`(turn,re closure,im closure)`. -/
def orthogonalResidualDerivativeMatrix (e0 e3 : ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![
    1, 1, 1;
    0, (-Complex.I * e0).re, (Complex.I * e3).re;
    0, (-Complex.I * e0).im, (Complex.I * e3).im]

/-- The full controller determinant is the negative cross product of the
first and last core edges. -/
theorem orthogonal_residual_derivative_matrix_det (e0 e3 : ℂ) :
    Matrix.det (orthogonalResidualDerivativeMatrix e0 e3) = -crossR2 0 e0 e3 := by
  rw [Matrix.det_fin_three]
  simp [orthogonalResidualDerivativeMatrix, crossR2]
  ring

/-- The residual-controller derivative of a positively oriented orthogonal
quadrilateral has positive determinant. -/
theorem orthogonal_residual_derivative_matrix_det_pos
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    0 < Matrix.det
      (orthogonalResidualDerivativeMatrix
        (orthogonalQuadFirstEdge a b) (orthogonalQuadLastEdge a d)) := by
  rw [orthogonal_residual_derivative_matrix_det,
    crossR2_orthogonal_quad_first_last]
  nlinarith [mul_pos ha (add_pos hb hd)]

/-- The exact variable matrix factoring the nonlinear controller through its
residual vector. -/
noncomputable def orthogonalResidualFactorMatrix
    (e0 e3 : ℂ) (r : ℝ × (ℝ × ℝ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  let a := -unitPhaseSlope r.2.1 * e0
  let b := unitPhase r.2.1 * unitPhaseSlope r.2.2 * e3
  !![
    1, 1, 1;
    0, a.re, b.re;
    0, a.im, b.im]

/-- At zero residual, the exact factor matrix is the controller derivative
matrix. -/
@[simp] theorem orthogonal_residual_factor_matrix_zero (e0 e3 : ℂ) :
    orthogonalResidualFactorMatrix e0 e3 0 =
      orthogonalResidualDerivativeMatrix e0 e3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orthogonalResidualFactorMatrix, orthogonalResidualDerivativeMatrix,
      unitPhase]

/-- The exact factor matrix sends the residual vector to the literal
controller in real coordinates. -/
theorem orthogonal_residual_factor_matrix_mulVec
    (e0 e3 : ℂ) (r : ℝ × (ℝ × ℝ)) :
    (orthogonalResidualFactorMatrix e0 e3 r).mulVec ![r.1, r.2.1, r.2.2] =
      ![(orthogonalResidualController e0 e3 r).1,
        (orthogonalResidualController e0 e3 r).2.re,
        (orthogonalResidualController e0 e3 r).2.im] := by
  have hclose :=
    orthogonal_residual_closure_factorization e0 e3 r.2.1 r.2.2
  ext i
  fin_cases i <;>
    simp [orthogonalResidualFactorMatrix, Matrix.mulVec,
      orthogonalResidualController, hclose, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- The oriented determinant of the two exact planar factor columns. -/
noncomputable def orthogonalResidualFactorDet
    (e0 e3 : ℂ) (r : ℝ × (ℝ × ℝ)) : ℝ :=
  let a := -unitPhaseSlope r.2.1 * e0
  let b := unitPhase r.2.1 * unitPhaseSlope r.2.2 * e3
  a.re * b.im - a.im * b.re

/-- The full exact factor determinant is its oriented planar minor. -/
theorem orthogonal_residual_factor_matrix_det
    (e0 e3 : ℂ) (r : ℝ × (ℝ × ℝ)) :
    Matrix.det (orthogonalResidualFactorMatrix e0 e3 r) =
      orthogonalResidualFactorDet e0 e3 r := by
  rw [Matrix.det_fin_three]
  simp [orthogonalResidualFactorMatrix, orthogonalResidualFactorDet]
  ring

/-- The exact factor determinant varies continuously with the retained edges
and residuals. -/
theorem continuous_orthogonalResidualFactorDet :
    Continuous fun p : (ℂ × ℂ) × (ℝ × (ℝ × ℝ)) ↦
      orthogonalResidualFactorDet p.1.1 p.1.2 p.2 := by
  have hphase : Continuous unitPhase := by
    unfold unitPhase
    fun_prop
  unfold orthogonalResidualFactorDet
  fun_prop

/-- The exact factor determinant varies continuously along continuous edge
and residual families. -/
theorem continuousOn_orthogonalResidualFactorDet
    {X : Type*} [TopologicalSpace X] {s : Set X}
    {e0 e3 : X → ℂ} {r : X → ℝ × (ℝ × ℝ)}
    (he0 : ContinuousOn e0 s) (he3 : ContinuousOn e3 s)
    (hr : ContinuousOn r s) :
    ContinuousOn (fun x ↦
      orthogonalResidualFactorDet (e0 x) (e3 x) (r x)) s := by
  have hr1 : ContinuousOn (fun x ↦ (r x).2.1) s :=
    continuous_fst.comp_continuousOn
      (continuous_snd.comp_continuousOn hr)
  have hr3 : ContinuousOn (fun x ↦ (r x).2.2) s :=
    continuous_snd.comp_continuousOn
      (continuous_snd.comp_continuousOn hr)
  have hphase : ContinuousOn (fun x ↦ unitPhase ((r x).2.1)) s := by
    intro x hx
    exact continuousWithinAt_unitPhase (hr1 x hx)
  have hslope1 : ContinuousOn (fun x ↦ unitPhaseSlope ((r x).2.1)) s :=
    continuous_unitPhaseSlope.comp_continuousOn hr1
  have hslope3 : ContinuousOn (fun x ↦ unitPhaseSlope ((r x).2.2)) s :=
    continuous_unitPhaseSlope.comp_continuousOn hr3
  let a : X → ℂ := fun x ↦ -unitPhaseSlope ((r x).2.1) * e0 x
  let b : X → ℂ := fun x ↦
    unitPhase ((r x).2.1) * unitPhaseSlope ((r x).2.2) * e3 x
  have ha : ContinuousOn a s := hslope1.neg.mul he0
  have hb : ContinuousOn b s := (hphase.mul hslope3).mul he3
  have hare := Complex.continuous_re.comp_continuousOn ha
  have haim := Complex.continuous_im.comp_continuousOn ha
  have hbre := Complex.continuous_re.comp_continuousOn hb
  have hbim := Complex.continuous_im.comp_continuousOn hb
  change ContinuousOn (fun x ↦
    (a x).re * (b x).im - (a x).im * (b x).re) s
  exact (hare.mul hbim).sub (haim.mul hbre)

/-- At zero residual, the exact factor determinant is the negative retained
edge cross product. -/
@[simp] theorem orthogonal_residual_factor_matrix_det_zero (e0 e3 : ℂ) :
    Matrix.det (orthogonalResidualFactorMatrix e0 e3 0) = -crossR2 0 e0 e3 := by
  rw [orthogonal_residual_factor_matrix_zero,
    orthogonal_residual_derivative_matrix_det]

/-- Wherever the exact factor matrix is nonsingular, the literal controller
vanishes exactly at zero residual. -/
theorem orthogonal_residual_controller_eq_zero_iff_of_factor_det_ne_zero
    {e0 e3 : ℂ} {r : ℝ × (ℝ × ℝ)}
    (hdet : Matrix.det (orthogonalResidualFactorMatrix e0 e3 r) ≠ 0) :
    orthogonalResidualController e0 e3 r = 0 ↔ r = 0 := by
  constructor
  · intro hzero
    have hmul :
        (orthogonalResidualFactorMatrix e0 e3 r).mulVec
            ![r.1, r.2.1, r.2.2] = 0 := by
      rw [orthogonal_residual_factor_matrix_mulVec, hzero]
      simp
    have hvec : ![r.1, r.2.1, r.2.2] = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
    apply Prod.ext
    · simpa using congrFun hvec 0
    · apply Prod.ext
      · simpa using congrFun hvec 1
      · simpa using congrFun hvec 2
  · rintro rfl
    exact orthogonal_residual_controller_zero e0 e3

/-- The displayed matrix represents the controller derivative in real
coordinates. -/
theorem orthogonal_residual_derivative_matrix_mulVec
    (e0 e3 : ℂ) (w : ℝ × (ℝ × ℝ)) :
    (orthogonalResidualDerivativeMatrix e0 e3).mulVec ![w.1, w.2.1, w.2.2] =
      ![(orthogonalResidualFDeriv e0 e3 w).1,
        (orthogonalResidualFDeriv e0 e3 w).2.re,
        (orthogonalResidualFDeriv e0 e3 w).2.im] := by
  ext i
  fin_cases i <;>
    simp [orthogonalResidualDerivativeMatrix, Matrix.mulVec, Complex.mul_re,
      Complex.mul_im] <;>
    ring

private theorem real_linear_combination_eq_zero_aux
    {a b : ℂ} {x y : ℝ}
    (hdet : a.re * b.im - a.im * b.re ≠ 0)
    (hzero : (x : ℂ) * a + (y : ℂ) * b = 0) :
    x = 0 ∧ y = 0 := by
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.zero_re] at hre
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.zero_im] at him
  have hxMul : (a.re * b.im - a.im * b.re) * x = 0 := by
    linear_combination b.im * hre - b.re * him
  have hyMul : (a.re * b.im - a.im * b.re) * y = 0 := by
    linear_combination -a.im * hre + a.re * him
  exact ⟨(mul_eq_zero.mp hxMul).resolve_left hdet,
    (mul_eq_zero.mp hyMul).resolve_left hdet⟩

/-- Transverse first and last core edges make the controller derivative
injective. -/
theorem orthogonal_residual_fderiv_injective {e0 e3 : ℂ}
    (hcross : crossR2 0 e0 e3 ≠ 0) :
    Function.Injective (orthogonalResidualFDeriv e0 e3) := by
  intro x y hxy
  let a := -Complex.I * e0
  let b := Complex.I * e3
  let d1 := x.2.1 - y.2.1
  let d3 := x.2.2 - y.2.2
  have hturn : x.1 + x.2.1 + x.2.2 = y.1 + y.2.1 + y.2.2 := by
    simpa only [orthogonal_residual_fderiv_apply] using congrArg Prod.fst hxy
  have hclosure :
      (x.2.1 : ℂ) * a + (x.2.2 : ℂ) * b =
        (y.2.1 : ℂ) * a + (y.2.2 : ℂ) * b := by
    simpa only [orthogonal_residual_fderiv_apply, a, b] using congrArg Prod.snd hxy
  have hclosure' : (d1 : ℂ) * a + (d3 : ℂ) * b = 0 := by
    calc
      (d1 : ℂ) * a + (d3 : ℂ) * b =
          ((x.2.1 : ℂ) * a + (x.2.2 : ℂ) * b) -
            ((y.2.1 : ℂ) * a + (y.2.2 : ℂ) * b) := by
        simp [d1, d3]
        ring
      _ = 0 := by rw [hclosure]; ring
  have hJ : a.re * b.im - a.im * b.re ≠ 0 := by
    dsimp only [a, b]
    rw [orthogonal_residual_planar_jacobian_eq]
    exact neg_ne_zero.mpr hcross
  obtain ⟨hd1, hd3⟩ := real_linear_combination_eq_zero_aux hJ hclosure'
  have hx1 : x.2.1 = y.2.1 := sub_eq_zero.mp (by simpa [d1] using hd1)
  have hx3 : x.2.2 = y.2.2 := sub_eq_zero.mp (by simpa [d3] using hd3)
  apply Prod.ext
  · linarith
  · exact Prod.ext hx1 hx3

/-- The nondegenerate controller derivative as a continuous linear
equivalence. -/
noncomputable def orthogonalResidualFDerivEquiv (e0 e3 : ℂ)
    (hcross : crossR2 0 e0 e3 ≠ 0) :
    (ℝ × (ℝ × ℝ)) ≃L[ℝ] (ℝ × ℂ) :=
  let f := orthogonalResidualFDeriv e0 e3
  let hinj := orthogonal_residual_fderiv_injective hcross
  ContinuousLinearEquiv.ofBijective f
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr <|
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by simp [Complex.finrank_real_complex])).mp hinj)

/-- The derivative equivalence acts by the displayed residual columns. -/
@[simp] theorem orthogonal_residual_fderiv_equiv_apply
    (e0 e3 : ℂ) (hcross : crossR2 0 e0 e3 ≠ 0) (w : ℝ × (ℝ × ℝ)) :
    orthogonalResidualFDerivEquiv e0 e3 hcross w =
      (w.1 + w.2.1 + w.2.2,
        (w.2.1 : ℂ) * (-Complex.I * e0) + (w.2.2 : ℂ) * (Complex.I * e3)) := by
  exact orthogonal_residual_fderiv_apply e0 e3 w

private theorem has_strict_fderiv_at_unit_phase_comp_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
    (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun y ↦ unitPhase (f y))
      ((unitPhase (f x) * Complex.I) • (Complex.ofRealCLM.comp f')) x := by
  unfold unitPhase
  have h := ((Complex.ofRealCLM.hasStrictFDerivAt.comp x hf).mul_const Complex.I).cexp
  apply h.congr_fderiv
  ext y
  simp [smul_smul]

/-- The residual controller has its displayed strict derivative at the
closed-core residual origin. -/
theorem hasStrictFDerivAt_orthogonalResidualController (e0 e3 : ℂ) :
    HasStrictFDerivAt (orthogonalResidualController e0 e3)
      (orthogonalResidualFDeriv e0 e3) 0 := by
  let residual := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)
  let r0 := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  let r1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp residual
  let r3 := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp residual
  have hr0 : HasStrictFDerivAt (fun r : ℝ × (ℝ × ℝ) ↦ r.1) r0 0 :=
    r0.hasStrictFDerivAt
  have hr1 : HasStrictFDerivAt (fun r : ℝ × (ℝ × ℝ) ↦ r.2.1) r1 0 :=
    r1.hasStrictFDerivAt
  have hr3 : HasStrictFDerivAt (fun r : ℝ × (ℝ × ℝ) ↦ r.2.2) r3 0 :=
    r3.hasStrictFDerivAt
  have hp1 := has_strict_fderiv_at_unit_phase_comp_aux hr1
  have hp3 := has_strict_fderiv_at_unit_phase_comp_aux hr3
  have hturn := (hr0.add hr1).add hr3
  have hclose :=
    ((hasStrictFDerivAt_const (1 : ℂ) (0 : ℝ × (ℝ × ℝ))).sub hp1).mul_const e0
      |>.add ((hp1.mul (hp3.sub_const 1)).mul_const e3)
  have hcontroller := hturn.prodMk hclose
  apply hcontroller.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  apply Prod.ext
  · simp [orthogonalResidualFDeriv, residual, r0, r1, r3]
  · simp [orthogonalResidualFDeriv, residual, r0, r1, r3, unitPhase, smul_smul]
    ring

/-- At zero residual, the joint edge-and-residual controller has no
first-order dependence on its edge parameters. -/
theorem hasFDerivAt_orthogonalResidualControllerVarying_zero
    (e : ℂ × ℂ) :
    HasFDerivAt orthogonalResidualControllerVarying
      ((orthogonalResidualFDeriv e.1 e.2).comp
        (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ)))) (e, 0) := by
  let F := orthogonalResidualControllerVarying
  have hcdf : ContDiffAt ℝ 1 F (e, 0) :=
    contDiff_orthogonalResidualControllerVarying.contDiffAt
  have hfull := (hcdf.differentiableAt one_ne_zero).hasFDerivAt
  have hleftPath := hfull.comp e
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) e (0 : ℝ × (ℝ × ℝ)))
  have hleft :
      (fderiv ℝ F (e, 0)).comp
          (ContinuousLinearMap.inl ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ))) = 0 := by
    have hconst : HasFDerivAt (fun _ : ℂ × ℂ ↦ (0 : ℝ × ℂ)) 0 e :=
      hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ × ℂ) e
    have heq : (fun q : ℂ × ℂ ↦ F (q, 0)) = fun _ ↦ 0 := by
      funext q
      exact orthogonal_residual_controller_varying_zero q
    change HasFDerivAt (fun q : ℂ × ℂ ↦ F (q, 0))
      ((fderiv ℝ F (e, 0)).comp
        (ContinuousLinearMap.inl ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ)))) e at hleftPath
    rw [heq] at hleftPath
    exact hleftPath.unique hconst
  have hrightPath := hfull.comp (0 : ℝ × (ℝ × ℝ))
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) e (0 : ℝ × (ℝ × ℝ)))
  have hright :
      (fderiv ℝ F (e, 0)).comp
          (ContinuousLinearMap.inr ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ))) =
        orthogonalResidualFDeriv e.1 e.2 := by
    change HasFDerivAt (orthogonalResidualController e.1 e.2)
      ((fderiv ℝ F (e, 0)).comp
        (ContinuousLinearMap.inr ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ)))) 0 at hrightPath
    exact hrightPath.unique
      (hasStrictFDerivAt_orthogonalResidualController e.1 e.2).hasFDerivAt
  apply hfull.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  have hw : w =
      ContinuousLinearMap.inl ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ)) w.1 +
        ContinuousLinearMap.inr ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ)) w.2 := by
    ext <;> simp
  rw [hw, map_add]
  have hleftApply := DFunLike.congr_fun hleft w.1
  have hrightApply := DFunLike.congr_fun hright w.2
  simpa using congrArg₂ (· + ·) hleftApply hrightApply

/-- Transverse core edges identify the controller derivative with a linear
equivalence. -/
theorem hasStrictFDerivAt_orthogonalResidualController_equiv
    {e0 e3 : ℂ} (hcross : crossR2 0 e0 e3 ≠ 0) :
    HasStrictFDerivAt (orthogonalResidualController e0 e3)
      (orthogonalResidualFDerivEquiv e0 e3 hcross :
        (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × ℂ)) 0 := by
  apply (hasStrictFDerivAt_orthogonalResidualController e0 e3).congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  rw [orthogonal_residual_fderiv_apply]
  exact (orthogonal_residual_fderiv_equiv_apply e0 e3 hcross w).symm

private theorem orthogonal_residual_partial_fderiv_eq_aux
    {e : ℂ × ℂ} (hcross : crossR2 0 e.1 e.2 ≠ 0) :
    (fderiv ℝ orthogonalResidualControllerVarying (e, 0)).comp
        (ContinuousLinearMap.inr ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ))) =
      (orthogonalResidualFDerivEquiv e.1 e.2 hcross :
        (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × ℂ)) := by
  have hcdf :
      ContDiffAt ℝ 1 orthogonalResidualControllerVarying (e, 0) :=
    contDiff_orthogonalResidualControllerVarying.contDiffAt
  have hfull := (hcdf.differentiableAt one_ne_zero).hasFDerivAt
  have hfixed := hfull.comp 0 (hasFDerivAt_prodMk_right e 0)
  change HasFDerivAt (orthogonalResidualController e.1 e.2)
    ((fderiv ℝ orthogonalResidualControllerVarying (e, 0)).comp
      (ContinuousLinearMap.inr ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ)))) 0 at hfixed
  exact hfixed.unique
    (hasStrictFDerivAt_orthogonalResidualController_equiv hcross).hasFDerivAt

private theorem orthogonal_residual_partial_fderiv_isInvertible_aux
    {e : ℂ × ℂ} (hcross : crossR2 0 e.1 e.2 ≠ 0) :
    ((fderiv ℝ orthogonalResidualControllerVarying (e, 0)).comp
      (ContinuousLinearMap.inr ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ)))).IsInvertible := by
  rw [orthogonal_residual_partial_fderiv_eq_aux hcross]
  exact ContinuousLinearMap.isInvertible_equiv

/-- Edge transversality makes the zero residual the unique nearby controller
zero, uniformly for nearby edge pairs. -/
theorem eventually_orthogonal_residual_controller_varying_eq_zero_iff
    {e : ℂ × ℂ} (hcross : crossR2 0 e.1 e.2 ≠ 0) :
    ∀ᶠ p : (ℂ × ℂ) × (ℝ × (ℝ × ℝ)) in 𝓝 (e, 0),
      orthogonalResidualControllerVarying p = 0 ↔ p.2 = 0 := by
  let F := orthogonalResidualControllerVarying
  have hcdf : ContDiffAt ℝ 1 F (e, 0) :=
    contDiff_orthogonalResidualControllerVarying.contDiffAt
  have hinv :
      ((fderiv ℝ F (e, 0)).comp
        (ContinuousLinearMap.inr ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ)))).IsInvertible := by
    exact orthogonal_residual_partial_fderiv_isInvertible_aux hcross
  let sol := hcdf.implicitFunction one_ne_zero hinv
  have hiff := hcdf.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv
  have hslice :
      ∀ᶠ q : ℂ × ℂ in 𝓝 e,
        F (q, 0) = F (e, 0) ↔ sol q = 0 :=
    (tendsto_id.prodMk_nhds tendsto_const_nhds).eventually hiff
  have hsol : ∀ᶠ q : ℂ × ℂ in 𝓝 e, sol q = 0 := by
    filter_upwards [hslice] with q hq
    exact hq.mp (by simp [F])
  filter_upwards [hiff, continuousAt_fst.eventually hsol] with p hp hsp
  change hcdf.implicitFunction one_ne_zero hinv p.1 = 0 at hsp
  rw [hsp] at hp
  have hF0 : F (e, 0) = 0 := by simp [F]
  rw [hF0] at hp
  change F p = 0 ↔ p.2 = 0
  exact hp.trans eq_comm

/-- Near the residual origin, the literal controller vanishes exactly when
all three turn residuals vanish. -/
theorem eventually_orthogonal_residual_controller_eq_zero_iff
    {e0 e3 : ℂ} (hcross : crossR2 0 e0 e3 ≠ 0) :
    ∀ᶠ r : ℝ × (ℝ × ℝ) in 𝓝 0,
      orthogonalResidualController e0 e3 r = 0 ↔ r = 0 := by
  let f := orthogonalResidualController e0 e3
  let f' := orthogonalResidualFDerivEquiv e0 e3 hcross
  have hf : HasStrictFDerivAt f
      (f' : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × ℂ)) 0 :=
    hasStrictFDerivAt_orthogonalResidualController_equiv hcross
  let g := hf.localInverse f f' 0
  have hleft : ∀ᶠ r : ℝ × (ℝ × ℝ) in 𝓝 0, g (f r) = r :=
    hf.eventually_left_inverse
  filter_upwards [hleft] with r hr
  constructor
  · intro hzero
    have hzero' : f r = 0 := hzero
    have hzero0 : f 0 = 0 := orthogonal_residual_controller_zero e0 e3
    calc
      r = g (f r) := hr.symm
      _ = g (f 0) := by rw [hzero', hzero0]
      _ = 0 := by simp [g]
  · rintro rfl
    exact orthogonal_residual_controller_zero e0 e3

/-- The local zero equivalence holds on a closed positive-radius residual
ball. -/
theorem exists_pos_orthogonal_residual_controller_zero_iff
    {e0 e3 : ℂ} (hcross : crossR2 0 e0 e3 ≠ 0) :
    ∃ eta, 0 < eta ∧ ∀ r : ℝ × (ℝ × ℝ), ‖r‖ ≤ eta →
      (orthogonalResidualController e0 e3 r = 0 ↔ r = 0) := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_orthogonal_residual_controller_eq_zero_iff hcross)
  refine ⟨delta / 2, half_pos hdelta, fun r hr ↦ hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact hr.trans_lt (half_lt_self hdelta)

private theorem exists_pos_uniform_residual_tube_aux
    {E : Type*} [TopologicalSpace E] {K : Set E}
    {S : Set (E × (ℝ × (ℝ × ℝ)))}
    (hS : S ∈ 𝓝ˢ K ×ˢ 𝓝 (0 : ℝ × (ℝ × ℝ))) :
    ∃ eta, 0 < eta ∧
      ∀ e ∈ K, ∀ r : ℝ × (ℝ × ℝ), ‖r‖ ≤ eta → (e, r) ∈ S := by
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hS
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨delta / 2, half_pos hdelta, fun e he r hr ↦ hUV ⟨?_, ?_⟩⟩
  · exact subset_of_mem_nhdsSet hU he
  · exact hball <| by
      rw [Metric.mem_ball, dist_zero_right]
      exact hr.trans_lt (half_lt_self hdelta)

/-- A compact consistently oriented transverse family admits a uniform
residual tube on which the exact factor matrix has positive determinant. -/
theorem exists_pos_uniform_orthogonal_residual_factor_matrix_det
    {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hcross : ∀ e ∈ K, 0 < -crossR2 0 e.1 e.2) :
    ∃ eta, 0 < eta ∧
      ∀ e ∈ K, ∀ r : ℝ × (ℝ × ℝ), ‖r‖ ≤ eta →
        0 < Matrix.det (orthogonalResidualFactorMatrix e.1 e.2 r) := by
  let S : Set ((ℂ × ℂ) × (ℝ × (ℝ × ℝ))) :=
    {p | 0 < orthogonalResidualFactorDet p.1.1 p.1.2 p.2}
  have hSOpen : IsOpen S := by
    exact isOpen_lt continuous_const continuous_orthogonalResidualFactorDet
  have hS : S ∈ 𝓝ˢ K ×ˢ 𝓝 (0 : ℝ × (ℝ × ℝ)) := by
    apply hK.mem_nhdsSet_prod_of_forall
    intro e he
    rw [← nhds_prod_eq]
    have hcenter : 0 < orthogonalResidualFactorDet e.1 e.2 0 := by
      rw [← orthogonal_residual_factor_matrix_det,
        orthogonal_residual_factor_matrix_det_zero]
      exact hcross e he
    exact hSOpen.mem_nhds (show (e, 0) ∈ S from hcenter)
  obtain ⟨eta, heta, htube⟩ := exists_pos_uniform_residual_tube_aux hS
  refine ⟨eta, heta, fun e he r hr ↦ ?_⟩
  rw [orthogonal_residual_factor_matrix_det]
  exact htube e he r hr

/-- A compact transverse family admits a uniform residual tube on which the
exact factor matrix is nonsingular. -/
theorem exists_pos_uniform_orthogonal_residual_factor_matrix_det_ne_zero
    {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hcross : ∀ e ∈ K, crossR2 0 e.1 e.2 ≠ 0) :
    ∃ eta, 0 < eta ∧
      ∀ e ∈ K, ∀ r : ℝ × (ℝ × ℝ), ‖r‖ ≤ eta →
        Matrix.det (orthogonalResidualFactorMatrix e.1 e.2 r) ≠ 0 := by
  let S : Set ((ℂ × ℂ) × (ℝ × (ℝ × ℝ))) :=
    {p | orthogonalResidualFactorDet p.1.1 p.1.2 p.2 ≠ 0}
  have hSOpen : IsOpen S := by
    exact isOpen_ne_fun continuous_orthogonalResidualFactorDet continuous_const
  have hS : S ∈ 𝓝ˢ K ×ˢ 𝓝 (0 : ℝ × (ℝ × ℝ)) := by
    apply hK.mem_nhdsSet_prod_of_forall
    intro e he
    rw [← nhds_prod_eq]
    have hcenter : orthogonalResidualFactorDet e.1 e.2 0 ≠ 0 := by
      rw [← orthogonal_residual_factor_matrix_det,
        orthogonal_residual_factor_matrix_det_zero]
      exact neg_ne_zero.mpr (hcross e he)
    exact hSOpen.mem_nhds (show (e, 0) ∈ S from hcenter)
  obtain ⟨eta, heta, htube⟩ := exists_pos_uniform_residual_tube_aux hS
  refine ⟨eta, heta, fun e he r hr ↦ ?_⟩
  rw [orthogonal_residual_factor_matrix_det]
  exact htube e he r hr

/-- A compact transverse family admits one residual radius on which literal
controller zeros and residual zeros agree for every core. -/
theorem exists_pos_uniform_orthogonal_residual_controller_zero_iff
    {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hcross : ∀ e ∈ K, crossR2 0 e.1 e.2 ≠ 0) :
    ∃ eta, 0 < eta ∧ ∀ e ∈ K, ∀ r : ℝ × (ℝ × ℝ), ‖r‖ ≤ eta →
      (orthogonalResidualController e.1 e.2 r = 0 ↔ r = 0) := by
  obtain ⟨eta, heta, hdet⟩ :=
    exists_pos_uniform_orthogonal_residual_factor_matrix_det_ne_zero hK hcross
  exact ⟨eta, heta, fun e he r hr ↦
    orthogonal_residual_controller_eq_zero_iff_of_factor_det_ne_zero
      (hdet e he r hr)⟩

/-! ## Exact planar residual coordinates -/

/-- The first real coordinate of `E` in the ordered complex basis `(a,b)`. -/
noncomputable def complexBasisCoordinateOne (a b E : ℂ) : ℝ :=
  (E.re * b.im - E.im * b.re) / (a.re * b.im - a.im * b.re)

/-- The second real coordinate of `E` in the ordered complex basis `(a,b)`. -/
noncomputable def complexBasisCoordinateTwo (a b E : ℂ) : ℝ :=
  (a.re * E.im - a.im * E.re) / (a.re * b.im - a.im * b.re)

/-- Cramer's-rule coordinates of a complex vector in a moving real basis,
bundled again as a complex number. -/
noncomputable def complexBasisCoordinates (a b E : ℂ) : ℂ :=
  Complex.ofReal (complexBasisCoordinateOne a b E) +
    Complex.ofReal (complexBasisCoordinateTwo a b E) * Complex.I

@[simp] theorem complex_basis_coordinates_re (a b E : ℂ) :
    (complexBasisCoordinates a b E).re =
      (E.re * b.im - E.im * b.re) / (a.re * b.im - a.im * b.re) := by
  rw [complexBasisCoordinates]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
  rw [add_zero]
  rfl

@[simp] theorem complex_basis_coordinates_im (a b E : ℂ) :
    (complexBasisCoordinates a b E).im =
      (a.re * E.im - a.im * E.re) / (a.re * b.im - a.im * b.re) := by
  rw [complexBasisCoordinates]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul, mul_one, add_zero,
    zero_add]
  rfl

/-- Applying the first Cramer coordinate to a differentiable complex path
commutes with differentiation. -/
theorem HasDerivAt.complexBasisCoordinateOne
    (a b : ℂ) {E : ℝ → ℂ} {E' : ℂ} {x : ℝ}
    (hE : HasDerivAt E E' x) :
    HasDerivAt (fun k ↦ complexBasisCoordinateOne a b (E k))
      (complexBasisCoordinateOne a b E') x := by
  unfold Gluck.Discrete.complexBasisCoordinateOne
  have hre : HasDerivAt (fun k ↦ (E k).re) E'.re x := by
    simpa using (hasDerivAt_const x Complex.reCLM).clm_apply hE
  have him : HasDerivAt (fun k ↦ (E k).im) E'.im x := by
    simpa using (hasDerivAt_const x Complex.imCLM).clm_apply hE
  convert ((hre.mul_const b.im).sub (him.mul_const b.re)).div_const
    (a.re * b.im - a.im * b.re) using 1 <;> rfl

/-- Applying the second Cramer coordinate to a differentiable complex path
commutes with differentiation. -/
theorem HasDerivAt.complexBasisCoordinateTwo
    (a b : ℂ) {E : ℝ → ℂ} {E' : ℂ} {x : ℝ}
    (hE : HasDerivAt E E' x) :
    HasDerivAt (fun k ↦ complexBasisCoordinateTwo a b (E k))
      (complexBasisCoordinateTwo a b E') x := by
  unfold Gluck.Discrete.complexBasisCoordinateTwo
  have hre : HasDerivAt (fun k ↦ (E k).re) E'.re x := by
    simpa using (hasDerivAt_const x Complex.reCLM).clm_apply hE
  have him : HasDerivAt (fun k ↦ (E k).im) E'.im x := by
    simpa using (hasDerivAt_const x Complex.imCLM).clm_apply hE
  convert (him.const_mul a.re).sub (hre.const_mul a.im) |>.div_const
      (a.re * b.im - a.im * b.re) using 1 <;> rfl

/-- The coordinate map exactly recovers the coefficients of a real linear
combination in a transverse complex basis. -/
theorem complex_basis_coordinates_linear_combination
    {a b : ℂ} (hdet : a.re * b.im - a.im * b.re ≠ 0) (x y : ℝ) :
    complexBasisCoordinates a b ((x : ℂ) * a + (y : ℂ) * b) =
      (x : ℂ) + (y : ℂ) * Complex.I := by
  have hdet' : a.re * b.im - b.re * a.im ≠ 0 := by
    simpa [mul_comm] using hdet
  apply Complex.ext <;>
    simp only [complex_basis_coordinates_re, complex_basis_coordinates_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
      Complex.I_re, Complex.I_im, mul_zero, mul_one] <;>
    field_simp [hdet, hdet'] <;> ring

/-- Recombining the two Cramer coordinates recovers the original complex
vector in every transverse basis. -/
theorem complex_linear_combination_basis_coordinates
    {a b E : ℂ} (hdet : a.re * b.im - a.im * b.re ≠ 0) :
    ((complexBasisCoordinates a b E).re : ℂ) * a +
        ((complexBasisCoordinates a b E).im : ℂ) * b = E := by
  have hdet' : b.im * a.re - b.re * a.im ≠ 0 := by
    simpa [mul_comm] using hdet
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
      complex_basis_coordinates_re, complex_basis_coordinates_im] <;>
    field_simp [hdet, hdet'] <;> ring

/-- A transverse moving-basis transform preserves the zero set. -/
theorem complex_basis_coordinates_eq_zero_iff
    {a b E : ℂ} (hdet : a.re * b.im - a.im * b.re ≠ 0) :
    complexBasisCoordinates a b E = 0 ↔ E = 0 := by
  constructor
  · intro h
    have hre : (complexBasisCoordinates a b E).re = 0 := by rw [h]; simp
    have him : (complexBasisCoordinates a b E).im = 0 := by rw [h]; simp
    have hrec := complex_linear_combination_basis_coordinates
      (a := a) (b := b) (E := E) hdet
    calc
      E = ((complexBasisCoordinates a b E).re : ℂ) * a +
          ((complexBasisCoordinates a b E).im : ℂ) * b := hrec.symm
      _ = 0 := by rw [hre, him]; simp
  · rintro rfl
    apply Complex.ext <;>
      simp [complexBasisCoordinates, complexBasisCoordinateOne,
        complexBasisCoordinateTwo]

/-- Cramer coordinates vary continuously with a continuous transverse basis
and a continuous vector family. -/
theorem continuousOn_complexBasisCoordinates
    {X : Type*} [TopologicalSpace X] {s : Set X} {a b E : X → ℂ}
    (ha : ContinuousOn a s) (hb : ContinuousOn b s)
    (hE : ContinuousOn E s)
    (hdet : ∀ x ∈ s, (a x).re * (b x).im - (a x).im * (b x).re ≠ 0) :
    ContinuousOn (fun x ↦ complexBasisCoordinates (a x) (b x) (E x)) s := by
  have hare := Complex.continuous_re.comp_continuousOn ha
  have haim := Complex.continuous_im.comp_continuousOn ha
  have hbre := Complex.continuous_re.comp_continuousOn hb
  have hbim := Complex.continuous_im.comp_continuousOn hb
  have hEre := Complex.continuous_re.comp_continuousOn hE
  have hEim := Complex.continuous_im.comp_continuousOn hE
  have hd : ContinuousOn
      (fun x ↦ (a x).re * (b x).im - (a x).im * (b x).re) s :=
    (hare.mul hbim).sub (haim.mul hbre)
  have hx : ContinuousOn (fun x ↦
      ((E x).re * (b x).im - (E x).im * (b x).re) /
        ((a x).re * (b x).im - (a x).im * (b x).re)) s :=
    ((hEre.mul hbim).sub (hEim.mul hbre)).div hd hdet
  have hy : ContinuousOn (fun x ↦
      ((a x).re * (E x).im - (a x).im * (E x).re) /
        ((a x).re * (b x).im - (a x).im * (b x).re)) s :=
    ((hare.mul hEim).sub (haim.mul hEre)).div hd hdet
  change ContinuousOn (fun x ↦
    (((((E x).re * (b x).im - (E x).im * (b x).re) /
      ((a x).re * (b x).im - (a x).im * (b x).re)) : ℝ) : ℂ) +
      (((((a x).re * (E x).im - (a x).im * (E x).re) /
        ((a x).re * (b x).im - (a x).im * (b x).re)) : ℝ) : ℂ) *
          Complex.I) s
  exact (Complex.continuous_ofReal.comp_continuousOn hx).add
    ((Complex.continuous_ofReal.comp_continuousOn hy).mul continuousOn_const)

/-- Literal closure transformed back to its two nonlinear residual
coordinates.  This is the planar target chart used by the Type-A `R` cell. -/
noncomputable def orthogonalResidualPlanarCoordinates
    (e0 e3 : ℂ) (r1 r3 : ℝ) (E : ℂ) : ℂ :=
  complexBasisCoordinates (-unitPhaseSlope r1 * e0)
    (unitPhase r1 * unitPhaseSlope r3 * e3) E

/-- On the compactified orthogonal core, the planar target chart recovers
the two residuals exactly. -/
theorem orthogonal_residual_planar_coordinates_closure
    {e0 e3 : ℂ} {r1 r3 : ℝ}
    (hdet : orthogonalResidualFactorDet e0 e3 (0, (r1, r3)) ≠ 0) :
    orthogonalResidualPlanarCoordinates e0 e3 r1 r3
        (orthogonalResidualClosure e0 e3 r1 r3) =
      (r1 : ℂ) + (r3 : ℂ) * Complex.I := by
  rw [orthogonal_residual_closure_factorization]
  apply complex_basis_coordinates_linear_combination
  simpa [orthogonalResidualFactorDet] using hdet

/-- Wherever the exact planar factor is nonsingular, residualizing literal
closure preserves its zero set. -/
theorem orthogonal_residual_planar_coordinates_eq_zero_iff
    {e0 e3 E : ℂ} {r1 r3 : ℝ}
    (hdet : orthogonalResidualFactorDet e0 e3 (0, (r1, r3)) ≠ 0) :
    orthogonalResidualPlanarCoordinates e0 e3 r1 r3 E = 0 ↔ E = 0 := by
  apply complex_basis_coordinates_eq_zero_iff
  simpa [orthogonalResidualFactorDet] using hdet

/-- Recover three residual coordinates from a target consisting of total-turn
defect and complex closure.  Once the two closure coefficients are known,
the remaining coefficient is their sum subtracted from the turn defect. -/
noncomputable def residualTargetCoordinates
    (a b : ℂ) (Y : ℝ × ℂ) : ℝ × ℂ :=
  let z := complexBasisCoordinates a b Y.2
  (Y.1 - z.re - z.im, z)

/-- The full target-coordinate map recovers all three coefficients exactly. -/
theorem residual_target_coordinates_linear_combination
    {a b : ℂ} (hdet : a.re * b.im - a.im * b.re ≠ 0)
    (r0 r1 r3 : ℝ) :
    residualTargetCoordinates a b
        (r0 + r1 + r3, (r1 : ℂ) * a + (r3 : ℂ) * b) =
      (r0, (r1 : ℂ) + (r3 : ℂ) * Complex.I) := by
  rw [residualTargetCoordinates,
    complex_basis_coordinates_linear_combination hdet]
  apply Prod.ext
  · simp
    ring
  · rfl

/-- A transverse full target-coordinate transform preserves the zero set. -/
theorem residual_target_coordinates_eq_zero_iff
    {a b : ℂ} {Y : ℝ × ℂ}
    (hdet : a.re * b.im - a.im * b.re ≠ 0) :
    residualTargetCoordinates a b Y = 0 ↔ Y = 0 := by
  let z := complexBasisCoordinates a b Y.2
  constructor
  · intro h
    have hz : z = 0 := by
      simpa [residualTargetCoordinates, z] using congrArg Prod.snd h
    have hturn : Y.1 = 0 := by
      have hfirst := congrArg Prod.fst h
      simp only [residualTargetCoordinates, z, hz, Complex.zero_re,
        Complex.zero_im, sub_zero, Prod.fst_zero] at hfirst
      exact hfirst
    have hclosure : Y.2 = 0 :=
      (complex_basis_coordinates_eq_zero_iff hdet).mp hz
    exact Prod.ext hturn hclosure
  · rintro rfl
    simp [residualTargetCoordinates, complexBasisCoordinates,
      complexBasisCoordinateOne, complexBasisCoordinateTwo]

/-- The full residual target coordinates vary continuously with a continuous
transverse basis and target family. -/
theorem continuousOn_residualTargetCoordinates
    {X : Type*} [TopologicalSpace X] {s : Set X}
    {a b : X → ℂ} {Y : X → ℝ × ℂ}
    (ha : ContinuousOn a s) (hb : ContinuousOn b s)
    (hY : ContinuousOn Y s)
    (hdet : ∀ x ∈ s, (a x).re * (b x).im - (a x).im * (b x).re ≠ 0) :
    ContinuousOn (fun x ↦ residualTargetCoordinates (a x) (b x) (Y x)) s := by
  have hturn : ContinuousOn (fun x ↦ (Y x).1) s :=
    continuous_fst.comp_continuousOn hY
  have hclosure : ContinuousOn (fun x ↦ (Y x).2) s :=
    continuous_snd.comp_continuousOn hY
  have hz : ContinuousOn
      (fun x ↦ complexBasisCoordinates (a x) (b x) (Y x).2) s :=
    continuousOn_complexBasisCoordinates ha hb hclosure hdet
  change ContinuousOn (fun x ↦
    ((Y x).1 - (complexBasisCoordinates (a x) (b x) (Y x).2).re -
      (complexBasisCoordinates (a x) (b x) (Y x).2).im,
        complexBasisCoordinates (a x) (b x) (Y x).2)) s
  exact ((hturn.sub (Complex.continuous_re.comp_continuousOn hz)).sub
    (Complex.continuous_im.comp_continuousOn hz)).prodMk hz

/-- The full nonlinear target chart associated with an orthogonal residual
core. -/
noncomputable def orthogonalResidualTargetCoordinates
    (e0 e3 : ℂ) (r1 r3 : ℝ) (Y : ℝ × ℂ) : ℝ × ℂ :=
  residualTargetCoordinates (-unitPhaseSlope r1 * e0)
    (unitPhase r1 * unitPhaseSlope r3 * e3) Y

/-- The nonlinear residual target chart is continuous along any continuous
family on which its moving planar basis remains transverse. -/
theorem continuousOn_orthogonalResidualTargetCoordinates
    {X : Type*} [TopologicalSpace X] {s : Set X}
    {e0 e3 : X → ℂ} {r1 r3 : X → ℝ} {Y : X → ℝ × ℂ}
    (he0 : ContinuousOn e0 s) (he3 : ContinuousOn e3 s)
    (hr1 : ContinuousOn r1 s) (hr3 : ContinuousOn r3 s)
    (hY : ContinuousOn Y s)
    (hdet : ∀ x ∈ s,
      orthogonalResidualFactorDet (e0 x) (e3 x) (0, (r1 x, r3 x)) ≠ 0) :
    ContinuousOn (fun x ↦
      orthogonalResidualTargetCoordinates (e0 x) (e3 x)
        (r1 x) (r3 x) (Y x)) s := by
  have hphase : ContinuousOn (fun x ↦ unitPhase (r1 x)) s := by
    intro x hx
    exact continuousWithinAt_unitPhase (hr1 x hx)
  have hslope1 : ContinuousOn (fun x ↦ unitPhaseSlope (r1 x)) s :=
    continuous_unitPhaseSlope.comp_continuousOn hr1
  have hslope3 : ContinuousOn (fun x ↦ unitPhaseSlope (r3 x)) s :=
    continuous_unitPhaseSlope.comp_continuousOn hr3
  unfold orthogonalResidualTargetCoordinates
  apply continuousOn_residualTargetCoordinates
  · exact hslope1.neg.mul he0
  · exact (hphase.mul hslope3).mul he3
  · exact hY
  · intro x hx
    simpa only [orthogonalResidualFactorDet] using hdet x hx

/-- The nonlinear target chart turns the literal residual controller back
into the residual vector itself. -/
theorem orthogonal_residual_target_coordinates_controller
    {e0 e3 : ℂ} {r : ℝ × (ℝ × ℝ)}
    (hdet : orthogonalResidualFactorDet e0 e3 r ≠ 0) :
    orthogonalResidualTargetCoordinates e0 e3 r.2.1 r.2.2
        (orthogonalResidualController e0 e3 r) =
      (r.1, (r.2.1 : ℂ) + (r.2.2 : ℂ) * Complex.I) := by
  rw [orthogonalResidualTargetCoordinates, orthogonalResidualController,
    orthogonal_residual_closure_factorization]
  apply residual_target_coordinates_linear_combination
  simpa [orthogonalResidualFactorDet] using hdet

/-- Along a differentiable path through zero residual, the first coordinate
of a frozen transverse target chart has exactly the first residual
derivative. Edge motion contributes only at second order. -/
theorem hasDerivAt_orthogonalResidualTargetCoordinates_controllerVarying_fst
    {P : ℝ → (ℂ × ℂ) × (ℝ × (ℝ × ℝ))}
    {P' : (ℂ × ℂ) × (ℝ × (ℝ × ℝ))} {x : ℝ} {e : ℂ × ℂ}
    (hP : HasDerivAt P P' x) (hPx : P x = (e, 0))
    (hcross : crossR2 0 e.1 e.2 ≠ 0) :
    HasDerivAt (fun k ↦
      (orthogonalResidualTargetCoordinates e.1 e.2 0 0
        (orthogonalResidualControllerVarying (P k))).1) P'.2.1 x := by
  have houter := hasFDerivAt_orthogonalResidualControllerVarying_zero e
  have houter' : HasFDerivAt orthogonalResidualControllerVarying
      ((orthogonalResidualFDeriv e.1 e.2).comp
        (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℝ × (ℝ × ℝ)))) (P x) := by
    simpa only [hPx] using houter
  have hYF := houter'.comp x hP.hasFDerivAt
  have hY : HasDerivAt
      (fun k ↦ orthogonalResidualControllerVarying (P k))
      (orthogonalResidualFDeriv e.1 e.2 P'.2) x := by
    convert hYF.hasDerivAt using 1 <;> first | rfl | simp
  have hturn : HasDerivAt
      (fun k ↦ (orthogonalResidualControllerVarying (P k)).1)
      (orthogonalResidualFDeriv e.1 e.2 P'.2).1 x := by
    simpa using
      (hasDerivAt_const x (ContinuousLinearMap.fst ℝ ℝ ℂ)).clm_apply hY
  have hclose : HasDerivAt
      (fun k ↦ (orthogonalResidualControllerVarying (P k)).2)
      (orthogonalResidualFDeriv e.1 e.2 P'.2).2 x := by
    simpa using
      (hasDerivAt_const x (ContinuousLinearMap.snd ℝ ℝ ℂ)).clm_apply hY
  let a : ℂ := -Complex.I * e.1
  let b : ℂ := Complex.I * e.2
  have hdet : a.re * b.im - a.im * b.re ≠ 0 := by
    dsimp only [a, b]
    rw [orthogonal_residual_planar_jacobian_eq]
    exact neg_ne_zero.mpr hcross
  have hcoord1 := HasDerivAt.complexBasisCoordinateOne a b hclose
  have hcoord2 := HasDerivAt.complexBasisCoordinateTwo a b hclose
  unfold orthogonalResidualTargetCoordinates residualTargetCoordinates
  simp only [unitPhaseSlope_zero, unitPhase, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_mul]
  have hcoords := complex_basis_coordinates_linear_combination hdet
    P'.2.2.1 P'.2.2.2
  have hre := congrArg Complex.re hcoords
  have him := congrArg Complex.im hcoords
  simp only [complexBasisCoordinates, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, sub_zero] at hre
  simp only [complexBasisCoordinates, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, Complex.I_re,
    Complex.I_im, mul_one] at him
  have hderiv : P'.2.1 =
      (orthogonalResidualFDeriv e.1 e.2 P'.2).1 -
        complexBasisCoordinateOne a b
          (orthogonalResidualFDeriv e.1 e.2 P'.2).2 -
        complexBasisCoordinateTwo a b
          (orthogonalResidualFDeriv e.1 e.2 P'.2).2 := by
    rw [orthogonal_residual_fderiv_apply]
    dsimp only [a, b] at hre him ⊢
    linarith
  have hfun : (fun k ↦
      (orthogonalResidualControllerVarying (P k)).1 -
          (complexBasisCoordinates (-Complex.I * e.1) (Complex.I * e.2)
            (orthogonalResidualControllerVarying (P k)).2).re -
        (complexBasisCoordinates (-Complex.I * e.1) (Complex.I * e.2)
          (orthogonalResidualControllerVarying (P k)).2).im) =
      (((fun k ↦ (orthogonalResidualControllerVarying (P k)).1) -
        fun k ↦ complexBasisCoordinateOne a b
          (orthogonalResidualControllerVarying (P k)).2) -
        fun k ↦ complexBasisCoordinateTwo a b
          (orthogonalResidualControllerVarying (P k)).2) := by
    funext k
    simp only [complex_basis_coordinates_re, complex_basis_coordinates_im]
    rfl
  rw [hfun, hderiv]
  exact (hturn.sub hcoord1).sub hcoord2

/-- On a nonsingular residual chart, transformed-target zero is equivalent
to literal controller zero. -/
theorem orthogonal_residual_target_coordinates_eq_zero_iff
    {e0 e3 : ℂ} {r1 r3 : ℝ} {Y : ℝ × ℂ}
    (hdet : orthogonalResidualFactorDet e0 e3 (0, (r1, r3)) ≠ 0) :
    orthogonalResidualTargetCoordinates e0 e3 r1 r3 Y = 0 ↔ Y = 0 := by
  apply residual_target_coordinates_eq_zero_iff
  simpa [orthogonalResidualFactorDet] using hdet

/-! ## Globally regularized residual coordinates -/

/-- A continuous reciprocal regularization at scale `delta`. -/
noncomputable def regularizedReciprocal (delta x : ℝ) : ℝ :=
  x / max (x ^ 2) (delta ^ 2)

theorem continuous_regularizedReciprocal {delta : ℝ} (hdelta : delta ≠ 0) :
    Continuous (regularizedReciprocal delta) := by
  unfold regularizedReciprocal
  fun_prop (disch := intro x; positivity)

/-- Outside the protected determinant scale, the regularization is the true
reciprocal. -/
theorem regularizedReciprocal_eq_inv {delta x : ℝ}
    (hdelta : 0 < delta) (hx : delta ≤ |x|) :
    regularizedReciprocal delta x = x⁻¹ := by
  have hx0 : x ≠ 0 := by
    intro h
    simp only [h, abs_zero] at hx
    linarith
  have hsquare : delta ^ 2 ≤ x ^ 2 := by
    rw [sq_le_sq]
    simpa only [abs_of_pos hdelta] using hx
  rw [regularizedReciprocal, max_eq_left hsquare]
  field_simp

/-- Globally continuous Cramer coordinates, equal to the exact coordinates
where the determinant has magnitude at least `delta`. -/
noncomputable def regularizedComplexBasisCoordinates
    (delta : ℝ) (a b E : ℂ) : ℂ :=
  let d := a.re * b.im - a.im * b.re
  Complex.ofReal ((E.re * b.im - E.im * b.re) *
      regularizedReciprocal delta d) +
    Complex.ofReal ((a.re * E.im - a.im * E.re) *
      regularizedReciprocal delta d) * Complex.I

/-- The regularized Cramer chart agrees with the exact chart on its
protected determinant region. -/
theorem regularizedComplexBasisCoordinates_eq
    {delta : ℝ} (hdelta : 0 < delta) {a b E : ℂ}
    (hdet : delta ≤ |a.re * b.im - a.im * b.re|) :
    regularizedComplexBasisCoordinates delta a b E =
      complexBasisCoordinates a b E := by
  rw [regularizedComplexBasisCoordinates, complexBasisCoordinates,
    complexBasisCoordinateOne, complexBasisCoordinateTwo,
    regularizedReciprocal_eq_inv hdelta hdet]
  simp only [div_eq_mul_inv]

/-- Regularized Cramer coordinates vary continuously without a determinant
hypothesis. -/
theorem continuousOn_regularizedComplexBasisCoordinates
    {X : Type*} [TopologicalSpace X] {s : Set X} {delta : ℝ}
    (hdelta : delta ≠ 0) {a b E : X → ℂ}
    (ha : ContinuousOn a s) (hb : ContinuousOn b s)
    (hE : ContinuousOn E s) :
    ContinuousOn (fun x ↦
      regularizedComplexBasisCoordinates delta (a x) (b x) (E x)) s := by
  have hare := Complex.continuous_re.comp_continuousOn ha
  have haim := Complex.continuous_im.comp_continuousOn ha
  have hbre := Complex.continuous_re.comp_continuousOn hb
  have hbim := Complex.continuous_im.comp_continuousOn hb
  have hEre := Complex.continuous_re.comp_continuousOn hE
  have hEim := Complex.continuous_im.comp_continuousOn hE
  have hd : ContinuousOn
      (fun x ↦ (a x).re * (b x).im - (a x).im * (b x).re) s :=
    (hare.mul hbim).sub (haim.mul hbre)
  have hinv : ContinuousOn (fun x ↦ regularizedReciprocal delta
      ((a x).re * (b x).im - (a x).im * (b x).re)) s :=
    (continuous_regularizedReciprocal hdelta).comp_continuousOn hd
  unfold regularizedComplexBasisCoordinates
  exact (Complex.continuous_ofReal.comp_continuousOn
      (((hEre.mul hbim).sub (hEim.mul hbre)).mul hinv)).add
    ((Complex.continuous_ofReal.comp_continuousOn
      (((hare.mul hEim).sub (haim.mul hEre)).mul hinv)).mul
        continuousOn_const)

/-- Full target coordinates using the globally continuous regularized
planar chart. -/
noncomputable def regularizedResidualTargetCoordinates
    (delta : ℝ) (a b : ℂ) (Y : ℝ × ℂ) : ℝ × ℂ :=
  let z := regularizedComplexBasisCoordinates delta a b Y.2
  (Y.1 - z.re - z.im, z)

/-- The full regularized target chart is continuous without transversality. -/
theorem continuousOn_regularizedResidualTargetCoordinates
    {X : Type*} [TopologicalSpace X] {s : Set X} {delta : ℝ}
    (hdelta : delta ≠ 0) {a b : X → ℂ} {Y : X → ℝ × ℂ}
    (ha : ContinuousOn a s) (hb : ContinuousOn b s)
    (hY : ContinuousOn Y s) :
    ContinuousOn (fun x ↦
      regularizedResidualTargetCoordinates delta (a x) (b x) (Y x)) s := by
  have hturn : ContinuousOn (fun x ↦ (Y x).1) s :=
    continuous_fst.comp_continuousOn hY
  have hclosure : ContinuousOn (fun x ↦ (Y x).2) s :=
    continuous_snd.comp_continuousOn hY
  have hz := continuousOn_regularizedComplexBasisCoordinates hdelta ha hb hclosure
  unfold regularizedResidualTargetCoordinates
  exact ((hturn.sub (Complex.continuous_re.comp_continuousOn hz)).sub
    (Complex.continuous_im.comp_continuousOn hz)).prodMk hz

/-- The full regularized chart agrees with the exact chart on the protected
determinant region. -/
theorem regularizedResidualTargetCoordinates_eq
    {delta : ℝ} (hdelta : 0 < delta) {a b : ℂ} {Y : ℝ × ℂ}
    (hdet : delta ≤ |a.re * b.im - a.im * b.re|) :
    regularizedResidualTargetCoordinates delta a b Y =
      residualTargetCoordinates a b Y := by
  rw [regularizedResidualTargetCoordinates, residualTargetCoordinates,
    regularizedComplexBasisCoordinates_eq hdelta hdet]

/-- The regularized full nonlinear chart associated with an orthogonal
residual core. -/
noncomputable def regularizedOrthogonalResidualTargetCoordinates
    (delta : ℝ) (e0 e3 : ℂ) (r1 r3 : ℝ) (Y : ℝ × ℂ) : ℝ × ℂ :=
  regularizedResidualTargetCoordinates delta (-unitPhaseSlope r1 * e0)
    (unitPhase r1 * unitPhaseSlope r3 * e3) Y

/-- The regularized nonlinear chart is continuous along arbitrary
continuous edge, residual, and target families. -/
theorem continuousOn_regularizedOrthogonalResidualTargetCoordinates
    {X : Type*} [TopologicalSpace X] {s : Set X} {delta : ℝ}
    (hdelta : delta ≠ 0) {e0 e3 : X → ℂ} {r1 r3 : X → ℝ}
    {Y : X → ℝ × ℂ}
    (he0 : ContinuousOn e0 s) (he3 : ContinuousOn e3 s)
    (hr1 : ContinuousOn r1 s) (hr3 : ContinuousOn r3 s)
    (hY : ContinuousOn Y s) :
    ContinuousOn (fun x ↦
      regularizedOrthogonalResidualTargetCoordinates delta (e0 x) (e3 x)
        (r1 x) (r3 x) (Y x)) s := by
  have hphase : ContinuousOn (fun x ↦ unitPhase (r1 x)) s := by
    intro x hx
    exact continuousWithinAt_unitPhase (hr1 x hx)
  have hslope1 : ContinuousOn (fun x ↦ unitPhaseSlope (r1 x)) s :=
    continuous_unitPhaseSlope.comp_continuousOn hr1
  have hslope3 : ContinuousOn (fun x ↦ unitPhaseSlope (r3 x)) s :=
    continuous_unitPhaseSlope.comp_continuousOn hr3
  unfold regularizedOrthogonalResidualTargetCoordinates
  exact continuousOn_regularizedResidualTargetCoordinates hdelta
    (hslope1.neg.mul he0) ((hphase.mul hslope3).mul he3) hY

/-- The regularized nonlinear chart agrees with the exact one throughout
its protected determinant region. -/
theorem regularizedOrthogonalResidualTargetCoordinates_eq
    {delta : ℝ} (hdelta : 0 < delta) {e0 e3 : ℂ} {r1 r3 : ℝ}
    {Y : ℝ × ℂ}
    (hdet : delta ≤
      |orthogonalResidualFactorDet e0 e3 (0, (r1, r3))|) :
    regularizedOrthogonalResidualTargetCoordinates delta e0 e3 r1 r3 Y =
      orthogonalResidualTargetCoordinates e0 e3 r1 r3 Y := by
  unfold regularizedOrthogonalResidualTargetCoordinates
    orthogonalResidualTargetCoordinates
  apply regularizedResidualTargetCoordinates_eq hdelta
  simpa only [orthogonalResidualFactorDet] using hdet

/-- On the protected determinant region, the regularized chart preserves
the target zero set. -/
theorem regularizedOrthogonalResidualTargetCoordinates_eq_zero_iff
    {delta : ℝ} (hdelta : 0 < delta) {e0 e3 : ℂ} {r1 r3 : ℝ}
    {Y : ℝ × ℂ}
    (hdet : delta ≤
      |orthogonalResidualFactorDet e0 e3 (0, (r1, r3))|) :
    regularizedOrthogonalResidualTargetCoordinates delta e0 e3 r1 r3 Y = 0 ↔
      Y = 0 := by
  rw [regularizedOrthogonalResidualTargetCoordinates_eq hdelta hdet]
  exact orthogonal_residual_target_coordinates_eq_zero_iff
    (abs_pos.mp (hdelta.trans_le hdet))

/-! ## Local-to-global suspension patch -/

/-- Continuous cutoff equal to one on the inner residual sublevel and zero
outside the outer residual sublevel. -/
noncomputable def residualNormCutoff (inner outer : ℝ) (z : ℂ) : ℝ :=
  max 0 (min 1 ((outer - ‖z‖) / (outer - inner)))

theorem continuous_residualNormCutoff (inner outer : ℝ) :
    Continuous (residualNormCutoff inner outer) := by
  unfold residualNormCutoff
  fun_prop

theorem residualNormCutoff_mem_Icc (inner outer : ℝ) (z : ℂ) :
    residualNormCutoff inner outer z ∈ Set.Icc 0 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_left _ _)

/-- The cutoff is identically one on its inner sublevel. -/
theorem residualNormCutoff_eq_one {inner outer : ℝ} (hio : inner < outer)
    {z : ℂ} (hz : ‖z‖ ≤ inner) :
    residualNormCutoff inner outer z = 1 := by
  have hden : 0 < outer - inner := sub_pos.mpr hio
  have hratio : 1 ≤ (outer - ‖z‖) / (outer - inner) := by
    rw [le_div_iff₀ hden]
    linarith
  rw [residualNormCutoff, min_eq_left hratio, max_eq_right zero_le_one]

/-- The cutoff is identically zero outside its outer sublevel. -/
theorem residualNormCutoff_eq_zero {inner outer : ℝ} (hio : inner < outer)
    {z : ℂ} (hz : outer ≤ ‖z‖) :
    residualNormCutoff inner outer z = 0 := by
  have hden : 0 ≤ outer - inner := (sub_pos.mpr hio).le
  have hratio : (outer - ‖z‖) / (outer - inner) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) hden
  rw [residualNormCutoff, min_eq_right (hratio.trans zero_le_one),
    max_eq_left hratio]

/-- A nonzero cutoff lies strictly inside its outer residual sublevel. -/
theorem norm_lt_outer_of_residualNormCutoff_ne_zero
    {inner outer : ℝ} (hio : inner < outer) {z : ℂ}
    (hcut : residualNormCutoff inner outer z ≠ 0) :
    ‖z‖ < outer := by
  by_contra hnot
  exact hcut (residualNormCutoff_eq_zero hio (not_lt.mp hnot))

/-- Patch a local target into a global monotone suspension. The planar
correction makes the initial slice exactly `F`, while the scalar coordinate
blends the local sheet with the linear coordinate `k - kMid`. -/
noncomputable def localizedResidualSuspensionTarget
    {X : Type*} (inner outer kMid : ℝ) (F : X → ℂ)
    (G : (ℝ × X) × ℝ → ℝ × ℂ)
    (x : (ℝ × X) × ℝ) : ℝ × ℂ :=
  let cut := residualNormCutoff inner outer (F x.1.2)
  let G₀ := G ((0, x.1.2), kMid)
  (cut * (G₀.1 - (G x).1) + (1 - cut) * (x.2 - kMid),
    (G x).2 + F x.1.2 - G₀.2)

@[simp] theorem localizedResidualSuspensionTarget_initial
    {X : Type*} (inner outer kMid : ℝ) (F : X → ℂ)
    (G : (ℝ × X) × ℝ → ℝ × ℂ) (z : X) :
    localizedResidualSuspensionTarget inner outer kMid F G ((0, z), kMid) =
      (0, F z) := by
  simp [localizedResidualSuspensionTarget]

/-- The patched target is continuous whenever its local target and initial
slice are continuous. -/
theorem continuousOn_localizedResidualSuspensionTarget
    {X : Type*} [TopologicalSpace X] {S : Set ((ℝ × X) × ℝ)}
    (inner outer kMid : ℝ) {F : X → ℂ}
    {G : (ℝ × X) × ℝ → ℝ × ℂ}
    (hF : ContinuousOn (fun x : (ℝ × X) × ℝ ↦ F x.1.2) S)
    (hG : ContinuousOn G S)
    (hG₀ : ContinuousOn (fun x : (ℝ × X) × ℝ ↦
      G ((0, x.1.2), kMid)) S) :
    ContinuousOn
      (localizedResidualSuspensionTarget inner outer kMid F G) S := by
  have hcut : ContinuousOn (fun x : (ℝ × X) × ℝ ↦
      residualNormCutoff inner outer (F x.1.2)) S :=
    (continuous_residualNormCutoff inner outer).comp_continuousOn hF
  have hGfst := continuous_fst.comp_continuousOn hG
  have hGsnd := continuous_snd.comp_continuousOn hG
  have hG₀fst := continuous_fst.comp_continuousOn hG₀
  have hG₀snd := continuous_snd.comp_continuousOn hG₀
  unfold localizedResidualSuspensionTarget
  exact ((hcut.mul (hG₀fst.sub hGfst)).add
      ((continuousOn_const.sub hcut).mul
        (continuous_snd.sub continuous_const).continuousOn)).prodMk
    ((hGsnd.add hF).sub hG₀snd)

/-- On the inner sublevel, a correct initial local chart makes the patch
equal to the local target with its scalar orientation reversed. -/
theorem localizedResidualSuspensionTarget_eq_local
    {X : Type*} {inner outer kMid : ℝ} (hio : inner < outer)
    {F : X → ℂ} {G : (ℝ × X) × ℝ → ℝ × ℂ}
    {ε k : ℝ} {z : X} (hz : ‖F z‖ ≤ inner)
    (hbase : G ((0, z), kMid) = (0, F z)) :
    localizedResidualSuspensionTarget inner outer kMid F G ((ε, z), k) =
      (-(G ((ε, z), k)).1, (G ((ε, z), k)).2) := by
  rw [localizedResidualSuspensionTarget,
    residualNormCutoff_eq_one hio hz, hbase]
  simp

/-- On the inner sublevel, the patch and its correct local target have the
same zero set. -/
theorem localizedResidualSuspensionTarget_eq_zero_iff
    {X : Type*} {inner outer kMid : ℝ} (hio : inner < outer)
    {F : X → ℂ} {G : (ℝ × X) × ℝ → ℝ × ℂ}
    {ε k : ℝ} {z : X} (hz : ‖F z‖ ≤ inner)
    (hbase : G ((0, z), kMid) = (0, F z)) :
    localizedResidualSuspensionTarget inner outer kMid F G ((ε, z), k) = 0 ↔
      G ((ε, z), k) = 0 := by
  rw [localizedResidualSuspensionTarget_eq_local hio hz hbase]
  constructor
  · intro h
    apply Prod.ext
    · have hfirst := congrArg Prod.fst h
      exact neg_eq_zero.mp (by simpa using hfirst)
    · simpa using congrArg Prod.snd h
  · intro h
    rw [h]
    simp

/-- Strict decrease of the local scalar wherever the cutoff is active makes
the patched scalar strictly increasing on every parameter slice. -/
theorem strictMonoOn_localizedResidualSuspensionTarget_fst
    {X : Type*} {inner outer kMid ε : ℝ} {F : X → ℂ}
    {G : (ℝ × X) × ℝ → ℝ × ℂ} {D : Set ℝ}
    (z : X)
    (hlocal : residualNormCutoff inner outer (F z) ≠ 0 →
      StrictAntiOn (fun k ↦ (G ((ε, z), k)).1) D) :
    StrictMonoOn (fun k ↦
      (localizedResidualSuspensionTarget inner outer kMid F G
        ((ε, z), k)).1) D := by
  intro x hx y hy hxy
  let cut := residualNormCutoff inner outer (F z)
  have hcut := residualNormCutoff_mem_Icc inner outer (F z)
  by_cases hcut0 : cut = 0
  · simp only [localizedResidualSuspensionTarget, cut, hcut0, zero_mul,
      sub_zero, one_mul]
    linarith
  · have hcutPos : 0 < cut := lt_of_le_of_ne hcut.1 (Ne.symm hcut0)
    have hanti := hlocal hcut0 hx hy hxy
    have hlocalDiff :
        (G ((0, z), kMid)).1 - (G ((ε, z), x)).1 <
          (G ((0, z), kMid)).1 - (G ((ε, z), y)).1 := by
      linarith
    have hscaledLocal := mul_lt_mul_of_pos_left hlocalDiff hcutPos
    have hscaledLinear :
        (1 - cut) * (x - kMid) ≤ (1 - cut) * (y - kMid) :=
      mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hcut.2)
    simp only [localizedResidualSuspensionTarget]
    exact add_lt_add_of_lt_of_le hscaledLocal hscaledLinear

end Gluck.Discrete
