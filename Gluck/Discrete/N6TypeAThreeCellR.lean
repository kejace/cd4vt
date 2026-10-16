/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.CrossedFourArcWinding
public import Gluck.Discrete.FourArcRectangle
public import Gluck.Discrete.N6TypeAThreeCellAnalytic
public import Gluck.Discrete.N6TypeAOrthogonalCore
public import Gluck.Discrete.OrthogonalResidualController
public import ForMathlib.Topology.Order.ParametricRoot

/-!
# The planar R-cell branch of the Type-A three-cell selector

This file defines the two normalized residuals of the Type-A `R` cell and
proves their four crossed boundary signs.
-/

@[expose] public section

namespace Gluck.Discrete.N6TypeAThreeCell

open Set

/-- The first mixed-corner residual for the effective `R` profile `(1,u,q,v)`. -/
noncomputable def rResidualOne (p t q u v : ℝ) : ℝ :=
  let d := √(q ^ 2 - u ^ 2 * v ^ 2)
  let a := √(q ^ 2 - v ^ 2) / d
  let b := √(1 - v ^ 2) / d
  Real.arcsin (p * a) + Real.arcsin (t * b) -
    Real.arcsin (u * a) - Real.arcsin (u * b)

/-- The third mixed-corner residual for the effective `R` profile `(1,u,q,v)`. -/
noncomputable def rResidualThree (q h l u v : ℝ) : ℝ :=
  let d := √(q ^ 2 - u ^ 2 * v ^ 2)
  let c := √(1 - u ^ 2) / d
  let e := √(q ^ 2 - u ^ 2) / d
  Real.arcsin (h * c) + Real.arcsin (l * e) -
    Real.arcsin (v * c) - Real.arcsin (v * e)

/-- The singleton-zero residual after releasing its effective curvature from
`1` to `k`. -/
noncomputable def rResidualZeroReleased (k u q v : ℝ) : ℝ :=
  Real.arcsin (rCoreSideD k u q v / 2) +
    Real.arcsin (rCoreSideA k u q v / 2) -
      Real.arcsin (k * (rCoreSideD k u q v / 2)) -
        Real.arcsin (k * (rCoreSideA k u q v / 2))

/-- The first mixed residual on the released core `(k,u,q,v)`. -/
noncomputable def rResidualOneReleased
    (p t k u q v : ℝ) : ℝ :=
  Real.arcsin (p * (rCoreSideA k u q v / 2)) +
    Real.arcsin (t * (rCoreSideB k u q v / 2)) -
      Real.arcsin (u * (rCoreSideA k u q v / 2)) -
        Real.arcsin (u * (rCoreSideB k u q v / 2))

/-- The third mixed residual on the released core `(k,u,q,v)`. -/
noncomputable def rResidualThreeReleased
    (h l k u q v : ℝ) : ℝ :=
  Real.arcsin (h * (rCoreSideC k u q v / 2)) +
    Real.arcsin (l * (rCoreSideD k u q v / 2)) -
      Real.arcsin (v * (rCoreSideC k u q v / 2)) -
        Real.arcsin (v * (rCoreSideD k u q v / 2))

@[simp] theorem r_residual_zero_released_one (u q v : ℝ) :
    rResidualZeroReleased 1 u q v = 0 := by
  simp [rResidualZeroReleased]

private theorem hasDerivAt_arcsin_sub_arcsin_mul
    {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 1)
    (hneg : f 1 ≠ -1) (hpos : f 1 ≠ 1) :
    HasDerivAt (fun k ↦ Real.arcsin (f k) - Real.arcsin (k * f k))
      (-f 1 / √(1 - (f 1) ^ 2)) 1 := by
  have hfirst := (Real.hasDerivAt_arcsin hneg hpos).comp 1 hf
  have hprod := (hasDerivAt_id 1).mul hf
  have hsecond := (Real.hasDerivAt_arcsin (by simpa using hneg)
    (by simpa using hpos)).comp 1 hprod
  convert! hfirst.sub hsecond using 1
  all_goals simp only [Pi.mul_apply, id_eq, one_mul]
  all_goals ring

/-- At the compact core, releasing the singleton curvature has the explicit
negative first variation used by the local suspension. -/
theorem hasDerivAt_rResidualZeroReleased_one
    {u q v : ℝ} (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (hu1 : u < 1) (huq : u < q) (hv1 : v < 1) (hvq : v < q) :
    HasDerivAt (fun k ↦ rResidualZeroReleased k u q v)
      (-((rCoreSideD 1 u q v / 2) /
          √(1 - (rCoreSideD 1 u q v / 2) ^ 2)) -
        (rCoreSideA 1 u q v / 2) /
          √(1 - (rCoreSideA 1 u q v / 2) ^ 2)) 1 := by
  have hDelta : 0 < orthogonalDelta 1 u q v :=
    orthogonal_delta_pos_of_strict_alternation zero_lt_one hu hq hv
      hu1 huq hv1 hvq
  have hsqrtDiff : DifferentiableAt ℝ (fun k ↦ √(orthogonalDelta k u q v)) 1 :=
    (show DifferentiableAt ℝ (fun k ↦ orthogonalDelta k u q v) 1 by
      unfold orthogonalDelta; fun_prop).sqrt hDelta.ne'
  have hsqrtNe : √(orthogonalDelta 1 u q v) ≠ 0 := (Real.sqrt_pos.2 hDelta).ne'
  have hAdiff : DifferentiableAt ℝ (fun k ↦ rCoreSideA k u q v / 2) 1 := by
    unfold rCoreSideA
    exact ((differentiableAt_const _).div hsqrtDiff hsqrtNe).div_const 2
  have hDdiff : DifferentiableAt ℝ (fun k ↦ rCoreSideD k u q v / 2) 1 := by
    unfold rCoreSideD
    exact ((differentiableAt_const _).div hsqrtDiff hsqrtNe).div_const 2
  have hdata := r_core_realization_data zero_lt_one hu hq hv
    hu1 huq hv1 hvq
  have hsides := r_core_sides_pos zero_lt_one hu hq hv
    hu1 huq hv1 hvq
  have hw := (moderateArc_zero_iff.mp hdata.1) (0 : ZMod 4)
  norm_num [fourProfile] at hw
  have hA0 : 0 < rCoreSideA 1 u q v / 2 := half_pos hsides.1
  have hD0 : 0 < rCoreSideD 1 u q v / 2 := half_pos hsides.2.2.2
  have hA1 : rCoreSideA 1 u q v / 2 < 1 := by
    rw [rCoreSideA, orthogonalDelta]
    norm_num
    calc
      2 * √(q ^ 2 - v ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) / 2 =
          √(q ^ 2 - v ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) := by ring
      _ < 1 := hw.2.2
  have hD1 : rCoreSideD 1 u q v / 2 < 1 := by
    rw [rCoreSideD, orthogonalDelta]
    norm_num
    calc
      2 * √(q ^ 2 - u ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) / 2 =
          √(q ^ 2 - u ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) := by ring
      _ < 1 := hw.2.1
  have hAderiv := hasDerivAt_arcsin_sub_arcsin_mul hAdiff.hasDerivAt
    (by linarith) (ne_of_lt hA1)
  have hDderiv := hasDerivAt_arcsin_sub_arcsin_mul hDdiff.hasDerivAt
    (by linarith) (ne_of_lt hD1)
  convert! hDderiv.add hAderiv using 1
  · funext k
    unfold rResidualZeroReleased
    simp only [Pi.add_apply]
    ring
  · ring

/-- The released singleton residual decreases strictly at the compact
core slice `k = 1`. -/
theorem deriv_rResidualZeroReleased_one_neg
    {u q v : ℝ} (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (hu1 : u < 1) (huq : u < q) (hv1 : v < 1) (hvq : v < q) :
    deriv (fun k ↦ rResidualZeroReleased k u q v) 1 < 0 := by
  have hderiv := hasDerivAt_rResidualZeroReleased_one
    hu hq hv hu1 huq hv1 hvq
  rw [hderiv.deriv]
  have hdata := r_core_realization_data zero_lt_one hu hq hv
    hu1 huq hv1 hvq
  have hsides := r_core_sides_pos zero_lt_one hu hq hv
    hu1 huq hv1 hvq
  have hw := (moderateArc_zero_iff.mp hdata.1) (0 : ZMod 4)
  norm_num [fourProfile] at hw
  have hA0 : 0 < rCoreSideA 1 u q v / 2 := half_pos hsides.1
  have hD0 : 0 < rCoreSideD 1 u q v / 2 := half_pos hsides.2.2.2
  have hA1 : rCoreSideA 1 u q v / 2 < 1 := by
    rw [rCoreSideA, orthogonalDelta]
    norm_num
    calc
      2 * √(q ^ 2 - v ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) / 2 =
          √(q ^ 2 - v ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) := by ring
      _ < 1 := hw.2.2
  have hD1 : rCoreSideD 1 u q v / 2 < 1 := by
    rw [rCoreSideD, orthogonalDelta]
    norm_num
    calc
      2 * √(q ^ 2 - u ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) / 2 =
          √(q ^ 2 - u ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) := by ring
      _ < 1 := hw.2.1
  have hAden : 0 < √(1 - (rCoreSideA 1 u q v / 2) ^ 2) :=
    Real.sqrt_pos.2 (sub_pos.2 ((sq_lt_one_iff₀ hA0.le).2 hA1))
  have hDden : 0 < √(1 - (rCoreSideD 1 u q v / 2) ^ 2) :=
    Real.sqrt_pos.2 (sub_pos.2 ((sq_lt_one_iff₀ hD0.le).2 hD1))
  have hDratio := div_pos hD0 hDden
  have hAratio := div_pos hA0 hAden
  linarith

@[simp] theorem r_residual_one_released_one (p t q u v : ℝ) :
    rResidualOneReleased p t 1 u q v = rResidualOne p t q u v := by
  simp [rResidualOneReleased, rResidualOne]

@[simp] theorem r_residual_three_released_one (q h l u v : ℝ) :
    rResidualThreeReleased h l 1 u q v = rResidualThree q h l u v := by
  simp [rResidualThreeReleased, rResidualThree]

/-- The two real `R` residuals bundled as a complex map. -/
noncomputable def rResidualMap (p t q h l : ℝ) (z : ℝ × ℝ) : ℂ :=
  (rResidualOne p t q z.1 z.2 : ℂ) +
    (rResidualThree q h l z.1 z.2 : ℂ) * Complex.I

/-- The first `R` residual is the grouped actual turn minus the effective
turn at corner one of the normalized orthogonal core. -/
theorem r_residual_one_eq_core_sides (p t q u v : ℝ) :
    rResidualOne p t q u v =
      Real.arcsin (p * (rCoreSideA 1 u q v / 2)) +
        Real.arcsin (t * (rCoreSideB 1 u q v / 2)) -
          Real.arcsin (u * (rCoreSideA 1 u q v / 2)) -
            Real.arcsin (u * (rCoreSideB 1 u q v / 2)) := by
  simp only [r_core_side_a_half_at_one, r_core_side_b_half_at_one]
  rfl

/-- The third `R` residual is the grouped actual turn minus the effective
turn at corner three of the normalized orthogonal core. -/
theorem r_residual_three_eq_core_sides (q h l u v : ℝ) :
    rResidualThree q h l u v =
      Real.arcsin (h * (rCoreSideC 1 u q v / 2)) +
        Real.arcsin (l * (rCoreSideD 1 u q v / 2)) -
          Real.arcsin (v * (rCoreSideC 1 u q v / 2)) -
            Real.arcsin (v * (rCoreSideD 1 u q v / 2)) := by
  simp only [r_core_side_c_half_at_one, r_core_side_d_half_at_one]
  rfl

/-- At the released singleton, the actual turn is the core turn plus its
residual. -/
theorem turning_angle_r_core_zero (p t k u q h l v : ℝ) :
    turningAngle 0 (rActualProfile p t q h l)
        (rCoreCompactLengths k u q v) 0 =
      turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 0 +
        rResidualZeroReleased k u q v := by
  norm_num [turningAngle, rActualProfile, rCoreCompactLengths,
    rResidualZeroReleased, fourProfile]

/-- The two actual turns in the first collapsed pair equal its effective
core turn plus the first mixed residual. -/
theorem turning_angle_r_core_one_two (p t k u q h l v : ℝ) :
    turningAngle 0 (rActualProfile p t q h l)
          (rCoreCompactLengths k u q v) 1 +
        turningAngle 0 (rActualProfile p t q h l)
          (rCoreCompactLengths k u q v) 2 =
      turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 1 +
        rResidualOneReleased p t k u q v := by
  norm_num [turningAngle, rResidualOneReleased]

/-- The retained `q` corner has no residual. -/
theorem turning_angle_r_core_three (p t k u q h l v : ℝ) :
    turningAngle 0 (rActualProfile p t q h l)
        (rCoreCompactLengths k u q v) 3 =
      turningAngle 0 (fourProfile k u q v)
        (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
          (rCoreSideC k u q v) (rCoreSideD k u q v)) 2 := by
  norm_num [turningAngle]

/-- The two actual turns in the last collapsed pair equal its effective
core turn plus the third mixed residual. -/
theorem turning_angle_r_core_four_five (p t k u q h l v : ℝ) :
    turningAngle 0 (rActualProfile p t q h l)
          (rCoreCompactLengths k u q v) 4 +
        turningAngle 0 (rActualProfile p t q h l)
          (rCoreCompactLengths k u q v) 5 =
      turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 3 +
        rResidualThreeReleased h l k u q v := by
  norm_num [turningAngle, rResidualThreeReleased]

/-- The literal total-turn defect of the compactified six-edge family is
exactly the sum of the three released orthogonal residuals. -/
theorem turning_sum_r_core_compact {p t k u q h l v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    turningSum (rActualProfile p t q h l) (rCoreCompactLengths k u q v) =
      2 * Real.pi + rResidualZeroReleased k u q v +
        rResidualOneReleased p t k u q v +
          rResidualThreeReleased h l k u q v := by
  let coreK := fourProfile k u q v
  let coreL := fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
    (rCoreSideC k u q v) (rCoreSideD k u q v)
  have hcore : turningSum coreK coreL = 2 * Real.pi := by
    simpa only [coreK, coreL] using
      (r_core_realization_data hk hu hq hv huk huq hvk hvq).2.2.1
  have hcoreExpand :
      turningAngle 0 coreK coreL 0 + turningAngle 0 coreK coreL 1 +
          turningAngle 0 coreK coreL 2 + turningAngle 0 coreK coreL 3 =
        2 * Real.pi := by
    rw [← hcore]
    unfold turningSum
    rw [← sum_range_natCast_add (turningAngle 0 coreK coreL) 0]
    norm_num [Finset.sum_range_succ]
  have h0 := turning_angle_r_core_zero p t k u q h l v
  have h12 := turning_angle_r_core_one_two p t k u q h l v
  have h3 := turning_angle_r_core_three p t k u q h l v
  have h45 := turning_angle_r_core_four_five p t k u q h l v
  unfold turningSum
  rw [← sum_range_natCast_add
    (turningAngle 0 (rActualProfile p t q h l) (rCoreCompactLengths k u q v)) 0]
  norm_num [Finset.sum_range_succ]
  linarith

/-- The literal compactified closure is, up to the harmless global phase
from the released singleton, exactly the nonlinear orthogonal residual
controller applied to the three grouped turn residuals. -/
theorem closure_gap_r_core_compact (p t k u q h l v : ℝ) :
    closureGap (rActualProfile p t q h l) (rCoreCompactLengths k u q v) =
      unitPhase (rResidualZeroReleased k u q v) *
      orthogonalResidualDevelopedClosure
        (rCoreDevelopedEdge k u q v 0) (rCoreDevelopedEdge k u q v 1)
        (rCoreDevelopedEdge k u q v 2) (rCoreDevelopedEdge k u q v 3)
        (rResidualOneReleased p t k u q v)
        (rResidualThreeReleased h l k u q v) := by
  let actualK := rActualProfile p t q h l
  let actualL := rCoreCompactLengths k u q v
  let coreK := fourProfile k u q v
  let coreL := fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
    (rCoreSideC k u q v) (rCoreSideD k u q v)
  let α0 := turningAngle 0 coreK coreL 0
  let α1 := turningAngle 0 coreK coreL 1
  let α2 := turningAngle 0 coreK coreL 2
  let α3 := turningAngle 0 coreK coreL 3
  let θ0 := turningAngle 0 actualK actualL 0
  let θ1 := turningAngle 0 actualK actualL 1
  let θ2 := turningAngle 0 actualK actualL 2
  let θ3 := turningAngle 0 actualK actualL 3
  let θ4 := turningAngle 0 actualK actualL 4
  let θ5 := turningAngle 0 actualK actualL 5
  let r0 := rResidualZeroReleased k u q v
  let r1 := rResidualOneReleased p t k u q v
  let r3 := rResidualThreeReleased h l k u q v
  have h0 : θ0 = α0 + r0 := by
    simpa only [actualK, actualL, coreK, coreL, θ0, α0, r0] using
      turning_angle_r_core_zero p t k u q h l v
  have h12 : θ1 + θ2 = α1 + r1 := by
    simpa only [actualK, actualL, coreK, coreL, θ1, θ2, α1, r1] using
      turning_angle_r_core_one_two p t k u q h l v
  have h3 : θ3 = α2 := by
    simpa only [actualK, actualL, coreK, coreL, θ3, α2] using
      turning_angle_r_core_three p t k u q h l v
  have h45 : θ4 + θ5 = α3 + r3 := by
    simpa only [actualK, actualL, coreK, coreL, θ4, θ5, α3, r3] using
      turning_angle_r_core_four_five p t k u q h l v
  have hp0 : unitPhase θ0 = unitPhase r0 * unitPhase α0 := by
    rw [h0, unitPhase_add]
    ring
  have hp12 : unitPhase θ1 * unitPhase θ2 = unitPhase r1 * unitPhase α1 := by
    rw [← unitPhase_add, h12, unitPhase_add]
    ring
  have hp3 : unitPhase θ3 = unitPhase α2 := by rw [h3]
  have hp45 : unitPhase θ4 * unitPhase θ5 = unitPhase r3 * unitPhase α3 := by
    rw [← unitPhase_add, h45, unitPhase_add]
    ring
  have hp012 : unitPhase θ0 * unitPhase θ1 * unitPhase θ2 =
      unitPhase r0 * unitPhase α0 * unitPhase r1 * unitPhase α1 := by
    calc
      _ = unitPhase θ0 * (unitPhase θ1 * unitPhase θ2) := by ring
      _ = _ := by rw [hp0, hp12]; ring
  have hp0123 : unitPhase θ0 * unitPhase θ1 * unitPhase θ2 * unitPhase θ3 =
      unitPhase r0 * unitPhase α0 * unitPhase r1 * unitPhase α1 *
        unitPhase α2 := by rw [hp012, hp3]
  have hp012345 : unitPhase θ0 * unitPhase θ1 * unitPhase θ2 * unitPhase θ3 *
      unitPhase θ4 * unitPhase θ5 =
      unitPhase r0 * unitPhase α0 * unitPhase r1 * unitPhase α1 *
        unitPhase α2 * unitPhase r3 * unitPhase α3 := by
    calc
      _ = (unitPhase θ0 * unitPhase θ1 * unitPhase θ2 * unitPhase θ3) *
          (unitPhase θ4 * unitPhase θ5) := by ring
      _ = _ := by rw [hp0123, hp45]; ring
  rw [closure_gap_six_unit_phase]
  simp only [r_core_compact_lengths_zero, r_core_compact_lengths_one,
    r_core_compact_lengths_two, r_core_compact_lengths_three,
    r_core_compact_lengths_four, r_core_compact_lengths_five,
    Complex.ofReal_zero, zero_mul, add_zero]
  change (rCoreSideA k u q v : ℂ) * unitPhase θ0 +
      (rCoreSideB k u q v : ℂ) * (unitPhase θ0 * unitPhase θ1 * unitPhase θ2) +
      (rCoreSideC k u q v : ℂ) *
        (unitPhase θ0 * unitPhase θ1 * unitPhase θ2 * unitPhase θ3) +
      (rCoreSideD k u q v : ℂ) *
        (unitPhase θ0 * unitPhase θ1 * unitPhase θ2 * unitPhase θ3 *
          unitPhase θ4 * unitPhase θ5) = _
  rw [orthogonalResidualDevelopedClosure, hp012345, hp0123, hp012, hp0]
  simp only [r_core_developed_edge_zero, r_core_developed_edge_one,
    r_core_developed_edge_two, r_core_developed_edge_three]
  dsimp only [coreL, α0, α1, α2, α3, r0, r1, r3]
  norm_num [unitPhase_add]
  ring

/-- On a strict released core, its literal compactified closure factors
through only the first and third mixed residuals. -/
theorem closure_gap_r_core_compact_eq_residual
    {p t k u q h l v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    closureGap (rActualProfile p t q h l) (rCoreCompactLengths k u q v) =
      unitPhase (rResidualZeroReleased k u q v) *
        orthogonalResidualClosure (rCoreDevelopedEdge k u q v 0)
          (rCoreDevelopedEdge k u q v 3)
          (rResidualOneReleased p t k u q v)
          (rResidualThreeReleased h l k u q v) := by
  rw [closure_gap_r_core_compact]
  rw [orthogonal_residual_developed_closure_eq
    (r_core_developed_edges_close hk hu hq hv huk huq hvk hvq)]

/-- The phase-normalized literal target of the compactified Type-A `R`
family. -/
noncomputable def rCoreCompactTarget
    (p t k u q h l v : ℝ) : ℝ × ℂ :=
  (turningSum (rActualProfile p t q h l) (rCoreCompactLengths k u q v) -
      2 * Real.pi,
    unitPhase (-rResidualZeroReleased k u q v) *
      closureGap (rActualProfile p t q h l) (rCoreCompactLengths k u q v))

/-- Vanishing of the phase-normalized target is exactly literal total turn
and closure of the compactified six-edge family. -/
theorem r_core_compact_target_eq_zero_iff (p t k u q h l v : ℝ) :
    rCoreCompactTarget p t k u q h l v = 0 ↔
      turningSum (rActualProfile p t q h l) (rCoreCompactLengths k u q v) =
          2 * Real.pi ∧
        closureGap (rActualProfile p t q h l) (rCoreCompactLengths k u q v) = 0 := by
  simp [rCoreCompactTarget, Prod.ext_iff, unitPhase, sub_eq_zero]

/-- The phase-normalized literal target is exactly the nonlinear residual
controller, with no limiting or first-order approximation. -/
theorem r_core_compact_target_eq_controller
    {p t k u q h l v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    rCoreCompactTarget p t k u q h l v =
      orthogonalResidualController (rCoreDevelopedEdge k u q v 0)
        (rCoreDevelopedEdge k u q v 3)
        (rResidualZeroReleased k u q v,
          (rResidualOneReleased p t k u q v,
            rResidualThreeReleased h l k u q v)) := by
  apply Prod.ext
  · rw [rCoreCompactTarget, orthogonalResidualController,
      turning_sum_r_core_compact hk hu hq hv huk huq hvk hvq]
    simp
    ring
  · rw [rCoreCompactTarget, orthogonalResidualController,
      closure_gap_r_core_compact_eq_residual hk hu hq hv huk huq hvk hvq]
    have hphase : unitPhase (-rResidualZeroReleased k u q v) *
        unitPhase (rResidualZeroReleased k u q v) = 1 := by
      rw [← unitPhase_add]
      simp [unitPhase]
    rw [← mul_assoc, hphase, one_mul]

/-- Residual coordinates of the literal compactified target. -/
noncomputable def rCoreCompactResidualTarget
    (p t k u q h l v : ℝ) : ℝ × ℂ :=
  orthogonalResidualTargetCoordinates (rCoreDevelopedEdge k u q v 0)
    (rCoreDevelopedEdge k u q v 3)
    (rResidualOneReleased p t k u q v)
    (rResidualThreeReleased h l k u q v)
    (rCoreCompactTarget p t k u q h l v)

/-- Wherever the nonlinear closure factor is nonsingular, residualizing the
literal compactified target recovers `(R0,R1+iR3)` exactly. -/
theorem r_core_compact_residual_target_eq
    {p t k u q h l v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q)
    (hdet : orthogonalResidualFactorDet (rCoreDevelopedEdge k u q v 0)
      (rCoreDevelopedEdge k u q v 3)
      (rResidualZeroReleased k u q v,
        (rResidualOneReleased p t k u q v,
          rResidualThreeReleased h l k u q v)) ≠ 0) :
    rCoreCompactResidualTarget p t k u q h l v =
      (rResidualZeroReleased k u q v,
        (rResidualOneReleased p t k u q v : ℂ) +
          (rResidualThreeReleased h l k u q v : ℂ) * Complex.I) := by
  rw [rCoreCompactResidualTarget,
    r_core_compact_target_eq_controller hk hu hq hv huk huq hvk hvq]
  exact orthogonal_residual_target_coordinates_controller hdet

/-- At the unreleased slice `k=1`, the transformed literal target is exactly
the planar `R` residual map used by the winding theorem. -/
theorem r_core_compact_residual_target_one
    {p t q h l u v : ℝ}
    (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (hu1 : u < 1) (huq : u < q) (hv1 : v < 1) (hvq : v < q)
    (hdet : orthogonalResidualFactorDet (rCoreDevelopedEdge 1 u q v 0)
      (rCoreDevelopedEdge 1 u q v 3)
      (0, (rResidualOne p t q u v, rResidualThree q h l u v)) ≠ 0) :
    rCoreCompactResidualTarget p t 1 u q h l v =
      (0, rResidualMap p t q h l (u, v)) := by
  have hdet' : orthogonalResidualFactorDet (rCoreDevelopedEdge 1 u q v 0)
      (rCoreDevelopedEdge 1 u q v 3)
      (rResidualZeroReleased 1 u q v,
        (rResidualOneReleased p t 1 u q v,
          rResidualThreeReleased h l 1 u q v)) ≠ 0 := by
    simpa using hdet
  simpa [rResidualMap] using
    r_core_compact_residual_target_eq (p := p) (t := t) (k := 1)
      (u := u) (q := q) (h := h) (l := l) (v := v)
      zero_lt_one hu hq hv hu1 huq hv1 hvq hdet'

/-- The real coordinate of the bundled `R` residual. -/
@[simp] theorem r_residual_map_re (p t q h l : ℝ) (z : ℝ × ℝ) :
    (rResidualMap p t q h l z).re = rResidualOne p t q z.1 z.2 := by
  simp [rResidualMap]

/-- The imaginary coordinate of the bundled `R` residual. -/
@[simp] theorem r_residual_map_im (p t q h l : ℝ) (z : ℝ × ℝ) :
    (rResidualMap p t q h l z).im = rResidualThree q h l z.1 z.2 := by
  simp [rResidualMap]

private lemma arcsin_scaled_lt_aux {x y c d : ℝ}
    (hx : 0 ≤ x) (hxy : x < y) (hc : 0 < c) (hd : 0 < d) (hyc : y * c ≤ d) :
    Real.arcsin (x * c / d) < Real.arcsin (y * c / d) := by
  apply Real.arcsin_lt_arcsin
  · have := div_nonneg (mul_nonneg hx hc.le) hd.le
    linarith
  · exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hxy hc) hd
  · exact (div_le_one hd).2 hyc

private lemma square_root_data_aux {x : ℝ} (hx : 0 < x) :
    0 < √x ∧ (√x) ^ 2 = x :=
  ⟨Real.sqrt_pos.2 hx, Real.sq_sqrt hx.le⟩

/-- On the left face `u=p`, the first `R` residual is positive away from
the top-left corner. -/
theorem r_residual_one_left_pos {p t q v : ℝ}
    (hp : 0 < p) (hpt : p < t) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hwall : t ^ 2 * (1 - v ^ 2) < q ^ 2 - p ^ 2 * v ^ 2) :
    0 < rResidualOne p t q p v := by
  let b := √(1 - v ^ 2)
  let d := √(q ^ 2 - p ^ 2 * v ^ 2)
  have hbInside : 0 < 1 - v ^ 2 := by nlinarith
  obtain ⟨hb, hbsq⟩ := square_root_data_aux hbInside
  have hleft : 0 < t ^ 2 * (1 - v ^ 2) :=
    mul_pos (sq_pos_of_pos (hp.trans hpt)) hbInside
  have hdInside : 0 < q ^ 2 - p ^ 2 * v ^ 2 := hleft.trans hwall
  obtain ⟨hd, hdsq⟩ := square_root_data_aux hdInside
  have htb : t * b < d := by
    apply (sq_lt_sq₀ (mul_pos (hp.trans hpt) hb).le hd.le).1
    rw [mul_pow, hbsq, hdsq]
    exact hwall
  have hangle := arcsin_scaled_lt_aux hp.le hpt hb hd htb.le
  have hangle' : Real.arcsin (p * (b / d)) < Real.arcsin (t * (b / d)) := by
    simpa [b, d, div_eq_mul_inv, mul_assoc] using hangle
  dsimp only [rResidualOne]
  linarith

/-- On the top face `v=1`, the first `R` residual is negative away from
the top-left corner. -/
theorem r_residual_one_top_neg {p t q u : ℝ}
    (hp : 0 ≤ p) (hpu : p < u) (hu1 : u ≤ 1) (hq : 1 < q) :
    rResidualOne p t q u 1 < 0 := by
  let a := √(q ^ 2 - 1)
  let d := √(q ^ 2 - u ^ 2)
  have haInside : 0 < q ^ 2 - 1 := by nlinarith
  obtain ⟨ha, hasq⟩ := square_root_data_aux haInside
  have hdInside : 0 < q ^ 2 - u ^ 2 := by nlinarith
  obtain ⟨hd, hdsq⟩ := square_root_data_aux hdInside
  have hua : u * a ≤ d := by
    apply (sq_le_sq₀ (mul_pos (lt_of_le_of_lt hp hpu) ha).le hd.le).1
    rw [mul_pow, hasq, hdsq]
    have huSq : u ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (lt_of_le_of_lt hp hpu).le zero_le_one).2 hu1
    nlinarith [mul_nonneg (sq_nonneg q) (sub_nonneg.mpr huSq)]
  have hangle := arcsin_scaled_lt_aux hp hpu ha hd hua
  have hangle' : Real.arcsin (p * (a / d)) < Real.arcsin (u * (a / d)) := by
    simpa [a, d, div_eq_mul_inv, mul_assoc] using hangle
  dsimp only [rResidualOne]
  simpa using hangle'

/-- On the bottom face `v=l`, the third `R` residual is positive away from
the bottom-right corner. -/
theorem r_residual_three_bottom_pos {q h l u : ℝ}
    (hl : 0 ≤ l) (hlh : l < h) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hwall : h ^ 2 * (1 - u ^ 2) < q ^ 2 - u ^ 2 * l ^ 2) :
    0 < rResidualThree q h l u l := by
  let c := √(1 - u ^ 2)
  let d := √(q ^ 2 - u ^ 2 * l ^ 2)
  have hcInside : 0 < 1 - u ^ 2 := by nlinarith
  obtain ⟨hc, hcsq⟩ := square_root_data_aux hcInside
  have hleft : 0 < h ^ 2 * (1 - u ^ 2) :=
    mul_pos (sq_pos_of_pos (hl.trans_lt hlh)) hcInside
  have hdInside : 0 < q ^ 2 - u ^ 2 * l ^ 2 := hleft.trans hwall
  obtain ⟨hd, hdsq⟩ := square_root_data_aux hdInside
  have hhc : h * c < d := by
    apply (sq_lt_sq₀ (mul_pos (hl.trans_lt hlh) hc).le hd.le).1
    rw [mul_pow, hcsq, hdsq]
    exact hwall
  have hangle := arcsin_scaled_lt_aux hl hlh hc hd hhc.le
  have hangle' : Real.arcsin (l * (c / d)) < Real.arcsin (h * (c / d)) := by
    simpa [c, d, div_eq_mul_inv, mul_assoc] using hangle
  dsimp only [rResidualThree]
  linarith

/-- On the right face `u=1`, the third `R` residual is negative away from
the bottom-right corner. -/
theorem r_residual_three_right_neg {q h l v : ℝ}
    (hl : 0 ≤ l) (hlv : l < v) (hv1 : v ≤ 1) (hq : 1 < q) :
    rResidualThree q h l 1 v < 0 := by
  let e := √(q ^ 2 - 1)
  let d := √(q ^ 2 - v ^ 2)
  have heInside : 0 < q ^ 2 - 1 := by nlinarith
  obtain ⟨he, hesq⟩ := square_root_data_aux heInside
  have hdInside : 0 < q ^ 2 - v ^ 2 := by nlinarith
  obtain ⟨hd, hdsq⟩ := square_root_data_aux hdInside
  have hve : v * e ≤ d := by
    apply (sq_le_sq₀ (mul_pos (hl.trans_lt hlv) he).le hd.le).1
    rw [mul_pow, hesq, hdsq]
    have hvSq : v ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ (hl.trans_lt hlv).le zero_le_one).2 hv1
    nlinarith [mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hvSq)]
  have hangle := arcsin_scaled_lt_aux hl hlv he hd hve
  have hangle' : Real.arcsin (l * (e / d)) < Real.arcsin (v * (e / d)) := by
    simpa [e, d, div_eq_mul_inv, mul_assoc] using hangle
  dsimp only [rResidualThree]
  simpa using hangle'

/-- The first residual vanishes at the top-left corner `(p,1)`. -/
@[simp] theorem r_residual_one_top_left (p t q : ℝ) :
    rResidualOne p t q p 1 = 0 := by
  simp [rResidualOne]

/-- The third residual vanishes at the bottom-right corner `(1,l)`. -/
@[simp] theorem r_residual_three_bottom_right (q h l : ℝ) :
    rResidualThree q h l 1 l = 0 := by
  simp [rResidualThree]

/-- The third residual at `(p,1)` is the upper-left corner discriminator. -/
theorem r_residual_three_top_left_eq {p q h l : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) :
    rResidualThree q h l p 1 =
      Real.arcsin (h * (√(1 - p ^ 2) / √(q ^ 2 - p ^ 2))) +
        Real.arcsin l - Real.arcsin (√(1 - p ^ 2) / √(q ^ 2 - p ^ 2)) -
          Real.pi / 2 := by
  have hden : √(q ^ 2 - p ^ 2) ≠ 0 := (Real.sqrt_pos.2 <| by
    nlinarith [sq_lt_sq₀ hp (hp.trans_lt hpq).le |>.2 hpq]).ne'
  simp [rResidualThree, hden, Real.arcsin_one]

/-- The first residual at `(1,l)` is the bottom-right discriminator `B`. -/
theorem r_residual_one_bottom_right_eq {p t q l : ℝ}
    (hl : 0 ≤ l) (hlq : l < q) :
    rResidualOne p t q 1 l =
      Real.arcsin p +
        Real.arcsin (t * (√(1 - l ^ 2) / √(q ^ 2 - l ^ 2))) -
          Real.pi / 2 -
            Real.arcsin (√(1 - l ^ 2) / √(q ^ 2 - l ^ 2)) := by
  have hden : √(q ^ 2 - l ^ 2) ≠ 0 := (Real.sqrt_pos.2 <| by
    nlinarith [sq_lt_sq₀ hl (hl.trans_lt hlq).le |>.2 hlq]).ne'
  simp [rResidualOne, hden, Real.arcsin_one]

/-- The first `R` residual is continuous wherever the orthogonal denominator
is strictly positive. -/
theorem continuousOn_rResidualOne_of_denom_pos
    {p t q : ℝ} {s : Set (ℝ × ℝ)}
    (hden : ∀ z ∈ s, 0 < q ^ 2 - z.1 ^ 2 * z.2 ^ 2) :
    ContinuousOn (fun z ↦ rResidualOne p t q z.1 z.2) s := by
  let d : ℝ × ℝ → ℝ := fun z ↦ √(q ^ 2 - z.1 ^ 2 * z.2 ^ 2)
  let a : ℝ × ℝ → ℝ := fun z ↦ √(q ^ 2 - z.2 ^ 2) / d z
  let b : ℝ × ℝ → ℝ := fun z ↦ √(1 - z.2 ^ 2) / d z
  have hd : Continuous d := by
    dsimp only [d]
    fun_prop
  have hdNe : ∀ z ∈ s, d z ≠ 0 :=
    fun z hz ↦ (Real.sqrt_pos.2 (hden z hz)).ne'
  have ha : ContinuousOn a s := by
    dsimp only [a]
    exact (by fun_prop : Continuous fun z : ℝ × ℝ ↦ √(q ^ 2 - z.2 ^ 2)).continuousOn.div
      hd.continuousOn hdNe
  have hb : ContinuousOn b s := by
    dsimp only [b]
    exact (by fun_prop : Continuous fun z : ℝ × ℝ ↦ √(1 - z.2 ^ 2)).continuousOn.div
      hd.continuousOn hdNe
  change ContinuousOn (fun z ↦ Real.arcsin (p * a z) + Real.arcsin (t * b z) -
    Real.arcsin (z.1 * a z) - Real.arcsin (z.1 * b z)) s
  exact (((continuousOn_const.mul ha).arcsin.add
    (continuousOn_const.mul hb).arcsin).sub
      (continuousOn_fst.mul ha).arcsin).sub (continuousOn_fst.mul hb).arcsin

/-- The third `R` residual is continuous wherever the orthogonal denominator
is strictly positive. -/
theorem continuousOn_rResidualThree_of_denom_pos
    {q h l : ℝ} {s : Set (ℝ × ℝ)}
    (hden : ∀ z ∈ s, 0 < q ^ 2 - z.1 ^ 2 * z.2 ^ 2) :
    ContinuousOn (fun z ↦ rResidualThree q h l z.1 z.2) s := by
  let d : ℝ × ℝ → ℝ := fun z ↦ √(q ^ 2 - z.1 ^ 2 * z.2 ^ 2)
  let c : ℝ × ℝ → ℝ := fun z ↦ √(1 - z.1 ^ 2) / d z
  let e : ℝ × ℝ → ℝ := fun z ↦ √(q ^ 2 - z.1 ^ 2) / d z
  have hd : Continuous d := by
    dsimp only [d]
    fun_prop
  have hdNe : ∀ z ∈ s, d z ≠ 0 :=
    fun z hz ↦ (Real.sqrt_pos.2 (hden z hz)).ne'
  have hc : ContinuousOn c s := by
    dsimp only [c]
    exact (by fun_prop : Continuous fun z : ℝ × ℝ ↦ √(1 - z.1 ^ 2)).continuousOn.div
      hd.continuousOn hdNe
  have he : ContinuousOn e s := by
    dsimp only [e]
    exact (by fun_prop : Continuous fun z : ℝ × ℝ ↦ √(q ^ 2 - z.1 ^ 2)).continuousOn.div
      hd.continuousOn hdNe
  change ContinuousOn (fun z ↦ Real.arcsin (h * c z) + Real.arcsin (l * e z) -
    Real.arcsin (z.2 * c z) - Real.arcsin (z.2 * e z)) s
  exact (((continuousOn_const.mul hc).arcsin.add
    (continuousOn_const.mul he).arcsin).sub
      (continuousOn_snd.mul hc).arcsin).sub (continuousOn_snd.mul he).arcsin

/-- The bundled complex `R` residual is continuous wherever its orthogonal
denominator is strictly positive. -/
theorem continuousOn_rResidualMap_of_denom_pos
    {p t q h l : ℝ} {s : Set (ℝ × ℝ)}
    (hden : ∀ z ∈ s, 0 < q ^ 2 - z.1 ^ 2 * z.2 ^ 2) :
    ContinuousOn (rResidualMap p t q h l) s := by
  have hOne := continuousOn_rResidualOne_of_denom_pos (p := p) (t := t) hden
  have hThree := continuousOn_rResidualThree_of_denom_pos (h := h) (l := l) hden
  exact (Complex.continuous_ofReal.comp_continuousOn hOne).add
    ((Complex.continuous_ofReal.comp_continuousOn hThree).mul continuousOn_const)

/-- The normalized `R` rectangle has positive orthogonal denominator when
`q > 1`. -/
lemma r_denom_pos_aux {q u v : ℝ}
    (hq : 1 < q) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < q ^ 2 - u ^ 2 * v ^ 2 := by
  have huv0 : 0 ≤ u * v := mul_nonneg hu0 hv0
  have huv1 : u * v ≤ 1 := by
    simpa using mul_le_mul hu1 hv1 hv0 zero_le_one
  have huvq : u * v < q := huv1.trans_lt hq
  have hsquare := (sq_lt_sq₀ huv0 (lt_trans zero_lt_one hq).le).2 huvq
  nlinarith [hsquare]

private lemma r_t_wall_pos_aux {q t u v : ℝ}
    (ht : 0 < t) (htq : t < q) (hq : 1 < q)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    t ^ 2 * (1 - v ^ 2) < q ^ 2 - u ^ 2 * v ^ 2 := by
  rw [← sub_pos, tWall_margin_identity]
  by_cases htu : t < u
  · have huq : u < q := hu1.trans_lt hq
    have hqu : 0 < q ^ 2 - u ^ 2 :=
      sub_pos.mpr <| (sq_lt_sq₀ hu0 (lt_trans zero_lt_one hq).le).2 huq
    have hut : 0 < u ^ 2 - t ^ 2 :=
      sub_pos.mpr <| (sq_lt_sq₀ ht.le (ht.trans htu).le).2 htu
    have hvSq : v ^ 2 ≤ 1 := by
      simpa using (sq_le_sq₀ hv0 zero_le_one).2 hv1
    have hnonneg : 0 ≤ (1 - v ^ 2) * (u ^ 2 - t ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hvSq) hut.le
    rw [show q ^ 2 - t ^ 2 + v ^ 2 * (t ^ 2 - u ^ 2) =
      (q ^ 2 - u ^ 2) + (1 - v ^ 2) * (u ^ 2 - t ^ 2) by ring]
    positivity
  · have hut : u ^ 2 ≤ t ^ 2 :=
      (sq_le_sq₀ hu0 ht.le).2 (le_of_not_gt htu)
    have hqt : 0 < q ^ 2 - t ^ 2 :=
      sub_pos.mpr <| (sq_lt_sq₀ ht.le (lt_trans zero_lt_one hq).le).2 htq
    exact add_pos_of_pos_of_nonneg hqt
      (mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hut))

private lemma r_h_wall_pos_aux {p q h u v : ℝ}
    (hp : 0 ≤ p) (hpu : p ≤ u)
    (hh : 1 < h) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2) :
    h ^ 2 * (1 - u ^ 2) < q ^ 2 - u ^ 2 * v ^ 2 := by
  rw [← sub_pos, hWall_margin_identity]
  have hpSq : p ^ 2 ≤ u ^ 2 := (sq_le_sq₀ hp (hp.trans hpu)).2 hpu
  have hvSq : v ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ hv0 zero_le_one).2 hv1
  have hvh : v ^ 2 ≤ h ^ 2 := hvSq.trans <| by nlinarith
  have hfirst : 0 ≤ (u ^ 2 - p ^ 2) * (h ^ 2 - v ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hpSq) (sub_nonneg.mpr hvh)
  have hsecond : 0 ≤ p ^ 2 * (1 - v ^ 2) :=
    mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hvSq)
  have hbase' : 0 < q ^ 2 - h ^ 2 + p ^ 2 * (h ^ 2 - 1) := by
    nlinarith [hbase]
  rw [show q ^ 2 - h ^ 2 + u ^ 2 * (h ^ 2 - v ^ 2) =
    (q ^ 2 - h ^ 2 + p ^ 2 * (h ^ 2 - 1)) +
      (u ^ 2 - p ^ 2) * (h ^ 2 - v ^ 2) + p ^ 2 * (1 - v ^ 2) by ring]
  positivity

/-- The actual `t`-wall stays strict on the whole closed physical
`R` rectangle. -/
theorem r_t_wall_pos_on_rectangle {q t u v : ℝ}
    (ht : 0 < t) (htq : t < q) (hq : 1 < q)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    t ^ 2 * (1 - v ^ 2) < q ^ 2 - u ^ 2 * v ^ 2 :=
  r_t_wall_pos_aux ht htq hq hu0 hu1 hv0 hv1

/-- The actual `h`-wall stays strict on the whole closed physical
`R` rectangle once the lower-left wall inequality holds. -/
theorem r_h_wall_pos_on_rectangle {p q h u v : ℝ}
    (hp : 0 ≤ p) (hpu : p ≤ u) (hh : 1 < h)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2) :
    h ^ 2 * (1 - u ^ 2) < q ^ 2 - u ^ 2 * v ^ 2 :=
  r_h_wall_pos_aux hp hpu hh hv0 hv1 hbase

/-- The squared `t`-wall inequality is exactly the strict arcsine wall for
the second orthogonal side. -/
theorem r_actual_t_sideB_wall_lt_one {q t u v : ℝ}
    (ht : 0 < t) (htq : t < q) (hq : 1 < q)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    |t * (rCoreSideB 1 u q v / 2)| < 1 := by
  let b := √(1 - v ^ 2)
  let d := √(q ^ 2 - u ^ 2 * v ^ 2)
  have hbInside : 0 < 1 - v ^ 2 := by nlinarith
  obtain ⟨hb, hbsq⟩ := square_root_data_aux hbInside
  have hwall := r_t_wall_pos_on_rectangle ht htq hq hu0 hu1 hv0 hv1.le
  have hleft : 0 < t ^ 2 * (1 - v ^ 2) :=
    mul_pos (sq_pos_of_pos ht) hbInside
  have hdInside : 0 < q ^ 2 - u ^ 2 * v ^ 2 := hleft.trans hwall
  obtain ⟨hd, hdsq⟩ := square_root_data_aux hdInside
  have htb : t * b < d := by
    apply (sq_lt_sq₀ (mul_pos ht hb).le hd.le).1
    rw [mul_pow, hbsq, hdsq]
    exact hwall
  have hratio : t * (b / d) < 1 := by
    calc
      t * (b / d) = (t * b) / d := by ring
      _ < 1 := (div_lt_one hd).2 htb
  rw [r_core_side_b_half_at_one, abs_of_pos]
  · simpa only [b, d] using hratio
  · exact mul_pos ht (div_pos hb hd)

/-- The squared `h`-wall inequality is exactly the strict arcsine wall for
the third orthogonal side. -/
theorem r_actual_h_sideC_wall_lt_one {p q h u v : ℝ}
    (hp : 0 ≤ p) (hpu : p ≤ u) (hh : 1 < h)
    (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2) :
    |h * (rCoreSideC 1 u q v / 2)| < 1 := by
  let c := √(1 - u ^ 2)
  let d := √(q ^ 2 - u ^ 2 * v ^ 2)
  have hcInside : 0 < 1 - u ^ 2 := by nlinarith
  obtain ⟨hc, hcsq⟩ := square_root_data_aux hcInside
  have hwall := r_h_wall_pos_on_rectangle hp hpu hh hv0 hv1 hbase
  have hh0 : 0 < h := zero_lt_one.trans hh
  have hleft : 0 < h ^ 2 * (1 - u ^ 2) :=
    mul_pos (sq_pos_of_pos hh0) hcInside
  have hdInside : 0 < q ^ 2 - u ^ 2 * v ^ 2 := hleft.trans hwall
  obtain ⟨hd, hdsq⟩ := square_root_data_aux hdInside
  have hhc : h * c < d := by
    apply (sq_lt_sq₀ (mul_pos hh0 hc).le hd.le).1
    rw [mul_pow, hcsq, hdsq]
    exact hwall
  have hratio : h * (c / d) < 1 := by
    calc
      h * (c / d) = (h * c) / d := by ring
      _ < 1 := (div_lt_one hd).2 hhc
  rw [r_core_side_c_half_at_one, abs_of_pos]
  · simpa only [c, d] using hratio
  · exact mul_pos hh0 (div_pos hc hd)

private lemma r_boundary_right_neg_aux {p t q h l : ℝ}
    (hp1 : p ≤ 1) (hl : 0 ≤ l) (hl1 : l < 1) (hq : 1 < q)
    {s : unitInterval} (hs : (s : ℝ) ≤ 1 / 8 ∨ 7 / 8 < (s : ℝ)) :
    (rResidualMap p t q h l (fourArcRectangleBoundary p 1 l 1 s)).im < 0 := by
  let z := fourArcRectangleBoundary p 1 l 1 s
  have hz := fourArcRectangleBoundary_mem hp1 hl1.le s
  have hzu : z.1 = 1 := fourArcRectangleBoundary_fst_eq_right _ _ _ _
    (hs.imp_right LT.lt.le)
  have hzv := fourArcRectangleBoundary_snd_gt_bottom_of_right
    (u₁ := p) (u₂ := 1) hl1 hs
  rw [r_residual_map_im]
  change rResidualThree q h l z.1 z.2 < 0
  rw [hzu]
  exact r_residual_three_right_neg hl hzv (by simpa [z] using hz.2.2) hq

private lemma r_boundary_top_neg_aux {p t q h l : ℝ}
    (hp : 0 ≤ p) (hp1 : p < 1) (hl1 : l ≤ 1) (hq : 1 < q)
    {s : unitInterval} (hs0 : 1 / 8 ≤ (s : ℝ)) (hs1 : (s : ℝ) < 3 / 8) :
    (rResidualMap p t q h l (fourArcRectangleBoundary p 1 l 1 s)).re < 0 := by
  let z := fourArcRectangleBoundary p 1 l 1 s
  have hz := fourArcRectangleBoundary_mem hp1.le hl1 s
  have hzv : z.2 = 1 := fourArcRectangleBoundary_snd_eq_top _ _ _ _ hs0 hs1.le
  have hzu := fourArcRectangleBoundary_fst_gt_left_of_top
    (v₁ := l) (v₂ := 1) hp1 hs0 hs1
  rw [r_residual_map_re]
  change rResidualOne p t q z.1 z.2 < 0
  rw [hzv]
  exact r_residual_one_top_neg hp hzu hz.1.2 hq

private lemma r_boundary_left_pos_aux {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hpt : p < t) (htq : t < q)
    (hq : 1 < q) (hl : 0 ≤ l) (hl1 : l < 1)
    {s : unitInterval} (hs0 : 3 / 8 < (s : ℝ)) (hs1 : (s : ℝ) ≤ 5 / 8) :
    0 < (rResidualMap p t q h l (fourArcRectangleBoundary p 1 l 1 s)).re := by
  let z := fourArcRectangleBoundary p 1 l 1 s
  have hz := fourArcRectangleBoundary_mem hp1.le hl1.le s
  have hzu : z.1 = p := fourArcRectangleBoundary_fst_eq_left _ _ _ _ hs0.le hs1
  have hzv := fourArcRectangleBoundary_snd_lt_top_of_left
    (u₁ := p) (u₂ := 1) hl1 hs0 hs1
  have hwall := r_t_wall_pos_aux (hp.trans hpt) htq hq hp.le hp1.le
    (hl.trans hz.2.1) hz.2.2
  rw [r_residual_map_re]
  change 0 < rResidualOne p t q z.1 z.2
  rw [hzu]
  exact r_residual_one_left_pos hp hpt (hl.trans hz.2.1) hzv hwall

private lemma r_boundary_bottom_pos_aux {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hh : 1 < h) (hl : 0 ≤ l) (hl1 : l < 1)
    (hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2)
    {s : unitInterval} (hs0 : 5 / 8 ≤ (s : ℝ)) (hs1 : (s : ℝ) < 7 / 8) :
    0 < (rResidualMap p t q h l (fourArcRectangleBoundary p 1 l 1 s)).im := by
  let z := fourArcRectangleBoundary p 1 l 1 s
  have hz := fourArcRectangleBoundary_mem hp1.le hl1.le s
  have hzv : z.2 = l := fourArcRectangleBoundary_snd_eq_bottom _ _ _ _ hs0 hs1.le
  have hzu := fourArcRectangleBoundary_fst_lt_right_of_bottom
    (v₁ := l) (v₂ := 1) hp1 hs0 hs1
  have hwall := r_h_wall_pos_aux hp.le hz.1.1 hh (hl.trans hz.2.1) hz.2.2 hbase
  change h ^ 2 * (1 - z.1 ^ 2) < q ^ 2 - z.1 ^ 2 * z.2 ^ 2 at hwall
  rw [hzv] at hwall
  rw [r_residual_map_im]
  change 0 < rResidualThree q h l z.1 z.2
  rw [hzv]
  exact r_residual_three_bottom_pos hl (hl1.trans hh) (hp.le.trans hz.1.1) hzu hwall

private lemma r_boundary_top_left_neg_aux {p t q h l : ℝ}
    (hcorner : rResidualThree q h l p 1 < 0)
    {s : unitInterval} (hs : (s : ℝ) = 3 / 8) :
    (rResidualMap p t q h l (fourArcRectangleBoundary p 1 l 1 s)).im < 0 := by
  have hzu := fourArcRectangleBoundary_fst_eq_left p 1 l 1
    (show 3 / 8 ≤ (s : ℝ) by rw [hs]) (show (s : ℝ) ≤ 5 / 8 by rw [hs]; norm_num)
  have hzv := fourArcRectangleBoundary_snd_eq_top p 1 l 1
    (show 1 / 8 ≤ (s : ℝ) by rw [hs]; norm_num) (show (s : ℝ) ≤ 3 / 8 by rw [hs])
  rw [r_residual_map_im, hzu, hzv]
  exact hcorner

private lemma r_boundary_bottom_right_neg_aux {p t q h l : ℝ}
    (hcorner : rResidualOne p t q 1 l < 0)
    {s : unitInterval} (hs : (s : ℝ) = 7 / 8) :
    (rResidualMap p t q h l (fourArcRectangleBoundary p 1 l 1 s)).re < 0 := by
  have hzu := fourArcRectangleBoundary_fst_eq_right p 1 l 1 <| Or.inr <|
    show 7 / 8 ≤ (s : ℝ) by rw [hs]
  have hzv := fourArcRectangleBoundary_snd_eq_bottom p 1 l 1
    (show 5 / 8 ≤ (s : ℝ) by rw [hs]; norm_num) (show (s : ℝ) ≤ 7 / 8 by rw [hs])
  rw [r_residual_map_re, hzu, hzv]
  exact hcorner

/-- The `R` residual on the counterclockwise boundary of
`[p,1] × [l,1]` is zero-free and has winding number one. -/
theorem exists_r_rectangle_boundary_winding_eq_one
    {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hpt : p < t) (htq : t < q)
    (hq : 1 < q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2)
    (htopLeft : rResidualThree q h l p 1 < 0)
    (hbottomRight : rResidualOne p t q 1 l < 0) :
    ∃ (gamma : C(unitInterval, ℂ)) (hgamma : ∀ s, gamma s ≠ 0),
      (∀ s, gamma s =
        rResidualMap p t q h l (fourArcRectangleBoundary p 1 l 1 s)) ∧
      Gluck.windingNumberC gamma hgamma = 1 := by
  have hden : ∀ z ∈ Icc p 1 ×ˢ Icc l 1,
      0 < q ^ 2 - z.1 ^ 2 * z.2 ^ 2 := by
    intro z hz
    exact r_denom_pos_aux hq (hp.le.trans hz.1.1) hz.1.2
      (hl.le.trans hz.2.1) hz.2.2
  have hcont := continuousOn_rResidualMap_of_denom_pos
    (p := p) (t := t) (h := h) (l := l) hden
  let gamma := fourArcRectangleBoundaryMap (rResidualMap p t q h l)
    hp1.le hl1.le hcont
  have hright : ∀ s : unitInterval,
      ((s : ℝ) ≤ 1 / 8 ∨ 7 / 8 < (s : ℝ)) → (gamma s).im < 0 :=
    fun _ hs ↦ r_boundary_right_neg_aux hp1.le hl.le hl1 hq hs
  have htop : ∀ s : unitInterval,
      1 / 8 ≤ (s : ℝ) → (s : ℝ) < 3 / 8 → (gamma s).re < 0 :=
    fun _ hs0 hs1 ↦ r_boundary_top_neg_aux hp.le hp1 hl1.le hq hs0 hs1
  have hleft : ∀ s : unitInterval,
      3 / 8 < (s : ℝ) → (s : ℝ) ≤ 5 / 8 → 0 < (gamma s).re :=
    fun _ hs0 hs1 ↦
      r_boundary_left_pos_aux hp hp1 hpt htq hq hl.le hl1 hs0 hs1
  have hbottom : ∀ s : unitInterval,
      5 / 8 ≤ (s : ℝ) → (s : ℝ) < 7 / 8 → 0 < (gamma s).im :=
    fun _ hs0 hs1 ↦ r_boundary_bottom_pos_aux hp hp1 hh hl.le hl1 hbase hs0 hs1
  have htopLeft' : ∀ s : unitInterval,
      (s : ℝ) = 3 / 8 → (gamma s).im < 0 :=
    fun _ hs ↦ r_boundary_top_left_neg_aux htopLeft hs
  have hbottomRight' : ∀ s : unitInterval,
      (s : ℝ) = 7 / 8 → (gamma s).re < 0 :=
    fun _ hs ↦ r_boundary_bottom_right_neg_aux hbottomRight hs
  have hgamma := ne_zero_of_crossed_fourArcs gamma hright htop hleft hbottom
    htopLeft' hbottomRight'
  have hloop : gamma 0 = gamma 1 :=
    fourArcRectangleBoundaryMap_zero_eq_one _ hp1.le hl1.le hcont
  have hwind := windingNumberC_eq_one_of_crossed_fourArcs gamma hgamma hloop
    hright htop hleft hbottom htopLeft' hbottomRight'
  exact ⟨gamma, hgamma, fun _ ↦ rfl, hwind⟩

/-- Every zero of the `R` residual in the closed physical rectangle is
strictly interior when the four boundary signs hold. -/
theorem r_residual_zero_mem_interior
    {p t q h l : ℝ} {z : ℝ × ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hpt : p < t) (htq : t < q)
    (hq : 1 < q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2)
    (htopLeft : rResidualThree q h l p 1 < 0)
    (hbottomRight : rResidualOne p t q 1 l < 0)
    (hz : z ∈ Icc p 1 ×ˢ Icc l 1)
    (hzero : rResidualMap p t q h l z = 0) :
    z ∈ Ioo p 1 ×ˢ Ioo l 1 := by
  have hOne : rResidualOne p t q z.1 z.2 = 0 := by
    have hre := congrArg Complex.re hzero
    simpa using hre
  have hThree : rResidualThree q h l z.1 z.2 = 0 := by
    have him := congrArg Complex.im hzero
    simpa using him
  have hpu : p < z.1 := by
    by_contra hnot
    have huEq : z.1 = p := le_antisymm (not_lt.mp hnot) hz.1.1
    by_cases hvEq : z.2 = 1
    · have hneg : rResidualThree q h l z.1 z.2 < 0 := by
        simpa [huEq, hvEq] using htopLeft
      linarith
    · have hv1 : z.2 < 1 := lt_of_le_of_ne hz.2.2 hvEq
      have hwall := r_t_wall_pos_aux (hp.trans hpt) htq hq hp.le hp1.le
        (hl.le.trans hz.2.1) hz.2.2
      have hpos : 0 < rResidualOne p t q z.1 z.2 := by
        simpa [huEq] using
          r_residual_one_left_pos hp hpt (hl.le.trans hz.2.1) hv1 hwall
      linarith
  have hu1 : z.1 < 1 := by
    by_contra hnot
    have huEq : z.1 = 1 := le_antisymm hz.1.2 (not_lt.mp hnot)
    by_cases hvEq : z.2 = l
    · have hneg : rResidualOne p t q z.1 z.2 < 0 := by
        simpa [huEq, hvEq] using hbottomRight
      linarith
    · have hlv : l < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm hvEq)
      have hneg : rResidualThree q h l z.1 z.2 < 0 := by
        simpa [huEq] using
          r_residual_three_right_neg hl.le hlv hz.2.2 hq
      linarith
  have hlv : l < z.2 := by
    by_contra hnot
    have hvEq : z.2 = l := le_antisymm (not_lt.mp hnot) hz.2.1
    have hwall := r_h_wall_pos_aux hp.le hz.1.1 hh hl.le hl1.le hbase
    have hpos : 0 < rResidualThree q h l z.1 z.2 := by
      simpa [hvEq] using r_residual_three_bottom_pos hl.le
        (hl1.trans hh) (hp.le.trans hz.1.1) hu1 hwall
    linarith
  have hv1 : z.2 < 1 := by
    by_contra hnot
    have hvEq : z.2 = 1 := le_antisymm hz.2.2 (not_lt.mp hnot)
    have hneg : rResidualOne p t q z.1 z.2 < 0 := by
      simpa [hvEq] using r_residual_one_top_neg hp.le hpu hz.1.2 hq
    linarith
  exact ⟨⟨hpu, hu1⟩, ⟨hlv, hv1⟩⟩

/-- Failure of the scalar `X` test, together with a negative complementary
corner discriminator, forces the `R`-boundary winding certificate. -/
theorem exists_r_rectangle_boundary_winding_eq_one_of_failure
    {p t q h l r a s rho : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hs : 0 < s) (hsp : s < p)
    (hpt : p < t) (htq : t < q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1)
    (hseq : s ^ 2 * (1 + a ^ 2) = 1)
    (hqcrit : p + r * a ≤ q) (hrho : 0 < rho)
    (hrhoSq : rho ^ 2 * (q ^ 2 - p ^ 2) = r ^ 2)
    (hrhoEq : rho = √(1 - p ^ 2) / √(q ^ 2 - p ^ 2))
    (hbottomRight : rResidualOne p t q 1 l < 0) :
    ∃ (gamma : C(unitInterval, ℂ)) (hgamma : ∀ u, gamma u ≠ 0),
      (∀ u, gamma u =
        rResidualMap p t q h l (fourArcRectangleBoundary p 1 l 1 u)) ∧
      Gluck.windingNumberC gamma hgamma = 1 := by
  have hp1 : p < 1 := by nlinarith [sq_pos_of_pos hr]
  have hcritical := one_lt_criticalValue hp hr ha hs hsp hrsq hseq
  have hq : 1 < q := hcritical.trans_le hqcrit
  have hcriticalSq : (p + r * a) ^ 2 ≤ q ^ 2 :=
    (sq_le_sq₀ (lt_trans zero_lt_one hcritical).le
      (lt_trans zero_lt_one hq).le).2 hqcrit
  have hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2 := by
    rw [← hrsq]
    exact (critical_hWall_pos hp hr ha hs hsp hh hl hl1 hrsq haeq hseq).trans_le
      hcriticalSq
  have htopLeft : rResidualThree q h l p 1 < 0 := by
    rw [r_residual_three_top_left_eq hp.le (hp1.trans hq), ← hrhoEq]
    exact r_corner_residual_neg_of_failure hp hr ha hs hsp hh hl hl1 hrsq
      haeq hseq hqcrit hrho hrhoSq
  exact exists_r_rectangle_boundary_winding_eq_one hp hp1 hpt htq hq hh hl hl1
    hbase htopLeft hbottomRight

private lemma exists_r_residual_zero_of_winding_aux
    {p t q h l : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (hq : 1 < q)
    (hl : 0 ≤ l) (hl1 : l < 1)
    (hcert : ∃ (gamma : C(unitInterval, ℂ)) (hgamma : ∀ u, gamma u ≠ 0),
      (∀ u, gamma u =
        rResidualMap p t q h l (fourArcRectangleBoundary p 1 l 1 u)) ∧
      Gluck.windingNumberC gamma hgamma = 1) :
    ∃ z ∈ Ioo p 1 ×ˢ Ioo l 1, rResidualMap p t q h l z = 0 := by
  have hden : ∀ z ∈ Icc p 1 ×ˢ Icc l 1,
      0 < q ^ 2 - z.1 ^ 2 * z.2 ^ 2 := by
    intro z hz
    exact r_denom_pos_aux hq (hp.trans hz.1.1) hz.1.2
      (hl.trans hz.2.1) hz.2.2
  have hcont := continuousOn_rResidualMap_of_denom_pos
    (p := p) (t := t) (h := h) (l := l) hden
  obtain ⟨gamma, hgamma, hgammaEq, hwind⟩ := hcert
  exact exists_zero_of_fourArcRectangleBoundary_winding hp1 hl1 hcont
    gamma hgamma hgammaEq (by rw [hwind]; norm_num)

/-- The Type-A `R` hypotheses force a simultaneous residual zero strictly
inside the physical rectangle. -/
theorem exists_r_residual_zero
    {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hpt : p < t) (htq : t < q)
    (hq : 1 < q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2)
    (htopLeft : rResidualThree q h l p 1 < 0)
    (hbottomRight : rResidualOne p t q 1 l < 0) :
    ∃ z ∈ Ioo p 1 ×ˢ Ioo l 1, rResidualMap p t q h l z = 0 :=
  exists_r_residual_zero_of_winding_aux hp.le hp1 hq hl.le hl1 <|
    exists_r_rectangle_boundary_winding_eq_one hp hp1 hpt htq hq hh hl hl1
      hbase htopLeft hbottomRight

/-- Scalar-`X` failure and `B<0` force a simultaneous `R` residual zero
strictly inside the physical rectangle. -/
theorem exists_r_residual_zero_of_failure
    {p t q h l r a s rho : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hs : 0 < s) (hsp : s < p)
    (hpt : p < t) (htq : t < q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1)
    (hseq : s ^ 2 * (1 + a ^ 2) = 1)
    (hqcrit : p + r * a ≤ q) (hrho : 0 < rho)
    (hrhoSq : rho ^ 2 * (q ^ 2 - p ^ 2) = r ^ 2)
    (hrhoEq : rho = √(1 - p ^ 2) / √(q ^ 2 - p ^ 2))
    (hbottomRight : rResidualOne p t q 1 l < 0) :
    ∃ z ∈ Ioo p 1 ×ˢ Ioo l 1, rResidualMap p t q h l z = 0 := by
  have hp1 : p < 1 := by nlinarith [sq_pos_of_pos hr]
  have hq : 1 < q :=
    (one_lt_criticalValue hp hr ha hs hsp hrsq hseq).trans_le hqcrit
  exact exists_r_residual_zero_of_winding_aux hp.le hp1 hq hl.le hl1 <|
    exists_r_rectangle_boundary_winding_eq_one_of_failure hp hr ha hs hsp hpt
      htq hh hl hl1 hrsq haeq hseq hqcrit hrho hrhoSq hrhoEq hbottomRight

private lemma exists_pos_forall_lt_r_residual_perturbation_zero_aux
    {p t q h l ε₀ : ℝ} (hp1 : p < 1) (hl1 : l < 1) (hε₀ : 0 < ε₀)
    {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (hΦ : ContinuousOn Φ
      (Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1)))
    (hinitial : ∀ z ∈ Icc p 1 ×ˢ Icc l 1,
      Φ (0, z) = rResidualMap p t q h l z)
    (hcert : ∃ (gamma : C(unitInterval, ℂ)) (hgamma : ∀ u, gamma u ≠ 0),
      (∀ u, gamma u =
        rResidualMap p t q h l (fourArcRectangleBoundary p 1 l 1 u)) ∧
      Gluck.windingNumberC gamma hgamma = 1) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Ioo 0 ε₁,
      ∃ z ∈ Ioo p 1 ×ˢ Ioo l 1, Φ (ε, z) = 0 := by
  obtain ⟨gamma, hgamma, hgammaEq, hwind⟩ := hcert
  apply exists_pos_forall_lt_exists_zero_of_fourArcRectangleBoundary_winding
    hp1 hl1 hε₀ hΦ gamma hgamma
  · intro u
    exact (hgammaEq u).trans <|
      (hinitial _ (fourArcRectangleBoundary_mem hp1.le hl1.le u)).symm
  · rw [hwind]
    norm_num

/-- Every jointly continuous planar perturbation of the Type-A `R` residual
has an interior zero on all sufficiently small positive slices. -/
theorem exists_pos_forall_lt_r_residual_perturbation_zero
    {p t q h l ε₀ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hpt : p < t) (htq : t < q)
    (hq : 1 < q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2)
    (htopLeft : rResidualThree q h l p 1 < 0)
    (hbottomRight : rResidualOne p t q 1 l < 0)
    (hε₀ : 0 < ε₀) {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (hΦ : ContinuousOn Φ (Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1)))
    (hinitial : ∀ z ∈ Icc p 1 ×ˢ Icc l 1,
      Φ (0, z) = rResidualMap p t q h l z) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Ioo 0 ε₁,
      ∃ z ∈ Ioo p 1 ×ˢ Ioo l 1, Φ (ε, z) = 0 :=
  exists_pos_forall_lt_r_residual_perturbation_zero_aux hp1 hl1 hε₀ hΦ hinitial <|
    exists_r_rectangle_boundary_winding_eq_one hp hp1 hpt htq hq hh hl hl1
      hbase htopLeft hbottomRight

/-- After scalar-`X` failure and `B<0`, every jointly continuous planar
perturbation of the `R` residual has small positive-slice interior zeros. -/
theorem exists_pos_forall_lt_r_residual_perturbation_zero_of_failure
    {p t q h l r a s rho ε₀ : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hs : 0 < s) (hsp : s < p)
    (hpt : p < t) (htq : t < q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1)
    (hseq : s ^ 2 * (1 + a ^ 2) = 1)
    (hqcrit : p + r * a ≤ q) (hrho : 0 < rho)
    (hrhoSq : rho ^ 2 * (q ^ 2 - p ^ 2) = r ^ 2)
    (hrhoEq : rho = √(1 - p ^ 2) / √(q ^ 2 - p ^ 2))
    (hbottomRight : rResidualOne p t q 1 l < 0)
    (hε₀ : 0 < ε₀) {Φ : ℝ × (ℝ × ℝ) → ℂ}
    (hΦ : ContinuousOn Φ (Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1)))
    (hinitial : ∀ z ∈ Icc p 1 ×ˢ Icc l 1,
      Φ (0, z) = rResidualMap p t q h l z) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Ioo 0 ε₁,
      ∃ z ∈ Ioo p 1 ×ˢ Ioo l 1, Φ (ε, z) = 0 := by
  have hp1 : p < 1 := by nlinarith [sq_pos_of_pos hr]
  exact exists_pos_forall_lt_r_residual_perturbation_zero_aux hp1 hl1 hε₀ hΦ
    hinitial <| exists_r_rectangle_boundary_winding_eq_one_of_failure hp hr ha hs
      hsp hpt htq hh hl hl1 hrsq haeq hseq hqcrit hrho hrhoSq hrhoEq
        hbottomRight

/-- The Type-A `R` winding survives after a continuous literal target is
expressed in any continuous transverse complex basis.  At the compactified
slice the target need only be the real linear combination of the two proved
`R` residuals with that basis.  Thus a zero of the transformed perturbation
is a zero of the original target, without a separate variable-`GL(2)` degree
theorem. -/
theorem exists_pos_forall_lt_r_complex_family_zero_of_failure
    {p t q h l r a s rho ε₀ : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hs : 0 < s) (hsp : s < p)
    (hpt : p < t) (htq : t < q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1)
    (hseq : s ^ 2 * (1 + a ^ 2) = 1)
    (hqcrit : p + r * a ≤ q) (hrho : 0 < rho)
    (hrhoSq : rho ^ 2 * (q ^ 2 - p ^ 2) = r ^ 2)
    (hrhoEq : rho = √(1 - p ^ 2) / √(q ^ 2 - p ^ 2))
    (hbottomRight : rResidualOne p t q 1 l < 0)
    (hε₀ : 0 < ε₀) {E A B : ℝ × (ℝ × ℝ) → ℂ}
    (hE : ContinuousOn E (Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1)))
    (hA : ContinuousOn A (Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1)))
    (hB : ContinuousOn B (Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1)))
    (hdet : ∀ x ∈ Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1),
      (A x).re * (B x).im - (A x).im * (B x).re ≠ 0)
    (hinitial : ∀ z ∈ Icc p 1 ×ˢ Icc l 1,
      E (0, z) = (rResidualOne p t q z.1 z.2 : ℂ) * A (0, z) +
        (rResidualThree q h l z.1 z.2 : ℂ) * B (0, z)) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Ioo 0 ε₁,
      ∃ z ∈ Ioo p 1 ×ˢ Ioo l 1, E (ε, z) = 0 := by
  let Φ : ℝ × (ℝ × ℝ) → ℂ := fun x ↦
    complexBasisCoordinates (A x) (B x) (E x)
  have hΦ : ContinuousOn Φ (Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1)) :=
    continuousOn_complexBasisCoordinates hA hB hE hdet
  have hinitialΦ : ∀ z ∈ Icc p 1 ×ˢ Icc l 1,
      Φ (0, z) = rResidualMap p t q h l z := by
    intro z hz
    dsimp only [Φ]
    rw [hinitial z hz]
    rw [complex_basis_coordinates_linear_combination
      (hdet (0, z) ⟨⟨le_rfl, hε₀.le⟩, hz⟩)]
    rfl
  obtain ⟨ε₁, hε₁, hε₁ε₀, hzero⟩ :=
    exists_pos_forall_lt_r_residual_perturbation_zero_of_failure hp hr ha hs
      hsp hpt htq hh hl hl1 hrsq haeq hseq hqcrit hrho hrhoSq hrhoEq
        hbottomRight hε₀ hΦ hinitialΦ
  refine ⟨ε₁, hε₁, hε₁ε₀, fun ε hε ↦ ?_⟩
  obtain ⟨z, hz, hzΦ⟩ := hzero ε hε
  have hεClosed : ε ∈ Icc 0 ε₀ :=
    ⟨hε.1.le, hε.2.trans_le hε₁ε₀ |>.le⟩
  have hzClosed : z ∈ Icc p 1 ×ˢ Icc l 1 :=
    ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  refine ⟨z, hz, ?_⟩
  exact (complex_basis_coordinates_eq_zero_iff
    (hdet (ε, z) ⟨hεClosed, hzClosed⟩)).mp hzΦ

/-- A strictly monotone released singleton coordinate turns the full
three-coordinate Type-A `R` problem back into the proved planar winding.
The scalar coordinate is solved continuously on every `(ε,z)` slice; at
`ε=0` its unique root is the unreleased value `kMid`, where the other two
coordinates are exactly `rResidualMap`.  Thus no three-dimensional degree
theory is needed for this suspension step. -/
theorem exists_pos_forall_lt_r_released_target_zero_of_failure
    {p t q h l r a s rho ε₀ kLo kMid kHi : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hs : 0 < s) (hsp : s < p)
    (hpt : p < t) (htq : t < q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1)
    (hseq : s ^ 2 * (1 + a ^ 2) = 1)
    (hqcrit : p + r * a ≤ q) (hrho : 0 < rho)
    (hrhoSq : rho ^ 2 * (q ^ 2 - p ^ 2) = r ^ 2)
    (hrhoEq : rho = √(1 - p ^ 2) / √(q ^ 2 - p ^ 2))
    (hbottomRight : rResidualOne p t q 1 l < 0)
    (hε₀ : 0 < ε₀) (hkLo : kLo < kMid) (hkHi : kMid < kHi)
    {Ψ : (ℝ × (ℝ × ℝ)) × ℝ → ℝ × ℂ}
    (hΨ : ContinuousOn Ψ
      ((Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1)) ×ˢ Icc kLo kHi))
    (hmono : ∀ x ∈ Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1),
      StrictMonoOn (fun k ↦ (Ψ (x, k)).1) (Icc kLo kHi))
    (hneg : ∀ x ∈ Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1),
      (Ψ (x, kLo)).1 < 0)
    (hpos : ∀ x ∈ Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1),
      0 < (Ψ (x, kHi)).1)
    (hinitial : ∀ z ∈ Icc p 1 ×ˢ Icc l 1,
      Ψ ((0, z), kMid) = (0, rResidualMap p t q h l z)) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Ioo 0 ε₁,
      ∃ z ∈ Ioo p 1 ×ˢ Ioo l 1, ∃ k ∈ Ioo kLo kHi,
        Ψ ((ε, z), k) = 0 := by
  let S : Set (ℝ × (ℝ × ℝ)) := Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1)
  let F : (ℝ × (ℝ × ℝ)) → ℝ → ℝ := fun x k ↦ (Ψ (x, k)).1
  have hF : ContinuousOn (fun q ↦ (Ψ q).1) (S ×ˢ Icc kLo kHi) :=
    continuous_fst.comp_continuousOn hΨ
  have hFy : ∀ x ∈ S, ContinuousOn (F x) (Icc kLo kHi) := by
    intro x hx
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun k hk ↦ ⟨hx, hk⟩)
  have hFc : ∀ x ∈ S, ∀ k ∈ Ioo kLo kHi,
      ContinuousWithinAt (fun y ↦ F y k) S x := by
    intro x hx k hk
    have hslice : ContinuousOn (fun y ↦ F y k) S :=
      hF.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy ↦ ⟨hy, ⟨hk.1.le, hk.2.le⟩⟩)
    exact hslice x hx
  obtain ⟨K, hKcont, hK⟩ := continuous_root_of_strictMono
    (F := F) (S := S) (l := fun _ ↦ kLo) (u := fun _ ↦ kHi)
    continuousOn_const continuousOn_const (fun _ _ ↦ hkLo.le.trans hkHi.le)
    hmono hFy hFc hneg hpos
  have hkMidMem : kMid ∈ Icc kLo kHi := ⟨hkLo.le, hkHi.le⟩
  have hKzero : ∀ z ∈ Icc p 1 ×ˢ Icc l 1, K (0, z) = kMid := by
    intro z hz
    have hx : (0, z) ∈ S := ⟨⟨le_rfl, hε₀.le⟩, hz⟩
    have hrootMid : F (0, z) kMid = 0 := by
      simpa [F] using congrArg Prod.fst (hinitial z hz)
    exact (hmono (0, z) hx).injOn (Set.Ioo_subset_Icc_self (hK (0, z) hx).1)
      hkMidMem ((hK (0, z) hx).2.trans hrootMid.symm)
  let Φ : ℝ × (ℝ × ℝ) → ℂ := fun x ↦ (Ψ (x, K x)).2
  have hgraph : ContinuousOn (fun x ↦ (x, K x)) S :=
    continuousOn_id.prodMk hKcont
  have hgraphMaps : MapsTo (fun x ↦ (x, K x)) S (S ×ˢ Icc kLo kHi) := by
    intro x hx
    exact ⟨hx, Set.Ioo_subset_Icc_self (hK x hx).1⟩
  have hΦ : ContinuousOn Φ S :=
    continuous_snd.comp_continuousOn (hΨ.comp hgraph hgraphMaps)
  have hinitialΦ : ∀ z ∈ Icc p 1 ×ˢ Icc l 1,
      Φ (0, z) = rResidualMap p t q h l z := by
    intro z hz
    rw [show Φ (0, z) = (Ψ ((0, z), K (0, z))).2 from rfl, hKzero z hz]
    exact congrArg Prod.snd (hinitial z hz)
  obtain ⟨ε₁, hε₁, hε₁ε₀, hzero⟩ :=
    exists_pos_forall_lt_r_residual_perturbation_zero_of_failure hp hr ha hs
      hsp hpt htq hh hl hl1 hrsq haeq hseq hqcrit hrho hrhoSq hrhoEq
        hbottomRight hε₀ hΦ hinitialΦ
  refine ⟨ε₁, hε₁, hε₁ε₀, fun ε hε ↦ ?_⟩
  obtain ⟨z, hz, hzΦ⟩ := hzero ε hε
  have hεClosed : ε ∈ Icc 0 ε₀ :=
    ⟨hε.1.le, (hε.2.trans_le hε₁ε₀).le⟩
  have hzClosed : z ∈ Icc p 1 ×ˢ Icc l 1 :=
    ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hx : (ε, z) ∈ S := ⟨hεClosed, hzClosed⟩
  refine ⟨z, hz, K (ε, z), (hK (ε, z) hx).1, ?_⟩
  exact Prod.ext (hK (ε, z) hx).2 hzΦ

/-- The monotone released-sheet theorem can force its roots into an
arbitrarily small residual sublevel of the initial planar map. -/
theorem exists_pos_forall_lt_r_released_target_zero_localized_of_failure
    {p t q h l r a s rho ε₀ kLo kMid kHi μ : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha : 0 < a) (hs : 0 < s) (hsp : s < p)
    (hpt : p < t) (htq : t < q) (hh : 1 < h) (hl : 0 < l) (hl1 : l < 1)
    (hrsq : r ^ 2 = 1 - p ^ 2)
    (haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1)
    (hseq : s ^ 2 * (1 + a ^ 2) = 1)
    (hqcrit : p + r * a ≤ q) (hrho : 0 < rho)
    (hrhoSq : rho ^ 2 * (q ^ 2 - p ^ 2) = r ^ 2)
    (hrhoEq : rho = √(1 - p ^ 2) / √(q ^ 2 - p ^ 2))
    (hbottomRight : rResidualOne p t q 1 l < 0)
    (hε₀ : 0 < ε₀) (hkLo : kLo < kMid) (hkHi : kMid < kHi)
    (hμ : 0 < μ)
    {Ψ : (ℝ × (ℝ × ℝ)) × ℝ → ℝ × ℂ}
    (hΨ : ContinuousOn Ψ
      ((Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1)) ×ˢ Icc kLo kHi))
    (hmono : ∀ x ∈ Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1),
      StrictMonoOn (fun k ↦ (Ψ (x, k)).1) (Icc kLo kHi))
    (hneg : ∀ x ∈ Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1),
      (Ψ (x, kLo)).1 < 0)
    (hpos : ∀ x ∈ Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1),
      0 < (Ψ (x, kHi)).1)
    (hinitial : ∀ z ∈ Icc p 1 ×ˢ Icc l 1,
      Ψ ((0, z), kMid) = (0, rResidualMap p t q h l z)) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Ioo 0 ε₁,
      ∃ z ∈ Ioo p 1 ×ˢ Ioo l 1, ∃ k ∈ Ioo kLo kHi,
        Ψ ((ε, z), k) = 0 ∧ ‖rResidualMap p t q h l z‖ < μ := by
  obtain ⟨εE, hεE, hεEε₀, hroot⟩ :=
    exists_pos_forall_lt_r_released_target_zero_of_failure hp hr ha hs hsp
      hpt htq hh hl hl1 hrsq haeq hseq hqcrit hrho hrhoSq hrhoEq
        hbottomRight hε₀ hkLo hkHi hΨ hmono hneg hpos hinitial
  let Q : Set (ℝ × ℝ) := Icc p 1 ×ˢ Icc l 1
  let K : Set ((ℝ × ℝ) × ℝ) := Q ×ˢ Icc kLo kHi
  have hKcomp : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hkMidMem : kMid ∈ Icc kLo kHi := ⟨hkLo.le, hkHi.le⟩
  let measure : ((ℝ × ℝ) × ℝ) → ℝ := fun x ↦
    ‖(Ψ ((0, x.1), kMid)).2‖
  have hslice : ContinuousOn (fun x : (ℝ × ℝ) × ℝ ↦
      Ψ ((0, x.1), kMid)) K := by
    apply hΨ.comp
      ((continuous_const.prodMk continuous_fst).prodMk
        continuous_const).continuousOn
    intro x hx
    exact ⟨⟨⟨le_rfl, hε₀.le⟩, hx.1⟩, hkMidMem⟩
  have hmeasure : ContinuousOn measure K := by
    exact continuous_norm.comp_continuousOn
      (continuous_snd.comp_continuousOn hslice)
  let Φ : ℝ × ((ℝ × ℝ) × ℝ) → ℝ × ℂ := fun x ↦
    Ψ ((x.1, x.2.1), x.2.2)
  have hΦ : ContinuousOn Φ (Icc 0 ε₀ ×ˢ K) := by
    apply hΨ.comp
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd)).continuousOn
    intro x hx
    exact ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩
  have hinitialGood : ∀ x ∈ K, Φ (0, x) = 0 → measure x < μ := by
    intro x hx hzero
    have hxBase :
        (0, x.1) ∈ Icc 0 ε₀ ×ˢ (Icc p 1 ×ˢ Icc l 1) :=
      ⟨⟨le_rfl, hε₀.le⟩, hx.1⟩
    have hfirstK : (Ψ ((0, x.1), x.2)).1 = 0 := by
      have hfirst := congrArg Prod.fst hzero
      change (Ψ ((0, x.1), x.2)).1 = (0 : ℝ) at hfirst
      exact hfirst
    have hfirstMid : (Ψ ((0, x.1), kMid)).1 = 0 := by
      rw [hinitial x.1 hx.1]
    have hkEq : x.2 = kMid :=
      (hmono (0, x.1) hxBase).injOn hx.2 hkMidMem
        (hfirstK.trans hfirstMid.symm)
    have hzero' : Ψ ((0, x.1), kMid) = 0 := by
      simpa only [Φ, hkEq] using hzero
    have hsnd : (Ψ ((0, x.1), kMid)).2 = 0 :=
      congrArg Prod.snd hzero'
    simp only [measure, hsnd, norm_zero]
    exact hμ
  obtain ⟨εL, hεL, hεLε₀, hlocal⟩ :=
    exists_pos_forall_lt_zero_localized_near_initial hKcomp hε₀
      hmeasure hΦ hinitialGood
  refine ⟨min εE εL, lt_min hεE hεL,
    (min_le_left _ _).trans hεEε₀, fun ε hε ↦ ?_⟩
  have hεE' : ε ∈ Ioo 0 εE :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  obtain ⟨z, hz, k, hk, hzero⟩ := hroot ε hεE'
  have hzClosed : z ∈ Q :=
    ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hkClosed : k ∈ Icc kLo kHi := ⟨hk.1.le, hk.2.le⟩
  have hεL' : ε ∈ Ico 0 εL :=
    ⟨hε.1.le, hε.2.trans_le (min_le_right _ _)⟩
  have hnear := hlocal ε hεL' (z, k) ⟨hzClosed, hkClosed⟩ hzero
  refine ⟨z, hz, k, hk, hzero, ?_⟩
  simpa only [measure, hinitial z hzClosed] using hnear

end Gluck.Discrete.N6TypeAThreeCell
