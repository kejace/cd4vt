/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4EndpointSpliceRegularity
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Curvature at a circle–interior endpoint splice

The signed Menger curvature at a circle–interior splice eventually exceeds
the circle curvature as the circle chord collapses.
-/

namespace Gluck.Forward

open Gluck.Discrete
open Metric Filter
open scoped Topology

private theorem dist_circlePoint_sq_lt_neg_two_mul_radial_of_interior_aux
    {O P : ℂ} {R θ : ℝ} (hR : 0 < R) (hP : dist O P < R) :
    dist (circlePoint O R θ) P ^ 2 <
      -2 * R * inner ℝ (circleRadial θ) (P - circlePoint O R θ) := by
  have hsq : dist O P ^ 2 < R ^ 2 :=
    sq_lt_sq' (by linarith [dist_nonneg (x := O) (y := P)]) hP
  have hpower := dist_center_sq_eq_dist_circlePoint_sq_add O P R θ
  linarith

/-- The chord from angle `θ - δ` to `θ` has its usual half-angle
length. -/
theorem dist_circlePoint_sub_eq_two_mul_sin_half
    {O : ℂ} {R θ δ : ℝ} (hR : 0 < R)
    (hδ0 : 0 < δ) (hδ2π : δ < 2 * Real.pi) :
    dist (circlePoint O R (θ - δ)) (circlePoint O R θ) =
      2 * R * Real.sin (δ / 2) := by
  have hsin : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [dist_circlePoint_eq_two_mul_abs_sin_half, show θ - (θ - δ) = δ by ring,
    abs_of_pos hR, abs_of_pos hsin]

/-- Symmetric half-angle formula for the forward circle chord. -/
theorem dist_circlePoint_add_eq_two_mul_sin_half
    {O : ℂ} {R θ δ : ℝ} (hR : 0 < R)
    (hδ0 : 0 < δ) (hδ2π : δ < 2 * Real.pi) :
    dist (circlePoint O R θ) (circlePoint O R (θ + δ)) =
      2 * R * Real.sin (δ / 2) := by
  have hsin : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [dist_circlePoint_eq_two_mul_abs_sin_half, show θ + δ - θ = δ by ring,
    abs_of_pos hR, abs_of_pos hsin]

private noncomputable def endpointPredecessorCurvatureModel
    (O P : ℂ) (R θ δ : ℝ) : ℝ :=
  2 * (Real.sin (δ / 2) *
        inner ℝ (circleTangent θ) (P - circlePoint O R θ) -
      Real.cos (δ / 2) *
        inner ℝ (circleRadial θ) (P - circlePoint O R θ)) /
    (dist (circlePoint O R θ) P *
      dist (circlePoint O R (θ - δ)) P)

private noncomputable def endpointSuccessorCurvatureModel
    (O P : ℂ) (R θ δ : ℝ) : ℝ :=
  2 * (-Real.sin (δ / 2) *
        inner ℝ (circleTangent θ) (P - circlePoint O R θ) -
      Real.cos (δ / 2) *
        inner ℝ (circleRadial θ) (P - circlePoint O R θ)) /
    (dist (circlePoint O R θ) P *
      dist (circlePoint O R (θ + δ)) P)

@[simp] private theorem endpointPredecessorCurvatureModel_zero_aux
    (O P : ℂ) (R θ : ℝ) :
    endpointPredecessorCurvatureModel O P R θ 0 =
      (-2 * inner ℝ (circleRadial θ) (P - circlePoint O R θ)) /
        dist (circlePoint O R θ) P ^ 2 := by
  simp only [endpointPredecessorCurvatureModel, Real.sin_zero, zero_mul, Real.cos_zero, one_mul,
    zero_sub, pow_two, div_eq_mul_inv]
  ring_nf

@[simp] private theorem endpointSuccessorCurvatureModel_zero_aux
    (O P : ℂ) (R θ : ℝ) :
    endpointSuccessorCurvatureModel O P R θ 0 =
      (-2 * inner ℝ (circleRadial θ) (P - circlePoint O R θ)) /
        dist (circlePoint O R θ) P ^ 2 := by
  simp only [endpointSuccessorCurvatureModel, Real.sin_zero, neg_zero, zero_mul, Real.cos_zero,
    one_mul, zero_sub, pow_two, div_eq_mul_inv]
  ring_nf

private theorem continuousAt_endpointPredecessorCurvatureModel_aux
    {O P : ℂ} {R θ : ℝ} (hP : dist O P < R) :
    ContinuousAt (fun δ : ℝ ↦
      endpointPredecessorCurvatureModel O P R θ δ) 0 := by
  have hself : dist (circlePoint O R θ) P ≠ 0 := by
    rw [dist_ne_zero]
    intro heq
    have hboundary : dist O P = |R| := by
      rw [← heq, dist_circlePoint_center]
    rw [hboundary] at hP
    exact (not_lt_of_ge (le_abs_self R)) hP
  unfold endpointPredecessorCurvatureModel
  apply ContinuousAt.div
  · fun_prop
  · have hcircle : ContinuousAt
        (fun δ : ℝ ↦ circlePoint O R (θ - δ)) 0 := by
      exact (continuous_circleMap O R).continuousAt.comp (by fun_prop)
    exact continuousAt_const.mul (hcircle.dist continuousAt_const)
  · simpa using mul_ne_zero hself hself

private theorem continuousAt_endpointSuccessorCurvatureModel_aux
    {O P : ℂ} {R θ : ℝ} (hP : dist O P < R) :
    ContinuousAt (fun δ : ℝ ↦
      endpointSuccessorCurvatureModel O P R θ δ) 0 := by
  have hself : dist (circlePoint O R θ) P ≠ 0 := by
    rw [dist_ne_zero]
    intro heq
    have hboundary : dist O P = |R| := by
      rw [← heq, dist_circlePoint_center]
    rw [hboundary] at hP
    exact (not_lt_of_ge (le_abs_self R)) hP
  unfold endpointSuccessorCurvatureModel
  apply ContinuousAt.div
  · fun_prop
  · have hcircle : ContinuousAt
        (fun δ : ℝ ↦ circlePoint O R (θ + δ)) 0 := by
      exact (continuous_circleMap O R).continuousAt.comp (by fun_prop)
    exact continuousAt_const.mul (hcircle.dist continuousAt_const)
  · simpa using mul_ne_zero hself hself

private theorem inv_radius_lt_endpointCurvatureModel_zero_aux
    {O P : ℂ} {R θ : ℝ} (hR : 0 < R) (hP : dist O P < R) :
    1 / R < endpointPredecessorCurvatureModel O P R θ 0 ∧
      1 / R < endpointSuccessorCurvatureModel O P R θ 0 := by
  have hd : 0 < dist (circlePoint O R θ) P := by
    rw [dist_pos]
    intro heq
    have : dist O P = R := by
      rw [← heq, dist_circlePoint_center, abs_of_pos hR]
    linarith
  have hmargin :=
    dist_circlePoint_sq_lt_neg_two_mul_radial_of_interior_aux
      (θ := θ) hR hP
  have hlt : 1 / R <
      (-2 * inner ℝ (circleRadial θ) (P - circlePoint O R θ)) /
        dist (circlePoint O R θ) P ^ 2 := by
    rw [div_lt_div_iff₀ hR (sq_pos_of_pos hd)]
    nlinarith
  simpa using And.intro hlt hlt

private theorem signedMengerR2_circlePoint_predecessor_eq_model_aux
    {O P : ℂ} {R θ δ : ℝ} (hR : 0 < R)
    (hP : dist O P < R) (hδ0 : 0 < δ) (hδ2π : δ < 2 * Real.pi) :
    signedMengerR2 (circlePoint O R (θ - δ)) (circlePoint O R θ) P =
      endpointPredecessorCurvatureModel O P R θ δ := by
  have hhalfPos : 0 < Real.sin (δ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have hsinδ : Real.sin δ =
      2 * Real.sin (δ / 2) * Real.cos (δ / 2) := by
    convert Real.sin_two_mul (δ / 2) using 1
    all_goals ring_nf
  have hcosδ : 1 - Real.cos δ = 2 * Real.sin (δ / 2) ^ 2 := by
    have hcosTwo := Real.cos_two_mul (δ / 2)
    have hunit := Real.sin_sq_add_cos_sq (δ / 2)
    rw [show 2 * (δ / 2) = δ by ring] at hcosTwo
    nlinarith
  have hself : dist (circlePoint O R θ) P ≠ 0 := by
    rw [dist_ne_zero]
    intro heq
    have : dist O P = R := by
      rw [← heq, dist_circlePoint_center, abs_of_pos hR]
    linarith
  have hprev : dist (circlePoint O R (θ - δ)) P ≠ 0 := by
    rw [dist_ne_zero]
    intro heq
    have : dist O P = R := by
      rw [← heq, dist_circlePoint_center, abs_of_pos hR]
    linarith
  unfold signedMengerR2 endpointPredecessorCurvatureModel
  rw [endpointPredecessor_cross_eq,
    dist_circlePoint_sub_eq_two_mul_sin_half hR hδ0 hδ2π,
    dist_comm P (circlePoint O R (θ - δ)), hsinδ, hcosδ]
  field_simp [hR.ne', hhalfPos.ne', hself, hprev]

private theorem signedMengerR2_circlePoint_successor_eq_model_aux
    {O P : ℂ} {R θ δ : ℝ} (hR : 0 < R)
    (hP : dist O P < R) (hδ0 : 0 < δ) (hδ2π : δ < 2 * Real.pi) :
    signedMengerR2 P (circlePoint O R θ) (circlePoint O R (θ + δ)) =
      endpointSuccessorCurvatureModel O P R θ δ := by
  have hhalfPos : 0 < Real.sin (δ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have hsinδ : Real.sin δ =
      2 * Real.sin (δ / 2) * Real.cos (δ / 2) := by
    convert Real.sin_two_mul (δ / 2) using 1
    all_goals ring_nf
  have hcosδ : 1 - Real.cos δ = 2 * Real.sin (δ / 2) ^ 2 := by
    have hcosTwo := Real.cos_two_mul (δ / 2)
    have hunit := Real.sin_sq_add_cos_sq (δ / 2)
    rw [show 2 * (δ / 2) = δ by ring] at hcosTwo
    nlinarith
  have hself : dist (circlePoint O R θ) P ≠ 0 := by
    rw [dist_ne_zero]
    intro heq
    have : dist O P = R := by
      rw [← heq, dist_circlePoint_center, abs_of_pos hR]
    linarith
  have hnext : dist (circlePoint O R (θ + δ)) P ≠ 0 := by
    rw [dist_ne_zero]
    intro heq
    have : dist O P = R := by
      rw [← heq, dist_circlePoint_center, abs_of_pos hR]
    linarith
  unfold signedMengerR2 endpointSuccessorCurvatureModel
  rw [endpointSuccessor_cross_eq,
    dist_comm P (circlePoint O R θ),
    dist_circlePoint_add_eq_two_mul_sin_half hR hδ0 hδ2π,
    hsinδ, hcosδ]
  field_simp [hR.ne', hhalfPos.ne', hself, hnext]

private theorem exists_step_bound_signedMengerR2_circlePoint_predecessor_aux
    {O P : ℂ} {R θ : ℝ} (hR : 0 < R) (hP : dist O P < R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      1 / R < signedMengerR2
        (circlePoint O R (θ - δ)) (circlePoint O R θ) P := by
  have hzero := (inv_radius_lt_endpointCurvatureModel_zero_aux
    (θ := θ) hR hP).1
  have hevent : ∀ᶠ δ : ℝ in nhds 0,
      1 / R < endpointPredecessorCurvatureModel O P R θ δ :=
    (continuousAt_endpointPredecessorCurvatureModel_aux hP).eventually_const_lt hzero
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let ε : ℝ := min η (2 * Real.pi)
  have hε : 0 < ε := lt_min hη Real.two_pi_pos
  refine ⟨ε, hε, ?_⟩
  intro δ hδ0 hδε
  rw [signedMengerR2_circlePoint_predecessor_eq_model_aux hR hP hδ0
    (hδε.trans_le (min_le_right η (2 * Real.pi)))]
  apply hball
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ0] using
    hδε.trans_le (min_le_left η (2 * Real.pi))

/-- Symmetric sufficiently-small-step theorem for the successor endpoint. -/
theorem exists_step_bound_signedMengerR2_circlePoint_successor
    {O P : ℂ} {R θ : ℝ} (hR : 0 < R) (hP : dist O P < R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      1 / R < signedMengerR2
        P (circlePoint O R θ) (circlePoint O R (θ + δ)) := by
  have hzero := (inv_radius_lt_endpointCurvatureModel_zero_aux
    (θ := θ) hR hP).2
  have hevent : ∀ᶠ δ : ℝ in nhds 0,
      1 / R < endpointSuccessorCurvatureModel O P R θ δ :=
    (continuousAt_endpointSuccessorCurvatureModel_aux hP).eventually_const_lt hzero
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let ε : ℝ := min η (2 * Real.pi)
  have hε : 0 < ε := lt_min hη Real.two_pi_pos
  refine ⟨ε, hε, ?_⟩
  intro δ hδ0 hδε
  rw [signedMengerR2_circlePoint_successor_eq_model_aux hR hP hδ0
    (hδε.trans_le (min_le_right η (2 * Real.pi)))]
  apply hball
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ0] using
    hδε.trans_le (min_le_left η (2 * Real.pi))

private theorem exists_step_bound_signedMengerR2_circlePoint_endpoints_aux
    {O Pleft Pright : ℂ} {R θleft θright : ℝ}
    (hR : 0 < R) (hleft : dist O Pleft < R)
    (hright : dist O Pright < R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      (1 / R < signedMengerR2
          (circlePoint O R (θleft - δ)) (circlePoint O R θleft) Pleft) ∧
      (1 / R < signedMengerR2
          Pright (circlePoint O R θright) (circlePoint O R (θright + δ))) := by
  obtain ⟨εleft, hεleft, hleftGap⟩ :=
    exists_step_bound_signedMengerR2_circlePoint_predecessor_aux
      (P := Pleft) (θ := θleft) hR hleft
  obtain ⟨εright, hεright, hrightGap⟩ :=
    exists_step_bound_signedMengerR2_circlePoint_successor
      (P := Pright) (θ := θright) hR hright
  refine ⟨min εleft εright, lt_min hεleft hεright, ?_⟩
  intro δ hδ0 hδ
  exact ⟨hleftGap δ hδ0 (hδ.trans_le (min_le_left _ _)),
    hrightGap δ hδ0 (hδ.trans_le (min_le_right _ _))⟩

private theorem exists_odd_mesh_step_bounds_aux {a τ : ℝ} (ha : 0 < a)
    (ha2π : a < 2 * Real.pi) (hτ : 0 < τ) :
    ∃ k : ℕ, 1 ≤ k ∧ 0 < a / ((2 * k + 1) + 1 : ℕ) ∧
      a / ((2 * k + 1) + 1 : ℕ) < Real.pi ∧ a / ((2 * k + 1) + 1 : ℕ) < τ := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (a / τ))
  have hkOneReal : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkOne : 1 ≤ k := by exact_mod_cast hkOneReal.le
  have hratioK : a / τ < (k : ℝ) := (le_max_right _ _).trans_lt hk
  have hdenPos : (0 : ℝ) < ((2 * k + 1) + 1 : ℕ) := by positivity
  have hratioDen : a / τ < (((2 * k + 1) + 1 : ℕ) : ℝ) := by
    exact hratioK.trans (by push_cast; linarith)
  have hstepLtτ : a / (((2 * k + 1) + 1 : ℕ) : ℝ) < τ := by
    apply (div_lt_iff₀ hdenPos).mpr
    simpa [mul_comm] using (div_lt_iff₀ hτ).mp hratioDen
  have hstepPos : 0 < a / (((2 * k + 1) + 1 : ℕ) : ℝ) := div_pos ha hdenPos
  have hdenTwo : (2 : ℝ) ≤ (((2 * k + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ (2 * k + 1) + 1 by omega)
  have hstepLeHalf : a / (((2 * k + 1) + 1 : ℕ) : ℝ) ≤ a / 2 :=
    div_le_div_of_nonneg_left ha.le (by norm_num) hdenTwo
  exact ⟨k, hkOne, hstepPos, hstepLeHalf.trans_lt (by linarith), hstepLtτ⟩

private theorem exists_oddCircleMeshStep_supporting_innerRadius_lt_aux
    {R ρ α η : ℝ} (hρ : ρ < R) (hα0 : 0 < α)
    (hα2π : α < 2 * Real.pi) (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < α / ((2 * k + 1) + 1 : ℕ) ∧
      α / ((2 * k + 1) + 1 : ℕ) < Real.pi ∧
      ρ < R * Real.cos ((α / ((2 * k + 1) + 1 : ℕ)) / 2) ∧
      α / ((2 * k + 1) + 1 : ℕ) < η := by
  let inner : ℝ → ℝ := fun x ↦ R * Real.cos (x / 2)
  have hinnerLim : Tendsto inner (nhds 0) (nhds R) := by
    simpa [inner, ContinuousAt] using (show ContinuousAt inner 0 by dsimp [inner]; fun_prop)
  obtain ⟨ζ, hζ, hball⟩ := Metric.mem_nhds_iff.mp <|
    hinnerLim.eventually (lt_mem_nhds hρ)
  obtain ⟨k, hk, hstepPos, hstepPi, hstepLt⟩ :=
    exists_odd_mesh_step_bounds_aux hα0 hα2π (lt_min hη hζ)
  refine ⟨k, hk, hstepPos, hstepPi, ?_, hstepLt.trans_le (min_le_left _ _)⟩
  change ρ < inner (α / (((2 * k + 1) + 1 : ℕ) : ℝ))
  apply hball
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hstepPos] using
    hstepLt.trans_le (min_le_right η ζ)

private theorem exists_oddCircleMeshAngle_supporting_innerRadius_endpointCurvatures_aux
    {O Pleft Pright : ℂ} {R ρ θB θA : ℝ}
    (hR : 0 < R) (hρ : ρ < R) (hBA : θB < θA)
    (hspan : θA < θB + 2 * Real.pi)
    (hleft : dist O Pleft < R) (hright : dist O Pright < R) :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < (θA - θB) / ((2 * k + 1) + 1 : ℕ) ∧
      (θA - θB) / ((2 * k + 1) + 1 : ℕ) < Real.pi ∧
      ρ < R * Real.cos
        (((θA - θB) / ((2 * k + 1) + 1 : ℕ)) / 2) ∧
      1 / R < signedMengerR2
        (circlePoint O R
          (θA - (θA - θB) / ((2 * k + 1) + 1 : ℕ)))
        (circlePoint O R θA) Pleft ∧
      1 / R < signedMengerR2 Pright (circlePoint O R θB)
        (circlePoint O R
          (θB + (θA - θB) / ((2 * k + 1) + 1 : ℕ))) := by
  obtain ⟨η, hη, hcurvatures⟩ :=
    exists_step_bound_signedMengerR2_circlePoint_endpoints_aux
      (θleft := θA) (θright := θB) hR hleft hright
  obtain ⟨k, hk, hstepPos, hstepPi, hinner, hstepLt⟩ :=
    exists_oddCircleMeshStep_supporting_innerRadius_lt_aux hρ
      (sub_pos.mpr hBA) (by linarith) hη
  have hgaps := hcurvatures
    ((θA - θB) / ((2 * k + 1) + 1 : ℕ)) hstepPos hstepLt
  exact ⟨k, hk, hstepPos, hstepPi, hinner, hgaps.1, hgaps.2⟩

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

private theorem circleSplice_endpoint_gaps_aux {q : ℕ} (hq : 0 < q) {θB θA : ℝ}
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hleft : 1 / R < signedMengerR2
      (circlePoint O R (θA - (θA - θB) / (q + 1 : ℕ)))
      (circlePoint O R θA) (run.point run.a))
    (hright : 1 / R < signedMengerR2 (run.point run.b) (circlePoint O R θB)
      (circlePoint O R (θB + (θA - θB) / (q + 1 : ℕ)))) :
    1 / R < SignedMengerProfile (run.circleSplice q θB θA) 0 ∧
      1 / R < SignedMengerProfile (run.circleSplice q θB θA)
        ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) := by
  letI : NeZero (run.spliceVertexCount q) := ⟨(run.spliceVertexCount_pos q).ne'⟩
  obtain ⟨hleftPrev, hleftSelf, hleftNext⟩ :=
    run.circleSplice_leftEndpoint_triple q hq θB θA hA
  obtain ⟨hrightPrev, hrightSelf, hrightNext⟩ :=
    run.circleSplice_rightEndpoint_triple q hq θB θA hB
  constructor
  · rw [SignedMengerProfile_apply]
    simpa only [zero_sub, zero_add, hleftPrev, hleftSelf, hleftNext] using hleft
  · rwa [SignedMengerProfile_apply, hrightPrev, hrightSelf, hrightNext]

/-- An odd splice mesh supports the inner-radius and endpoint-curvature inequalities. -/
theorem exists_oddCircleMeshAngle_supporting_innerRadius_spliceEndpointGaps
    {ρ θB θA : ℝ}
    (hR : 0 < R) (hΔ : MinimalEnclosingDiskR2 v O R) (hρ : ρ < R)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi) :
    ∃ k : ℕ, 1 ≤ k ∧
      0 < (θA - θB) / ((2 * k + 1) + 1 : ℕ) ∧
      (θA - θB) / ((2 * k + 1) + 1 : ℕ) < Real.pi ∧
      ρ < R * Real.cos
        (((θA - θB) / ((2 * k + 1) + 1 : ℕ)) / 2) ∧
      1 / R < SignedMengerProfile
        (run.circleSplice (2 * k + 1) θB θA) 0 ∧
      1 / R < SignedMengerProfile
        (run.circleSplice (2 * k + 1) θB θA)
          ((run.chainLength - 1 : ℕ) :
            ZMod (run.spliceVertexCount (2 * k + 1))) := by
  obtain ⟨k, hk, hstepPos, hstepPi, hinner, hleftRaw, hrightRaw⟩ :=
    exists_oddCircleMeshAngle_supporting_innerRadius_endpointCurvatures_aux
      hR hρ hBA hspan (run.internal_dist_lt hΔ le_rfl run.a_le_b)
        (run.internal_dist_lt hΔ run.a_le_b le_rfl)
  obtain ⟨hleft, hright⟩ := circleSplice_endpoint_gaps_aux run (q := 2 * k + 1)
    (by omega) hB hA hleftRaw hrightRaw
  exact ⟨k, hk, hstepPos, hstepPi, hinner, hleft, hright⟩

end Section4PositiveRunCertificate

end Gluck.Forward
