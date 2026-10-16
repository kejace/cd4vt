module

public import Gluck.Discrete.SideTangentField
public import ForMathlib.Analysis.InnerProductSpace.ProjectiveBalance
public import ForMathlib.Analysis.Complex.DiamondStability
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Persistence of the labelled side-tangent balancing field

All original coefficients stay fixed. Positivity of every projective denominator
and all four boundary signs persist for nearby finite vertex configurations,
so the perturbed configuration has an actual field zero.
-/

@[expose] public section

open Set Filter
open scoped Topology InnerProductSpace BigOperators

namespace Gluck.Discrete.SideTangent

variable {ι : Type*} [Fintype ι]

/-- The finite rational field is jointly continuous wherever its denominators do not vanish. -/
lemma continuousAt_projectiveField (c : ι → ℝ) {x : ι → ℂ} {a : ℂ}
    (hden : ∀ i, ProjectiveBall.denominator a (x i) ≠ 0) :
    ContinuousAt (fun p : (ι → ℂ) × ℂ ↦ ProjectiveBall.field c p.1 p.2) (x, a) := by
  unfold ProjectiveBall.field
  apply tendsto_finsetSum
  intro i _
  have hx : Continuous (fun p : (ι → ℂ) × ℂ ↦ p.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hd : Continuous (fun p : (ι → ℂ) × ℂ ↦ ProjectiveBall.denominator p.2 (p.1 i)) :=
    continuous_const.sub (continuous_snd.inner hx)
  exact (continuousAt_const.div hd.continuousAt (hden i)).smul hx.continuousAt

/-- All denominators stay positive on the entire fixed diamond for nearby vertex lists. -/
lemma eventually_projective_denominators_pos {x : ι → ℂ} {r : ℝ}
    (hden : ∀ a ∈ Complex.diamond r, ∀ i, 0 < ProjectiveBall.denominator a (x i)) :
    ∀ᶠ y in 𝓝 x, ∀ a ∈ Complex.diamond r, ∀ i,
      0 < ProjectiveBall.denominator a (y i) := by
  apply (Complex.isCompact_diamond r).eventually_forall_of_forall_eventually
  intro a ha
  apply Filter.eventually_all.mpr
  intro i
  have hc : Continuous (fun p : (ι → ℂ) × ℂ ↦ ProjectiveBall.denominator p.2 (p.1 i)) :=
    continuous_const.sub (continuous_snd.inner ((continuous_apply i).comp continuous_fst))
  exact hc.continuousAt (Ioi_mem_nhds (hden a ha i))

/-- A zero persists for all sufficiently close finite vertex configurations. -/
theorem eventually_exists_projectiveField_zero (c : ι → ℝ) {x : ι → ℂ} {r : ℝ}
    (hr : 0 < r)
    (hden : ∀ a ∈ Complex.diamond r, ∀ i, 0 < ProjectiveBall.denominator a (x i))
    (hs : Complex.DiamondSigns (ProjectiveBall.field c x) r) :
    ∀ᶠ y in 𝓝 x, ∃ a ∈ Complex.diamond r,
      (∀ i, 0 < ProjectiveBall.denominator a (y i)) ∧ ProjectiveBall.field c y a = 0 := by
  have hsigns := Complex.eventually_diamondSigns
    (fun a ha ↦ continuousAt_projectiveField c (fun i ↦ (hden a ha i).ne')) hs
  filter_upwards [hsigns, eventually_projective_denominators_pos hden] with y hsy hdy
  have hc : ContinuousOn (ProjectiveBall.field c y) (Complex.diamond r) := by
    apply continuousOn_of_forall_continuousAt
    intro a ha
    exact (continuousAt_projectiveField c (fun i ↦ (hdy a ha i).ne')).comp
      (continuousAt_const.prodMk continuousAt_id)
  obtain ⟨a, ha, hzero⟩ := Complex.exists_zero_of_diamondSigns hr
    (ProjectiveBall.field c y) hc hsy
  exact ⟨a, ha, hdy a ha, hzero⟩

/-- A zero-sum coefficient list retains an actual projectively balanced realization
through sufficiently small finite vertex perturbations. -/
theorem eventually_exists_projective_balance (c : ι → ℝ) {x : ι → ℂ} {r : ℝ}
    (hr : 0 < r) (hr₁ : r < 1) (hsum : ∑ i, c i = 0)
    (hden : ∀ a ∈ Complex.diamond r, ∀ i, 0 < ProjectiveBall.denominator a (x i))
    (hs : Complex.DiamondSigns (ProjectiveBall.field c x) r) :
    ∀ᶠ y in 𝓝 x, ∃ a : ℂ, ∃ σ : ℝ, ‖a‖ < 1 ∧ 0 < σ ∧ σ ^ 2 + ‖a‖ ^ 2 = 1 ∧
      (∀ i, 0 < ProjectiveBall.denominator a (y i)) ∧
      ∑ i, c i • ProjectiveBall.transform a σ (y i) = 0 := by
  filter_upwards [eventually_exists_projectiveField_zero c hr hden hs] with y hy
  obtain ⟨a, ha, hda, hzero⟩ := hy
  have hanorm : ‖a‖ < 1 := ((Complex.norm_le_abs_re_add_abs_im a).trans ha).trans_lt hr₁
  have hrad : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  refine ⟨a, Real.sqrt (1 - ‖a‖ ^ 2), hanorm, Real.sqrt_pos.mpr hrad,
    by rw [Real.sq_sqrt hrad.le]; ring, hda, ?_⟩
  exact ProjectiveBall.sum_smul_transform_eq_zero_of_field_eq_zero c y a _
    (fun i ↦ (hda i).ne') hsum hzero

end Gluck.Discrete.SideTangent
