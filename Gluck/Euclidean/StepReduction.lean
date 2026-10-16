module

public import Gluck.Euclidean.Closure
public import Gluck.Curvature
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Reduction to a four-arc step function

This file carries out the first move of Gluck's argument (DeTurck–Gluck §5–6):
replace the general continuous curvature function `κ` by a two-valued *four-arc
step* function `κ₀` taking the values `a, b, a, b` (with `0 < a < b`), and
justify that solving the closure problem for the step family solves it for `κ`.

The deliberate departure from the source is recorded in the blueprint: we do
*not* use the (false) "ε-close in measure ⇒ C¹-close" implication. What the
winding argument actually consumes is that the *error vector*
`E(ρ) = ∫₀^{2π} e^{iθ} ρ(θ) dθ` depends Lipschitz-continuously on the weight
`ρ = 1/κ` in the `L¹`/measure sense (`dist_errorVector_le`). This is the rigorous
substitute for the source's `C¹`-closeness claim.

-/

@[expose] public section

namespace Gluck

open scoped Real
open Complex MeasureTheory

/-- The *four-arc step curvature* `κ₀ : ℝ → ℝ` determined by levels `0 < a < b`
and four breakpoint angles `θ₁ < θ₂ < θ₃ < θ₄` in one period. Using the
representative `t = toIcoMod` of `θ` in `[θ₁, θ₁ + 2π)`, it takes the value `b`
on the arcs `[θ₁, θ₂)` and `[θ₃, θ₄)` and the value `a` on the complementary
arcs `[θ₂, θ₃)` and `[θ₄, θ₁ + 2π)`. It is `2π`-periodic (by construction via
`toIcoMod`) and strictly positive (`≥ a > 0`) but discontinuous at the four
breakpoints. (Blueprint `def:four_arc_step_function`.) -/
noncomputable def stepCurvature (a b θ₁ θ₂ θ₃ θ₄ : ℝ) (θ : ℝ) : ℝ :=
  let t := toIcoMod Real.two_pi_pos θ₁ θ
  if t < θ₂ ∨ (θ₃ ≤ t ∧ t < θ₄) then b else a

/-- `stepCurvature` is `2π`-periodic. -/
lemma stepCurvature_periodic (a b θ₁ θ₂ θ₃ θ₄ : ℝ) :
    Function.Periodic (stepCurvature a b θ₁ θ₂ θ₃ θ₄) (2 * Real.pi) := by
  intro θ
  simp only [stepCurvature]
  rw [toIcoMod_add_right]

/-- **Error vector is `L¹`-Lipschitz in the weight.** For integrable weights
`ρ, ρ'` on `[0, 2π]`,
`‖E(ρ) - E(ρ')‖ ≤ ∫₀^{2π} |ρ θ - ρ' θ| dθ`. This is the rigorous replacement for
the source's `C¹`-closeness claim. (Blueprint `lem:error_vector_lipschitz`.) -/
theorem dist_errorVector_le {ρ ρ' : ℝ → ℝ}
    (hρ : IntervalIntegrable ρ volume 0 (2 * π))
    (hρ' : IntervalIntegrable ρ' volume 0 (2 * π)) :
    ‖errorVector ρ - errorVector ρ'‖ ≤ ∫ θ in (0 : ℝ)..(2 * π), |ρ θ - ρ' θ| := by
  have hexp : Continuous fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hρC : IntervalIntegrable (fun φ : ℝ => (ρ φ : ℂ)) volume 0 (2 * π) :=
    ⟨hρ.1.ofReal, hρ.2.ofReal⟩
  have hρ'C : IntervalIntegrable (fun φ : ℝ => (ρ' φ : ℂ)) volume 0 (2 * π) :=
    ⟨hρ'.1.ofReal, hρ'.2.ofReal⟩
  have hI : IntervalIntegrable
      (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ)) volume 0 (2 * π) :=
    hρC.continuousOn_mul hexp.continuousOn
  have hI' : IntervalIntegrable
      (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) * (ρ' φ : ℂ)) volume 0 (2 * π) :=
    hρ'C.continuousOn_mul hexp.continuousOn
  have hsub : errorVector ρ - errorVector ρ'
      = ∫ φ in (0 : ℝ)..(2 * π),
          Complex.exp ((φ : ℂ) * Complex.I) * ((ρ φ - ρ' φ : ℝ) : ℂ) := by
    rw [errorVector, errorVector, reconstruct, reconstruct,
      ← intervalIntegral.integral_sub hI hI']
    refine intervalIntegral.integral_congr ?_
    intro φ _
    push_cast
    ring
  rw [hsub]
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  calc ‖∫ φ in (0 : ℝ)..(2 * π),
            Complex.exp ((φ : ℂ) * Complex.I) * ((ρ φ - ρ' φ : ℝ) : ℂ)‖
      ≤ ∫ φ in (0 : ℝ)..(2 * π),
            ‖Complex.exp ((φ : ℂ) * Complex.I) * ((ρ φ - ρ' φ : ℝ) : ℂ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hpi
    _ = ∫ φ in (0 : ℝ)..(2 * π), |ρ φ - ρ' φ| := by
        refine intervalIntegral.integral_congr ?_
        intro φ _
        simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs]

/-- Pointwise modulus of continuity of `κ` at a point `c`: for every `ε > 0`
there is `η > 0` with `|κ t - κ c| ≤ ε` whenever `|t - c| ≤ η`. Applied at the
four crossing points to control `κ ∘ h₁` on the plateaus. -/
lemma kappa_modulus_at {κ : ℝ → ℝ} (hcont : Continuous κ) (c : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ η > 0, ∀ t, |t - c| ≤ η → |κ t - κ c| ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hcont.continuousAt ε hε
  refine ⟨δ / 2, by positivity, fun t ht => ?_⟩
  have : dist t c < δ := by rw [Real.dist_eq]; linarith
  exact le_of_lt (by simpa [Real.dist_eq] using h this)

/-! ### Helpers for the plateau-density construction (project-bespoke)

The continuous, `2π`-periodic trapezoidal speed density is built as a positive
constant plus four triangular *race* bumps centred at `0, π/2, π, 3π/2`.  Each
bump is a `2π`-periodic unit-height tent of half-width `δ/2`, realised through
the periodic distance `arccos (cos (θ - τ))` to its centre `τ`; this makes
continuity and periodicity automatic. -/

/-- `∫ (c + s·u) du` over `[a,b]`, in closed form. -/
lemma integral_affine (c s a b : ℝ) :
    (∫ u in a..b, (c + s * u)) = c * (b - a) + s * ((b ^ 2 - a ^ 2) / 2) := by
  have h1 : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun u : ℝ => s * u) MeasureTheory.volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]; ring

/-- Periodic unit triangular bump centred at `τ`, half-width `δ/2`, period `2π`. -/
noncomputable def tentBump (δ τ θ : ℝ) : ℝ :=
  max 0 (1 - (2 / δ) * Real.arccos (Real.cos (θ - τ)))

private lemma tentBump_nonneg (δ τ θ : ℝ) : 0 ≤ tentBump δ τ θ := le_max_left _ _

@[fun_prop]
private lemma tentBump_continuous (δ τ : ℝ) : Continuous (fun θ => tentBump δ τ θ) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul
    (Real.continuous_arccos.comp (Real.continuous_cos.comp
      (continuous_id.sub continuous_const)))))

private lemma tentBump_periodic (δ τ : ℝ) :
    Function.Periodic (fun θ => tentBump δ τ θ) (2 * π) := by
  intro θ
  simp only [tentBump]
  rw [show θ + 2 * π - τ = (θ - τ) + 2 * π by ring, Real.cos_add_two_pi]

/-- For `y` at angular distance `≥ δ/2` from `0` (within one period),
`cos y ≤ cos (δ/2)`. -/
private lemma cos_le_cos_half {δ y : ℝ} (hδ : 0 < δ) (hδ' : δ < π)
    (h1 : δ / 2 ≤ y) (h2 : y ≤ 2 * π - δ / 2) : Real.cos y ≤ Real.cos (δ / 2) := by
  have hδ2 : δ / 2 ≤ π := by linarith
  rcases le_total y π with hy | hy
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hy h1
  · rw [← Real.cos_two_pi_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)

/-- Periodic version: shift `y` by `n` periods into `[δ/2, 2π - δ/2]`. -/
lemma cos_le_cos_half_shift {δ y : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (n : ℤ)
    (h1 : δ / 2 ≤ y + n * (2 * π)) (h2 : y + n * (2 * π) ≤ 2 * π - δ / 2) :
    Real.cos y ≤ Real.cos (δ / 2) := by
  rw [← Real.cos_add_int_mul_two_pi y n]
  exact cos_le_cos_half hδ hδ' h1 h2

/-- The bump vanishes wherever the periodic distance to its centre is `≥ δ/2`. -/
lemma tentBump_eq_zero_of_cos_le {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) {τ θ : ℝ}
    (h : Real.cos (θ - τ) ≤ Real.cos (δ / 2)) : tentBump δ τ θ = 0 := by
  have hδ2 : δ / 2 ≤ π := by linarith
  have harc : δ / 2 ≤ Real.arccos (Real.cos (θ - τ)) := by
    have h' := Real.arccos_le_arccos h
    rwa [Real.arccos_cos (by positivity) hδ2] at h'
  unfold tentBump
  refine max_eq_left ?_
  have hge : (1 : ℝ) ≤ 2 / δ * Real.arccos (Real.cos (θ - τ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]; linarith
  linarith

/-- On the support of the centred bump it equals the affine tent `1 - (2/δ)|u|`. -/
private lemma tentBump_affine_zero {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) {u : ℝ}
    (h1 : -(δ / 2) ≤ u) (h2 : u ≤ δ / 2) : tentBump δ 0 u = 1 - (2 / δ) * |u| := by
  have habs : |u| ≤ δ / 2 := abs_le.mpr ⟨by linarith, h2⟩
  have hπ := Real.pi_pos
  have harc : Real.arccos (Real.cos (u - 0)) = |u| := by
    rw [sub_zero, ← Real.cos_abs]
    exact Real.arccos_cos (abs_nonneg u) (by linarith)
  unfold tentBump
  rw [harc]
  refine max_eq_right ?_
  have : (2 / δ) * |u| ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hδ]; linarith
  linarith

/-- `∫` of the centred bump over `[0, δ/2]` (its right half) is `δ/4`. -/
private lemma tentBump_integral_right {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    (∫ u in (0 : ℝ)..(δ / 2), tentBump δ 0 u) = δ / 4 := by
  have hδne : δ ≠ 0 := hδ.ne'
  have hcong : (∫ u in (0 : ℝ)..(δ / 2), tentBump δ 0 u)
      = ∫ u in (0 : ℝ)..(δ / 2), (1 + (-(2 / δ)) * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    rw [tentBump_affine_zero hδ hδ' (by linarith [hu.1]) hu.2, abs_of_nonneg hu.1]; ring
  rw [hcong, integral_affine]; field_simp; ring

/-- `∫` of the centred bump over `[-δ/2, 0]` (its left half) is `δ/4`. -/
private lemma tentBump_integral_left {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    (∫ u in (-(δ / 2))..(0 : ℝ), tentBump δ 0 u) = δ / 4 := by
  have hδne : δ ≠ 0 := hδ.ne'
  have hcong : (∫ u in (-(δ / 2))..(0 : ℝ), tentBump δ 0 u)
      = ∫ u in (-(δ / 2))..(0 : ℝ), (1 + (2 / δ) * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    rw [tentBump_affine_zero hδ hδ' hu.1 (by linarith [hu.2]), abs_of_nonpos hu.2]; ring
  rw [hcong, integral_affine]; field_simp; ring

/-- The centred bump integrates to `δ/2` over its full support `[-δ/2, δ/2]`. -/
private lemma tentBump_integral_center {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    (∫ u in (-(δ / 2))..(δ / 2), tentBump δ 0 u) = δ / 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
        ((tentBump_continuous δ 0).intervalIntegrable _ _)
        ((tentBump_continuous δ 0).intervalIntegrable _ _),
      tentBump_integral_left hδ hδ', tentBump_integral_right hδ hδ']
  ring

/-- A bump centred at `τ` integrates to `δ/2` over its support `[τ-δ/2, τ+δ/2]`. -/
private lemma tentBump_integral_support {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (τ : ℝ) :
    (∫ θ in (τ - δ / 2)..(τ + δ / 2), tentBump δ τ θ) = δ / 2 := by
  have hshift : ∀ θ, tentBump δ τ θ = tentBump δ 0 (θ - τ) := by
    intro θ; simp [tentBump, sub_zero]
  simp only [hshift]
  rw [intervalIntegral.integral_comp_sub_right (fun u => tentBump δ 0 u) τ,
      show τ - δ / 2 - τ = -(δ / 2) by ring, show τ + δ / 2 - τ = δ / 2 by ring]
  exact tentBump_integral_center hδ hδ'

/-- Integral over an interval on which the bump is identically zero. -/
private lemma tentBump_integral_zero_of_forall {δ τ a b : ℝ}
    (h : ∀ θ ∈ Set.uIcc a b, tentBump δ τ θ = 0) :
    (∫ θ in a..b, tentBump δ τ θ) = 0 := by
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_zero]

/-- Cumulative integral from `0` past the full support: `δ/2`. -/
private lemma tentBump_integral_full {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) {τ θ : ℝ}
    (hτ : δ / 2 ≤ τ) (hθ1 : τ + δ / 2 ≤ θ) (hθ2 : θ ≤ 2 * π - δ / 2)
    (_hτ2 : τ ≤ 2 * π - δ / 2) :
    (∫ s in (0 : ℝ)..θ, tentBump δ τ s) = δ / 2 := by
  have hz1 : (∫ s in (0 : ℝ)..(τ - δ / 2), tentBump δ τ s) = 0 := by
    apply tentBump_integral_zero_of_forall
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    apply tentBump_eq_zero_of_cos_le hδ hδ'
    exact cos_le_cos_half_shift hδ hδ' 1 (by push_cast; linarith [hs.1])
      (by push_cast; linarith [hs.2])
  have hz2 : (∫ s in (τ + δ / 2)..θ, tentBump δ τ s) = 0 := by
    apply tentBump_integral_zero_of_forall
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    apply tentBump_eq_zero_of_cos_le hδ hδ'
    exact cos_le_cos_half hδ hδ' (by linarith [hs.1]) (by linarith [hs.2])
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := τ - δ / 2)
        ((tentBump_continuous δ τ).intervalIntegrable _ _)
        ((tentBump_continuous δ τ).intervalIntegrable _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := τ - δ / 2) (b := τ + δ / 2)
        ((tentBump_continuous δ τ).intervalIntegrable _ _)
        ((tentBump_continuous δ τ).intervalIntegrable _ _),
      tentBump_integral_support hδ hδ', hz1, hz2]
  ring

/-- Cumulative integral from `0` not yet reaching the support: `0`. -/
private lemma tentBump_integral_none {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) {τ θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ τ - δ / 2) (hτ2 : τ ≤ 2 * π - δ / 2) :
    (∫ s in (0 : ℝ)..θ, tentBump δ τ s) = 0 := by
  apply tentBump_integral_zero_of_forall
  intro s hs
  rw [Set.uIcc_of_le hθ0] at hs
  apply tentBump_eq_zero_of_cos_le hδ hδ'
  exact cos_le_cos_half_shift hδ hδ' 1 (by push_cast; linarith [hs.1])
    (by push_cast; linarith [hs.2])

/-- Cumulative integral from `0` of the boundary bump (centred at `0`): its right
half `δ/4`. -/
private lemma tentBump_integral_boundary {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) {θ : ℝ}
    (hθ1 : δ / 2 ≤ θ) (hθ2 : θ ≤ 2 * π - δ / 2) :
    (∫ s in (0 : ℝ)..θ, tentBump δ 0 s) = δ / 4 := by
  have hz : (∫ s in (δ / 2)..θ, tentBump δ 0 s) = 0 := by
    apply tentBump_integral_zero_of_forall
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    apply tentBump_eq_zero_of_cos_le hδ hδ'
    rw [sub_zero]
    exact cos_le_cos_half hδ hδ' hs.1 (by linarith [hs.2])
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := δ / 2)
        ((tentBump_continuous δ 0).intervalIntegrable _ _)
        ((tentBump_continuous δ 0).intervalIntegrable _ _),
      tentBump_integral_right hδ hδ', hz]
  ring

/-- A bump integrates to `δ/2` over a full period centred at its centre. -/
private lemma tentBump_integral_period {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (τ : ℝ) :
    (∫ θ in (τ - π)..(τ + π), tentBump δ τ θ) = δ / 2 := by
  have hz1 : (∫ θ in (τ - π)..(τ - δ / 2), tentBump δ τ θ) = 0 := by
    apply tentBump_integral_zero_of_forall
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    apply tentBump_eq_zero_of_cos_le hδ hδ'
    have habs : |s - τ| = τ - s := by rw [abs_of_nonpos (by linarith [hs.2])]; ring
    rw [← Real.cos_abs, habs]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [hs.1])
      (by linarith [hs.2])
  have hz2 : (∫ θ in (τ + δ / 2)..(τ + π), tentBump δ τ θ) = 0 := by
    apply tentBump_integral_zero_of_forall
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    apply tentBump_eq_zero_of_cos_le hδ hδ'
    rw [← Real.cos_abs, abs_of_nonneg (by linarith [hs.1])]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [hs.2])
      (by linarith [hs.1])
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := τ - δ / 2)
        ((tentBump_continuous δ τ).intervalIntegrable _ _)
        ((tentBump_continuous δ τ).intervalIntegrable _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := τ - δ / 2) (b := τ + δ / 2)
        ((tentBump_continuous δ τ).intervalIntegrable _ _)
        ((tentBump_continuous δ τ).intervalIntegrable _ _),
      tentBump_integral_support hδ hδ', hz1, hz2]
  ring

/-- A bump integrates to `δ/2` over the standard period `[0, 2π]`. -/
private lemma tentBump_integral_two_pi {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (τ : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * π), tentBump δ τ θ) = δ / 2 := by
  have hper := (tentBump_periodic δ τ).intervalIntegral_add_eq 0 (τ - π)
  rw [zero_add] at hper
  rw [hper, show τ - π + 2 * π = τ + π by ring]
  exact tentBump_integral_period hδ hδ' τ

set_option maxHeartbeats 1600000 in
-- The four plateau branches each elaborate several `tentBump` cumulative-integral
-- lemmas over a large hypothesis context, exceeding the default heartbeat budget.
/-- **Geometric core: the calibrated continuous plateau density.**

This is the analytic heart of the preliminary-reparametrization construction
(blueprint `lem:exists_preliminary_reparam`). Given the four crossing points
`c₁ < c₂ < c₃ < c₄ < c₁ + 2π` it asserts the existence of a *continuous,
strictly positive, `2π`-periodic* speed density `w` whose cumulative integral
`θ ↦ m₀ + ∫₀^θ w` (the reparametrization `h₁`) has total increment `2π` over a
period and maps the central plateau of each target arc `Iₖ = [(k-1)π/2, kπ/2)`
into the `η`-ball `[cₖ - η, cₖ + η]` of the `k`-th crossing point.

Concretely `w` is the continuous trapezoidal density that is large (a "race") on
the two flanking sub-arcs of total length `δ` of each `Iₖ` and small (a
"plateau") on the central sub-arc of length `π/2 - δ`, calibrated so that the
plateau is carried affinely onto `[cₖ - η, cₖ + η]`. The structural facts
(continuity, positivity, periodicity, period-integral `= 2π`) are exactly what
`exists_preliminary_reparam` consumes to get a circle reparametrization, and the
four plateau-image bounds are what drives the measure estimate.

The construction is elementary but long (an explicit 12-piece continuous
piecewise-linear density with per-arc calibration); it is isolated here as a
single obligation so the surrounding `exists_preliminary_reparam` can be proved
unconditionally. (Blueprint `lem:exists_preliminary_reparam`, density part.) -/
lemma exists_plateau_density {c₁ c₂ c₃ c₄ m₀ η δ : ℝ}
    (_h12 : c₁ < c₂) (_h23 : c₂ < c₃) (_h34 : c₃ < c₄) (_h41 : c₄ < c₁ + 2 * π)
    (hm₀ : m₀ = (c₁ + c₄) / 2 - π)
    (hη : 0 < η) (hδ : 0 < δ) (hδ' : δ < π / 2)
    (hfit₁ : η < (c₂ - c₁) / 2) (hfit₂ : η < (c₃ - c₂) / 2)
    (hfit₃ : η < (c₄ - c₃) / 2) (hfit₄ : η < (c₁ + 2 * π - c₄) / 2) :
    ∃ w : ℝ → ℝ, Continuous w ∧ (∀ x, 0 < w x) ∧ Function.Periodic w (2 * π) ∧
      (∫ s in (0:ℝ)..(2 * π), w s) = 2 * π ∧
      (∀ θ, δ / 2 ≤ θ → θ ≤ π / 2 - δ / 2 →
        |m₀ + (∫ s in (0:ℝ)..θ, w s) - c₁| ≤ η) ∧
      (∀ θ, π / 2 + δ / 2 ≤ θ → θ ≤ π - δ / 2 →
        |m₀ + (∫ s in (0:ℝ)..θ, w s) - c₂| ≤ η) ∧
      (∀ θ, π + δ / 2 ≤ θ → θ ≤ 3 * π / 2 - δ / 2 →
        |m₀ + (∫ s in (0:ℝ)..θ, w s) - c₃| ≤ η) ∧
      (∀ θ, 3 * π / 2 + δ / 2 ≤ θ → θ ≤ 2 * π - δ / 2 →
        |m₀ + (∫ s in (0:ℝ)..θ, w s) - c₄| ≤ η) := by
  have hπ : 0 < π := Real.pi_pos
  have hδπ : δ < π := by linarith
  have hδne : δ ≠ 0 := hδ.ne'
  have hπne : π ≠ 0 := hπ.ne'
  set p : ℝ := 4 * η / π with hp
  set A₀ : ℝ := c₁ + 2 * π - c₄ - 2 * η with hA0
  set A₁ : ℝ := c₂ - c₁ - 2 * η with hA1
  set A₂ : ℝ := c₃ - c₂ - 2 * η with hA2
  set A₃ : ℝ := c₄ - c₃ - 2 * η with hA3
  have hA0pos : 0 < A₀ := by rw [hA0]; linarith
  have hA1pos : 0 < A₁ := by rw [hA1]; linarith
  have hA2pos : 0 < A₂ := by rw [hA2]; linarith
  have hA3pos : 0 < A₃ := by rw [hA3]; linarith
  have hppos : 0 < p := by rw [hp]; exact div_pos (by linarith) hπ
  set w : ℝ → ℝ := fun θ => p + (2 * A₀ / δ) * tentBump δ 0 θ
      + (2 * A₁ / δ) * tentBump δ (π / 2) θ + (2 * A₂ / δ) * tentBump δ π θ
      + (2 * A₃ / δ) * tentBump δ (3 * π / 2) θ with hwdef
  have ii : ∀ (k τ θ : ℝ), IntervalIntegrable (fun s => k * tentBump δ τ s)
      MeasureTheory.volume 0 θ :=
    fun k τ θ => ((tentBump_continuous δ τ).intervalIntegrable _ _).const_mul k
  have hsplit : ∀ θ : ℝ, (∫ s in (0:ℝ)..θ, w s)
      = p * θ + (2 * A₀ / δ) * (∫ s in (0:ℝ)..θ, tentBump δ 0 s)
        + (2 * A₁ / δ) * (∫ s in (0:ℝ)..θ, tentBump δ (π / 2) s)
        + (2 * A₂ / δ) * (∫ s in (0:ℝ)..θ, tentBump δ π s)
        + (2 * A₃ / δ) * (∫ s in (0:ℝ)..θ, tentBump δ (3 * π / 2) s) := by
    intro θ
    have iic : IntervalIntegrable (fun _ : ℝ => p) MeasureTheory.volume 0 θ :=
      intervalIntegrable_const
    have i0 : IntervalIntegrable
        (fun s => p + (2 * A₀ / δ) * tentBump δ 0 s) MeasureTheory.volume 0 θ :=
      iic.add (ii _ _ _)
    have i1 : IntervalIntegrable
        (fun s => p + (2 * A₀ / δ) * tentBump δ 0 s
          + (2 * A₁ / δ) * tentBump δ (π / 2) s) MeasureTheory.volume 0 θ :=
      i0.add (ii _ _ _)
    have i2 : IntervalIntegrable
        (fun s => p + (2 * A₀ / δ) * tentBump δ 0 s
          + (2 * A₁ / δ) * tentBump δ (π / 2) s
          + (2 * A₂ / δ) * tentBump δ π s) MeasureTheory.volume 0 θ :=
      i1.add (ii _ _ _)
    simp only [hwdef]
    rw [intervalIntegral.integral_add i2 (ii _ _ _),
        intervalIntegral.integral_add i1 (ii _ _ _),
        intervalIntegral.integral_add i0 (ii _ _ _),
        intervalIntegral.integral_add iic (ii _ _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
    simp only [smul_eq_mul]; ring
  have hfinal : ∀ X : ℝ, |X| ≤ π → |η * X / π| ≤ η := by
    intro X hX
    rw [abs_div, abs_of_pos hπ, abs_mul, abs_of_pos hη, div_le_iff₀ hπ]
    nlinarith [mul_le_mul_of_nonneg_left hX hη.le]
  refine ⟨w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Continuity.
    rw [hwdef]
    exact ((((continuous_const.add (continuous_const.mul (tentBump_continuous δ 0))).add
      (continuous_const.mul (tentBump_continuous δ (π / 2)))).add
      (continuous_const.mul (tentBump_continuous δ π))).add
      (continuous_const.mul (tentBump_continuous δ (3 * π / 2))))
  · -- Strict positivity.
    intro x
    have t0 : 0 ≤ (2 * A₀ / δ) * tentBump δ 0 x :=
      mul_nonneg (div_nonneg (by linarith) hδ.le) (tentBump_nonneg δ 0 x)
    have t1 : 0 ≤ (2 * A₁ / δ) * tentBump δ (π / 2) x :=
      mul_nonneg (div_nonneg (by linarith) hδ.le) (tentBump_nonneg δ (π / 2) x)
    have t2 : 0 ≤ (2 * A₂ / δ) * tentBump δ π x :=
      mul_nonneg (div_nonneg (by linarith) hδ.le) (tentBump_nonneg δ π x)
    have t3 : 0 ≤ (2 * A₃ / δ) * tentBump δ (3 * π / 2) x :=
      mul_nonneg (div_nonneg (by linarith) hδ.le) (tentBump_nonneg δ (3 * π / 2) x)
    simp only [hwdef]
    linarith
  · -- `2π`-periodicity.
    intro θ
    have e : ∀ τ : ℝ, tentBump δ τ (θ + 2 * π) = tentBump δ τ θ :=
      fun τ => tentBump_periodic δ τ θ
    simp only [hwdef, e]
  · -- Period integral `= 2π`.
    rw [hsplit, tentBump_integral_two_pi hδ hδπ 0, tentBump_integral_two_pi hδ hδπ (π / 2),
        tentBump_integral_two_pi hδ hδπ π, tentBump_integral_two_pi hδ hδπ (3 * π / 2),
        hp, hA0, hA1, hA2, hA3]
    field_simp
    ring
  · -- Plateau 1.
    intro θ hl hr
    have e0 : (∫ s in (0:ℝ)..θ, tentBump δ 0 s) = δ / 4 :=
      tentBump_integral_boundary hδ hδπ (by linarith) (by linarith)
    have e1 : (∫ s in (0:ℝ)..θ, tentBump δ (π / 2) s) = 0 :=
      tentBump_integral_none hδ hδπ (by linarith) (by linarith) (by linarith)
    have e2 : (∫ s in (0:ℝ)..θ, tentBump δ π s) = 0 :=
      tentBump_integral_none hδ hδπ (by linarith) (by linarith) (by linarith)
    have e3 : (∫ s in (0:ℝ)..θ, tentBump δ (3 * π / 2) s) = 0 :=
      tentBump_integral_none hδ hδπ (by linarith) (by linarith) (by linarith)
    have hval : m₀ + (∫ s in (0:ℝ)..θ, w s) = c₁ + η * (4 * θ - π) / π := by
      rw [hsplit θ, e0, e1, e2, e3, hm₀, hp, hA0]; field_simp; ring
    rw [hval, add_sub_cancel_left]
    exact hfinal _ (by rw [abs_le]; constructor <;> linarith)
  · -- Plateau 2.
    intro θ hl hr
    have e0 : (∫ s in (0:ℝ)..θ, tentBump δ 0 s) = δ / 4 :=
      tentBump_integral_boundary hδ hδπ (by linarith) (by linarith)
    have e1 : (∫ s in (0:ℝ)..θ, tentBump δ (π / 2) s) = δ / 2 :=
      tentBump_integral_full hδ hδπ (by linarith) (by linarith) (by linarith) (by linarith)
    have e2 : (∫ s in (0:ℝ)..θ, tentBump δ π s) = 0 :=
      tentBump_integral_none hδ hδπ (by linarith) (by linarith) (by linarith)
    have e3 : (∫ s in (0:ℝ)..θ, tentBump δ (3 * π / 2) s) = 0 :=
      tentBump_integral_none hδ hδπ (by linarith) (by linarith) (by linarith)
    have hval : m₀ + (∫ s in (0:ℝ)..θ, w s) = c₂ + η * (4 * θ - 3 * π) / π := by
      rw [hsplit θ, e0, e1, e2, e3, hm₀, hp, hA0, hA1]; field_simp; ring
    rw [hval, add_sub_cancel_left]
    exact hfinal _ (by rw [abs_le]; constructor <;> linarith)
  · -- Plateau 3.
    intro θ hl hr
    have e0 : (∫ s in (0:ℝ)..θ, tentBump δ 0 s) = δ / 4 :=
      tentBump_integral_boundary hδ hδπ (by linarith) (by linarith)
    have e1 : (∫ s in (0:ℝ)..θ, tentBump δ (π / 2) s) = δ / 2 :=
      tentBump_integral_full hδ hδπ (by linarith) (by linarith) (by linarith) (by linarith)
    have e2 : (∫ s in (0:ℝ)..θ, tentBump δ π s) = δ / 2 :=
      tentBump_integral_full hδ hδπ (by linarith) (by linarith) (by linarith) (by linarith)
    have e3 : (∫ s in (0:ℝ)..θ, tentBump δ (3 * π / 2) s) = 0 :=
      tentBump_integral_none hδ hδπ (by linarith) (by linarith) (by linarith)
    have hval : m₀ + (∫ s in (0:ℝ)..θ, w s) = c₃ + η * (4 * θ - 5 * π) / π := by
      rw [hsplit θ, e0, e1, e2, e3, hm₀, hp, hA0, hA1, hA2]; field_simp; ring
    rw [hval, add_sub_cancel_left]
    exact hfinal _ (by rw [abs_le]; constructor <;> linarith)
  · -- Plateau 4.
    intro θ hl hr
    have e0 : (∫ s in (0:ℝ)..θ, tentBump δ 0 s) = δ / 4 :=
      tentBump_integral_boundary hδ hδπ (by linarith) (by linarith)
    have e1 : (∫ s in (0:ℝ)..θ, tentBump δ (π / 2) s) = δ / 2 :=
      tentBump_integral_full hδ hδπ (by linarith) (by linarith) (by linarith) (by linarith)
    have e2 : (∫ s in (0:ℝ)..θ, tentBump δ π s) = δ / 2 :=
      tentBump_integral_full hδ hδπ (by linarith) (by linarith) (by linarith) (by linarith)
    have e3 : (∫ s in (0:ℝ)..θ, tentBump δ (3 * π / 2) s) = δ / 2 :=
      tentBump_integral_full hδ hδπ (by linarith) (by linarith) (by linarith) (by linarith)
    have hval : m₀ + (∫ s in (0:ℝ)..θ, w s) = c₄ + η * (4 * θ - 7 * π) / π := by
      rw [hsplit θ, e0, e1, e2, e3, hm₀, hp, hA0, hA1, hA2, hA3]; field_simp; ring
    rw [hval, add_sub_cancel_left]
    exact hfinal _ (by rw [abs_le]; constructor <;> linarith)

/-- The four flanking plateau intervals (each of length `π/2 - δ`, separated by the
four `δ`-wide "race" sub-arcs) have total Lebesgue measure `2π - 4δ`, for `0 < δ < π/2`. -/
private lemma plateau_union_measure {δ : ℝ} (hδpos : 0 < δ) (hδlt : δ < π / 2) :
    MeasureTheory.volume
        (Set.Icc (δ / 2) (π / 2 - δ / 2) ∪ Set.Icc (π / 2 + δ / 2) (π - δ / 2) ∪
          Set.Icc (π + δ / 2) (3 * π / 2 - δ / 2) ∪
          Set.Icc (3 * π / 2 + δ / 2) (2 * π - δ / 2))
      = ENNReal.ofReal (2 * π - 4 * δ) := by
  have hπ : 0 < π := Real.pi_pos
  have hxpos : 0 ≤ π / 2 - δ := by linarith
  have hvP1 : MeasureTheory.volume (Set.Icc (δ / 2) (π / 2 - δ / 2))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hvP2 : MeasureTheory.volume (Set.Icc (π / 2 + δ / 2) (π - δ / 2))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hvP3 : MeasureTheory.volume (Set.Icc (π + δ / 2) (3 * π / 2 - δ / 2))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hvP4 : MeasureTheory.volume (Set.Icc (3 * π / 2 + δ / 2) (2 * π - δ / 2))
      = ENNReal.ofReal (π / 2 - δ) := by rw [Real.volume_Icc]; congr 1; ring
  have hd12 : Disjoint (Set.Icc (δ / 2) (π / 2 - δ / 2))
      (Set.Icc (π / 2 + δ / 2) (π - δ / 2)) := by
    rw [Set.disjoint_left]; intro x hx hy
    simp only [Set.mem_Icc] at hx hy; linarith
  have hd123 : Disjoint (Set.Icc (δ / 2) (π / 2 - δ / 2) ∪ Set.Icc (π / 2 + δ / 2) (π - δ / 2))
      (Set.Icc (π + δ / 2) (3 * π / 2 - δ / 2)) := by
    rw [Set.disjoint_left]; intro x hx hy
    rw [Set.mem_Icc] at hy
    simp only [Set.mem_union, Set.mem_Icc] at hx
    rcases hx with h | h <;> linarith [h.1, h.2]
  have hd1234 : Disjoint (Set.Icc (δ / 2) (π / 2 - δ / 2) ∪
      Set.Icc (π / 2 + δ / 2) (π - δ / 2) ∪ Set.Icc (π + δ / 2) (3 * π / 2 - δ / 2))
      (Set.Icc (3 * π / 2 + δ / 2) (2 * π - δ / 2)) := by
    rw [Set.disjoint_left]; intro x hx hy
    rw [Set.mem_Icc] at hy
    simp only [Set.mem_union, Set.mem_Icc] at hx
    rcases hx with (h | h) | h <;> linarith [h.1, h.2]
  rw [MeasureTheory.measure_union hd1234 measurableSet_Icc,
      MeasureTheory.measure_union hd123 measurableSet_Icc,
      MeasureTheory.measure_union hd12 measurableSet_Icc,
      hvP1, hvP2, hvP3, hvP4,
      ← ENNReal.ofReal_add hxpos hxpos,
      ← ENNReal.ofReal_add (by linarith) hxpos,
      ← ENNReal.ofReal_add (by linarith) hxpos]
  congr 1; ring

/-- Values of the canonical four-arc step curvature `stepCurvature b a 0 (π/2) π (3π/2)`
on the four arcs of `[0, 2π)`: `a` on `[0,π/2)` and `[π,3π/2)`, `b` on `[π/2,π)` and
`[3π/2,2π)`. -/
private lemma stepCurvature_canonical_values (a b : ℝ) :
    (∀ θ, 0 ≤ θ → θ < π / 2 → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a) ∧
    (∀ θ, π / 2 ≤ θ → θ < π → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b) ∧
    (∀ θ, π ≤ θ → θ < 3 * π / 2 → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = a) ∧
    (∀ θ, 3 * π / 2 ≤ θ → θ < 2 * π → stepCurvature b a 0 (π / 2) π (3 * π / 2) θ = b) := by
  have hπ : 0 < π := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨h0, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_pos]; left; linarith
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨by linarith, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_neg]
    simp only [not_or, not_and, not_lt]; exact ⟨by linarith, fun h => by linarith⟩
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨by linarith, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_pos]; right; exact ⟨h0, h2⟩
  · intro θ h0 h2
    have ht : toIcoMod Real.two_pi_pos 0 θ = θ := by
      rw [toIcoMod_eq_self]; refine ⟨by linarith, ?_⟩; simp; linarith
    simp only [stepCurvature, ht]; rw [if_neg]
    simp only [not_or, not_and, not_lt]; exact ⟨by linarith, fun h => by linarith⟩

/-- Given four positive moduli and four positive gaps, there is a single positive
radius `η` below all four moduli and strictly below all four gaps (take half their
common minimum). -/
private lemma exists_plateau_radius {η₁ η₂ η₃ η₄ g₁ g₂ g₃ g₄ : ℝ}
    (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (hη₃ : 0 < η₃) (hη₄ : 0 < η₄)
    (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) (hg₃ : 0 < g₃) (hg₄ : 0 < g₄) :
    ∃ η : ℝ, 0 < η ∧ η ≤ η₁ ∧ η ≤ η₂ ∧ η ≤ η₃ ∧ η ≤ η₄ ∧
      η < g₁ ∧ η < g₂ ∧ η < g₃ ∧ η < g₄ := by
  set M : ℝ := min (min (min η₁ η₂) (min η₃ η₄)) (min (min g₁ g₂) (min g₃ g₄)) with hMdef
  have hMle₁ : M ≤ η₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hMle₂ : M ≤ η₂ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hMle₃ : M ≤ η₃ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hMle₄ : M ≤ η₄ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMg₁ : M ≤ g₁ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hMg₂ : M ≤ g₂ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hMg₃ : M ≤ g₃ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hMg₄ : M ≤ g₄ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hMpos : 0 < M := by
    rw [hMdef]
    exact lt_min (lt_min (lt_min hη₁ hη₂) (lt_min hη₃ hη₄))
      (lt_min (lt_min hg₁ hg₂) (lt_min hg₃ hg₄))
  exact ⟨M / 2, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 1000000 in
-- The measure-bound branch reasons over a large local hypothesis context
-- (four moduli, plateau radii, plateau intervals and their disjointness), so
-- the default heartbeat budget is insufficient.
/-- **Existence of a step-approximating reparametrization** (blueprint
`lem:exists_preliminary_reparam`).

Given the crossing data `0 < a < b`, `c₁ < c₂ < c₃ < c₄ < c₁ + 2π` with
`κ(c₁,c₂,c₃,c₄) = (a,b,a,b)` supplied by `exists_abab_of_fourVertex`, for every
`ε > 0` there is an orientation-preserving circle reparametrization `h₁` (a
`StrictMono`, `Continuous` map with `h₁(θ+2π) = h₁(θ)+2π`) such that, off a set
of measure `< ε`, `κ ∘ h₁` is within `ε` of the canonical four-arc step curvature
`κ₀ = stepCurvature b a 0 (π/2) π (3π/2)` (values `a,b,a,b` on the four arcs).

The construction is `h₁(θ) = m₀ + ∫₀^θ w` for the calibrated continuous plateau
density `w` of `exists_plateau_density`; the structural properties come for free
from `w` being continuous, positive, `2π`-periodic with period-integral `2π`, and
the measure bound follows because the bad set is contained in the four flanking
"race" sub-arcs of total measure `4δ < ε`. -/
theorem exists_preliminary_reparam {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    {a b c₁ c₂ c₃ c₄ : ℝ} (_ha : 0 < a) (_hab : a < b)
    (h12 : c₁ < c₂) (h23 : c₂ < c₃) (h34 : c₃ < c₄) (h41 : c₄ < c₁ + 2 * π)
    (hc₁ : κ c₁ = a) (hc₂ : κ c₂ = b) (hc₃ : κ c₃ = a) (hc₄ : κ c₄ = b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h₁ : ℝ → ℝ, StrictMono h₁ ∧ Continuous h₁ ∧
      (∀ θ, h₁ (θ + 2 * π) = h₁ θ + 2 * π) ∧
      MeasureTheory.volume
          {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π) ∧
            ε < |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|}
        < ENNReal.ofReal ε ∧
      (∃ v₁ : ℝ → ℝ, Continuous v₁ ∧ (∀ θ, 0 < v₁ θ) ∧
        ∀ θ, HasDerivAt h₁ (v₁ θ) θ) := by
  obtain ⟨hcont, hper, hpos⟩ := hκ
  obtain ⟨η₁, hη₁, hm1⟩ := kappa_modulus_at hcont c₁ hε
  obtain ⟨η₂, hη₂, hm2⟩ := kappa_modulus_at hcont c₂ hε
  obtain ⟨η₃, hη₃, hm3⟩ := kappa_modulus_at hcont c₃ hε
  obtain ⟨η₄, hη₄, hm4⟩ := kappa_modulus_at hcont c₄ hε
  have hπ : 0 < π := Real.pi_pos
  have hgap₁ : 0 < (c₂ - c₁) / 2 := by linarith
  have hgap₂ : 0 < (c₃ - c₂) / 2 := by linarith
  have hgap₃ : 0 < (c₄ - c₃) / 2 := by linarith
  have hgap₄ : 0 < (c₁ + 2 * π - c₄) / 2 := by linarith
  obtain ⟨η, hηpos, hηle₁, hηle₂, hηle₃, hηle₄, hfit₁, hfit₂, hfit₃, hfit₄⟩ :=
    exists_plateau_radius hη₁ hη₂ hη₃ hη₄ hgap₁ hgap₂ hgap₃ hgap₄
  set δ : ℝ := min (ε / 8) (π / 4) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
  have hδlt : δ < π / 2 := by
    rw [hδdef]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨w, hw, hwpos, hwper, hwint, hpl1, hpl2, hpl3, hpl4⟩ :=
    exists_plateau_density (m₀ := (c₁ + c₄) / 2 - π) h12 h23 h34 h41 rfl
      hηpos hδpos hδlt hfit₁ hfit₂ hfit₃ hfit₄
  set m₀ : ℝ := (c₁ + c₄) / 2 - π with hm₀def
  set h₁ : ℝ → ℝ := fun θ => m₀ + ∫ s in (0:ℝ)..θ, w s with hh₁def
  have hh₁diff : Differentiable ℝ h₁ := by
    have hd : Differentiable ℝ (fun θ : ℝ => ∫ s in (0:ℝ)..θ, w s) := fun θ =>
      (intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 θ)
        (hw.stronglyMeasurableAtFilter _ _) hw.continuousAt).differentiableAt
    simpa only [hh₁def] using hd.const_add m₀
  have hh₁cont : Continuous h₁ := hh₁diff.continuous
  have hh₁deriv : ∀ θ, HasDerivAt h₁ (w θ) θ := fun θ => by
    have hd : HasDerivAt (fun θ : ℝ => ∫ s in (0:ℝ)..θ, w s) (w θ) θ :=
      intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 θ)
        (hw.stronglyMeasurableAtFilter _ _) hw.continuousAt
    simpa only [hh₁def] using hd.const_add m₀
  refine ⟨h₁, ?_, hh₁cont, ?_, ?_, ⟨w, hw, hwpos, hh₁deriv⟩⟩
  · -- StrictMono
    intro x y hxy
    have hposint : (0:ℝ) < ∫ s in x..y, w s :=
      intervalIntegral.intervalIntegral_pos_of_pos (hw.intervalIntegrable _ _) hwpos hxy
    have hadd : (∫ s in (0:ℝ)..x, w s) + (∫ s in x..y, w s) = ∫ s in (0:ℝ)..y, w s :=
      intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable _ _)
        (hw.intervalIntegrable _ _)
    simp only [hh₁def]; linarith
  · -- Quasi-periodicity `h₁(θ+2π) = h₁(θ) + 2π`.
    intro θ
    have hadd : (∫ s in (0:ℝ)..θ, w s) + (∫ s in θ..(θ + 2 * π), w s)
        = ∫ s in (0:ℝ)..(θ + 2 * π), w s :=
      intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable _ _)
        (hw.intervalIntegrable _ _)
    have hshift : (∫ s in θ..(θ + 2 * π), w s) = ∫ s in (0:ℝ)..(0 + 2 * π), w s :=
      hwper.intervalIntegral_add_eq θ 0
    rw [zero_add] at hshift
    simp only [hh₁def]
    rw [← hadd, hshift, hwint]; ring
  · -- Measure bound: the bad set avoids all four plateaus, hence sits in the
    obtain ⟨hstep1, hstep2, hstep3, hstep4⟩ := stepCurvature_canonical_values a b
    set U := Set.Ico (0 : ℝ) (2 * π) with hUdef
    set P₁ := Set.Icc (δ / 2) (π / 2 - δ / 2) with hP1def
    set P₂ := Set.Icc (π / 2 + δ / 2) (π - δ / 2) with hP2def
    set P₃ := Set.Icc (π + δ / 2) (3 * π / 2 - δ / 2) with hP3def
    set P₄ := Set.Icc (3 * π / 2 + δ / 2) (2 * π - δ / 2) with hP4def
    have hgood : ∀ θ, θ ∈ P₁ ∪ P₂ ∪ P₃ ∪ P₄ →
        |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ| ≤ ε := by
      intro θ hmem
      simp only [Set.mem_union] at hmem
      rcases hmem with ((h | h) | h) | h
      · obtain ⟨hl, hr⟩ := h
        have hb : |h₁ θ - c₁| ≤ η := by simp only [hh₁def]; exact hpl1 θ hl hr
        have := hm1 (h₁ θ) (le_trans hb hηle₁)
        rw [hstep1 θ (by linarith) (by linarith), ← hc₁]; exact this
      · obtain ⟨hl, hr⟩ := h
        have hb : |h₁ θ - c₂| ≤ η := by simp only [hh₁def]; exact hpl2 θ hl hr
        have := hm2 (h₁ θ) (le_trans hb hηle₂)
        rw [hstep2 θ (by linarith) (by linarith), ← hc₂]; exact this
      · obtain ⟨hl, hr⟩ := h
        have hb : |h₁ θ - c₃| ≤ η := by simp only [hh₁def]; exact hpl3 θ hl hr
        have := hm3 (h₁ θ) (le_trans hb hηle₃)
        rw [hstep3 θ (by linarith) (by linarith), ← hc₃]; exact this
      · obtain ⟨hl, hr⟩ := h
        have hb : |h₁ θ - c₄| ≤ η := by simp only [hh₁def]; exact hpl4 θ hl hr
        have := hm4 (h₁ θ) (le_trans hb hηle₄)
        rw [hstep4 θ (by linarith) (by linarith), ← hc₄]; exact this
    have hBsub : {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π) ∧
        ε < |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|}
        ⊆ U \ (P₁ ∪ P₂ ∪ P₃ ∪ P₄) := by
      intro θ hθ
      obtain ⟨hU, hbad⟩ := hθ
      refine ⟨hU, fun hP => ?_⟩
      exact absurd (hgood θ hP) (not_le.mpr hbad)
    have hδle : δ ≤ π / 4 := by rw [hδdef]; exact min_le_right _ _
    have h4δlt : 4 * δ < ε := by
      rw [hδdef]; have := min_le_left (ε / 8) (π / 4); linarith
    have hmeasP : MeasurableSet (P₁ ∪ P₂ ∪ P₃ ∪ P₄) :=
      ((measurableSet_Icc.union measurableSet_Icc).union measurableSet_Icc).union
        measurableSet_Icc
    have hvP : MeasureTheory.volume (P₁ ∪ P₂ ∪ P₃ ∪ P₄)
        = ENNReal.ofReal (2 * π - 4 * δ) := by
      rw [hP1def, hP2def, hP3def, hP4def]
      exact plateau_union_measure hδpos hδlt
    have hvU : MeasureTheory.volume U = ENNReal.ofReal (2 * π) := by
      rw [hUdef, Real.volume_Ico]; congr 1; ring
    have hPU : (P₁ ∪ P₂ ∪ P₃ ∪ P₄) ⊆ U := by
      rw [hUdef, hP1def, hP2def, hP3def, hP4def]
      intro x hx
      simp only [Set.mem_union, Set.mem_Icc] at hx
      rw [Set.mem_Ico]
      rcases hx with ((h | h) | h) | h <;> constructor <;> linarith [h.1, h.2]
    calc MeasureTheory.volume {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) (2 * π) ∧
              ε < |κ (h₁ θ) - stepCurvature b a 0 (π / 2) π (3 * π / 2) θ|}
        ≤ MeasureTheory.volume (U \ (P₁ ∪ P₂ ∪ P₃ ∪ P₄)) := MeasureTheory.measure_mono hBsub
      _ = MeasureTheory.volume U - MeasureTheory.volume (P₁ ∪ P₂ ∪ P₃ ∪ P₄) :=
          MeasureTheory.measure_sdiff hPU hmeasP.nullMeasurableSet
            (by rw [hvP]; exact ENNReal.ofReal_ne_top)
      _ = ENNReal.ofReal (2 * π) - ENNReal.ofReal (2 * π - 4 * δ) := by rw [hvU, hvP]
      _ = ENNReal.ofReal (4 * δ) := by
          rw [← ENNReal.ofReal_sub _ (by linarith : (0:ℝ) ≤ 2 * π - 4 * δ)]; congr 1; ring
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr h4δlt

end Gluck
