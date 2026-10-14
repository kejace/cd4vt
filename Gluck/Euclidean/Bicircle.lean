import Gluck.Euclidean.StepReduction

/-!
# Bicircle curves and their error vectors

This file analyses the geometry of curves reconstructed from a four-arc step
curvature `κ₀` (`stepCurvature`). Such a curve is a *bicircle*: four circular
arcs, two cut from a circle of curvature `a` and two from a circle of curvature
`b`, joined so the tangent line turns continuously through `2π`. The main result
is Dahlberg's explicit formula (DeTurck–Gluck, Proposition 9.1) for the error
vector of a bicircle, the input to the winding argument of `Gluck/Winding.lean`.

-/

namespace Gluck

open scoped Real
open Complex MeasureTheory

/-- The *bicircle error vector* `E_bi(a,b,θ₁,…,θ₄) = E(1/κ₀)`: the error vector of
the four-arc step weight `ρ₀ = 1/κ₀ = radius (stepCurvature …)`.
(Blueprint `def:bicircle_error_vector`.) -/
noncomputable def bicircleErrorVector (a b θ₁ θ₂ θ₃ θ₄ : ℝ) : ℂ :=
  errorVector (radius (stepCurvature a b θ₁ θ₂ θ₃ θ₄))

/-- Interval integral of the unit tangent: `∫_c^d e^{iθ} dθ = -i (e^{id} - e^{ic})`. -/
lemma integral_cexp_I (c d : ℝ) :
    (∫ θ in c..d, Complex.exp ((θ : ℂ) * Complex.I))
      = -Complex.I * (Complex.exp ((d : ℂ) * Complex.I) - Complex.exp ((c : ℂ) * Complex.I)) := by
  have h := integral_exp_mul_complex (a := c) (b := d) (c := Complex.I) Complex.I_ne_zero
  simp_rw [mul_comm Complex.I] at h
  rw [h, Complex.div_I]
  ring

/-- On the half-open arc `(c,d]` where the step curvature is constant `= v`, the
bicircle integrand `e^{iθ}·ρ₀(θ)` agrees a.e. with the continuous representative
`e^{iθ}·(1/v)`. (Endpoints, a null set, are ignored.) -/
lemma bicircle_arc_integrand_eq (a b θ₁ θ₂ θ₃ θ₄ v c d : ℝ) (hcd : c ≤ d)
    (hv : ∀ θ ∈ Set.Ioo c d, stepCurvature a b θ₁ θ₂ θ₃ θ₄ θ = v) :
    (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)
        * ((radius (stepCurvature a b θ₁ θ₂ θ₃ θ₄) θ : ℝ) : ℂ))
      =ᵐ[volume.restrict (Set.uIoc c d)]
    (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) * ((1 / v : ℝ) : ℂ)) := by
  rw [Set.uIoc_of_le hcd]
  have hd : ∀ᵐ θ ∂volume, θ ≠ d := Measure.ae_ne volume d
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hd] with θ hθd hθ
  have hmem : θ ∈ Set.Ioo c d := ⟨hθ.1, lt_of_le_of_ne hθ.2 hθd⟩
  have hr : radius (stepCurvature a b θ₁ θ₂ θ₃ θ₄) θ = 1 / v := by
    rw [radius, hv θ hmem]
  rw [hr]

/-- Integral of the bicircle integrand over an arc on which the step curvature is
constant `= v`: `∫_c^d e^{iθ}ρ₀ = (1/v)(-i)(e^{id} - e^{ic})`. -/
lemma bicircle_arc_integral (a b θ₁ θ₂ θ₃ θ₄ v c d : ℝ) (hcd : c ≤ d)
    (hv : ∀ θ ∈ Set.Ioo c d, stepCurvature a b θ₁ θ₂ θ₃ θ₄ θ = v) :
    (∫ θ in c..d, Complex.exp ((θ : ℂ) * Complex.I)
        * ((radius (stepCurvature a b θ₁ θ₂ θ₃ θ₄) θ : ℝ) : ℂ))
      = (1 / (v : ℂ)) * (-Complex.I)
        * (Complex.exp ((d : ℂ) * Complex.I) - Complex.exp ((c : ℂ) * Complex.I)) := by
  rw [intervalIntegral.integral_congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mp
        (bicircle_arc_integrand_eq a b θ₁ θ₂ θ₃ θ₄ v c d hcd hv))]
  rw [intervalIntegral.integral_mul_const, integral_cexp_I]
  push_cast
  ring

/-- The bicircle integrand is interval-integrable over an arc on which the step
curvature is constant. -/
lemma bicircle_arc_integrable (a b θ₁ θ₂ θ₃ θ₄ v c d : ℝ) (hcd : c ≤ d)
    (hv : ∀ θ ∈ Set.Ioo c d, stepCurvature a b θ₁ θ₂ θ₃ θ₄ θ = v) :
    IntervalIntegrable (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)
        * ((radius (stepCurvature a b θ₁ θ₂ θ₃ θ₄) θ : ℝ) : ℂ)) volume c d := by
  have hcont : IntervalIntegrable
      (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) * ((1 / v : ℝ) : ℂ)) volume c d :=
    (Continuous.intervalIntegrable (by fun_prop) c d)
  rw [intervalIntegrable_iff] at hcont ⊢
  exact hcont.congr (bicircle_arc_integrand_eq a b θ₁ θ₂ θ₃ θ₄ v c d hcd hv).symm

theorem bicircleErrorVector_eq (a b θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h1 : 0 ≤ θ₁) (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄) (h4 : θ₄ < 2 * π) :
    bicircleErrorVector a b θ₁ θ₂ θ₃ θ₄
      = (1 / (Complex.I * (b : ℂ)) - 1 / (Complex.I * (a : ℂ)))
        * ((Complex.exp ((θ₂ : ℂ) * Complex.I) - Complex.exp ((θ₁ : ℂ) * Complex.I))
          + (Complex.exp ((θ₄ : ℂ) * Complex.I) - Complex.exp ((θ₃ : ℂ) * Complex.I))) := by
  have htm : ∀ θ : ℝ, θ₁ ≤ θ → θ < θ₁ + 2 * π →
      toIcoMod Real.two_pi_pos θ₁ θ = θ :=
    fun θ hl hr => (toIcoMod_eq_self Real.two_pi_pos).mpr ⟨hl, hr⟩
  have hvP0 : ∀ θ ∈ Set.Ioo (0 : ℝ) θ₁, stepCurvature a b θ₁ θ₂ θ₃ θ₄ θ = a := by
    intro θ hθ; obtain ⟨hl, hr⟩ := hθ
    have htm0 : toIcoMod Real.two_pi_pos θ₁ θ = θ + 2 * π := by
      rw [← toIcoMod_add_right Real.two_pi_pos θ₁ θ]
      exact (toIcoMod_eq_self Real.two_pi_pos).mpr ⟨by linarith, by linarith⟩
    simp only [stepCurvature, htm0]
    rw [if_neg (by push Not; exact ⟨by linarith, fun _ => by linarith⟩)]
  have hvP1 : ∀ θ ∈ Set.Ioo θ₁ θ₂, stepCurvature a b θ₁ θ₂ θ₃ θ₄ θ = b := by
    intro θ hθ; obtain ⟨hl, hr⟩ := hθ
    have h := htm θ (le_of_lt hl) (by linarith)
    simp only [stepCurvature, h]
    rw [if_pos (Or.inl hr)]
  have hvP2 : ∀ θ ∈ Set.Ioo θ₂ θ₃, stepCurvature a b θ₁ θ₂ θ₃ θ₄ θ = a := by
    intro θ hθ; obtain ⟨hl, hr⟩ := hθ
    have h := htm θ (by linarith) (by linarith)
    simp only [stepCurvature, h]
    rw [if_neg (by push Not; exact ⟨by linarith, fun _ => by linarith⟩)]
  have hvP3 : ∀ θ ∈ Set.Ioo θ₃ θ₄, stepCurvature a b θ₁ θ₂ θ₃ θ₄ θ = b := by
    intro θ hθ; obtain ⟨hl, hr⟩ := hθ
    have h := htm θ (by linarith) (by linarith)
    simp only [stepCurvature, h]
    rw [if_pos (Or.inr ⟨le_of_lt hl, hr⟩)]
  have hvP4 : ∀ θ ∈ Set.Ioo θ₄ (2 * π), stepCurvature a b θ₁ θ₂ θ₃ θ₄ θ = a := by
    intro θ hθ; obtain ⟨hl, hr⟩ := hθ
    have h := htm θ (by linarith) (by linarith)
    simp only [stepCurvature, h]
    rw [if_neg (by push Not; exact ⟨by linarith, fun _ => by linarith⟩)]
  have hi0 := bicircle_arc_integrable a b θ₁ θ₂ θ₃ θ₄ a 0 θ₁ h1 hvP0
  have hi1 := bicircle_arc_integrable a b θ₁ θ₂ θ₃ θ₄ b θ₁ θ₂ (le_of_lt h12) hvP1
  have hi2 := bicircle_arc_integrable a b θ₁ θ₂ θ₃ θ₄ a θ₂ θ₃ (le_of_lt h23) hvP2
  have hi3 := bicircle_arc_integrable a b θ₁ θ₂ θ₃ θ₄ b θ₃ θ₄ (le_of_lt h34) hvP3
  have hi4 := bicircle_arc_integrable a b θ₁ θ₂ θ₃ θ₄ a θ₄ (2 * π) (le_of_lt h4) hvP4
  rw [bicircleErrorVector, errorVector, reconstruct]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0
        (((hi1.trans hi2).trans hi3).trans hi4),
      ← intervalIntegral.integral_add_adjacent_intervals hi1 ((hi2.trans hi3).trans hi4),
      ← intervalIntegral.integral_add_adjacent_intervals hi2 (hi3.trans hi4),
      ← intervalIntegral.integral_add_adjacent_intervals hi3 hi4]
  rw [bicircle_arc_integral a b θ₁ θ₂ θ₃ θ₄ a 0 θ₁ h1 hvP0,
      bicircle_arc_integral a b θ₁ θ₂ θ₃ θ₄ b θ₁ θ₂ (le_of_lt h12) hvP1,
      bicircle_arc_integral a b θ₁ θ₂ θ₃ θ₄ a θ₂ θ₃ (le_of_lt h23) hvP2,
      bicircle_arc_integral a b θ₁ θ₂ θ₃ θ₄ b θ₃ θ₄ (le_of_lt h34) hvP3,
      bicircle_arc_integral a b θ₁ θ₂ θ₃ θ₄ a θ₄ (2 * π) (le_of_lt h4) hvP4]
  have e0 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have e2pi : Complex.exp (((2 * π : ℝ) : ℂ) * Complex.I) = 1 := by
    have hc : ((2 * π : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [hc, Complex.exp_two_pi_mul_I]
  rw [e0, e2pi]
  have hkey : (1 : ℂ) / (Complex.I * (b : ℂ)) - 1 / (Complex.I * (a : ℂ))
      = -Complex.I * (1 / (b : ℂ) - 1 / (a : ℂ)) := by
    rw [one_div, one_div, mul_inv, mul_inv, Complex.inv_I]; ring
  rw [hkey]; ring

end Gluck
