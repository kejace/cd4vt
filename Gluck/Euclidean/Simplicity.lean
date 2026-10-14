import Gluck.Euclidean.Closure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Simplicity of the reconstructed curve

The winding argument produces a weight `ρ = 1/(κ ∘ h)`, continuous, `2π`-periodic
and strictly positive, whose error vector vanishes, so the reconstruction
`α_ρ` (`reconstruct`) closes up. This file supplies the last geometric input of
Gluck's converse: such a closed reconstruction is automatically *simple*
(injective on a period).

The argument is elementary — no Mathlib gap, no Umlaufsatz. If `α_ρ(θ₁) = α_ρ(θ₂)`
with `0 ≤ θ₁ < θ₂ < 2π`, the two complementary arcs `[θ₁, θ₂]` and `[θ₂, θ₁+2π]`
both have chord integral `0` (the second uses `E(ρ) = 0`, equivalently `2π`-periodicity
of `α_ρ`). One of them has length `≤ π`; projecting its chord integral onto the
midpoint direction `e^{iψ}` gives `0 = ∫ cos(φ−ψ)·ρ`, whose integrand is `≥ 0` and
`> 0` on the open interval — a contradiction.

Blueprint: `blueprint/src/chapters/Gluck_Simplicity.tex`
(`thm:reconstruct_injective`, `cor:positive_curvature_implies_simple`).
-/

namespace Gluck

open scoped Real
open Complex
open MeasureTheory

/-- The reconstruction curve `α_ρ` of a continuous, `2π`-periodic weight with
vanishing error vector is itself `2π`-periodic: a full period of the integrand
contributes exactly the error vector `E(ρ) = 0`. (Helper for
`thm:reconstruct_injective` / `cor:positive_curvature_implies_simple`.) -/
theorem reconstruct_periodic {ρ : ℝ → ℝ} (hcont : Continuous ρ)
    (hper : Function.Periodic ρ (2 * π)) (hE : errorVector ρ = 0) :
    Function.Periodic (reconstruct ρ) (2 * π) := by
  have hg : Continuous fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ) := by
    fun_prop
  have hgper : Function.Periodic
      (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ)) (2 * π) := by
    intro φ
    simp only
    rw [hper φ]
    congr 1
    have h2 : ((φ + 2 * π : ℝ) : ℂ) * Complex.I
        = (φ : ℂ) * Complex.I + 2 * (π : ℂ) * Complex.I := by push_cast; ring
    rw [h2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  intro x
  have h1 : reconstruct ρ x
      + (∫ φ in x..(x + 2 * π), Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ))
      = reconstruct ρ (x + 2 * π) := by
    rw [reconstruct, reconstruct]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable 0 x) (hg.intervalIntegrable x (x + 2 * π))
  have h2 : (∫ φ in x..(x + 2 * π), Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ))
      = errorVector ρ := by
    have hp := hgper.intervalIntegral_add_eq x 0
    simp only [zero_add] at hp
    rw [hp, errorVector, reconstruct]
  rw [← h1, h2, hE, add_zero]

/-- *Chord-integral positivity.* For a continuous strictly positive weight `ρ`,
the chord integral `∫_c^d e^{iφ} ρ(φ) dφ` over an interval of length `0 < d−c ≤ π`
is nonzero: projecting onto the midpoint direction gives a strictly positive real
integral. (Helper for `thm:reconstruct_injective`.) -/
theorem chord_integral_ne_zero {ρ : ℝ → ℝ} (hcont : Continuous ρ)
    (hpos : ∀ θ, 0 < ρ θ) {c d : ℝ} (hcd : c < d) (hlen : d - c ≤ π) :
    (∫ φ in c..d, Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ)) ≠ 0 := by
  set ψ : ℝ := (c + d) / 2 with hψ
  have hcos : Continuous fun φ : ℝ => Real.cos (φ - ψ) * ρ φ := by fun_prop
  have hsin : Continuous fun φ : ℝ => Real.sin (φ - ψ) * ρ φ := by fun_prop
  have hint : IntervalIntegrable (fun φ : ℝ => Real.cos (φ - ψ) * ρ φ)
      MeasureTheory.volume c d := hcos.intervalIntegrable c d
  have hppos : ∀ φ ∈ Set.Ioo c d, 0 < Real.cos (φ - ψ) * ρ φ := by
    intro φ hφ
    have hc1 : -(π / 2) < φ - ψ := by linarith [hφ.1]
    have hc2 : φ - ψ < π / 2 := by linarith [hφ.2]
    exact mul_pos (Real.cos_pos_of_mem_Ioo ⟨hc1, hc2⟩) (hpos φ)
  have hcospos : (0 : ℝ) < ∫ φ in c..d, Real.cos (φ - ψ) * ρ φ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hint hppos hcd
  intro hzero
  have hpt : (fun φ : ℝ => Complex.exp (-(↑ψ : ℂ) * Complex.I)
        * (Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ)))
      = fun φ : ℝ => ((Real.cos (φ - ψ) * ρ φ : ℝ) : ℂ)
          + Complex.I * ((Real.sin (φ - ψ) * ρ φ : ℝ) : ℂ) := by
    funext φ
    have hexp : Complex.exp (-(↑ψ : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I)
        = Complex.exp ((↑(φ - ψ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← mul_assoc, hexp, Complex.exp_mul_I]
    push_cast
    ring
  have hI1 : IntervalIntegrable (fun φ : ℝ => ((Real.cos (φ - ψ) * ρ φ : ℝ) : ℂ))
      MeasureTheory.volume c d :=
    (Complex.continuous_ofReal.comp hcos).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun φ : ℝ => Complex.I * ((Real.sin (φ - ψ) * ρ φ : ℝ) : ℂ))
      MeasureTheory.volume c d :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hsin)).intervalIntegrable _ _
  have heq2 : Complex.exp (-(↑ψ : ℂ) * Complex.I)
        * (∫ φ in c..d, Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ))
      = ((∫ φ in c..d, Real.cos (φ - ψ) * ρ φ : ℝ) : ℂ)
          + Complex.I * ((∫ φ in c..d, Real.sin (φ - ψ) * ρ φ : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul, hpt,
      intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  rw [hzero, mul_zero] at heq2
  have hre : (∫ φ in c..d, Real.cos (φ - ψ) * ρ φ) = 0 := by
    have := congrArg Complex.re heq2
    simpa using this.symm
  linarith [hcospos]

/-- *Closed inclination-parametrized curve with positive weight is simple.*
For `ρ : ℝ → ℝ` continuous, `2π`-periodic and strictly positive with vanishing
error vector, the reconstruction `α_ρ` is injective on the period `[0, 2π)`.
(Blueprint `thm:reconstruct_injective`.) -/
theorem injOn_reconstruct_of_closed {ρ : ℝ → ℝ} (hcont : Continuous ρ)
    (hper : Function.Periodic ρ (2 * π)) (hpos : ∀ θ, 0 < ρ θ)
    (hE : errorVector ρ = 0) :
    Set.InjOn (reconstruct ρ) (Set.Ico 0 (2 * π)) := by
  have hg : Continuous fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ) := by
    fun_prop
  have hαper : Function.Periodic (reconstruct ρ) (2 * π) :=
    reconstruct_periodic hcont hper hE
  have hchord : ∀ a b : ℝ,
      (∫ φ in a..b, Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ))
        = reconstruct ρ b - reconstruct ρ a := by
    intro a b
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 a)
      (hg.intervalIntegrable (μ := MeasureTheory.volume) a b)
    rw [reconstruct, reconstruct]
    exact (eq_sub_of_add_eq' hadj)
  have main : ∀ a b : ℝ, 0 ≤ a → a < b → b < 2 * π →
      reconstruct ρ a ≠ reconstruct ρ b := by
    intro a b ha hab hb heq2
    have hA : (∫ φ in a..b, Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ)) = 0 := by
      rw [hchord a b, heq2, sub_self]
    have hB : (∫ φ in b..(a + 2 * π), Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ)) = 0 := by
      rw [hchord b (a + 2 * π)]
      have : reconstruct ρ (a + 2 * π) = reconstruct ρ a := hαper a
      rw [this, heq2, sub_self]
    by_cases hL : b - a ≤ π
    · -- Arc A has length ≤ π.
      exact chord_integral_ne_zero hcont hpos hab hL hA
    · -- Arc B has length 2π − L < π.
      have hL : π < b - a := not_le.mp hL
      have hcd : b < a + 2 * π := by linarith
      have hlen : (a + 2 * π) - b ≤ π := by linarith
      exact chord_integral_ne_zero hcont hpos hcd hlen hB
  intro θ₁ hθ₁ θ₂ hθ₂ heq
  rcases lt_trichotomy θ₁ θ₂ with h | h | h
  · exact absurd heq (main θ₁ θ₂ hθ₁.1 h hθ₂.2)
  · exact h
  · exact absurd heq.symm (main θ₂ θ₁ hθ₂.1 h hθ₁.2)

/-- *Positive-curvature reconstruction is a simple closed curve.* For `ρ`
continuous, `2π`-periodic and strictly positive with `E(ρ) = 0`, the
reconstruction `α_ρ` is a simple closed curve: `2π`-periodic and injective on
`[0, 2π)`. (Blueprint `cor:positive_curvature_implies_simple`.) -/
theorem isSimpleClosed_reconstruct {ρ : ℝ → ℝ} (hcont : Continuous ρ)
    (hper : Function.Periodic ρ (2 * π)) (hpos : ∀ θ, 0 < ρ θ)
    (hE : errorVector ρ = 0) :
    IsSimpleClosed (reconstruct ρ) :=
  ⟨reconstruct_periodic hcont hper hE,
   injOn_reconstruct_of_closed hcont hper hpos hE⟩

end Gluck
