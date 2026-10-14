import Gluck.Curve
import Gluck.Curvature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Reconstruction and the closure condition

Given a positive radius-of-curvature weight `ρ = 1/κ`, the source builds a plane
curve by integrating the unit tangent `e^{iθ}` against `ρ`. This file records
that reconstruction and the precise condition for the resulting curve to close
up.

The *reconstruction curve* is `α_ρ(θ) = ∫₀^θ e^{iφ} ρ(φ) dφ ∈ ℂ`; it begins at
the origin and has velocity `α_ρ'(θ) = e^{iθ} ρ(θ)`. The curve closes up (extends
to a `2π`-periodic curve) exactly when the *error vector*
`E(ρ) = α_ρ(2π) = ∫₀^{2π} e^{iθ} ρ(θ) dθ` vanishes, equivalently when both
closure integrals `C(ρ) = ∫₀^{2π} cos θ ρ(θ) dθ` and
`S(ρ) = ∫₀^{2π} sin θ ρ(θ) dθ` vanish.

-/

namespace Gluck

open scoped Real
open Complex

/-- The *reconstruction curve* of a weight `ρ : ℝ → ℝ` is
`α_ρ(θ) = ∫₀^θ e^{iφ} ρ(φ) dφ ∈ ℂ`, the complex form of the source's
`α(θ) = ∫₀^θ (cos φ, sin φ) dφ / κ(φ)` with `ρ = 1/κ`. It begins at the origin
and has velocity `α_ρ'(θ) = e^{iθ} ρ(θ)`. (Blueprint `def:reconstruct`.) -/
noncomputable def reconstruct (ρ : ℝ → ℝ) (θ : ℝ) : ℂ :=
  ∫ φ in (0 : ℝ)..θ, Complex.exp (φ * Complex.I) * (ρ φ : ℂ)

/-- If `ρ` is continuous then the reconstruction curve `α_ρ` is differentiable
with `α_ρ'(θ) = e^{iθ} ρ(θ)` for all `θ`. (Blueprint `lem:reconstruct_deriv`.) -/
theorem hasDerivAt_reconstruct {ρ : ℝ → ℝ} (hρ : Continuous ρ) (θ : ℝ) :
    HasDerivAt (reconstruct ρ) (Complex.exp (θ * Complex.I) * (ρ θ : ℂ)) θ := by
  have hcont : Continuous fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) * (ρ φ : ℂ) :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
      (Complex.continuous_ofReal.comp hρ)
  exact (hcont.integral_hasStrictDerivAt 0 θ).hasDerivAt

/-- The *error vector* of the weight `ρ` is `E(ρ) = α_ρ(2π) = ∫₀^{2π} e^{iθ} ρ(θ) dθ`.
It measures the failure of the reconstruction curve to close up.
(Blueprint `def:error_vector`.) -/
noncomputable def errorVector (ρ : ℝ → ℝ) : ℂ :=
  reconstruct ρ (2 * π)

end Gluck
