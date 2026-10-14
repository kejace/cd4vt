import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Plane curves and signed curvature

This file sets up the elementary differential geometry of plane curves used
throughout the Gluck project. A plane curve is modelled as a map
`γ : ℝ → ℂ`, identifying the Euclidean plane `ℝ²` with the complex plane `ℂ`;
this matches the complex notation `e^{iθ}` used in the source for the
reconstruction integral.

-/

namespace Gluck

open scoped Real

/-- A map `γ : ℝ → ℂ` is a *regular curve* if it is twice continuously
differentiable and its velocity never vanishes. (Blueprint `def:is_regular`.) -/
def IsRegular (γ : ℝ → ℂ) : Prop :=
  ContDiff ℝ 2 γ ∧ ∀ t, deriv γ t ≠ 0

/-- The *signed curvature* of `γ : ℝ → ℂ` at `t`, given by the standard
parametrization-invariant formula
`(Re γ' · Im γ'' − Im γ' · Re γ'') / ‖γ'‖³`. (Blueprint `def:signed_curvature`.) -/
noncomputable def signedCurvature (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  ((deriv γ t).re * (deriv (deriv γ) t).im
      - (deriv γ t).im * (deriv (deriv γ) t).re) / ‖deriv γ t‖ ^ 3

/-- A curve `γ : ℝ → ℂ` is *closed* if it is `2π`-periodic.
(Blueprint `def:is_closed_curve`.) -/
def IsClosedCurve (γ : ℝ → ℂ) : Prop :=
  Function.Periodic γ (2 * π)

/-- A curve `γ` is a *simple closed curve* if it is closed and injective on a
fundamental period `[0, 2π)`. (Blueprint `def:is_simple_closed`.) -/
def IsSimpleClosed (γ : ℝ → ℂ) : Prop :=
  IsClosedCurve γ ∧ Set.InjOn γ (Set.Ico 0 (2 * π))

/-- A regular curve `γ` is *convex* if its signed curvature is strictly positive
everywhere. (Blueprint `def:is_convex_curve`.) -/
def IsConvexCurve (γ : ℝ → ℂ) : Prop :=
  IsRegular γ ∧ ∀ t, 0 < signedCurvature γ t

/-- A curve `γ : ℝ → ℂ` *realizes the curvature function* `κ : ℝ → ℝ` if it is
`C¹`, regular (its velocity never vanishes), and there is a *differentiable*
tangent-angle function `φ : ℝ → ℝ` such that, for all `t`,
`γ'(t) = ‖γ'(t)‖ · e^{i φ(t)}` and `φ'(t) = κ(t) · ‖γ'(t)‖`.

The first equation says `φ(t)` is the angle of inclination of the unit tangent;
the second is the source's defining relation `dθ/ds = κ` rewritten via the chain
rule with arc length `s`, `ds/dt = ‖γ'(t)‖`. Unlike `signedCurvature`, this is a
`C¹` notion (only the *angle* `φ`, not `γ`, needs to be differentiable), so it is
meaningful for the curve realized from a merely continuous curvature function.
(Blueprint `def:realizes_curvature`.) -/
def RealizesCurvature (γ : ℝ → ℂ) (κ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 γ ∧ (∀ t, deriv γ t ≠ 0) ∧
    ∃ φ : ℝ → ℝ, Differentiable ℝ φ ∧
      (∀ t, deriv γ t = (↑‖deriv γ t‖ : ℂ) * Complex.exp (↑(φ t) * Complex.I)) ∧
      (∀ t, deriv φ t = κ t * ‖deriv γ t‖)

/-- If `γ` is `C²`, regular and realizes `κ` (in the intrinsic sense
`RealizesCurvature`), then its `signedCurvature` equals `κ` everywhere. This is
the bridge between the intrinsic notion and the deriv²-formula on `C²` data.
(Blueprint `lem:realizes_curvature_signedCurvature`.) -/
theorem signedCurvature_of_realizesCurvature {γ : ℝ → ℂ} {κ : ℝ → ℝ}
    (hγ2 : ContDiff ℝ 2 γ) (hreg : ∀ t, deriv γ t ≠ 0)
    (hrc : RealizesCurvature γ κ) :
    ∀ t, signedCurvature γ t = κ t := by
  obtain ⟨_, _, φ, hφ, htan, hcurv⟩ := hrc
  intro t
  set v : ℝ → ℝ := fun s => ‖deriv γ s‖ with hv_def
  have hv_pos : 0 < v t := norm_pos_iff.mpr (hreg t)
  have hd1 : deriv γ t = (↑(v t) : ℂ) * Complex.exp (↑(φ t) * Complex.I) := htan t
  have hgeq : deriv γ = fun s => (↑(v s) : ℂ) * Complex.exp (↑(φ s) * Complex.I) := by
    funext s; exact htan s
  have hdγ_diff : DifferentiableAt ℝ (deriv γ) t := hγ2.differentiable_deriv_two t
  have hv_diff : DifferentiableAt ℝ v t := hdγ_diff.norm ℂ (hreg t)
  set vd : ℝ := deriv v t with hvd_def
  have hv_hd : HasDerivAt v vd t := hv_diff.hasDerivAt
  have hvc : HasDerivAt (fun s => (↑(v s) : ℂ)) (↑vd : ℂ) t := hv_hd.ofReal_comp
  set pd : ℝ := deriv φ t with hpd_def
  have hφ_hd : HasDerivAt φ pd t := (hφ t).hasDerivAt
  have hI : HasDerivAt (fun s => (↑(φ s) : ℂ) * Complex.I) ((↑pd : ℂ) * Complex.I) t :=
    hφ_hd.ofReal_comp.mul_const Complex.I
  have hexp : HasDerivAt (fun s => Complex.exp ((↑(φ s) : ℂ) * Complex.I))
      (Complex.exp ((↑(φ t) : ℂ) * Complex.I) * ((↑pd : ℂ) * Complex.I)) t := hI.cexp
  have hprod : HasDerivAt (deriv γ)
      ((↑vd : ℂ) * Complex.exp ((↑(φ t) : ℂ) * Complex.I)
        + (↑(v t) : ℂ) *
            (Complex.exp ((↑(φ t) : ℂ) * Complex.I) * ((↑pd : ℂ) * Complex.I))) t := by
    rw [hgeq]; exact hvc.mul hexp
  have hsecond : deriv (deriv γ) t =
      (↑vd : ℂ) * Complex.exp ((↑(φ t) : ℂ) * Complex.I)
        + (↑(v t) : ℂ) *
            (Complex.exp ((↑(φ t) : ℂ) * Complex.I) * ((↑pd : ℂ) * Complex.I)) := hprod.deriv
  have he_re : (Complex.exp (↑(φ t) * Complex.I)).re = Real.cos (φ t) :=
    Complex.exp_ofReal_mul_I_re _
  have he_im : (Complex.exp (↑(φ t) * Complex.I)).im = Real.sin (φ t) :=
    Complex.exp_ofReal_mul_I_im _
  have hvel_re : (deriv γ t).re = v t * Real.cos (φ t) := by
    rw [hd1]; simp [Complex.mul_re, he_re, he_im]
  have hvel_im : (deriv γ t).im = v t * Real.sin (φ t) := by
    rw [hd1]; simp [Complex.mul_im, he_re, he_im]
  have hsd_re : (deriv (deriv γ) t).re
      = vd * Real.cos (φ t) - v t * Real.sin (φ t) * pd := by
    rw [hsecond]
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, he_re, he_im]
    ring
  have hsd_im : (deriv (deriv γ) t).im
      = vd * Real.sin (φ t) + v t * Real.cos (φ t) * pd := by
    rw [hsecond]
    simp [Complex.add_im, Complex.mul_re, Complex.mul_im, he_re, he_im]
    ring
  have hpd : pd = κ t * v t := hcurv t
  have hnorm : ‖deriv γ t‖ = v t := rfl
  have hcs : Real.cos (φ t) ^ 2 + Real.sin (φ t) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  unfold signedCurvature
  rw [hvel_re, hvel_im, hsd_re, hsd_im, hnorm, hpd,
    div_eq_iff (pow_ne_zero 3 hv_pos.ne')]
  linear_combination (v t) ^ 3 * κ t * hcs

end Gluck
