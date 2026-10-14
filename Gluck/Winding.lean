import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic
import ForMathlib.Analysis.Complex.WindingNumber
import Gluck.Euclidean.Closure
import Gluck.Euclidean.Bicircle

/-!
# The winding-number argument (topological core)

This is the analytic core of Gluck's proof.  The general **topological winding
number** of a merely continuous curve (Mathlib only has the holomorphic Cauchy
winding number) lives in `ForMathlib.Analysis.Complex.WindingNumber`
(`Complex.windingNumberAt`), together with its invariance lemmas (congruence,
positive rescaling, the continuous Rouché/Estermann perturbation theorem,
degree additivity) and the planar degree existence principle
(`Complex.exists_eq_of_windingNumberAt_ne_zero`).

This file keeps only the project-facing surface:

* `windingNumberC`, the origin-centred winding number of a nonvanishing loop.
  Its *construction* (covering-space angle lift of the radial normalisation) is
  kept verbatim because `Gluck.Sphere.ConjWinding` replicates it locally and
  bridges with a definitional `rfl`; all its *lemmas* are derived from the
  `Complex.windingNumberAt` API through the bridge
  `windingNumberC_eq_windingNumberAt` (lift uniqueness,
  `Complex.windingNumberAt_eq_div_of_lift`).
* `diskBoundaryLoop` and the unit-disk degree principle
  `exists_zero_of_boundary_winding`.
* The configuration disk (`configSpace`) and the error-map assembly
  (`errorMap_winding_eq_one`, which exhibits the boundary winding `-1 ≠ 0`) —
  the genuinely project-specific π/4-lattice computation, needing the
  invertible-linear-map winding computation and the second-order Taylor bound.

Blueprint: `blueprint/src/chapters/Gluck_Winding.tex` (`thm:existence_of_zero`).
-/

namespace Gluck

open scoped Real unitInterval
open Complex

/-! ## The winding number of a nonvanishing `ℂ`-loop

The four private definitions below (angle lift, winding number of an `S¹`-loop,
radial projection, normalised loop) are the *verbatim* construction underlying
`windingNumberC`.  They are kept — instead of delegating the definition to
`Complex.windingNumberAt 0` — because `Gluck.Sphere.ConjWinding` computes the
winding of the conjugate loop through a local replica of this construction whose
bridge lemma is `rfl`, which pins the definition up to definitional equality.
Everything *provable about* `windingNumberC` is nevertheless derived from the
`Complex.windingNumberAt` API via `windingNumberC_eq_windingNumberAt`. -/

/-- The continuous **angle lift** of a loop `g : [0,1] → S¹`: the path obtained
by lifting `g` along the exponential covering `Circle.exp` starting at a chosen
real preimage of `g 0`.  It satisfies `Circle.exp (angleLift g t) = g t`
(`angleLift_lifts`) and `angleLift g 0` is the chosen base preimage. -/
private noncomputable def angleLift (g : C(I, Circle)) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm

private theorem angleLift_lifts (g : C(I, Circle)) (t : I) :
    Circle.exp (angleLift g t) = g t := by
  have h := Circle.isCoveringMap_exp.liftPath_lifts g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm
  have := congrFun h t
  simpa [angleLift, Function.comp] using this

/-- The **winding number** of a continuous loop `g : [0,1] → S¹` about the
origin: the total angle increment of its lift, normalised by `2π`. -/
private noncomputable def windingNumber (g : C(I, Circle)) : ℝ :=
  (angleLift g 1 - angleLift g 0) / (2 * π)

/-- Radial projection of a nonzero complex number onto the unit circle,
`z ↦ z / ‖z‖`. -/
private noncomputable def circleProj (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), by
    rw [← SetLike.mem_coe, Submonoid.coe_unitSphere, mem_sphere_zero_iff_norm, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.2 hz),
      div_self (norm_pos_iff.2 hz).ne']⟩

/-- The normalised loop of a nonvanishing continuous loop `γ : [0,1] → ℂ`. -/
private noncomputable def normLoop (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) : C(I, Circle) :=
  ⟨fun t => circleProj (γ t) (h t), by
    apply Continuous.subtype_mk
    exact γ.continuous.div
      (Complex.continuous_ofReal.comp (continuous_norm.comp γ.continuous))
      (fun t => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (h t)))⟩

/-- The **winding number of a nonvanishing `ℂ`-loop** `γ` about the origin,
defined via its radial normalisation onto `S¹`. -/
noncomputable def windingNumberC (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) : ℝ :=
  windingNumber (normLoop γ h)

/-- **Bridge**: `windingNumberC` agrees with the general
`Complex.windingNumberAt` about the origin.  The canonical angle lift of the
radial normalisation `t ↦ γ t / ‖γ t‖` is a polar angle lift of `γ` about `0`,
so `Complex.windingNumberAt_eq_div_of_lift` (lift uniqueness) evaluates
`Complex.windingNumberAt 0 γ h` to the very increment defining
`windingNumberC γ h`. -/
private theorem windingNumberC_eq_windingNumberAt (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) :
    windingNumberC γ h = Complex.windingNumberAt 0 γ h := by
  have hlift : ∀ t, γ t - 0
      = (‖γ t - 0‖ : ℂ)
        * Complex.exp ((angleLift (normLoop γ h) t : ℂ) * Complex.I) := by
    intro t
    have hcoe : Complex.exp ((angleLift (normLoop γ h) t : ℂ) * Complex.I)
        = γ t / (‖γ t‖ : ℂ) := by
      rw [← Circle.coe_exp, angleLift_lifts]
      rfl
    have hn : (‖γ t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (h t)
    rw [sub_zero, hcoe]
    field_simp
  rw [Complex.windingNumberAt_eq_div_of_lift h (angleLift (normLoop γ h)) hlift]
  rfl

/-- Winding number of a nonvanishing `ℂ`-loop depends only on its values:
pointwise-equal loops have equal winding number. -/
theorem windingNumberC_congr {γ γ' : C(I, ℂ)} {h : ∀ t, γ t ≠ 0} {h' : ∀ t, γ' t ≠ 0}
    (he : ∀ t, γ t = γ' t) : windingNumberC γ h = windingNumberC γ' h' := by
  rw [windingNumberC_eq_windingNumberAt, windingNumberC_eq_windingNumberAt]
  exact Complex.windingNumberAt_congr he

/-- A constant nonzero complex loop has winding number zero. -/
theorem windingNumberC_const (c : ℂ) (hc : c ≠ 0) :
    windingNumberC (ContinuousMap.const I c)
      (by intro t; rw [ContinuousMap.const_apply]; exact hc) = 0 := by
  rw [windingNumberC_eq_windingNumberAt]
  exact Complex.windingNumberAt_const 0 c (by
    intro t
    rw [ContinuousMap.const_apply]
    exact hc)

/-- A nowhere-zero free homotopy through loops preserves winding number about
the origin. -/
theorem windingNumberC_eq_of_homotopy (γ₀ γ₁ : C(I, ℂ))
    (hγ₀ : ∀ t, γ₀ t ≠ 0) (hγ₁ : ∀ t, γ₁ t ≠ 0)
    (H : C(I × I, ℂ)) (hH : ∀ st, H st ≠ 0)
    (h0 : ∀ t, H (0, t) = γ₀ t) (h1 : ∀ t, H (1, t) = γ₁ t)
    (hloop : ∀ s, H (s, 0) = H (s, 1)) :
    windingNumberC γ₀ hγ₀ = windingNumberC γ₁ hγ₁ := by
  rw [windingNumberC_eq_windingNumberAt, windingNumberC_eq_windingNumberAt]
  exact Complex.windingNumberAt_eq_of_homotopy 0 γ₀ γ₁ hγ₀ hγ₁ H hH h0 h1 hloop

/-! ## The boundary loop of a map on the closed unit disk -/

/-- The boundary loop `t ↦ F(e^{2π i t})` of a function `F` continuous on the
closed unit disk, as a continuous map `[0,1] → ℂ`. -/
noncomputable def diskBoundaryLoop (F : ℂ → ℂ)
    (hF : ContinuousOn F (Metric.closedBall 0 1)) : C(I, ℂ) :=
  ⟨fun t => F (Circle.exp (2 * π * t)), by
    apply hF.comp_continuous
    · exact continuous_subtype_val.comp
        (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val))
    · intro t
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [Circle.norm_coe]⟩

/-- The boundary loop never vanishes when `F ≠ 0` on the boundary circle. -/
theorem diskBoundaryLoop_ne_zero (F : ℂ → ℂ)
    (hF : ContinuousOn F (Metric.closedBall 0 1))
    (hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, F z ≠ 0) (t : I) :
    diskBoundaryLoop F hF t ≠ 0 := by
  apply hbd
  rw [mem_sphere_zero_iff_norm, Circle.norm_coe]

/-! ## The planar degree principle -/

/-- **Nonzero boundary winding forces an interior zero.**  If `F` is continuous
on the closed unit disk, nonzero on the boundary circle, and its boundary loop
has nonzero winding number about the origin, then `F` has a zero in the open
disk.  This is `Complex.exists_eq_of_windingNumberAt_ne_zero` (center `0`,
radius `1`, value `0`), transported along the pointwise identification of
`diskBoundaryLoop` with `Complex.circleLoop` (`e^{2πit} = circleMap 0 1 (2πt)`). -/
theorem exists_zero_of_boundary_winding (F : ℂ → ℂ)
    (hF : ContinuousOn F (Metric.closedBall 0 1))
    (hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, F z ≠ 0)
    (hw : windingNumberC (diskBoundaryLoop F hF)
      (diskBoundaryLoop_ne_zero F hF hbd) ≠ 0) :
    ∃ z ∈ Metric.ball (0 : ℂ) 1, F z = 0 := by
  have key : ∀ (hFs : ContinuousOn F (Metric.sphere 0 |(1 : ℝ)|))
      (hne : ∀ t, Complex.circleLoop F 0 1 hFs t ≠ 0),
      Complex.windingNumberAt 0 (Complex.circleLoop F 0 1 hFs) hne
        = windingNumberC (diskBoundaryLoop F hF) (diskBoundaryLoop_ne_zero F hF hbd) := by
    intro hFs hne
    rw [windingNumberC_eq_windingNumberAt]
    refine Complex.windingNumberAt_congr fun t => ?_
    change F (circleMap 0 1 (2 * π * (t : ℝ)))
      = F ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)
    congr 1
    simp [circleMap, Circle.coe_exp]
  refine Complex.exists_eq_of_windingNumberAt_ne_zero F 0 one_pos 0 hF hbd ?_
  rw [key]
  exact hw

/-! ## Perturbation and scaling invariance of the winding number -/

/-- **Perturbation stability of the `ℂ`-winding number.**  If `γ` and `γ'` are
loops (`γ 0 = γ 1`, `γ' 0 = γ' 1`) that are nowhere zero and `γ'` is a *small*
perturbation of `γ` in the sense `‖γ' t − γ t‖ < ‖γ t‖` for all `t`, then they
have the same winding number.  One-sided smallness implies the symmetric
Estermann hypothesis, so this is the continuous Rouché theorem
`Complex.windingNumberAt_eq_of_norm_sub_lt` about `0`. -/
theorem windingNumberC_eq_of_perturb (γ γ' : C(I, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hγ' : ∀ t, γ' t ≠ 0)
    (hloopγ : γ 0 = γ 1) (hloopγ' : γ' 0 = γ' 1)
    (hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t‖) :
    windingNumberC γ hγ = windingNumberC γ' hγ' := by
  rw [windingNumberC_eq_windingNumberAt, windingNumberC_eq_windingNumberAt]
  have hpert' : ∀ t, ‖γ' t - γ t‖ < ‖γ t - 0‖ + ‖γ' t - 0‖ := fun t => by
    rw [sub_zero, sub_zero]
    exact (hpert t).trans_le (le_add_of_nonneg_right (norm_nonneg _))
  exact Complex.windingNumberAt_eq_of_norm_sub_lt 0 γ γ' hloopγ hloopγ' hpert'

/-- **Positive-scalar-field invariance of the `ℂ`-winding number.**  Let `γ` be a
nowhere-zero loop and `c` a continuous loop of *strictly positive* reals.  Then
the scaled loop `t ↦ c t · γ t` is nowhere zero and has the same winding number as
`γ` (`Complex.windingNumberAt_pos_smul` about `0`; the loop hypotheses are kept
for signature compatibility but are not needed — the direction fields agree on
the nose).  It is what lets a positive configuration-dependent prefactor
`c(z)=1/λ(z)` be stripped from the clean arc-length error map (blueprint
`lem:winding_number_c_pos_scalar_field`). -/
theorem windingNumberC_posScalarField (c : C(I, ℝ)) (hc : ∀ t, 0 < c t)
    (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0)
    (_hloopγ : γ 0 = γ 1) (_hloopc : c 0 = c 1) :
    windingNumberC ⟨fun t => (c t : ℂ) * γ t,
        (Complex.continuous_ofReal.comp c.continuous).mul γ.continuous⟩
      (fun t => mul_ne_zero (by exact_mod_cast (hc t).ne') (hγ t)) = windingNumberC γ hγ := by
  rw [windingNumberC_eq_windingNumberAt, windingNumberC_eq_windingNumberAt]
  refine Eq.trans (Complex.windingNumberAt_congr fun t => ?_)
    (Complex.windingNumberAt_pos_smul 0 c hc γ hγ)
  change (c t : ℂ) * γ t = 0 + c t • (γ t - 0)
  rw [zero_add, sub_zero, Complex.real_smul]

/-! ## The reverse once-around loop (winding number `-1`) -/

/-- The reverse unit-circle parametrization `t ↦ e^{-2π i t}`, as a nonvanishing
`ℂ`-loop. -/
private noncomputable def negCircleExpLoop : C(I, ℂ) :=
  ⟨fun t => Complex.exp (((-(2 * π * (t : ℝ)) : ℝ) : ℂ) * Complex.I), by fun_prop⟩

/-- `negCircleExpLoop` is nowhere zero (the exponential never vanishes). -/
private theorem negCircleExpLoop_ne (t : I) : negCircleExpLoop t ≠ 0 :=
  Complex.exp_ne_zero _

/-- The reverse unit-circle parametrization has winding number `-1`
(`Complex.windingNumberAt_exp_int_mul` with `n = -1`). -/
private theorem windingNumberC_negCircleExp :
    windingNumberC negCircleExpLoop negCircleExpLoop_ne = -1 := by
  rw [windingNumberC_eq_windingNumberAt]
  calc Complex.windingNumberAt 0 negCircleExpLoop negCircleExpLoop_ne
      = Complex.windingNumberAt 0
          ⟨fun t : I => Complex.exp ((2 * π * ((-1 : ℤ) : ℝ) * (t : ℝ) : ℝ) * Complex.I),
            by fun_prop⟩
          (fun _ => Complex.exp_ne_zero _) :=
        Complex.windingNumberAt_congr fun t => by
          change Complex.exp (((-(2 * π * (t : ℝ)) : ℝ) : ℂ) * Complex.I)
            = Complex.exp (((2 * π * ((-1 : ℤ) : ℝ) * (t : ℝ) : ℝ) : ℂ) * Complex.I)
          congr 1
          push_cast
          ring
    _ = ((-1 : ℤ) : ℝ) := Complex.windingNumberAt_exp_int_mul (-1)
    _ = -1 := by norm_num

/-- **Scaling-invariance of the `ℂ`-winding number.**  Multiplying a nonvanishing
loop by a fixed nonzero constant `c` does not change its winding number
(`Complex.windingNumberAt_const_mul`). -/
private theorem windingNumberC_const_mul (c : ℂ) (hc : c ≠ 0) (γ : C(I, ℂ)) (h : ∀ t, γ t ≠ 0) :
    windingNumberC ⟨fun t => c * γ t, continuous_const.mul γ.continuous⟩
        (fun t => mul_ne_zero hc (h t)) = windingNumberC γ h := by
  rw [windingNumberC_eq_windingNumberAt, windingNumberC_eq_windingNumberAt]
  exact Eq.trans (Complex.windingNumberAt_congr fun t => rfl)
    (Complex.windingNumberAt_const_mul c hc γ h)

/-! ## Discrete research compatibility: conjugation and lift computation -/

/-- A continuous real-valued function on the connected interval `[0,1]` that
takes only integer values is constant (it cannot jump between integers without
hitting a non-integer, contradicting the intermediate value theorem). -/
private theorem int_valued_eq {q : C(I, ℝ)} (hq : ∀ t, ∃ m : ℤ, q t = (m : ℝ))
    (a b : I) : q a = q b := by
  rcases lt_trichotomy (q a) (q b) with h | h | h
  · exfalso
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have hmab : ma < mb := by
      have hh := h; rw [hma, hmb] at hh; exact_mod_cast hh
    have hv1 : q a ≤ (ma : ℝ) + 1 / 2 := by rw [hma]; linarith
    have hv2 : (ma : ℝ) + 1 / 2 ≤ q b := by
      rw [hmb]; have : (ma : ℝ) + 1 ≤ (mb : ℝ) := by exact_mod_cast hmab
      linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ a b q.continuous ⟨hv1, hv2⟩
    obtain ⟨m, hm⟩ := hq t
    rw [hm] at ht
    have hcontra : (2 * m : ℤ) = 2 * ma + 1 := by
      have h2 : (2 : ℝ) * (m : ℝ) = 2 * (ma : ℝ) + 1 := by linarith
      exact_mod_cast h2
    omega
  · exact h
  · exfalso
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have hmab : mb < ma := by
      have hh := h; rw [hma, hmb] at hh; exact_mod_cast hh
    have hv1 : q b ≤ (mb : ℝ) + 1 / 2 := by rw [hmb]; linarith
    have hv2 : (mb : ℝ) + 1 / 2 ≤ q a := by
      rw [hma]; have : (mb : ℝ) + 1 ≤ (ma : ℝ) := by exact_mod_cast hmab
      linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ b a q.continuous ⟨hv1, hv2⟩
    obtain ⟨m, hm⟩ := hq t
    rw [hm] at ht
    have hcontra : (2 * m : ℤ) = 2 * mb + 1 := by
      have h2 : (2 : ℝ) * (m : ℝ) = 2 * (mb : ℝ) + 1 := by linarith
      exact_mod_cast h2
    omega

/-- The winding number can be computed from *any* continuous angle lift `φ` of
the loop, not just the canonical one: if `Circle.exp (φ t) = g t` for all `t`,
then `windingNumber g = (φ 1 − φ 0) / 2π`.  Two lifts of the same loop differ by
a continuous integer multiple of `2π`, hence by a constant, so the increment is
independent of the choice. -/
private theorem windingNumber_eq_div_of_lift (g : C(I, Circle)) (φ : C(I, ℝ))
    (hφ : ∀ t, Circle.exp (φ t) = g t) :
    windingNumber g = (φ 1 - φ 0) / (2 * π) := by
  have hψ : ∀ t, Circle.exp (angleLift g t) = g t := angleLift_lifts g
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hcont : Continuous fun t : I => (φ t - angleLift g t) / (2 * π) :=
    (φ.continuous.sub (angleLift g).continuous).div_const _
  set q' : C(I, ℝ) := ⟨fun t => (φ t - angleLift g t) / (2 * π), hcont⟩ with hq'def
  have hq'int : ∀ t, ∃ m : ℤ, q' t = (m : ℝ) := by
    intro t
    have hee : Circle.exp (φ t) = Circle.exp (angleLift g t) := (hφ t).trans (hψ t).symm
    rw [Circle.exp_eq_exp] at hee
    obtain ⟨m, hm⟩ := hee
    refine ⟨m, ?_⟩
    change (φ t - angleLift g t) / (2 * π) = (m : ℝ)
    rw [hm]; field_simp; ring
  have hend := int_valued_eq hq'int 0 1
  have hkey : φ 0 - angleLift g 0 = φ 1 - angleLift g 1 := by
    have h2 := hend
    simp only [hq'def, ContinuousMap.coe_mk] at h2
    rw [div_eq_div_iff h2pi h2pi] at h2
    exact mul_right_cancel₀ h2pi h2
  rw [windingNumber]
  have hdiff : φ 1 - φ 0 = angleLift g 1 - angleLift g 0 := by linarith
  rw [hdiff]

/-- Pointwise inversion reverses the winding number of a circle loop. -/
private theorem windingNumber_inv (g : C(I, Circle)) :
    windingNumber g⁻¹ = -windingNumber g := by
  let φ : C(I, ℝ) := -angleLift g
  have hlift : ∀ t : I, Circle.exp (φ t) = (g⁻¹) t := by
    intro t
    change Circle.exp (-angleLift g t) = (g t)⁻¹
    rw [Circle.exp_neg, angleLift_lifts]
  rw [windingNumber_eq_div_of_lift g⁻¹ φ hlift, windingNumber]
  simp only [φ, ContinuousMap.neg_apply]
  ring

/-- Pointwise complex conjugation of a continuous loop. -/
noncomputable def conjugateLoop (γ : C(I, ℂ)) : C(I, ℂ) :=
  ⟨fun t => (starRingEnd ℂ) (γ t), Complex.continuous_conj.comp γ.continuous⟩

/-- The conjugate of a nowhere-zero loop is nowhere zero. -/
theorem conjugateLoop_ne_zero (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0) (t : I) :
    conjugateLoop γ t ≠ 0 := by
  simpa [conjugateLoop] using (star_ne_zero.mpr (hγ t))

/-- Complex conjugation reverses the winding number of a nowhere-zero loop. -/
theorem windingNumberC_conjugateLoop (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0) :
    windingNumberC (conjugateLoop γ) (conjugateLoop_ne_zero γ hγ) =
      -windingNumberC γ hγ := by
  have hnorm :
      normLoop (conjugateLoop γ) (conjugateLoop_ne_zero γ hγ) =
        (normLoop γ hγ)⁻¹ := by
    apply ContinuousMap.ext
    intro t
    change circleProj ((starRingEnd ℂ) (γ t))
      (conjugateLoop_ne_zero γ hγ t) = (circleProj (γ t) (hγ t))⁻¹
    apply Subtype.ext
    rw [Circle.coe_inv_eq_conj]
    change (starRingEnd ℂ) (γ t) / (‖(starRingEnd ℂ) (γ t)‖ : ℂ) =
      (starRingEnd ℂ) (γ t / (‖γ t‖ : ℂ))
    rw [map_div₀, RCLike.norm_conj, Complex.conj_ofReal]
  rw [windingNumberC, hnorm, windingNumber_inv, windingNumberC]

/-! ## The configuration disk -/

/-- The **configuration disk** (blueprint `def:configuration_space`): the explicit
affine two-parameter family of four breakpoints `(θ₁,θ₂,θ₃,θ₄)` over the closed
unit disk `{(x,y) : x²+y² ≤ 1}`.  The two leading breakpoints vary with radius
`δ`; the trailing two are pinned.  At the centre `(0,0)` it is the canonical
equally-spaced bicircle `(π/4, 3π/4, 5π/4, 7π/4)`. -/
noncomputable def configSpace (δ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (π / 4 + δ * p.1, 3 * π / 4 + δ * p.2, 5 * π / 4, 7 * π / 4)

/-- On the closed unit disk (recorded here through `|x| ≤ 1`, `|y| ≤ 1`, which
follow from `x²+y² ≤ 1`), with `0 < δ ≤ π/8`, the four breakpoints satisfy the
strict order constraint `0 < θ₁ < θ₂ < θ₃ < θ₄ < θ₁ + 2π`. -/
private theorem configSpace_ordered (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8)
    (p : ℝ × ℝ) (hx : |p.1| ≤ 1) (hy : |p.2| ≤ 1) :
    0 < (configSpace δ p).1 ∧ (configSpace δ p).1 < (configSpace δ p).2.1 ∧
    (configSpace δ p).2.1 < (configSpace δ p).2.2.1 ∧
    (configSpace δ p).2.2.1 < (configSpace δ p).2.2.2 ∧
    (configSpace δ p).2.2.2 < (configSpace δ p).1 + 2 * π := by
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hdx2 : δ * p.1 ≤ π / 8 := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 1 - p.1)]
  have hdx1 : -(π / 8) ≤ δ * p.1 := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ p.1 + 1)]
  have hdy2 : δ * p.2 ≤ π / 8 := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ 1 - p.2)]
  have hdy1 : -(π / 8) ≤ δ * p.2 := by nlinarith [mul_nonneg hδ.le (by linarith : (0:ℝ) ≤ p.2 + 1)]
  simp only [configSpace]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-! ## The error map and its boundary winding -/

/-- The **error map** (blueprint `lem:error_map_winds_boundary`): the bicircle
error vector of the configuration `configSpace δ (z.re, z.im)`.  The four
breakpoints are `(π/4 + δ·z.re, 3π/4 + δ·z.im, 5π/4, 7π/4)` (the explicit
components of `configSpace δ (z.re, z.im)`). -/
noncomputable def errorMap (a b δ : ℝ) (z : ℂ) : ℂ :=
  bicircleErrorVector a b (π / 4 + δ * z.re) (3 * π / 4 + δ * z.im) (5 * π / 4) (7 * π / 4)

/-- For `‖z‖ ≤ 1` and `0 < δ ≤ π/8`, the four breakpoints of `errorMap` satisfy
the order constraints required by `bicircleErrorVector_eq`. -/
private theorem errorMap_order (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (0 : ℝ) ≤ π / 4 + δ * z.re ∧ π / 4 + δ * z.re < 3 * π / 4 + δ * z.im ∧
    3 * π / 4 + δ * z.im < 5 * π / 4 ∧ 5 * π / 4 < 7 * π / 4 ∧ (7 * π / 4 : ℝ) < 2 * π := by
  have hpi : 0 < π := Real.pi_pos
  have hx : |z.re| ≤ 1 := le_trans (Complex.abs_re_le_norm z) hz
  have hy : |z.im| ≤ 1 := le_trans (Complex.abs_im_le_norm z) hz
  obtain ⟨h0, h12, h23, _, _⟩ := configSpace_ordered δ hδ hδ' (z.re, z.im) hx hy
  simp only [configSpace] at h0 h12 h23
  exact ⟨h0.le, h12, h23, by linarith, by linarith⟩

/-- Closed form of the error map on the closed unit disk: `errorMap z = s · V(z)`
with the nonzero scalar `s = 1/(ib) − 1/(ia)` and chord sum
`V(z) = (e^{iθ₂} − e^{iθ₁}) + (e^{iθ₄} − e^{iθ₃})`, where the trailing
exponential difference `e^{i·7π/4} − e^{i·5π/4} = √2`. -/
private theorem errorMap_eq (a b δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    errorMap a b δ z
      = (1 / (Complex.I * (b : ℂ)) - 1 / (Complex.I * (a : ℂ)))
        * ((Complex.exp (((3 * π / 4 + δ * z.im : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((π / 4 + δ * z.re : ℝ) : ℂ) * Complex.I))
          + (Real.sqrt 2 : ℂ)) := by
  obtain ⟨h1, h12, h23, h34, h4⟩ := errorMap_order δ hδ hδ' hz
  rw [errorMap, bicircleErrorVector_eq a b _ _ _ _ h1 h12 h23 h34 h4]
  congr 1
  have hpin : Complex.exp (((7 * π / 4 : ℝ) : ℂ) * Complex.I)
      - Complex.exp (((5 * π / 4 : ℝ) : ℂ) * Complex.I) = (Real.sqrt 2 : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re]
      rw [show (7 * π / 4 : ℝ) = 2 * π - π / 4 by ring,
          show (5 * π / 4 : ℝ) = π / 4 + π by ring,
          Real.cos_two_pi_sub, Real.cos_add_pi, Real.cos_pi_div_four]
      ring
    · simp only [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.ofReal_im]
      rw [show (7 * π / 4 : ℝ) = 2 * π - π / 4 by ring,
          show (5 * π / 4 : ℝ) = π / 4 + π by ring,
          Real.sin_two_pi_sub, Real.sin_add_pi, Real.sin_pi_div_four]
      ring
  rw [hpin]

/-- `errorMap` is continuous on the closed unit disk (it agrees there with the
manifestly continuous closed form `errorMap_eq`). -/
private theorem continuousOn_errorMap (a b δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) :
    ContinuousOn (errorMap a b δ) (Metric.closedBall 0 1) := by
  apply ContinuousOn.congr
    (f := fun z : ℂ => (1 / (Complex.I * (b : ℂ)) - 1 / (Complex.I * (a : ℂ)))
        * ((Complex.exp (((3 * π / 4 + δ * z.im : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((π / 4 + δ * z.re : ℝ) : ℂ) * Complex.I))
          + (Real.sqrt 2 : ℂ)))
  · fun_prop
  · intro z hz
    have hz' : ‖z‖ ≤ 1 := by simpa [dist_zero_right] using Metric.mem_closedBall.1 hz
    exact errorMap_eq a b δ hδ hδ' hz'

/-- **The second-order remainder identity.**  With `θ₁ = π/4 + δC`, `θ₂ =
3π/4 + δS`, the chord sum `V = (e^{iθ₂} − e^{iθ₁}) + √2` minus its linear model
`L = δ·e^{-iπ/4}·(C − iS)` equals the second-order Taylor remainder
`R = −e^{iπ/4}(e^{iδC} − 1 − iδC) + e^{3iπ/4}(e^{iδS} − 1 − iδS)`.  Pure complex
algebra after substituting `e^{iπ/4}, e^{3iπ/4}, e^{-iπ/4}` and `e^{iθⱼ} =
e^{i(const)}·e^{i(δ·)}`.  (The constant term `−e^{iπ/4} + e^{3iπ/4} + √2 = 0`.) -/
private theorem remainder_identity (δ C S : ℝ) :
    ((Complex.exp (((3 * π / 4 + δ * S : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((π / 4 + δ * C : ℝ) : ℂ) * Complex.I)) + (Real.sqrt 2 : ℂ))
      - (δ : ℂ) * Complex.exp ((↑(-(π / 4)) : ℂ) * Complex.I) * ((C : ℂ) - (S : ℂ) * Complex.I)
    = -Complex.exp ((↑(π / 4) : ℂ) * Complex.I)
        * (Complex.exp ((↑(δ * C) : ℂ) * Complex.I) - 1 - (↑(δ * C) : ℂ) * Complex.I)
      + Complex.exp ((↑(3 * π / 4) : ℂ) * Complex.I)
        * (Complex.exp ((↑(δ * S) : ℂ) * Complex.I) - 1 - (↑(δ * S) : ℂ) * Complex.I) := by
  have e14 : Complex.exp ((↑(π / 4) : ℂ) * Complex.I)
      = (↑(Real.sqrt 2 / 2) : ℂ) + (↑(Real.sqrt 2 / 2) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
  have e34 : Complex.exp ((↑(3 * π / 4) : ℂ) * Complex.I)
      = -(↑(Real.sqrt 2 / 2) : ℂ) + (↑(Real.sqrt 2 / 2) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show (3 * π / 4 : ℝ) = π - π / 4 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring
  have eneg14 : Complex.exp ((↑(-(π / 4)) : ℂ) * Complex.I)
      = (↑(Real.sqrt 2 / 2) : ℂ) - (↑(Real.sqrt 2 / 2) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring
  have hθ1 : Complex.exp (((π / 4 + δ * C : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((↑(π / 4) : ℂ) * Complex.I) * Complex.exp ((↑(δ * C) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hθ2 : Complex.exp (((3 * π / 4 + δ * S : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((↑(3 * π / 4) : ℂ) * Complex.I)
        * Complex.exp ((↑(δ * S) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hθ1, hθ2, e14, e34, eneg14]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] <;> ring

/-- The second-order remainder `R` is bounded by `δ²` on the unit circle
`C² + S² = 1`: `‖R‖ ≤ ‖e^{iπ/4}‖·‖e^{iδC}−1−iδC‖ + ‖e^{3iπ/4}‖·‖e^{iδS}−1−iδS‖
≤ (δC)² + (δS)² = δ²(C²+S²) = δ²`, using the quadratic exponential remainder
bound `Complex.norm_exp_sub_one_sub_id_le`. -/
private theorem remainder_norm_le (δ C S : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8)
    (hCS : C ^ 2 + S ^ 2 = 1) :
    ‖-Complex.exp ((↑(π / 4) : ℂ) * Complex.I)
        * (Complex.exp ((↑(δ * C) : ℂ) * Complex.I) - 1 - (↑(δ * C) : ℂ) * Complex.I)
      + Complex.exp ((↑(3 * π / 4) : ℂ) * Complex.I)
        * (Complex.exp ((↑(δ * S) : ℂ) * Complex.I) - 1 - (↑(δ * S) : ℂ) * Complex.I)‖ ≤ δ ^ 2 := by
  have hpi4 : π < 4 := Real.pi_lt_four
  have hδ1 : δ ≤ 1 := by nlinarith
  have hC1 : C ^ 2 ≤ 1 := by nlinarith [sq_nonneg S]
  have hS1 : S ^ 2 ≤ 1 := by nlinarith [sq_nonneg C]
  have normx : ∀ x : ℝ, ‖(↑x : ℂ) * Complex.I‖ = |x| := by
    intro x; rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hxC : ‖(↑(δ * C) : ℂ) * Complex.I‖ ≤ 1 := by
    rw [normx, abs_mul, abs_of_pos hδ]; nlinarith [abs_nonneg C, sq_abs C, hC1]
  have hxS : ‖(↑(δ * S) : ℂ) * Complex.I‖ ≤ 1 := by
    rw [normx, abs_mul, abs_of_pos hδ]; nlinarith [abs_nonneg S, sq_abs S, hS1]
  have bC := Complex.norm_exp_sub_one_sub_id_le hxC
  have bS := Complex.norm_exp_sub_one_sub_id_le hxS
  rw [normx] at bC bS
  have n14 : ‖Complex.exp ((↑(π / 4) : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have n34 : ‖Complex.exp ((↑(3 * π / 4) : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  calc ‖_‖
      ≤ ‖-Complex.exp ((↑(π / 4) : ℂ) * Complex.I)
            * (Complex.exp ((↑(δ * C) : ℂ) * Complex.I) - 1 - (↑(δ * C) : ℂ) * Complex.I)‖
        + ‖Complex.exp ((↑(3 * π / 4) : ℂ) * Complex.I)
            * (Complex.exp ((↑(δ * S) : ℂ) * Complex.I) - 1 - (↑(δ * S) : ℂ) * Complex.I)‖ :=
        norm_add_le _ _
    _ = ‖Complex.exp ((↑(δ * C) : ℂ) * Complex.I) - 1 - (↑(δ * C) : ℂ) * Complex.I‖
        + ‖Complex.exp ((↑(δ * S) : ℂ) * Complex.I) - 1 - (↑(δ * S) : ℂ) * Complex.I‖ := by
        rw [norm_mul, norm_neg, n14, one_mul, norm_mul, n34, one_mul]
    _ ≤ |δ * C| ^ 2 + |δ * S| ^ 2 := by gcongr
    _ = δ ^ 2 * (C ^ 2 + S ^ 2) := by rw [sq_abs, sq_abs]; ring
    _ = δ ^ 2 := by rw [hCS]; ring

/-- The chord sum `V(z) = (e^{iθ₂} − e^{iθ₁}) + √2` (θ₁ = π/4+δ·z.re,
θ₂ = 3π/4+δ·z.im); this is the bracket in `errorMap_eq`. -/
private noncomputable def Vpart (δ : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp (((3 * π / 4 + δ * z.im : ℝ) : ℂ) * Complex.I)
      - Complex.exp (((π / 4 + δ * z.re : ℝ) : ℂ) * Complex.I)) + (Real.sqrt 2 : ℂ)

/-- The invertible linear model `L(z) = δ·e^{-iπ/4}·(z.re − i·z.im)` of `Vpart`
at the centre. -/
private noncomputable def Lpart (δ : ℝ) (z : ℂ) : ℂ :=
  (δ : ℂ) * Complex.exp ((↑(-(π / 4)) : ℂ) * Complex.I) * ((z.re : ℂ) - (z.im : ℂ) * Complex.I)

/-- On the unit circle, the linear model has norm exactly `δ`. -/
private theorem Lpart_norm (δ : ℝ) (hδ : 0 < δ) {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 = 1) :
    ‖Lpart δ z‖ = δ := by
  rw [Lpart, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hδ]
  have hone : ‖(z.re : ℂ) - (z.im : ℂ) * Complex.I‖ = 1 := by
    rw [sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg, Complex.norm_add_mul_I, neg_sq, hz,
      Real.sqrt_one]
  rw [hone, mul_one]

/-- The key perturbation inequality: on the unit circle, `Vpart` is closer to its
linear model `Lpart` than the linear model is to `0`
(`‖V − L‖ ≤ δ² < δ = ‖L‖`). -/
private theorem pert_lt (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ}
    (hz : z.re ^ 2 + z.im ^ 2 = 1) : ‖Vpart δ z - Lpart δ z‖ < ‖Lpart δ z‖ := by
  have hpi4 : π < 4 := Real.pi_lt_four
  have hδ1 : δ < 1 := by nlinarith
  have hsub : Vpart δ z - Lpart δ z
      = -Complex.exp ((↑(π / 4) : ℂ) * Complex.I)
          * (Complex.exp ((↑(δ * z.re) : ℂ) * Complex.I) - 1 - (↑(δ * z.re) : ℂ) * Complex.I)
        + Complex.exp ((↑(3 * π / 4) : ℂ) * Complex.I)
          * (Complex.exp ((↑(δ * z.im) : ℂ) * Complex.I) - 1 - (↑(δ * z.im) : ℂ) * Complex.I) :=
    remainder_identity δ z.re z.im
  rw [hsub, Lpart_norm δ hδ hz]
  calc ‖_‖ ≤ δ ^ 2 := remainder_norm_le δ z.re z.im hδ hδ' hz
    _ < δ := by nlinarith

/-- On the unit circle, the chord sum `Vpart` is nonzero (it stays within `δ²` of
the radius-`δ` linear model, so its norm is at least `δ − δ² > 0`). -/
private theorem Vpart_ne (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ π / 8) {z : ℂ}
    (hz : z.re ^ 2 + z.im ^ 2 = 1) : Vpart δ z ≠ 0 := by
  have hp := pert_lt δ hδ hδ' hz
  have htri : ‖Lpart δ z‖ - ‖Vpart δ z - Lpart δ z‖ ≤ ‖Vpart δ z‖ := by
    have h := norm_sub_norm_le (Lpart δ z) (Lpart δ z - Vpart δ z)
    have he : Lpart δ z - (Lpart δ z - Vpart δ z) = Vpart δ z := by ring
    rw [he, norm_sub_rev (Lpart δ z) (Vpart δ z)] at h; linarith
  have : 0 < ‖Vpart δ z‖ := by linarith
  exact norm_pos_iff.1 this

/-- Continuity of the chord-sum boundary loop `t ↦ Vpart δ (e^{2π i t})`. -/
private theorem continuous_Vpart_boundary (δ : ℝ) :
    Continuous (fun t : I => Vpart δ (((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ))) := by
  have hz : Continuous (fun t : I => ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)) :=
    continuous_subtype_val.comp
      (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val))
  simp only [Vpart]
  fun_prop

/-- The chord-sum boundary loop `V|_{∂D}` of the error map. -/
private noncomputable def errVloop (δ : ℝ) : C(I, ℂ) :=
  ⟨fun t => Vpart δ (((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)), continuous_Vpart_boundary δ⟩

/-- The error map's boundary loop `s·V|_{∂D}`, as a constant `s` times `errVloop`. -/
private noncomputable def errSVloop (a b δ : ℝ) : C(I, ℂ) :=
  ⟨fun t => (1 / (Complex.I * (b : ℂ)) - 1 / (Complex.I * (a : ℂ))) * errVloop δ t,
    continuous_const.mul (errVloop δ).continuous⟩

/-- The linear-model boundary loop `L|_{∂D} = δ·e^{-iπ/4}·e^{-2π i t}`, as a
constant times `negCircleExpLoop`. -/
private noncomputable def errLloop (δ : ℝ) : C(I, ℂ) :=
  ⟨fun t => ((δ : ℂ) * Complex.exp ((↑(-(π / 4)) : ℂ) * Complex.I)) * negCircleExpLoop t,
    continuous_const.mul negCircleExpLoop.continuous⟩

/-- On the boundary, the linear-model loop equals the linear model `Lpart` of the
boundary point: `errLloop δ t = Lpart δ (e^{2π i t})`. -/
private theorem errLloop_eq_Lpart (δ : ℝ) (t : I) :
    errLloop δ t = Lpart δ (((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)) := by
  have hneg : negCircleExpLoop t
      = ((((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ).re : ℂ)
          - (((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ).im : ℂ) * Complex.I) := by
    change Complex.exp (((-(2 * π * (t : ℝ)) : ℝ) : ℂ) * Complex.I) = _
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  change ((δ : ℂ) * Complex.exp ((↑(-(π / 4)) : ℂ) * Complex.I)) * negCircleExpLoop t = _
  rw [hneg, Lpart]

/-- **The error map winds nontrivially on the boundary** (blueprint
`lem:error_map_winds_boundary`).  For `0 < a`, `0 < b`, `a ≠ b` and
`0 < δ ≤ π/8`, the error map is continuous on the closed unit disk, nonzero on
the boundary circle, and its boundary loop has winding number `-1` (hence
nonzero) about the origin.

The boundary loop `E|_{∂D} = s·V|_{∂D}` (scalar `s = 1/(ib) − 1/(ia) ≠ 0`) is
compared, via the perturbation-stability of the winding number, to its invertible
linear model `L|_{∂D} = δ·e^{-iπ/4}·e^{-2π i t}`: on `∂D` the remainder
`V − L` has norm `≤ δ² < δ = ‖L‖`, so `W(E) = W(V) = W(L) = -1` (the reverse
once-around loop). -/
theorem errorMap_winding_eq_one (a b δ : ℝ) (_ha : 0 < a) (_hb : 0 < b) (hab : a ≠ b)
    (hδ : 0 < δ) (hδ' : δ ≤ π / 8) :
    ∃ (hF : ContinuousOn (errorMap a b δ) (Metric.closedBall 0 1))
      (hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, errorMap a b δ z ≠ 0),
      windingNumberC (diskBoundaryLoop (errorMap a b δ) hF)
        (diskBoundaryLoop_ne_zero (errorMap a b δ) hF hbd) = -1 := by
  have hs : (1 / (Complex.I * (b : ℂ)) - 1 / (Complex.I * (a : ℂ))) ≠ 0 := by
    have hkey : (1 : ℂ) / (Complex.I * (b : ℂ)) - 1 / (Complex.I * (a : ℂ))
        = -Complex.I * (1 / (b : ℂ) - 1 / (a : ℂ)) := by
      rw [one_div, one_div, mul_inv, mul_inv, Complex.inv_I]; ring
    rw [hkey]
    apply mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    rw [sub_ne_zero, one_div, one_div, ne_eq, inv_inj]
    intro h; exact hab (by exact_mod_cast h.symm)
  have hcc : ((δ : ℂ) * Complex.exp ((↑(-(π / 4)) : ℂ) * Complex.I)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hδ.ne') (Complex.exp_ne_zero _)
  have hztcs : ∀ t : I, (((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)).re ^ 2
      + (((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)).im ^ 2 = 1 := by
    intro t
    have h2 := Complex.sq_norm ((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ)
    rw [Circle.norm_coe, Complex.normSq_apply] at h2; nlinarith [h2]
  have hV : ∀ t : I, errVloop δ t ≠ 0 := fun t => Vpart_ne δ hδ hδ' (hztcs t)
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, errorMap a b δ z ≠ 0 := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hcs : z.re ^ 2 + z.im ^ 2 = 1 := by
      have h2 := Complex.sq_norm z
      rw [hz, Complex.normSq_apply] at h2; nlinarith [h2]
    rw [errorMap_eq a b δ hδ hδ' (le_of_eq hz)]
    exact mul_ne_zero hs (Vpart_ne δ hδ hδ' hcs)
  refine ⟨continuousOn_errorMap a b δ hδ hδ', hbd, ?_⟩
  have hloopL : errLloop δ 0 = errLloop δ 1 := by
    change ((δ : ℂ) * _) * negCircleExpLoop 0 = ((δ : ℂ) * _) * negCircleExpLoop 1
    have e0 : negCircleExpLoop 0 = 1 := by
      change Complex.exp (((-(2 * π * ((0 : I) : ℝ)) : ℝ) : ℂ) * Complex.I) = 1
      rw [Set.Icc.coe_zero, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    have e1 : negCircleExpLoop 1 = 1 := by
      change Complex.exp (((-(2 * π * ((1 : I) : ℝ)) : ℝ) : ℂ) * Complex.I) = 1
      rw [Set.Icc.coe_one, mul_one, Complex.ofReal_neg, neg_mul, Complex.exp_neg,
        show ((2 * π : ℝ) : ℂ) * Complex.I = 2 * ↑π * Complex.I by push_cast; ring,
        Complex.exp_two_pi_mul_I, inv_one]
    rw [e0, e1]
  have hloopV : errVloop δ 0 = errVloop δ 1 := by
    change Vpart δ (((Circle.exp (2 * π * ((0 : I) : ℝ)) : Circle) : ℂ))
      = Vpart δ (((Circle.exp (2 * π * ((1 : I) : ℝ)) : Circle) : ℂ))
    have hz0 : ((Circle.exp (2 * π * ((0 : I) : ℝ)) : Circle) : ℂ) = 1 := by norm_num
    have hz1 : ((Circle.exp (2 * π * ((1 : I) : ℝ)) : Circle) : ℂ) = 1 := by
      rw [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]; norm_num
    rw [hz0, hz1]
  have hpert : ∀ t : I, ‖errVloop δ t - errLloop δ t‖ < ‖errLloop δ t‖ := by
    intro t
    rw [errLloop_eq_Lpart δ t]
    change ‖Vpart δ _ - Lpart δ _‖ < ‖Lpart δ _‖
    exact pert_lt δ hδ hδ' (hztcs t)
  calc windingNumberC (diskBoundaryLoop (errorMap a b δ) (continuousOn_errorMap a b δ hδ hδ'))
          (diskBoundaryLoop_ne_zero (errorMap a b δ) _ hbd)
      = windingNumberC (errSVloop a b δ) (fun t => mul_ne_zero hs (hV t)) := by
        apply windingNumberC_congr
        intro t
        change errorMap a b δ (((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ))
          = (1 / (Complex.I * (b : ℂ)) - 1 / (Complex.I * (a : ℂ)))
              * Vpart δ (((Circle.exp (2 * π * (t : ℝ)) : Circle) : ℂ))
        exact errorMap_eq a b δ hδ hδ' (le_of_eq (Circle.norm_coe _))
    _ = windingNumberC (errVloop δ) hV :=
        windingNumberC_const_mul _ hs (errVloop δ) hV
    _ = windingNumberC (errLloop δ)
          (fun t => mul_ne_zero hcc (negCircleExpLoop_ne t)) :=
        (windingNumberC_eq_of_perturb (errLloop δ) (errVloop δ)
          (fun t => mul_ne_zero hcc (negCircleExpLoop_ne t)) hV hloopL hloopV hpert).symm
    _ = -1 :=
        (windingNumberC_const_mul _ hcc negCircleExpLoop negCircleExpLoop_ne).trans
          windingNumberC_negCircleExp

/-! ## Explicit real-linear model loops -/

/-- The scaled forward once-around exponential loop. -/
noncomputable def expLoop (c : ℂ) : C(I, ℂ) :=
  ⟨fun t ↦ c * Complex.exp (((2 * π * (t : ℝ) : ℝ) : ℂ) * Complex.I), by fun_prop⟩

@[simp]
theorem expLoop_apply (c : ℂ) (t : I) :
    expLoop c t = c * Complex.exp (((2 * π * (t : ℝ) : ℝ) : ℂ) * Complex.I) := rfl

theorem expLoop_norm (c : ℂ) (t : I) : ‖expLoop c t‖ = ‖c‖ := by
  rw [expLoop_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem expLoop_ne_zero (c : ℂ) (hc : c ≠ 0) (t : I) : expLoop c t ≠ 0 := by
  rw [expLoop_apply]
  exact mul_ne_zero hc (Complex.exp_ne_zero _)

@[simp]
theorem expLoop_zero (c : ℂ) : expLoop c 0 = c := by
  rw [expLoop_apply]
  norm_num

@[simp]
theorem expLoop_one (c : ℂ) : expLoop c 1 = c := by
  have h : (((2 * π * ((1 : I) : ℝ) : ℝ)) : ℂ) * Complex.I =
      2 * (π : ℂ) * Complex.I := by
    rw [Set.Icc.coe_one]
    push_cast
    ring
  rw [expLoop_apply, h, Complex.exp_two_pi_mul_I, mul_one]

theorem expLoop_loop (c : ℂ) : expLoop c 0 = expLoop c 1 := by simp

theorem windingNumberC_expLoop (c : ℂ) (hc : c ≠ 0) :
    windingNumberC (expLoop c) (expLoop_ne_zero c hc) = 1 := by
  rw [windingNumberC_eq_windingNumberAt]
  let γ : C(I, ℂ) :=
    ⟨fun t ↦ Complex.exp ((2 * π * (1 : ℤ) * (t : ℝ) : ℝ) * Complex.I), by fun_prop⟩
  have hγ : ∀ t, γ t ≠ 0 := fun _ ↦ Complex.exp_ne_zero _
  calc
    Complex.windingNumberAt 0 (expLoop c) (expLoop_ne_zero c hc) =
        Complex.windingNumberAt 0
          ⟨fun t ↦ c * γ t, continuous_const.mul γ.continuous⟩
          (fun t ↦ mul_ne_zero hc (hγ t)) :=
      Complex.windingNumberAt_congr fun t ↦ by simp [γ, expLoop]
    _ = Complex.windingNumberAt 0 γ hγ :=
      Complex.windingNumberAt_const_mul c hc γ hγ
    _ = 1 := by simpa [γ] using Complex.windingNumberAt_exp_int_mul 1

/-- The scaled reverse once-around exponential loop. -/
noncomputable def expLoopRev (c : ℂ) : C(I, ℂ) :=
  ⟨fun t ↦ c * Complex.exp (((-(2 * π * (t : ℝ)) : ℝ) : ℂ) * Complex.I), by fun_prop⟩

@[simp]
theorem expLoopRev_apply (c : ℂ) (t : I) :
    expLoopRev c t =
      c * Complex.exp (((-(2 * π * (t : ℝ)) : ℝ) : ℂ) * Complex.I) := rfl

theorem expLoopRev_norm (c : ℂ) (t : I) : ‖expLoopRev c t‖ = ‖c‖ := by
  rw [expLoopRev_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem expLoopRev_ne_zero (c : ℂ) (hc : c ≠ 0) (t : I) : expLoopRev c t ≠ 0 := by
  rw [expLoopRev_apply]
  exact mul_ne_zero hc (Complex.exp_ne_zero _)

@[simp]
theorem expLoopRev_zero (c : ℂ) : expLoopRev c 0 = c := by
  rw [expLoopRev_apply]
  norm_num

@[simp]
theorem expLoopRev_one (c : ℂ) : expLoopRev c 1 = c := by
  have h : (((-(2 * π * ((1 : I) : ℝ)) : ℝ)) : ℂ) * Complex.I =
      -(2 * (π : ℂ) * Complex.I) := by
    rw [Set.Icc.coe_one]
    push_cast
    ring
  rw [expLoopRev_apply, h, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]

theorem expLoopRev_loop (c : ℂ) : expLoopRev c 0 = expLoopRev c 1 := by
  rw [expLoopRev_zero, expLoopRev_one]

theorem windingNumberC_expLoopRev (c : ℂ) (hc : c ≠ 0) :
    windingNumberC (expLoopRev c) (expLoopRev_ne_zero c hc) = -1 := by
  rw [windingNumberC_eq_windingNumberAt]
  let γ : C(I, ℂ) :=
    ⟨fun t ↦ Complex.exp ((2 * π * (-1 : ℤ) * (t : ℝ) : ℝ) * Complex.I), by fun_prop⟩
  have hγ : ∀ t, γ t ≠ 0 := fun _ ↦ Complex.exp_ne_zero _
  calc
    Complex.windingNumberAt 0 (expLoopRev c) (expLoopRev_ne_zero c hc) =
        Complex.windingNumberAt 0
          ⟨fun t ↦ c * γ t, continuous_const.mul γ.continuous⟩
          (fun t ↦ mul_ne_zero hc (hγ t)) :=
      Complex.windingNumberAt_congr fun t ↦ by simp [γ, expLoopRev]
    _ = Complex.windingNumberAt 0 γ hγ :=
      Complex.windingNumberAt_const_mul c hc γ hγ
    _ = -1 := by simpa [γ] using Complex.windingNumberAt_exp_int_mul (-1)

/-- The boundary loop of the real-linear map `z ↦ a z + b z̄`. -/
noncomputable def linearLoop (a b : ℂ) : C(I, ℂ) :=
  ⟨fun t ↦ expLoop a t + expLoopRev b t,
    (expLoop a).continuous.add (expLoopRev b).continuous⟩

@[simp]
theorem linearLoop_apply (a b : ℂ) (t : I) :
    linearLoop a b t =
      a * Complex.exp (((2 * π * (t : ℝ) : ℝ) : ℂ) * Complex.I) +
      b * Complex.exp (((-(2 * π * (t : ℝ)) : ℝ) : ℂ) * Complex.I) := rfl

theorem linearLoop_ne_zero (a b : ℂ) (hab : ‖a‖ ≠ ‖b‖) (t : I) : linearLoop a b t ≠ 0 := by
  intro h
  apply hab
  have hx : expLoop a t = -(expLoopRev b t) := by
    change expLoop a t + expLoopRev b t = 0 at h
    linear_combination h
  have hn := congrArg norm hx
  rwa [norm_neg, expLoop_norm, expLoopRev_norm] at hn

@[simp]
theorem linearLoop_zero (a b : ℂ) : linearLoop a b 0 = a + b := by
  change expLoop a 0 + expLoopRev b 0 = a + b
  simp

@[simp]
theorem linearLoop_one (a b : ℂ) : linearLoop a b 1 = a + b := by
  change expLoop a 1 + expLoopRev b 1 = a + b
  rw [expLoop_one, expLoopRev_one]

theorem linearLoop_loop (a b : ℂ) : linearLoop a b 0 = linearLoop a b 1 := by
  rw [linearLoop_zero, linearLoop_one]

theorem windingNumberC_linearLoop (a b : ℂ) (hab : ‖a‖ ≠ ‖b‖) :
    windingNumberC (linearLoop a b) (linearLoop_ne_zero a b hab) =
      if ‖b‖ < ‖a‖ then 1 else -1 := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · rw [if_neg (asymm hlt)]
    have hb : b ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (norm_nonneg a) hlt)
    have hpert : ∀ t : I, ‖linearLoop a b t - expLoopRev b t‖ < ‖expLoopRev b t‖ := by
      intro t
      have he : linearLoop a b t - expLoopRev b t = expLoop a t := by
        change expLoop a t + expLoopRev b t - expLoopRev b t = expLoop a t
        ring
      rw [he, expLoop_norm, expLoopRev_norm]
      exact hlt
    have h := windingNumberC_eq_of_perturb (expLoopRev b) (linearLoop a b)
      (expLoopRev_ne_zero b hb) (linearLoop_ne_zero a b hab)
      (expLoopRev_loop b) (linearLoop_loop a b) hpert
    rw [← h, windingNumberC_expLoopRev b hb]
  · rw [if_pos hgt]
    have ha : a ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt (norm_nonneg b) hgt)
    have hpert : ∀ t : I, ‖linearLoop a b t - expLoop a t‖ < ‖expLoop a t‖ := by
      intro t
      have he : linearLoop a b t - expLoop a t = expLoopRev b t := by
        change expLoop a t + expLoopRev b t - expLoop a t = expLoopRev b t
        ring
      rw [he, expLoopRev_norm, expLoop_norm]
      exact hgt
    have h := windingNumberC_eq_of_perturb (expLoop a) (linearLoop a b)
      (expLoop_ne_zero a ha) (linearLoop_ne_zero a b hab)
      (expLoop_loop a) (linearLoop_loop a b) hpert
    rw [← h, windingNumberC_expLoop a ha]

end Gluck
