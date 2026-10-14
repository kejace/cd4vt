/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Analysis.Normed.Module.Ray
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.Homotopy.Lifting

/-!
# The winding number of a continuous loop in the plane

Mathlib's Cauchy-integral machinery yields winding numbers only for holomorphic/rectifiable
data.  This file constructs the **topological** winding number of a merely continuous curve
`γ : C(I, ℂ)` about a point `w` avoided by it, via covering-space path lifting of the radially
normalised curve `t ↦ (γ t - w) / ‖γ t - w‖` along the exponential covering
`Circle.exp : ℝ → S¹` (`Circle.isCoveringMap_exp`): a continuous angle lift `φ` exists, and the
winding number is the total angle increment `(φ 1 - φ 0) / (2 * π)`.

## Main definitions

* `Complex.windingNumberAt w γ hγ`: the winding number (total argument variation divided by
  `2 * π`, a real number) of the continuous curve `γ` about the point `w`.
* `Complex.circleLoop F c R hF`: the boundary loop `t ↦ F (circleMap c R (2 * π * t))` of a
  function continuous on the circle with center `c` and radius `|R|`, bundled as `C(I, ℂ)`.

## Main results

* `Complex.windingNumberAt_congr`: the winding number depends only on the values of the curve.
* `Complex.windingNumberAt_eq_div_of_lift`: the fundamental **computation rule**: from any
  explicit polar angle lift `γ t - w = ‖γ t - w‖ * exp (φ t * I)`, the winding number is the
  total increment `(φ 1 - φ 0) / (2 * π)`.
* `Complex.windingNumberAt_const`: a constant curve has winding number `0`.
* `Complex.windingNumberAt_mul`: **degree additivity** about the origin: the winding number of
  a pointwise product of nonvanishing curves is the sum of the winding numbers; consequently a
  constant nonzero factor is invisible (`Complex.windingNumberAt_const_mul`).
* `Complex.windingNumberAt_congr_sameRay`: the winding number depends only on the unit
  direction field `t ↦ (γ t - w) / ‖γ t - w‖`: curves whose direction vectors from `w` lie
  pointwise on the same ray have equal winding numbers.
* `Complex.windingNumberAt_pos_smul`: scaling the vector from the center by a continuous
  strictly positive scalar field preserves the winding number.
* `Complex.windingNumberAt_eq_of_norm_sub_lt`: the **continuous Rouché theorem**
  ("dog-on-a-leash", symmetric Estermann form): closed loops with
  `‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖` have equal winding numbers about `w`; both
  nonvanishing conditions are derived from the hypothesis, not assumed
  (`Complex.ne_of_norm_sub_lt_left`, `Complex.ne_of_norm_sub_lt_right`).
* `Complex.windingNumberAt_circleLoop_id`: **normalisation**: the standard parametrisation
  of the circle with center `c` and radius `R > 0` winds exactly once about `c`; the `n`-fold
  cover `t ↦ exp (2 * π * n * t * I)` winds `n` times about the origin
  (`Complex.windingNumberAt_exp_int_mul`).
* `Complex.exists_eq_of_windingNumberAt_ne_zero`: the **existence property of the planar
  Brouwer degree** (Kronecker form): if `F` is continuous on `closedBall c R`, avoids `w` on
  the boundary sphere, and its boundary loop has nonzero winding number about `w`, then `F`
  attains the value `w` in the open ball.

The lemmas `Complex.circleLoop_apply`, `Complex.circleLoop_ne` and `Complex.circleLoop_id_ne`
are the evaluation rule for `Complex.circleLoop` and the feeders filling the avoidance slot of
`windingNumberAt` for boundary loops.

## Implementation notes

`windingNumberAt w γ hγ` takes the avoidance proof `hγ : ∀ t, γ t ≠ w` as an argument rather
than being a junk-valued total function: radial normalisation is meaningless on curves through
`w`, every use site has the proof at hand anyway, and carrying it keeps the side condition out
of the statement of every lemma.  The price is that `windingNumberAt` is not congruent under
`rw` on `γ`; `windingNumberAt_congr` is the escape hatch.

The winding number is real-valued (the total argument variation divided by `2 * π`) and does
not require the curve to be closed; for closed loops it is an integer, and integrality is what
drives the homotopy-invariance proofs (a continuous integer-valued function on a connected
space is constant).  The private layer `windingNumber : C(I, Circle) → ℝ` carries the engine:
well-definedness with respect to the choice of lift (`windingNumber_eq_div_of_lift`) and
invariance under free homotopies of loops (`windingNumber_eq_of_homotopy`).

## References

* [T. Estermann, *Complex Numbers and Functions*][estermann1962], for the symmetric
  ("dog-on-a-leash") form of Rouché's theorem.

## Tags

winding number, argument variation, degree, Rouché, Brouwer degree
-/

open scoped Real unitInterval
open Metric

namespace Complex

/-! ### The angle lift and the winding number of a loop in `S¹` -/

/-- The continuous **angle lift** of a curve `g : [0,1] → S¹`: the path obtained by lifting
`g` along the exponential covering `Circle.exp` starting at a chosen real preimage of `g 0`.
It satisfies `Circle.exp (angleLift g t) = g t` (`angleLift_lifts`). -/
private noncomputable def angleLift (g : C(I, Circle)) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm

private theorem angleLift_lifts (g : C(I, Circle)) (t : I) :
    Circle.exp (angleLift g t) = g t := by
  have h := Circle.isCoveringMap_exp.liftPath_lifts g (Circle.exp_surjective (g 0)).choose
    (Circle.exp_surjective (g 0)).choose_spec.symm
  simpa [angleLift, Function.comp] using congrFun h t

/-- The winding number of a continuous curve `g : [0,1] → S¹`: the total angle increment of
its lift, normalised by `2 * π`. -/
private noncomputable def windingNumber (g : C(I, Circle)) : ℝ :=
  (angleLift g 1 - angleLift g 0) / (2 * π)

/-- A constant curve has winding number `0`. -/
private theorem windingNumber_const (c : Circle) :
    windingNumber (ContinuousMap.const I c) = 0 := by
  -- Guard: deliberate typed identity; after `unfold` on rc2, `(const I c) 0` is only defeq to `c`.
  have h : angleLift (ContinuousMap.const I c) =
      ContinuousMap.const I (Circle.exp_surjective c).choose :=
    Circle.isCoveringMap_exp.liftPath_const (Circle.exp_surjective c).choose_spec.symm
  simp [windingNumber, h]

/-- A continuous real-valued function on the connected interval `[0,1]` taking only integer
values is constant (it cannot jump between integers without hitting a non-integer, by the
intermediate value theorem). -/
private theorem int_valued_eq {q : C(I, ℝ)} (hq : ∀ t, ∃ m : ℤ, q t = (m : ℝ))
    (a b : I) : q a = q b := by
  wlog hab : q a ≤ q b generalizing a b
  · exact (this b a (le_of_not_ge hab)).symm
  rcases hab.eq_or_lt with h | h
  · exact h
  exfalso
  obtain ⟨ma, hma⟩ := hq a
  obtain ⟨mb, hmb⟩ := hq b
  have hmab : ma < mb := by rw [hma, hmb] at h; exact_mod_cast h
  have hv2 : (ma : ℝ) + 1 / 2 ≤ q b := by
    rw [hmb]; have : (ma : ℝ) + 1 ≤ (mb : ℝ) := by exact_mod_cast hmab
    linarith
  obtain ⟨t, ht⟩ :=
    intermediate_value_univ a b q.continuous ⟨by rw [hma]; linarith, hv2⟩
  obtain ⟨m, hm⟩ := hq t
  rw [hm] at ht
  have hcontra : (2 * m : ℤ) = 2 * ma + 1 := by
    have h2 : (2 : ℝ) * (m : ℝ) = 2 * (ma : ℝ) + 1 := by linarith
    exact_mod_cast h2
  omega

/-- The winding number can be computed from *any* continuous angle lift `φ` of the curve, not
just the canonical one: if `Circle.exp (φ t) = g t` for all `t`, then
`windingNumber g = (φ 1 - φ 0) / (2 * π)`.  Two lifts of the same curve differ by a continuous
integer multiple of `2 * π`, hence by a constant, so the increment does not depend on the
choice of lift. -/
private theorem windingNumber_eq_div_of_lift (g : C(I, Circle)) (φ : C(I, ℝ))
    (hφ : ∀ t, Circle.exp (φ t) = g t) :
    windingNumber g = (φ 1 - φ 0) / (2 * π) := by
  have hψ : ∀ t, Circle.exp (angleLift g t) = g t := angleLift_lifts g
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hcont : Continuous fun t : I ↦ (φ t - angleLift g t) / (2 * π) :=
    (φ.continuous.sub (angleLift g).continuous).div_const _
  set q : C(I, ℝ) := ⟨fun t ↦ (φ t - angleLift g t) / (2 * π), hcont⟩ with hqdef
  have hqint : ∀ t, ∃ m : ℤ, q t = (m : ℝ) := by
    intro t
    have hee : Circle.exp (φ t) = Circle.exp (angleLift g t) := (hφ t).trans (hψ t).symm
    rw [Circle.exp_eq_exp] at hee
    obtain ⟨m, hm⟩ := hee
    refine ⟨m, ?_⟩
    change (φ t - angleLift g t) / (2 * π) = (m : ℝ)
    rw [hm]; field_simp; ring
  have hend := int_valued_eq hqint 0 1
  have hkey : φ 0 - angleLift g 0 = φ 1 - angleLift g 1 := by
    simp only [hqdef, ContinuousMap.coe_mk] at hend
    rw [div_eq_div_iff h2pi h2pi] at hend
    exact mul_right_cancel₀ h2pi hend
  rw [windingNumber]
  have hdiff : φ 1 - φ 0 = angleLift g 1 - angleLift g 0 := by linarith
  rw [hdiff]

/-- **Additivity of the winding number under pointwise multiplication.**  Since
`angleLift g + angleLift h` is a continuous lift of `g * h`, the increments add. -/
private theorem windingNumber_mul (g h : C(I, Circle)) :
    windingNumber (g * h) = windingNumber g + windingNumber h := by
  have hlift : ∀ t : I, Circle.exp ((angleLift g + angleLift h) t) = (g * h) t := by
    intro t
    change Circle.exp (angleLift g t + angleLift h t) = g t * h t
    rw [Circle.exp_add, angleLift_lifts, angleLift_lifts]
  rw [windingNumber_eq_div_of_lift (g * h) (angleLift g + angleLift h) hlift]
  simp only [ContinuousMap.add_apply]
  rw [windingNumber, windingNumber]
  ring

/-- **Free-homotopy invariance of the winding number.**  If `H : [0,1]² → S¹` is a homotopy
through loops (`H (s, 0) = H (s, 1)` for every `s`) from the loop `g₀` (at `s = 0`) to the
loop `g₁` (at `s = 1`), then `g₀` and `g₁` have the same winding number.  Proof: lift `H`
along `Circle.exp` (covering-space homotopy lifting); for each `s` the slice increment
`(H̃ (s, 1) - H̃ (s, 0)) / (2 * π)` is the winding number of that slice and is integer-valued
(since `H (s, 0) = H (s, 1)`), hence constant in the connected parameter `s`. -/
private theorem windingNumber_eq_of_homotopy {g₀ g₁ : C(I, Circle)} (H : C(I × I, Circle))
    (h0 : ∀ t, H (0, t) = g₀ t) (h1 : ∀ t, H (1, t) = g₁ t)
    (hloop : ∀ s, H (s, 0) = H (s, 1)) :
    windingNumber g₀ = windingNumber g₁ := by
  have H_0 : ∀ t : I, H (0, t) = Circle.exp (angleLift g₀ t) := by
    intro t; rw [h0 t]; exact (angleLift_lifts g₀ t).symm
  set Ht := Circle.isCoveringMap_exp.liftHomotopy H (angleLift g₀) H_0 with hHt
  have hlifts : ∀ st : I × I, Circle.exp (Ht st) = H st := by
    intro st
    have := congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H (angleLift g₀) H_0) st
    simpa [hHt, Function.comp] using this
  have hWcont : Continuous fun s : I ↦ (Ht (s, 1) - Ht (s, 0)) / (2 * π) := by
    apply Continuous.div_const
    exact (Ht.continuous.comp (continuous_id.prodMk continuous_const)).sub
      (Ht.continuous.comp (continuous_id.prodMk continuous_const))
  set W : C(I, ℝ) := ⟨fun s ↦ (Ht (s, 1) - Ht (s, 0)) / (2 * π), hWcont⟩ with hWdef
  have hWint : ∀ s, ∃ m : ℤ, W s = (m : ℝ) := by
    intro s
    have hee : Circle.exp (Ht (s, 1)) = Circle.exp (Ht (s, 0)) := by
      rw [hlifts (s, 1), hlifts (s, 0)]; exact (hloop s).symm
    rw [Circle.exp_eq_exp] at hee
    obtain ⟨m, hm⟩ := hee
    refine ⟨m, ?_⟩
    change (Ht (s, 1) - Ht (s, 0)) / (2 * π) = (m : ℝ)
    rw [hm]; field_simp; ring
  have key : ∀ s : I, ∀ gs : C(I, Circle), (∀ t, H (s, t) = gs t) →
      windingNumber gs = (Ht (s, 1) - Ht (s, 0)) / (2 * π) := by
    intro s gs hgs
    have hφcont : Continuous fun t : I ↦ Ht (s, t) :=
      Ht.continuous.comp (continuous_const.prodMk continuous_id)
    have hlift := windingNumber_eq_div_of_lift gs ⟨fun t ↦ Ht (s, t), hφcont⟩ (by
      intro t; change Circle.exp (Ht (s, t)) = gs t; rw [hlifts (s, t), hgs t])
    simpa using hlift
  have hW0 := key 0 g₀ h0
  have hW1 := key 1 g₁ h1
  have hWeq : W 0 = W 1 := int_valued_eq hWint 0 1
  rw [hW0, hW1]
  simpa [hWdef] using hWeq

/-! ### Normalising a curve avoiding `w` onto `S¹` -/

/-- Radial projection of a point `z ≠ w` onto the unit circle centered at the origin,
`z ↦ (z - w) / ‖z - w‖`. -/
private noncomputable def circleProjAt (w z : ℂ) (hz : z ≠ w) : Circle :=
  ⟨(z - w) / (‖z - w‖ : ℂ), by
    have hzw : z - w ≠ 0 := sub_ne_zero.2 hz
    rw [← SetLike.mem_coe, Submonoid.coe_unitSphere, mem_sphere_zero_iff_norm, norm_div,
      norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.2 hzw),
      div_self (norm_pos_iff.2 hzw).ne']⟩

/-- Radial projection depends only on the point, not on the proof of avoidance. -/
private theorem circleProjAt_congr {w a b : ℂ} (ha : a ≠ w) (hb : b ≠ w) (h : a = b) :
    circleProjAt w a ha = circleProjAt w b hb := by subst h; rfl

/-- Radial projection of a continuous function avoiding `w` is continuous. -/
private theorem continuous_circleProjAt {X : Type*} [TopologicalSpace X] {w : ℂ} {f : X → ℂ}
    (hf : Continuous f) (hne : ∀ x, f x ≠ w) :
    Continuous fun x ↦ circleProjAt w (f x) (hne x) := by
  apply Continuous.subtype_mk
  exact (hf.sub continuous_const).div
    (continuous_ofReal.comp (continuous_norm.comp (hf.sub continuous_const)))
    fun x ↦ ofReal_ne_zero.2 (norm_ne_zero_iff.2 (sub_ne_zero.2 (hne x)))

/-- The normalised curve `t ↦ (γ t - w) / ‖γ t - w‖` of a continuous curve avoiding `w`. -/
private noncomputable def normLoopAt (w : ℂ) (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ w) :
    C(I, Circle) :=
  ⟨fun t ↦ circleProjAt w (γ t) (hγ t), continuous_circleProjAt γ.continuous hγ⟩

/-! ### The winding number about a point -/

/-- The **winding number** of a continuous curve `γ : [0,1] → ℂ` about a point `w` it avoids:
the total angle increment of a continuous angle lift of the radially normalised curve
`t ↦ (γ t - w) / ‖γ t - w‖` along the covering `Circle.exp`, divided by `2 * π`.

The value is real; when `γ` is a closed loop it is an integer.  For open curves this is the
total argument variation of `γ - w` divided by `2 * π`. -/
noncomputable def windingNumberAt (w : ℂ) (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ w) : ℝ :=
  windingNumber (normLoopAt w γ hγ)

/-- The winding number depends only on the values of the curve: pointwise-equal curves have
equal winding numbers about any common avoided point.  This is the dependent-rewrite escape
hatch for the proof argument `hγ`, whose type mentions `γ`. -/
theorem windingNumberAt_congr {w : ℂ} {γ γ' : C(I, ℂ)} {hγ : ∀ t, γ t ≠ w}
    {hγ' : ∀ t, γ' t ≠ w} (he : ∀ t, γ t = γ' t) :
    windingNumberAt w γ hγ = windingNumberAt w γ' hγ' := by
  obtain rfl : γ = γ' := ContinuousMap.ext he
  rfl

/-- **Free-homotopy invariance of winding number about a point.**  A
nowhere-`w` homotopy through loops preserves winding number about `w`. -/
theorem windingNumberAt_eq_of_homotopy (w : ℂ) (γ₀ γ₁ : C(I, ℂ))
    (hγ₀ : ∀ t, γ₀ t ≠ w) (hγ₁ : ∀ t, γ₁ t ≠ w)
    (H : C(I × I, ℂ)) (hH : ∀ st, H st ≠ w)
    (h0 : ∀ t, H (0, t) = γ₀ t) (h1 : ∀ t, H (1, t) = γ₁ t)
    (hloop : ∀ s, H (s, 0) = H (s, 1)) :
    windingNumberAt w γ₀ hγ₀ = windingNumberAt w γ₁ hγ₁ := by
  set Hn : C(I × I, Circle) :=
    ⟨fun st ↦ circleProjAt w (H st) (hH st),
      continuous_circleProjAt H.continuous hH⟩ with hHndef
  have h0' : ∀ t : I, Hn (0, t) = normLoopAt w γ₀ hγ₀ t := by
    intro t
    change circleProjAt w (H (0, t)) (hH (0, t)) =
      circleProjAt w (γ₀ t) (hγ₀ t)
    exact circleProjAt_congr _ _ (h0 t)
  have h1' : ∀ t : I, Hn (1, t) = normLoopAt w γ₁ hγ₁ t := by
    intro t
    change circleProjAt w (H (1, t)) (hH (1, t)) =
      circleProjAt w (γ₁ t) (hγ₁ t)
    exact circleProjAt_congr _ _ (h1 t)
  have hloop' : ∀ s : I, Hn (s, 0) = Hn (s, 1) := by
    intro s
    change circleProjAt w (H (s, 0)) (hH (s, 0)) =
      circleProjAt w (H (s, 1)) (hH (s, 1))
    exact circleProjAt_congr _ _ (hloop s)
  exact windingNumber_eq_of_homotopy Hn h0' h1' hloop'

/-- The winding number computed from an explicit **polar angle lift**: if
`γ t - w = ‖γ t - w‖ * exp (φ t * I)` for a continuous real angle path `φ`, then the winding
number of `γ` about `w` is the total angle increment `(φ 1 - φ 0) / (2 * π)`.  This is the
fundamental computation rule for `windingNumberAt`: it reduces the covering-lift definition to
an explicit polar decomposition of the curve. -/
theorem windingNumberAt_eq_div_of_lift {w : ℂ} {γ : C(I, ℂ)} (hγ : ∀ t, γ t ≠ w) (φ : C(I, ℝ))
    (hφ : ∀ t, γ t - w = ‖γ t - w‖ * exp (φ t * Complex.I)) :
    windingNumberAt w γ hγ = (φ 1 - φ 0) / (2 * π) := by
  refine windingNumber_eq_div_of_lift _ φ fun t ↦ ?_
  apply Subtype.ext
  rw [Circle.coe_exp]
  change exp ((φ t : ℂ) * Complex.I) = (γ t - w) / (‖γ t - w‖ : ℂ)
  rw [eq_div_iff (by exact_mod_cast norm_ne_zero_iff.2 (sub_ne_zero.2 (hγ t)))]
  linear_combination -hφ t

/-- A constant curve has winding number `0` about any point it avoids. -/
@[simp]
theorem windingNumberAt_const (w z : ℂ) (h : ∀ t : I, (ContinuousMap.const I z) t ≠ w) :
    windingNumberAt w (ContinuousMap.const I z) h = 0 := by
  have hnl : normLoopAt w (ContinuousMap.const I z) h
      = ContinuousMap.const I (circleProjAt w z (h 0)) :=
    ContinuousMap.ext fun t ↦ circleProjAt_congr (h t) (h 0) rfl
  rw [windingNumberAt, hnl, windingNumber_const]

/-- **Normalisation invariance**: the winding number about `w` depends only on the unit
direction field `t ↦ (γ t - w) / ‖γ t - w‖`.  If the direction vectors from `w` are pointwise
on the same ray (`SameRay ℝ (γ t - w) (γ' t - w)`), the winding numbers agree.  No closedness
is required: the radially normalised curves are literally pointwise equal. -/
theorem windingNumberAt_congr_sameRay {w : ℂ} {γ γ' : C(I, ℂ)}
    (hγ : ∀ t, γ t ≠ w) (hγ' : ∀ t, γ' t ≠ w)
    (hray : ∀ t, SameRay ℝ (γ t - w) (γ' t - w)) :
    windingNumberAt w γ hγ = windingNumberAt w γ' hγ' := by
  unfold windingNumberAt
  congr 1
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (γ t - w) / (‖γ t - w‖ : ℂ) = (γ' t - w) / (‖γ' t - w‖ : ℂ)
  have hx : γ t - w ≠ 0 := sub_ne_zero.2 (hγ t)
  have hy : γ' t - w ≠ 0 := sub_ne_zero.2 (hγ' t)
  have hxn : (‖γ t - w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hx
  have hyn : (‖γ' t - w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hy
  have hkey := (hray t).norm_smul_eq
  rw [real_smul, real_smul] at hkey
  rw [div_eq_div_iff hxn hyn]
  linear_combination -hkey

/-- **Positive-scalar-field invariance**: scaling the vector from the center by a continuous
strictly positive scalar field preserves the winding number, `t ↦ w + c t • (γ t - w)` winding
as `γ` does.  No closedness hypotheses on `γ` or `c` are needed: the direction fields from `w`
agree on the nose. -/
theorem windingNumberAt_pos_smul (w : ℂ) (c : C(I, ℝ)) (hc : ∀ t, 0 < c t)
    (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ w) :
    windingNumberAt w
      ⟨fun t ↦ w + c t • (γ t - w),
        continuous_const.add (c.continuous.smul (γ.continuous.sub continuous_const))⟩
      (fun t ↦ by
        simp only [ContinuousMap.coe_mk, ne_eq, add_eq_left]
        exact smul_ne_zero (hc t).ne' (sub_ne_zero.2 (hγ t))) = windingNumberAt w γ hγ := by
  apply windingNumberAt_congr_sameRay
  intro t
  simp only [ContinuousMap.coe_mk, add_sub_cancel_left]
  exact SameRay.sameRay_nonneg_smul_left (γ t - w) (hc t).le

/-! ### Multiplicativity about the origin -/

/-- Radial projection onto the unit circle about the origin is multiplicative. -/
private theorem circleProjAt_zero_mul {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    circleProjAt 0 (a * b) (mul_ne_zero ha hb)
      = circleProjAt 0 a ha * circleProjAt 0 b hb := by
  apply Subtype.ext
  rw [Circle.coe_mul]
  change (a * b - 0) / (‖a * b - 0‖ : ℂ) = (a - 0) / (‖a - 0‖ : ℂ) * ((b - 0) / (‖b - 0‖ : ℂ))
  have hna : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ha
  have hnb : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hb
  simp only [sub_zero, norm_mul]
  push_cast
  field_simp

/-- **Additivity of the winding number about the origin under pointwise multiplication**
(degree additivity): for nonvanishing curves `γ, γ' : C(I, ℂ)`, the winding number of the
pointwise product `γ * γ'` about `0` is the sum of the winding numbers.  The radial
normalisation of a product is the pointwise product of the normalisations, and angle lifts
add. -/
theorem windingNumberAt_mul (γ γ' : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0) (hγ' : ∀ t, γ' t ≠ 0) :
    windingNumberAt 0 (γ * γ') (fun t ↦ mul_ne_zero (hγ t) (hγ' t))
      = windingNumberAt 0 γ hγ + windingNumberAt 0 γ' hγ' := by
  have hnl : normLoopAt 0 (γ * γ') (fun t ↦ mul_ne_zero (hγ t) (hγ' t))
      = normLoopAt 0 γ hγ * normLoopAt 0 γ' hγ' :=
    ContinuousMap.ext fun t ↦ circleProjAt_zero_mul (hγ t) (hγ' t)
  rw [windingNumberAt, hnl, windingNumber_mul, windingNumberAt, windingNumberAt]

/-- Multiplying a nonvanishing curve by a constant nonzero scalar does not change its winding
number about the origin. -/
theorem windingNumberAt_const_mul (c : ℂ) (hc : c ≠ 0) (γ : C(I, ℂ)) (hγ : ∀ t, γ t ≠ 0) :
    windingNumberAt 0 (ContinuousMap.const I c * γ) (fun t ↦ mul_ne_zero hc (hγ t))
      = windingNumberAt 0 γ hγ := by
  have h := windingNumberAt_mul (ContinuousMap.const I c) γ (fun _ ↦ hc) hγ
  rw [windingNumberAt_const 0 c fun _ ↦ hc, zero_add] at h
  exact h

/-! ### The continuous Rouché theorem ("dog-on-a-leash") -/

/-- Kernel of the symmetric Rouché hypothesis: a point of the segment `[c, d]` can be `0`
only if `‖c - d‖ = ‖c‖ + ‖d‖` (the points lie on opposite rays), so strict inequality keeps
the whole segment away from `0`. -/
private theorem segment_ne_zero {c d : ℂ} (h : ‖c - d‖ < ‖c‖ + ‖d‖) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : c + s • (d - c) ≠ 0 := by
  intro hzero
  have hzero' : c + (s : ℂ) * (d - c) = 0 := by rwa [real_smul] at hzero
  have hc : ‖c‖ = s * ‖d - c‖ := by
    have hsc : s • (d - c) = -c := by
      rw [real_smul]; linear_combination hzero'
    calc ‖c‖ = ‖s • (d - c)‖ := by rw [hsc, norm_neg]
      _ = s * ‖d - c‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hd : ‖d‖ = (1 - s) * ‖d - c‖ := by
    have hsd : (1 - s) • (d - c) = d := by
      rw [real_smul]; push_cast; linear_combination -hzero'
    calc ‖d‖ = ‖(1 - s) • (d - c)‖ := by rw [hsd]
      _ = (1 - s) * ‖d - c‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hsum : ‖c‖ + ‖d‖ = ‖d - c‖ := by rw [hc, hd]; ring
  have hrev : ‖c - d‖ = ‖d - c‖ := norm_sub_rev c d
  linarith

/-- Under the symmetric Rouché hypothesis `‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖`, the base
curve `γ` avoids `w`. -/
theorem ne_of_norm_sub_lt_left {w : ℂ} {γ γ' : C(I, ℂ)}
    (hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖) (t : I) : γ t ≠ w :=
  fun h ↦ by simpa [h] using hpert t

/-- Under the symmetric Rouché hypothesis `‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖`, the
perturbed curve `γ'` avoids `w`. -/
theorem ne_of_norm_sub_lt_right {w : ℂ} {γ γ' : C(I, ℂ)}
    (hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖) (t : I) : γ' t ≠ w :=
  fun h ↦ by simpa [h, norm_sub_rev w (γ t)] using hpert t

/-- **The continuous Rouché theorem** ("dog-on-a-leash", symmetric Estermann form).  If `γ`
and `γ'` are closed loops with `‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖` for all `t` — the dog
and the walker are never at opposite ends of a taut leash through the hydrant `w` — then they
have the same winding number about `w`.  Both nonvanishing conditions follow from the
hypothesis.  The straight-line homotopy from `γ` to `γ'` avoids `w` (a segment through `w`
would force the triangle-inequality equality case), so free-homotopy invariance applies. -/
theorem windingNumberAt_eq_of_norm_sub_lt (w : ℂ) (γ γ' : C(I, ℂ))
    (hloopγ : γ 0 = γ 1) (hloopγ' : γ' 0 = γ' 1)
    (hpert : ∀ t, ‖γ' t - γ t‖ < ‖γ t - w‖ + ‖γ' t - w‖) :
    windingNumberAt w γ (ne_of_norm_sub_lt_left hpert) =
      windingNumberAt w γ' (ne_of_norm_sub_lt_right hpert) := by
  have hγ : ∀ t, γ t ≠ w := ne_of_norm_sub_lt_left hpert
  have hγ' : ∀ t, γ' t ≠ w := ne_of_norm_sub_lt_right hpert
  set Hc : I × I → ℂ := fun st ↦ γ st.2 + (st.1 : ℝ) • (γ' st.2 - γ st.2) with hHcdef
  have hHccont : Continuous Hc := by
    rw [hHcdef]
    exact (γ.continuous.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((γ'.continuous.comp continuous_snd).sub (γ.continuous.comp continuous_snd)))
  have hHcne : ∀ st : I × I, Hc st ≠ w := by
    intro st
    have hs0 : (0 : ℝ) ≤ (st.1 : ℝ) := st.1.2.1
    have hs1 : (st.1 : ℝ) ≤ 1 := st.1.2.2
    have hkey : Hc st - w =
        (γ st.2 - w) + (st.1 : ℝ) • ((γ' st.2 - w) - (γ st.2 - w)) := by
      simp only [hHcdef]
      rw [sub_sub_sub_cancel_right]
      abel
    have hpert' : ‖(γ st.2 - w) - (γ' st.2 - w)‖ < ‖γ st.2 - w‖ + ‖γ' st.2 - w‖ := by
      have he : (γ st.2 - w) - (γ' st.2 - w) = γ st.2 - γ' st.2 := by ring
      rw [he, norm_sub_rev]
      exact hpert st.2
    intro hcon
    apply segment_ne_zero hpert' hs0 hs1
    rw [← hkey, hcon, sub_self]
  set H : C(I × I, Circle) :=
    ⟨fun st ↦ circleProjAt w (Hc st) (hHcne st), continuous_circleProjAt hHccont hHcne⟩
  have h0 : ∀ t : I, H (0, t) = normLoopAt w γ hγ t := by
    intro t
    change circleProjAt w (Hc (0, t)) (hHcne (0, t)) = circleProjAt w (γ t) (hγ t)
    apply circleProjAt_congr
    change γ t + ((0 : I) : ℝ) • (γ' t - γ t) = γ t
    rw [Set.Icc.coe_zero, zero_smul, add_zero]
  have h1 : ∀ t : I, H (1, t) = normLoopAt w γ' hγ' t := by
    intro t
    change circleProjAt w (Hc (1, t)) (hHcne (1, t)) = circleProjAt w (γ' t) (hγ' t)
    apply circleProjAt_congr
    change γ t + ((1 : I) : ℝ) • (γ' t - γ t) = γ' t
    rw [Set.Icc.coe_one, one_smul, add_sub_cancel]
  have hloop : ∀ s : I, H (s, 0) = H (s, 1) := by
    intro s
    change circleProjAt w (Hc (s, 0)) (hHcne (s, 0)) = circleProjAt w (Hc (s, 1)) (hHcne (s, 1))
    apply circleProjAt_congr
    change γ (0 : I) + (s : ℝ) • (γ' (0 : I) - γ (0 : I))
      = γ (1 : I) + (s : ℝ) • (γ' (1 : I) - γ (1 : I))
    rw [hloopγ, hloopγ']
  have hinv := windingNumber_eq_of_homotopy H h0 h1 hloop
  rw [windingNumberAt, windingNumberAt, hinv]

/-! ### The boundary loop of a circle -/

/-- The **boundary loop** `t ↦ F (circleMap c R (2 * π * t))` of a function `F` continuous on
the circle with center `c` and radius `|R|`, as a bundled continuous map `[0,1] → ℂ`. -/
noncomputable def circleLoop (F : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hF : ContinuousOn F (sphere c |R|)) : C(I, ℂ) :=
  ⟨fun t ↦ F (circleMap c R (2 * π * t)), by
    apply hF.comp_continuous
    · exact (continuous_circleMap c R).comp (continuous_const.mul continuous_subtype_val)
    · exact fun t ↦ circleMap_mem_sphere' c R _⟩

/-- Evaluation of the boundary loop: `circleLoop F c R hF t = F (circleMap c R (2 * π * t))`. -/
@[simp]
theorem circleLoop_apply (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (hF : ContinuousOn F (sphere c |R|))
    (t : I) : circleLoop F c R hF t = F (circleMap c R (2 * π * t)) :=
  rfl

/-- If `F` avoids the value `w` on the circle with center `c` and radius `|R|`, its boundary
loop avoids `w`.  This is the well-definedness feeder for winding numbers of boundary loops:
it fills the avoidance slot of `windingNumberAt w (circleLoop F c R hF)`. -/
theorem circleLoop_ne (F : ℂ → ℂ) (c : ℂ) (R : ℝ) (w : ℂ)
    (hF : ContinuousOn F (sphere c |R|)) (hbd : ∀ z ∈ sphere c |R|, F z ≠ w) (t : I) :
    circleLoop F c R hF t ≠ w :=
  hbd _ (circleMap_mem_sphere' c R _)

/-- The boundary loop of the identity — the standard parametrisation
`t ↦ circleMap c R (2 * π * t)` of the circle with center `c` and radius `|R|` — avoids the
center.  This fills the avoidance slot of `windingNumberAt_circleLoop_id`. -/
theorem circleLoop_id_ne (c : ℂ) {R : ℝ} (hR : R ≠ 0) (t : I) :
    circleLoop id c R continuous_id.continuousOn t ≠ c :=
  circleMap_ne_center hR

/-- **Normalisation of the winding number**: the standard parametrisation of the circle with
center `c` and radius `R > 0` winds exactly once about `c`.  Together with the invariance
lemmas this pins down the winding numbers of all loops comparable to a round circle. -/
theorem windingNumberAt_circleLoop_id (c : ℂ) {R : ℝ} (hR : 0 < R) :
    windingNumberAt c (circleLoop id c R continuous_id.continuousOn)
      (circleLoop_id_ne c hR.ne') = 1 := by
  have hlift : ∀ t : I,
      Circle.exp ((⟨fun t : I ↦ 2 * π * (t : ℝ), by fun_prop⟩ : C(I, ℝ)) t) =
        normLoopAt c (circleLoop id c R continuous_id.continuousOn)
          (circleLoop_id_ne c hR.ne') t := by
    intro t
    have hsub : circleLoop id c R continuous_id.continuousOn t - c =
        (R : ℂ) * Complex.exp ((2 * π * (t : ℝ) : ℝ) * Complex.I) := by
      change circleMap c R (2 * π * (t : ℝ)) - c = _
      rw [circleMap, add_sub_cancel_left]
    have hnorm : ‖circleLoop id c R continuous_id.continuousOn t - c‖ = R := by
      rw [hsub, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hR,
        norm_exp_ofReal_mul_I, mul_one]
    apply Subtype.ext
    rw [Circle.coe_exp]
    change Complex.exp (((2 * π * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
        (circleLoop id c R continuous_id.continuousOn t - c) /
          (‖circleLoop id c R continuous_id.continuousOn t - c‖ : ℂ)
    rw [hnorm, hsub, mul_div_cancel_left₀ _ (ofReal_ne_zero.2 hR.ne')]
  rw [windingNumberAt, windingNumber_eq_div_of_lift _ _ hlift]
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  change (2 * π * ((1 : I) : ℝ) - 2 * π * ((0 : I) : ℝ)) / (2 * π) = 1
  rw [Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero, sub_zero, div_self h2pi]

/-- **Normalisation of the winding number, `n`-fold form**: the loop
`t ↦ exp (2 * π * n * t * I)` — the `n`-fold cover of the unit circle, traversed clockwise
for negative `n` — has winding number `n` about the origin.  In particular (`n = -1`) the
clockwise unit-circle loop `t ↦ exp (-(2 * π * t) * I)` has winding number `-1`. -/
theorem windingNumberAt_exp_int_mul (n : ℤ) :
    windingNumberAt 0
      ⟨fun t : I ↦ exp ((2 * π * n * t : ℝ) * Complex.I), by fun_prop⟩
      (fun _ ↦ exp_ne_zero _) = n := by
  rw [windingNumberAt_eq_div_of_lift (fun _ ↦ exp_ne_zero _)
    ⟨fun t : I ↦ 2 * π * n * t, by fun_prop⟩ fun t ↦ by
      change exp ((2 * π * n * t : ℝ) * Complex.I) - 0
        = (‖exp (((2 * π * n * t : ℝ) : ℂ) * Complex.I) - 0‖ : ℂ)
          * exp (((2 * π * n * t : ℝ) : ℂ) * Complex.I)
      rw [sub_zero, norm_exp_ofReal_mul_I, ofReal_one, one_mul]]
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  change (2 * π * n * ((1 : I) : ℝ) - 2 * π * n * ((0 : I) : ℝ)) / (2 * π) = n
  rw [Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero, sub_zero,
    mul_div_cancel_left₀ _ h2pi]

/-! ### The planar degree existence principle -/

/-- **Existence property of the planar Brouwer degree** (Kronecker form).  If `F` is
continuous on the closed ball with center `c` and radius `R > 0`, avoids the value `w` on the
boundary sphere, and its boundary loop has nonzero winding number about `w`, then `F` attains
the value `w` in the open ball.

The proof is the null-homotopy argument: were `F ≠ w` throughout, the radial contraction
`(s, t) ↦ F (c + s • (circleMap c R (2 * π * t) - c))` would be a free homotopy of loops in
`ℂ \ {w}` from the boundary loop to a constant, forcing the boundary winding number to
vanish. -/
theorem exists_eq_of_windingNumberAt_ne_zero (F : ℂ → ℂ) (c : ℂ) {R : ℝ} (hR : 0 < R) (w : ℂ)
    (hF : ContinuousOn F (closedBall c R)) (hbd : ∀ z ∈ sphere c R, F z ≠ w)
    (hw : windingNumberAt w
      (circleLoop F c R (hF.mono (sphere_subset_closedBall.trans
        (closedBall_subset_closedBall (abs_of_pos hR).le))))
      (circleLoop_ne F c R w _
        fun z hz ↦ hbd z (mem_sphere.2 ((mem_sphere.1 hz).trans (abs_of_pos hR)))) ≠ 0) :
    ∃ z ∈ ball c R, F z = w := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hFs : ContinuousOn F (sphere c |R|) :=
    hF.mono (sphere_subset_closedBall.trans (closedBall_subset_closedBall (abs_of_pos hR).le))
  have hbd' : ∀ z ∈ sphere c |R|, F z ≠ w :=
    fun z hz ↦ hbd z (mem_sphere.2 ((mem_sphere.1 hz).trans (abs_of_pos hR)))
  have hne : ∀ z ∈ closedBall c R, F z ≠ w := by
    intro z hz
    rcases (mem_closedBall.1 hz).lt_or_eq with h | h
    · exact hcon z (mem_ball.2 h)
    · exact hbd z (mem_sphere.2 h)
  have hFc : F c ≠ w := hne c (mem_closedBall_self hR.le)
  set pt : I × I → ℂ := fun st ↦ c + ((st.1 : ℝ) : ℂ) * circleMap 0 R (2 * π * st.2)
    with hptdef
  have hptcont : Continuous pt := by
    rw [hptdef]
    exact continuous_const.add ((continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst)).mul ((continuous_circleMap 0 R).comp
        (continuous_const.mul (continuous_subtype_val.comp continuous_snd))))
  have hptmem : ∀ st : I × I, pt st ∈ closedBall c R := by
    intro st
    have hnorm : ‖pt st - c‖ = (st.1 : ℝ) * R := by
      rw [hptdef]
      simp only [add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs,
        norm_circleMap_zero, abs_of_nonneg st.1.2.1, abs_of_pos hR]
    rw [mem_closedBall, dist_eq_norm, hnorm]
    nlinarith [st.1.2.2, hR.le]
  have hFptcont : Continuous fun st ↦ F (pt st) := hF.comp_continuous hptcont hptmem
  have hFptne : ∀ st, F (pt st) ≠ w := fun st ↦ hne _ (hptmem st)
  set Hmap : C(I × I, Circle) :=
    ⟨fun st ↦ circleProjAt w (F (pt st)) (hFptne st), continuous_circleProjAt hFptcont hFptne⟩
  have h0 : ∀ t, Hmap (0, t) = (ContinuousMap.const I (circleProjAt w (F c) hFc)) t := by
    intro t
    change circleProjAt w (F (pt (0, t))) (hFptne (0, t)) = circleProjAt w (F c) hFc
    apply circleProjAt_congr
    have hpt0 : pt (0, t) = c := by simp [hptdef]
    rw [hpt0]
  have h1 : ∀ t, Hmap (1, t) =
      normLoopAt w (circleLoop F c R hFs) (circleLoop_ne F c R w hFs hbd') t := by
    intro t
    change circleProjAt w (F (pt (1, t))) (hFptne (1, t)) =
      circleProjAt w (circleLoop F c R hFs t) (circleLoop_ne F c R w hFs hbd' t)
    apply circleProjAt_congr
    change F (pt (1, t)) = F (circleMap c R (2 * π * t))
    congr 1
    simp [hptdef, circleMap]
  have hloop : ∀ s, Hmap (s, 0) = Hmap (s, 1) := by
    intro s
    change circleProjAt w (F (pt (s, 0))) (hFptne (s, 0)) =
      circleProjAt w (F (pt (s, 1))) (hFptne (s, 1))
    apply circleProjAt_congr
    have hpt : pt (s, 0) = pt (s, 1) := by
      have hper : circleMap 0 R (2 * π) = circleMap 0 R 0 := by
        simpa using periodic_circleMap 0 R 0
      rw [hptdef]
      simp only [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one, hper]
    rw [hpt]
  have hinv := windingNumber_eq_of_homotopy Hmap h0 h1 hloop
  rw [windingNumber_const] at hinv
  exact hw hinv.symm

end Complex
