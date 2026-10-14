/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.CircleParameterGeometry

/-!
# Support of short circle-mesh chords

A positively oriented circle chord with angular length less than `π` strictly
supports every point in the concentric disk whose radius is smaller than the
chord's distance from the center.  This supplies the inner-chain half of a
circle-mesh support argument.  The outer-circle half is already provided by
`crossR2_circlePoint_pos_of_ordered` from `CircleParameterGeometry`.
-/

open Metric

namespace Gluck.Discrete

private theorem crossR2_circlePoint_symmetric_eq_midpoint_projection
    (O P : ℂ) (R m δ : ℝ) :
    crossR2 (circlePoint O R (m - δ)) (circlePoint O R (m + δ)) P =
      2 * R * Real.sin δ *
        (R * Real.cos δ - inner ℝ (circlePoint 0 1 m) (P - O)) := by
  change _ = 2 * R * Real.sin δ *
    (R * Real.cos δ - ((P - O) * star (circlePoint 0 1 m)).re)
  simp only [crossR2, Complex.sub_re, Complex.sub_im,
    circlePoint_re, circlePoint_im, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.zero_im,
    zero_add, one_mul]
  rw [Real.cos_sub, Real.sin_sub, Real.cos_add, Real.sin_add]
  linear_combination 2 * R ^ 2 * Real.cos δ * Real.sin δ *
    Real.sin_sq_add_cos_sq m

/-- The signed area against a circle chord is its positive sine factor times
the difference between the chord's center distance and the midpoint-direction
projection of `P - O`. -/
theorem crossR2_circlePoint_eq_midpoint_projection
    (O P : ℂ) (R θ₀ θ₁ : ℝ) :
    crossR2 (circlePoint O R θ₀) (circlePoint O R θ₁) P =
      2 * R * Real.sin ((θ₁ - θ₀) / 2) *
        (R * Real.cos ((θ₁ - θ₀) / 2) -
          inner ℝ (circlePoint 0 1 ((θ₀ + θ₁) / 2)) (P - O)) := by
  simpa only [show (θ₀ + θ₁) / 2 - (θ₁ - θ₀) / 2 = θ₀ by ring,
    show (θ₀ + θ₁) / 2 + (θ₁ - θ₀) / 2 = θ₁ by ring] using
      crossR2_circlePoint_symmetric_eq_midpoint_projection
        O P R ((θ₀ + θ₁) / 2) ((θ₁ - θ₀) / 2)

/-- A positively oriented circle chord of angular length less than `π`
strictly supports every point lying inside its concentric inner radius. -/
theorem crossR2_circlePoint_pos_of_dist_lt_innerRadius
    (O P : ℂ) {R θ₀ θ₁ : ℝ} (hR : 0 < R)
    (h₀₁ : θ₀ < θ₁) (hspan : θ₁ < θ₀ + Real.pi)
    (hP : dist O P < R * Real.cos ((θ₁ - θ₀) / 2)) :
    0 < crossR2 (circlePoint O R θ₀) (circlePoint O R θ₁) P := by
  have hδpos : 0 < (θ₁ - θ₀) / 2 := by linarith
  have hδltpi : (θ₁ - θ₀) / 2 < Real.pi := by
    linarith [Real.pi_pos]
  have hsin : 0 < Real.sin ((θ₁ - θ₀) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hδpos hδltpi
  have hu : ‖circlePoint 0 1 ((θ₀ + θ₁) / 2)‖ = 1 := by
    simp
  have hinner :
      inner ℝ (circlePoint 0 1 ((θ₀ + θ₁) / 2)) (P - O) <
        R * Real.cos ((θ₁ - θ₀) / 2) := by
    calc
      inner ℝ (circlePoint 0 1 ((θ₀ + θ₁) / 2)) (P - O) ≤
          ‖circlePoint 0 1 ((θ₀ + θ₁) / 2)‖ * ‖P - O‖ :=
        real_inner_le_norm _ _
      _ = dist O P := by rw [hu]; simp [dist_eq_norm, norm_sub_rev]
      _ < R * Real.cos ((θ₁ - θ₀) / 2) := hP
  rw [crossR2_circlePoint_eq_midpoint_projection]
  positivity

/-- Uniform-radius form of
`crossR2_circlePoint_pos_of_dist_lt_innerRadius`, convenient for all vertices
of a finite inner chain. -/
theorem crossR2_circlePoint_pos_of_dist_le_of_innerRadius_lt
    (O P : ℂ) {R θ₀ θ₁ ρ : ℝ} (hR : 0 < R)
    (h₀₁ : θ₀ < θ₁) (hspan : θ₁ < θ₀ + Real.pi)
    (hP : dist O P ≤ ρ)
    (hρ : ρ < R * Real.cos ((θ₁ - θ₀) / 2)) :
    0 < crossR2 (circlePoint O R θ₀) (circlePoint O R θ₁) P := by
  exact crossR2_circlePoint_pos_of_dist_lt_innerRadius O P hR h₀₁ hspan
    (hP.trans_lt hρ)


end Gluck.Discrete
