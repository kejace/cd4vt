/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Dahlberg
import Gluck.Discrete.CircleParameterGeometry

/-!
# A finite radius obstruction from a circle arc spanning a semicircle

The two endpoints of an arc of angular length in `[π,2π)`, together with its
angular midpoint, have the circle center in their convex hull.  Consequently
any disk containing those three points has radius at least the circle radius.
-/

namespace Gluck.Forward

open Gluck.Discrete

private noncomputable def semicircleEndpointWeight (θ₀ θ₂ : ℝ) : ℝ :=
  1 / (2 * (1 - Real.cos ((θ₂ - θ₀) / 2)))

private noncomputable def semicircleMidpointWeight (θ₀ θ₂ : ℝ) : ℝ :=
  -Real.cos ((θ₂ - θ₀) / 2) /
    (1 - Real.cos ((θ₂ - θ₀) / 2))

private theorem semicircle_weights
    {θ₀ θ₂ : ℝ} (hlower : Real.pi ≤ θ₂ - θ₀)
    (hupper : θ₂ - θ₀ < 2 * Real.pi) :
    let a := semicircleEndpointWeight θ₀ θ₂
    let b := semicircleMidpointWeight θ₀ θ₂
    0 ≤ a ∧ 0 ≤ b ∧ a + b + a = 1 ∧
      2 * a * Real.cos ((θ₂ - θ₀) / 2) + b = 0 := by
  let h : ℝ := (θ₂ - θ₀) / 2
  have hhLower : Real.pi / 2 ≤ h := by dsimp [h]; linarith
  have hhUpper : h < Real.pi := by dsimp [h]; linarith
  have hc : Real.cos h ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hhLower
      (by linarith [Real.pi_pos])
  have hden : 0 < 1 - Real.cos h := by linarith
  dsimp [semicircleEndpointWeight, semicircleMidpointWeight]
  change 0 ≤ 1 / (2 * (1 - Real.cos h)) ∧
    0 ≤ -Real.cos h / (1 - Real.cos h) ∧
    1 / (2 * (1 - Real.cos h)) +
        -Real.cos h / (1 - Real.cos h) +
        1 / (2 * (1 - Real.cos h)) = 1 ∧
    2 * (1 / (2 * (1 - Real.cos h))) * Real.cos h +
        -Real.cos h / (1 - Real.cos h) = 0
  refine ⟨by positivity, div_nonneg (neg_nonneg.mpr hc) hden.le, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring

/-- The center of the circle is the indicated convex combination of an arc's
two endpoints and its angular midpoint. -/
theorem circlePoint_center_convexCombo_endpoints_midpoint
    (O : ℂ) (R θ₀ θ₂ : ℝ)
    (hlower : Real.pi ≤ θ₂ - θ₀)
    (hupper : θ₂ - θ₀ < 2 * Real.pi) :
    let a := semicircleEndpointWeight θ₀ θ₂
    let b := semicircleMidpointWeight θ₀ θ₂
    0 ≤ a ∧ 0 ≤ b ∧ a + b + a = 1 ∧
      O = (a : ℂ) * circlePoint O R θ₀ +
        (b : ℂ) * circlePoint O R ((θ₀ + θ₂) / 2) +
        (a : ℂ) * circlePoint O R θ₂ := by
  obtain ⟨ha, hb, hsum, hcancel⟩ :=
    semicircle_weights hlower hupper
  let a := semicircleEndpointWeight θ₀ θ₂
  let b := semicircleMidpointWeight θ₀ θ₂
  have hweights : 0 ≤ a ∧ 0 ≤ b ∧ a + b + a = 1 :=
    ⟨ha, hb, hsum⟩
  refine ⟨ha, hb, hsum, ?_⟩
  have hcosdiff :
      Real.cos ((θ₀ - θ₂) / 2) = Real.cos ((θ₂ - θ₀) / 2) := by
    rw [show (θ₀ - θ₂) / 2 = -((θ₂ - θ₀) / 2) by ring,
      Real.cos_neg]
  have hcosSum : Real.cos θ₀ + Real.cos θ₂ =
      2 * Real.cos ((θ₀ + θ₂) / 2) *
        Real.cos ((θ₂ - θ₀) / 2) := by
    rw [Real.cos_add_cos, hcosdiff]
  have hsinSum : Real.sin θ₀ + Real.sin θ₂ =
      2 * Real.sin ((θ₀ + θ₂) / 2) *
        Real.cos ((θ₂ - θ₀) / 2) := by
    rw [Real.sin_add_sin, hcosdiff]
  have hcosWeighted :
      semicircleEndpointWeight θ₀ θ₂ * Real.cos θ₀ +
        semicircleMidpointWeight θ₀ θ₂ *
          Real.cos ((θ₀ + θ₂) / 2) +
        semicircleEndpointWeight θ₀ θ₂ * Real.cos θ₂ = 0 := by
    linear_combination
      (semicircleEndpointWeight θ₀ θ₂) * hcosSum +
      Real.cos ((θ₀ + θ₂) / 2) * hcancel
  have hsinWeighted :
      semicircleEndpointWeight θ₀ θ₂ * Real.sin θ₀ +
        semicircleMidpointWeight θ₀ θ₂ *
          Real.sin ((θ₀ + θ₂) / 2) +
        semicircleEndpointWeight θ₀ θ₂ * Real.sin θ₂ = 0 := by
    linear_combination
      (semicircleEndpointWeight θ₀ θ₂) * hsinSum +
      Real.sin ((θ₀ + θ₂) / 2) * hcancel
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, circlePoint_re]
    linear_combination -O.re * hsum - R * hcosWeighted
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, circlePoint_im]
    linear_combination -O.im * hsum - R * hsinWeighted

/-- Any closed disk containing the endpoints and angular midpoint of a circle
arc of length in `[π,2π)` has radius at least the circle radius. -/
theorem circlePoint_radius_le_of_semicircle_triple_inClosedDisk
    {O C : ℂ} {R S θ₀ θ₂ : ℝ}
    (hR : 0 < R) (hS : 0 ≤ S)
    (hlower : Real.pi ≤ θ₂ - θ₀)
    (hupper : θ₂ - θ₀ < 2 * Real.pi)
    (h₀ : InClosedDiskR2 C S (circlePoint O R θ₀))
    (hm : InClosedDiskR2 C S (circlePoint O R ((θ₀ + θ₂) / 2)))
    (h₂ : InClosedDiskR2 C S (circlePoint O R θ₂)) :
    R ≤ S := by
  obtain ⟨ha, hb, hsum, hcenter⟩ :=
    circlePoint_center_convexCombo_endpoints_midpoint O R θ₀ θ₂
      hlower hupper
  have hcircle : CircumcircleR2
      (circlePoint O R θ₀)
      (circlePoint O R ((θ₀ + θ₂) / 2))
      (circlePoint O R θ₂) O R := by
    refine ⟨hR, ?_, ?_, ?_⟩ <;>
      simp [dist_circlePoint_center, abs_of_pos hR]
  exact circumcircleR2_radius_le_of_center_convexCombo_three
    hcircle ha hb ha hsum hcenter hS h₀ hm h₂

end Gluck.Forward
