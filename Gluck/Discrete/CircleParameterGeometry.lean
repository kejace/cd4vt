import Gluck.Discrete.PolygonConvexity
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Positively ordered points on a Euclidean circle

This file supplies the explicit circle-parameter geometry used when Dahlberg's
auxiliary polygon is completed by inserting vertices along a circle arc.  The
factorized cross-product formula makes strict left support a direct consequence
of positive cyclic angle gaps.
-/

namespace Gluck.Discrete

/-- Compatibility alias for mathlib's parametrization of a Euclidean circle. -/
noncomputable abbrev circlePoint (O : ℂ) (R θ : ℝ) : ℂ := circleMap O R θ

@[simp] theorem circlePoint_re (O : ℂ) (R θ : ℝ) :
    (circlePoint O R θ).re = O.re + R * Real.cos θ := by
  change (circleMap O R θ).re = _
  simp [circleMap]

@[simp] theorem circlePoint_im (O : ℂ) (R θ : ℝ) :
    (circlePoint O R θ).im = O.im + R * Real.sin θ := by
  change (circleMap O R θ).im = _
  simp [circleMap]

@[simp] theorem circlePoint_add_two_pi (O : ℂ) (R θ : ℝ) :
    circlePoint O R (θ + 2 * Real.pi) = circlePoint O R θ := by
  change circleMap O R (θ + 2 * Real.pi) = circleMap O R θ
  exact periodic_circleMap O R θ

@[simp] theorem dist_circlePoint_center (O : ℂ) (R θ : ℝ) :
    dist O (circlePoint O R θ) = |R| := by
  change dist O (circleMap O R θ) = |R|
  exact Metric.mem_sphere'.mp (circleMap_mem_sphere' O R θ)

/-- The chord length between two arbitrary points on a parametrized circle. -/
theorem dist_circlePoint_eq_two_mul_abs_sin_half (O : ℂ) (R θ₀ θ₁ : ℝ) :
    dist (circlePoint O R θ₀) (circlePoint O R θ₁) =
      2 * |R| * |Real.sin ((θ₁ - θ₀) / 2)| := by
  change dist (circleMap O R θ₀) (circleMap O R θ₁) = _
  rw [dist_eq_norm]
  have hexp : Complex.exp ((θ₁ : ℂ) * Complex.I) =
      Complex.exp ((θ₀ : ℂ) * Complex.I) *
        Complex.exp (((θ₁ - θ₀ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [Complex.ofReal_sub]
    ring_nf
  rw [circleMap, circleMap, show O + (R : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I) -
      (O + (R : ℂ) * Complex.exp ((θ₁ : ℂ) * Complex.I)) =
      (R : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I) *
        (1 - Complex.exp (((θ₁ - θ₀ : ℝ) : ℂ) * Complex.I)) by rw [hexp]; ring_nf,
    norm_mul, norm_mul]
  rw [show Complex.exp (((θ₁ - θ₀ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (θ₁ - θ₀ : ℝ)) by ring_nf]
  rw [show ‖1 - Complex.exp (Complex.I * (θ₁ - θ₀ : ℝ))‖ =
      ‖Complex.exp (Complex.I * (θ₁ - θ₀ : ℝ)) - 1‖ by
        rw [← norm_neg]
        congr 1
        ring_nf,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  simp
  ring_nf

/-- The cross product of three circle points, expanded as a cyclic sum of
sines of angle differences. -/
theorem crossR2_circlePoint_eq_sin_sub
    (O : ℂ) (R θ₀ θ₁ θ₂ : ℝ) :
    crossR2 (circlePoint O R θ₀) (circlePoint O R θ₁) (circlePoint O R θ₂) =
      R ^ 2 * (Real.sin (θ₁ - θ₀) + Real.sin (θ₂ - θ₁) -
        Real.sin (θ₂ - θ₀)) := by
  change crossR2 (circleMap O R θ₀) (circleMap O R θ₁) (circleMap O R θ₂) = _
  unfold crossR2
  simp only [Complex.sub_re, Complex.sub_im, circlePoint_re, circlePoint_im]
  rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]
  ring

private theorem sin_add_sin_sub_sin_add (a b : ℝ) :
    Real.sin a + Real.sin b - Real.sin (a + b) =
      4 * Real.sin (a / 2) * Real.sin (b / 2) * Real.sin ((a + b) / 2) := by
  have hsum := Real.sin_add_sin a b
  have htotal := Real.sin_two_mul ((a + b) / 2)
  have hproduct := Real.two_mul_sin_mul_sin (a / 2) (b / 2)
  calc
    Real.sin a + Real.sin b - Real.sin (a + b) =
        2 * Real.sin ((a + b) / 2) * Real.cos ((a - b) / 2) -
          2 * Real.sin ((a + b) / 2) * Real.cos ((a + b) / 2) := by
            rw [hsum]
            congr 1
            rw [← htotal]
            congr 1
            ring
    _ = 2 * Real.sin ((a + b) / 2) *
        (Real.cos ((a - b) / 2) - Real.cos ((a + b) / 2)) := by ring
    _ = 2 * Real.sin ((a + b) / 2) *
        (2 * Real.sin (a / 2) * Real.sin (b / 2)) := by
          rw [hproduct]
          congr 1
          rw [show (a - b) / 2 = a / 2 - b / 2 by ring,
            show (a + b) / 2 = a / 2 + b / 2 by ring]
    _ = 4 * Real.sin (a / 2) * Real.sin (b / 2) *
        Real.sin ((a + b) / 2) := by ring

/-- The exact factorization controlling the orientation of three points on a
circle. -/
theorem crossR2_circlePoint_eq_sin_half
    (O : ℂ) (R θ₀ θ₁ θ₂ : ℝ) :
    crossR2 (circlePoint O R θ₀) (circlePoint O R θ₁) (circlePoint O R θ₂) =
      4 * R ^ 2 * Real.sin ((θ₁ - θ₀) / 2) *
        Real.sin ((θ₂ - θ₁) / 2) * Real.sin ((θ₂ - θ₀) / 2) := by
  rw [crossR2_circlePoint_eq_sin_sub]
  have hsum : θ₂ - θ₀ = (θ₁ - θ₀) + (θ₂ - θ₁) := by ring
  rw [hsum, sin_add_sin_sub_sin_add]
  ring

/-- Three points whose real angle lifts satisfy
`θ₀ < θ₁ < θ₂ < θ₀ + 2π` have positive orientation. -/
theorem crossR2_circlePoint_pos_of_ordered
    (O : ℂ) {R θ₀ θ₁ θ₂ : ℝ} (hR : R ≠ 0)
    (h₀₁ : θ₀ < θ₁) (h₁₂ : θ₁ < θ₂) (hspan : θ₂ < θ₀ + 2 * Real.pi) :
    0 < crossR2 (circlePoint O R θ₀) (circlePoint O R θ₁)
      (circlePoint O R θ₂) := by
  have hsin₀₁ : 0 < Real.sin ((θ₁ - θ₀) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin₁₂ : 0 < Real.sin ((θ₂ - θ₁) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin₀₂ : 0 < Real.sin ((θ₂ - θ₀) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [crossR2_circlePoint_eq_sin_half]
  positivity

/-- If the third angle occurs before the oriented chord in the chosen real
window, lift it by one turn. The corresponding circle point is unchanged. -/
theorem crossR2_circlePoint_pos_of_ordered_after_wrap
    (O : ℂ) {R θ₀ θ₁ θ₂ : ℝ} (hR : R ≠ 0)
    (h₂₀ : θ₂ < θ₀) (h₀₁ : θ₀ < θ₁) (h₁₂ : θ₁ < θ₂ + 2 * Real.pi) :
    0 < crossR2 (circlePoint O R θ₀) (circlePoint O R θ₁)
      (circlePoint O R θ₂) := by
  rw [← circlePoint_add_two_pi O R θ₂]
  exact crossR2_circlePoint_pos_of_ordered O hR h₀₁ h₁₂ (by linarith)

/-- For the closing chord, lift its endpoint and every intermediate angle by
one turn. This gives the positive side of the closing oriented edge. -/
theorem crossR2_circlePoint_pos_of_wrapped_edge
    (O : ℂ) {R θ₀ θ₁ θ₂ : ℝ} (hR : R ≠ 0)
    (h₀₂ : θ₀ < θ₂) (h₂₁ : θ₂ < θ₁) (hspan : θ₁ < θ₀ + 2 * Real.pi) :
    0 < crossR2 (circlePoint O R θ₁) (circlePoint O R θ₀)
      (circlePoint O R θ₂) := by
  rw [← circlePoint_add_two_pi O R θ₀, ← circlePoint_add_two_pi O R θ₂]
  exact crossR2_circlePoint_pos_of_ordered O hR hspan (by linarith) (by linarith)

end Gluck.Discrete
