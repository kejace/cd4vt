/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.MinimalDiskBoundaryHull
import Gluck.Discrete.CircleParameterGeometry

/-!
# Angular span of minimal-disk boundary contacts

The boundary contacts of a positive-radius minimal enclosing Euclidean disk
cannot all lie in an open semicircle.  Quantitatively, any closed real-angle
interval parameterizing all boundary contacts has length at least `π`.
-/

open Set Metric

namespace Gluck.Forward

/-- Projection of a radius vector onto the unit circle direction at angle
`φ`. -/
theorem real_inner_circlePoint_sub_center
    (O : ℂ) (R θ φ : ℝ) :
    inner ℝ (Gluck.Discrete.circlePoint 0 1 φ)
        (Gluck.Discrete.circlePoint O R θ - O) =
      R * Real.cos (θ - φ) := by
  change ((Gluck.Discrete.circlePoint O R θ - O) *
    star (Gluck.Discrete.circlePoint 0 1 φ)).re = _
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Gluck.Discrete.circlePoint_re, Gluck.Discrete.circlePoint_im,
    Complex.zero_re, Complex.zero_im, zero_add, one_mul,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Real.cos_sub]
  ring

/-- If every boundary contact of a positive-radius minimal enclosing disk has
a circle parameter in `[α, β]`, then that parameter interval has length at
least `π`. -/
theorem minimalEnclosingDiskR2_pi_le_parameterSpan_of_boundaryContacts
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R α β : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) (hR : 0 < R)
    (hparam : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      ∃ θ : ℝ, θ ∈ Set.Icc α β ∧
        v i = Gluck.Discrete.circlePoint O R θ) :
    Real.pi ≤ β - α := by
  by_contra hspanNot
  have hspan : β - α < Real.pi := lt_of_not_ge hspanNot
  let φ : ℝ := (α + β) / 2
  let u : ℂ := Gluck.Discrete.circlePoint 0 1 φ
  obtain ⟨i, hi, hinnerNonpos⟩ :=
    exists_boundaryContact_real_inner_nonpos hΔ u
  obtain ⟨θ, hθ, hvi⟩ := hparam i hi
  have hθwindow : θ - φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rcases hθ with ⟨hαθ, hθβ⟩
    dsimp [φ]
    constructor <;> linarith
  have hcos : 0 < Real.cos (θ - φ) :=
    Real.cos_pos_of_mem_Ioo hθwindow
  have hinnerPos : 0 < inner ℝ u (v i - O) := by
    rw [hvi]
    dsimp only [u]
    rw [real_inner_circlePoint_sub_center]
    exact mul_pos hR hcos
  exact (not_lt_of_ge hinnerNonpos) hinnerPos

end Gluck.Forward
