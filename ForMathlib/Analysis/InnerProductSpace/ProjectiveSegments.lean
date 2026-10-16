module

public import ForMathlib.Analysis.InnerProductSpace.ProjectiveBall
public import Mathlib.Analysis.Convex.Segment

/-!
# Open segments under projective ball normalization

Positive affine denominators preserve the interior of every segment. In the
side-tangent construction this keeps the unit-circle contact inside its finite
edge after the projective balancing step.
-/

@[expose] public section

open scoped InnerProductSpace

namespace ProjectiveBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma denominator_affine (a x y : E) {s t : ℝ} (hst : s + t = 1) :
    denominator a (s • x + t • y) = s * denominator a x + t * denominator a y := by
  simp only [denominator, inner_add_right, real_inner_smul_right]
  nlinarith only [hst]

lemma numerator_affine (a x y : E) (σ : ℝ) {s t : ℝ} (hst : s + t = 1) :
    numerator a σ (s • x + t • y) = s • numerator a σ x + t • numerator a σ y := by
  simp only [numerator, inner_add_right, real_inner_smul_right]
  match_scalars
  · ring
  · ring
  · linear_combination hst

/-- Positive endpoint denominators keep every interior contact in the open image edge. -/
theorem transform_mem_openSegment {a x y z : E} (σ : ℝ)
    (hx : 0 < denominator a x) (hy : 0 < denominator a y)
    (hz : z ∈ openSegment ℝ x y) :
    transform a σ z ∈ openSegment ℝ (transform a σ x) (transform a σ y) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  have hd : 0 < denominator a (s • x + t • y) := by
    rw [denominator_affine a x y hst]
    exact add_pos (mul_pos hs hx) (mul_pos ht hy)
  refine ⟨s * denominator a x / denominator a (s • x + t • y),
    t * denominator a y / denominator a (s • x + t • y),
    div_pos (mul_pos hs hx) hd, div_pos (mul_pos ht hy) hd, ?_, ?_⟩
  · rw [← add_div, ← denominator_affine a x y hst, div_self hd.ne']
  · simp only [transform, numerator_affine a x y σ hst]
    match_scalars <;> field_simp

end ProjectiveBall
