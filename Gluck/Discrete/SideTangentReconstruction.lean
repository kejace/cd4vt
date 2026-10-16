module

public import Gluck.Discrete.SideTangentConverse

/-!
# Reconstructing a balanced polygon from three-line circles

Normalizing the circle at each vertex recovers a closed polygon whose edges
are positive inverse scalings of the original edges. Its strict support and
exact signed affine balance therefore follow from the actual realization.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace Gluck.Discrete.SideTangent

variable {n : ℕ} [NeZero n] {ρ : ZMod n → ℝ} {P N C : ZMod n → ℂ}

lemma IsSideTangentRealization.normal_cross_ne (hn : 3 ≤ n)
    (h : IsSideTangentRealization ρ P N C) (i : ZMod n) :
    crossR2 0 (N (i - 1)) (N i) ≠ 0 := by
  obtain ⟨l, hl, he⟩ := h.oriented_edge (i - 1)
  obtain ⟨m, hm, hf⟩ := h.oriented_edge i
  simp only [sub_add_cancel] at he
  have ho := positiveOrientation_of_strictSupport hn h.strict_convex i
  have hid : crossR2 (P (i - 1)) (P i) (P (i + 1)) =
      l * m * crossR2 0 (N (i - 1)) (N i) := by
    have hs : P (i + 1) - P (i - 1) =
        (P i - P (i - 1)) + (P (i + 1) - P i) := by abel
    unfold crossR2
    rw [hs, he, hf]
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, sub_zero]
    ring
  intro hc
  rw [hid, hc, mul_zero] at ho
  exact lt_irrefl 0 ho

/-- Normalize the radius at the outgoing central edge. -/
noncomputable def reconstructedVertex (ρ : ZMod n → ℝ) (P C : ZMod n → ℂ)
    (i : ZMod n) : ℂ := (ρ i)⁻¹ • (P i - C i)

lemma IsSideTangentRealization.reconstructed_inner
    (h : IsSideTangentRealization ρ P N C) (i : ZMod n) :
    ⟪N (i - 1), reconstructedVertex ρ P C i⟫_ℝ = 1 ∧
      ⟪N i, reconstructedVertex ρ P C i⟫_ℝ = 1 := by
  simp only [reconstructedVertex, real_inner_smul_right, (h.circles i).1,
    (h.circles i).2.1, inv_mul_cancel₀ (h.radius_pos i).ne', and_self]

lemma IsSideTangentRealization.reconstructed_next (hn : 3 ≤ n)
    (h : IsSideTangentRealization ρ P N C) (i : ZMod n) :
    reconstructedVertex ρ P C (i + 1) = (ρ i)⁻¹ • (P (i + 1) - C i) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_two_inner_eq_zero (h.normal_cross_ne hn (i + 1))
  · rw [inner_sub_right, (h.reconstructed_inner (i + 1)).1,
      real_inner_smul_right]
    have he : ⟪N (i + 1 - 1), P (i + 1) - C i⟫_ℝ = ρ i := by
      rw [add_sub_cancel_right,
        show P (i + 1) - C i = (P (i + 1) - P i) + (P i - C i) by abel,
        inner_add_right, h.normal_edge_orthogonal, (h.circles i).2.1, zero_add]
    rw [he, inv_mul_cancel₀ (h.radius_pos i).ne', sub_self]
  · rw [inner_sub_right, (h.reconstructed_inner (i + 1)).2,
      real_inner_smul_right, (h.circles i).2.2,
      inv_mul_cancel₀ (h.radius_pos i).ne', sub_self]

lemma IsSideTangentRealization.reconstructed_edge (hn : 3 ≤ n)
    (h : IsSideTangentRealization ρ P N C) (i : ZMod n) :
    reconstructedVertex ρ P C (i + 1) - reconstructedVertex ρ P C i =
      (ρ i)⁻¹ • (P (i + 1) - P i) := by
  rw [h.reconstructed_next hn, reconstructedVertex, ← smul_sub]
  congr 1
  abel

/-- Every actual three-line realization produces a strict polygon with the exact
radius-difference affine balance. No additional tangential-fan hypothesis is assumed. -/
theorem exists_strict_balanced_polygon_of_realization (hn : 3 ≤ n)
    (h : IsSideTangentRealization ρ P N C) :
    ∃ Y : ZMod n → ℂ, StrictConvexEdgeSupport Y ∧
      ∑ i, radiusDifference ρ i • Y i = 0 := by
  let Y := reconstructedVertex ρ P C
  have hY : StrictConvexEdgeSupport Y :=
    strictSupport_of_positive_edge_scaling hn h.strict_convex
      (fun i ↦ (ρ i)⁻¹) (fun i ↦ inv_pos.mpr (h.radius_pos i))
      (h.reconstructed_edge hn)
  refine ⟨Y, hY, ?_⟩
  have he : ∀ i, ρ i • (Y (i + 1) - Y i) = P (i + 1) - P i := by
    intro i
    rw [h.reconstructed_edge hn, smul_smul, mul_inv_cancel₀ (h.radius_pos i).ne', one_smul]
  rw [show (∑ i, radiusDifference ρ i • Y i) =
      ∑ i, ρ i • (Y (i + 1) - Y i) by
        simpa only [radiusDifference] using (sum_scaled_edges ρ Y).symm]
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) P)

end Gluck.Discrete.SideTangent
