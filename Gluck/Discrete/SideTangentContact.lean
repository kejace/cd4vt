module

public import Gluck.Discrete.SideTangentFan

/-!
# Central contacts of a tangential polygon

Consecutive tangent intersections lie on opposite sides of their common unit
normal. This puts the incircle contact in the open central edge, with explicit
positive distances and without an extra geometric hypothesis.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Gluck.Discrete.SideTangent

/-- Coordinates of the intersection in the positively oriented tangent frame. -/
lemma tangentIntersection_eq_add {u v : ℂ} (hu : ‖u‖ = 1)
    (hd : 1 + ⟪u, v⟫_ℝ ≠ 0) :
    tangentIntersection u v = u + (crossR2 0 u v / (1 + ⟪u, v⟫_ℝ)) • (Complex.I * u) := by
  have hu' : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := Complex.sq_norm u
    rw [hu, Complex.normSq_apply] at h
    nlinarith only [h]
  apply Complex.ext <;>
    simp only [tangentIntersection, Complex.smul_re, Complex.smul_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add,
      smul_eq_mul]
  all_goals field_simp
  all_goals simp [crossR2, Complex.inner]
  · linear_combination -v.re * hu'
  · linear_combination -v.im * hu'

/-- The same vertex lies behind the contact in the second normal's tangent frame. -/
lemma tangentIntersection_eq_sub {u v : ℂ} (hv : ‖v‖ = 1)
    (hd : 1 + ⟪u, v⟫_ℝ ≠ 0) :
    tangentIntersection u v = v - (crossR2 0 u v / (1 + ⟪u, v⟫_ℝ)) • (Complex.I * v) := by
  rw [tangentIntersection_comm, tangentIntersection_eq_add hv (by rwa [real_inner_comm])]
  simp only [crossR2_swap 0 u v, real_inner_comm v u, neg_div, neg_smul, sub_eq_add_neg]

/-- Positive consecutive tangent distances put the common contact in the open edge. -/
theorem contact_mem_openSegment {u v w : ℂ} (hv : ‖v‖ = 1)
    (hd₁ : 0 < 1 + ⟪u, v⟫_ℝ) (hd₂ : 0 < 1 + ⟪v, w⟫_ℝ)
    (h₁ : 0 < crossR2 0 u v) (h₂ : 0 < crossR2 0 v w) :
    v ∈ openSegment ℝ (tangentIntersection u v) (tangentIntersection v w) := by
  let α := crossR2 0 u v / (1 + ⟪u, v⟫_ℝ)
  let β := crossR2 0 v w / (1 + ⟪v, w⟫_ℝ)
  have hα : 0 < α := div_pos h₁ hd₁
  have hβ : 0 < β := div_pos h₂ hd₂
  have hab : 0 < α + β := add_pos hα hβ
  refine ⟨β / (α + β), α / (α + β), div_pos hβ hab, div_pos hα hab, ?_, ?_⟩
  · field_simp
    ring
  · rw [tangentIntersection_eq_sub hv hd₁.ne', tangentIntersection_eq_add hv hd₂.ne']
    change (β / (α + β)) • (v - α • (Complex.I * v)) +
      (α / (α + β)) • (v + β • (Complex.I * v)) = v
    match_scalars <;> field_simp <;> ring

end Gluck.Discrete.SideTangent
