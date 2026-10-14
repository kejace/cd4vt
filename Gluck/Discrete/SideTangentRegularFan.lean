import Gluck.Discrete.SideTangentProjectiveFan

/-!
# Regular unit-incircle polygons

A strict tangential polygon for a constant profile needs no balancing argument.
The regular fan supplies its unit normals, strict support and interior contacts.
-/

open scoped InnerProductSpace

namespace Gluck.Discrete.SideTangent

/-- A regular fan exists for every size used by the discrete converse. -/
theorem exists_strictTangentialFan_of_four_le {n : ℕ} [NeZero n] (hn : 4 ≤ n) :
    ∃ U Y : Fin n → ℂ, IsStrictTangentialFan U Y := by
  have h := projective_squareFan_isStrictTangentialFan (n := n) (p := 1) (q := 2) (r := 3)
    hn (by decide) (by decide) (by decide) (by omega) (η := 1) zero_lt_one le_rfl
    (a := 0) (σ := 1) (by simp) zero_lt_one (by simp)
    (by intro i; simp [ProjectiveBall.denominator])
  exact ⟨_, _, h⟩

/-- The equilateral triangle supplies the smallest strict tangential fan. -/
theorem exists_strictTangentialFan_three :
    ∃ U Y : Fin 3 → ℂ, IsStrictTangentialFan U Y := by
  let θ : Fin 3 → ℝ := ![0, 2 * Real.pi / 3, 4 * Real.pi / 3]
  let U : Fin 3 → ℂ := fun i ↦ normal (θ i)
  let Y : Fin 3 → ℂ := fun i ↦ tangentIntersection (U i) (U (i + 1))
  refine ⟨U, Y, isStrictTangentialFan_of_geometry (fun i ↦ norm_normal (θ i)) ?_
    (fun i ↦ rfl) ?_⟩
  · intro i
    fin_cases i <;> norm_num [U, θ, cross_normal]
    · exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    · exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    · rw [show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi by ring, Real.sin_add_pi]
      exact neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity)
        (by nlinarith [Real.pi_pos]))
  · intro i j hji hjnext
    fin_cases i <;> fin_cases j
    all_goals try exact False.elim (hji rfl)
    all_goals try exact False.elim (hjnext rfl)
    · change ⟪normal (4 * Real.pi / 3),
        tangentIntersection (normal 0) (normal (2 * Real.pi / 3))⟫_ℝ < 1
      apply normal_support_lt_of_ordered <;> nlinarith [Real.pi_pos]
    · change ⟪normal 0,
        tangentIntersection (normal (2 * Real.pi / 3)) (normal (4 * Real.pi / 3))⟫_ℝ < 1
      apply normal_support_lt_of_wrapped <;> nlinarith [Real.pi_pos]
    · change ⟪normal (2 * Real.pi / 3),
        tangentIntersection (normal (4 * Real.pi / 3)) (normal 0)⟫_ℝ < 1
      have hp : normal 0 = normal (2 * Real.pi) := by apply Complex.ext <;> simp
      rw [hp]
      apply normal_support_lt_of_wrapped <;> nlinarith [Real.pi_pos]

/-- A strict unit-incircle polygon exists for every size at least three. -/
theorem exists_strictTangentialFan {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ U Y : Fin n → ℂ, IsStrictTangentialFan U Y := by
  by_cases h : n = 3
  · subst n
    exact exists_strictTangentialFan_three
  · exact exists_strictTangentialFan_of_four_le (by omega)

end Gluck.Discrete.SideTangent
