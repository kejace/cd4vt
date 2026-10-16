module

public import Gluck.Discrete.SideTangentNecessityBalance
public import Gluck.Discrete.SideTangentReconstruction

/-!
# Wegner forward theorem and exact supporting-line-circle characterization

For the actual inward three-supporting-line circles with central contacts in
open edge segments, the radii are constant or their cyclic first differences
have at least four sign changes. Combined with the proved converse, this is an
exact characterization, including repeated adjacent radii.
-/

@[expose] public section

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- Zero cyclic first differences force the original radius profile to be constant. -/
lemma constant_of_radiusDifference_eq_zero [NeZero n] {ρ : ZMod n → ℝ}
    (h : ∀ i, radiusDifference ρ i = 0) : ∃ r, ∀ i, ρ i = r := by
  have hsucc : ∀ i, ρ (i + 1) = ρ i := by
    intro i
    have hi := h (i + 1)
    simp only [radiusDifference, add_sub_cancel_right, sub_eq_zero] at hi
    exact hi.symm
  have hnat : ∀ k : ℕ, ρ (k : ZMod n) = ρ 0 := by
    intro k
    induction k with
    | zero => simp only [Nat.cast_zero]
    | succ k ih =>
      simpa only [Nat.cast_add, Nat.cast_one] using (hsucc (k : ZMod n)).trans ih
  exact ⟨ρ 0, fun i ↦ by simpa only [ZMod.natCast_zmod_val] using hnat i.val⟩

/-- **Wegner necessity.** An actual side-tangent realization has positive radii
which are constant or have four cyclic sign changes in their first differences. -/
theorem sideTangentForward [NeZero n] (hn : 3 ≤ n) {ρ : ZMod n → ℝ}
    {P N C : ZMod n → ℂ} (h : IsSideTangentRealization ρ P N C) :
    SideTangentAdmissible ρ := by
  obtain ⟨Y, hY, hb⟩ := exists_strict_balanced_polygon_of_realization hn h
  refine ⟨h.radius_pos, ?_⟩
  rcases zero_or_dfv_of_strict_affine_balance hn hY (sum_radiusDifference ρ) hb with hz | hd
  · exact Or.inl (constant_of_radiusDifference_eq_zero hz)
  · exact Or.inr hd

/-- Positive constant profiles and exactly the four-sign-change profiles are the
radii of inward circles tangent to consecutive supporting lines of a simple strictly
convex polygon, with the central tangency point in its open edge. -/
theorem realizesSideTangent_iff_admissible [NeZero n] (hn : 4 ≤ n) (ρ : ZMod n → ℝ) :
    RealizesSideTangent ρ ↔ SideTangentAdmissible ρ := by
  constructor
  · rintro ⟨P, N, C, h⟩
    exact sideTangentForward (by omega) h
  · exact sideTangentConverse hn ρ

/-- The nonconstant positive-radius version of the side-tangent characterization. -/
theorem realizesSideTangent_iff_dfv [NeZero n] (hn : 4 ≤ n) {ρ : ZMod n → ℝ}
    (hρ : ∀ i, 0 < ρ i) (hnc : ¬ ∃ r, ∀ i, ρ i = r) :
    RealizesSideTangent ρ ↔ DFV (radiusDifference ρ) 0 := by
  rw [realizesSideTangent_iff_admissible hn]
  exact ⟨fun h ↦ h.2.resolve_left hnc, fun h ↦ ⟨hρ, Or.inr h⟩⟩

end Gluck.Discrete.SideTangent
