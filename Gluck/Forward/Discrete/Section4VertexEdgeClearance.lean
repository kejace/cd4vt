/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4ContactOrderCrosscut

/-!
# Local clearance from nonincident polygon edges

A vertex of a finite simple polygon has a positive-radius neighborhood which
misses any prescribed finite block of nonincident edges.  This is the local
stability input used when a boundary contact is perturbed by a tiny circle
detour in the three-contact orientation argument.
-/

namespace Gluck.Forward

open Gluck.Discrete Metric Set

private theorem initial_vertex_not_mem_natural_polygon_edge_aux
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) {k : ℕ}
    (hk : 1 < k) (hkn : k + 1 < n) :
    v (0 : ZMod n) ∉
      segment ℝ (v (k : ZMod n)) (v ((k + 1 : ℕ) : ZMod n)) := by
  intro hv0
  have hdisjoint := naturalPolygonEdges_disjoint_of_separated
    hsimple (by omega) hkn
  exact Set.disjoint_left.mp hdisjoint
    (left_mem_segment ℝ _ _) (by simpa using hv0)

/-- The initial vertex has a positive-radius neighborhood disjoint from every
edge in the natural block `m, …, n - 2`. -/
theorem exists_ball_disjoint_later_polygonEdges
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) {m : ℕ}
    (hm : 1 < m) (hmn : m < n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, m ≤ k → k + 1 < n →
      Disjoint (ball (v 0) ε)
        (segment ℝ (v (k : ZMod n)) (v ((k + 1 : ℕ) : ZMod n))) := by
  let K : Finset ℕ := Finset.Ico m (n - 1)
  let edge : ℕ → Set ℂ := fun k ↦
    segment ℝ (v (k : ZMod n)) (v ((k + 1 : ℕ) : ZMod n))
  let S : Set ℂ := ⋃ k ∈ K, edge k
  have hedgeCompact (k : ℕ) : IsCompact (edge k) := by
    dsimp [edge]
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hSclosed : IsClosed S := by
    apply isClosed_biUnion_finset
    intro k _hk
    exact (hedgeCompact k).isClosed
  have hv0not : v 0 ∉ S := by
    intro hv0
    simp only [S, Set.mem_iUnion] at hv0
    obtain ⟨k, hk⟩ := hv0
    obtain ⟨hkK, hv0edge⟩ := hk
    have hkm : m ≤ k := (Finset.mem_Ico.mp hkK).1
    have hkn : k + 1 < n := by
      have hklt : k < n - 1 := (Finset.mem_Ico.mp hkK).2
      omega
    exact initial_vertex_not_mem_natural_polygon_edge_aux hsimple
      (by omega) hkn (by simpa [edge] using hv0edge)
  have hv0comp : v 0 ∈ Sᶜ := hv0not
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hSclosed.isOpen_compl (v 0) hv0comp
  refine ⟨ε, hε, ?_⟩
  intro k hmk hkn
  have hkK : k ∈ K := by
    apply Finset.mem_Ico.mpr
    constructor
    · exact hmk
    · omega
  apply Set.disjoint_left.mpr
  intro x hxball hxedge
  have hxcomp : x ∈ Sᶜ := hball hxball
  apply hxcomp
  simp only [S, Set.mem_iUnion]
  exact ⟨k, hkK, hxedge⟩

end Gluck.Forward
