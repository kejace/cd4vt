/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Analysis.Convex.PathConnected

/-!
# Bundled paths for finite polygonal chains

This file turns a naturally indexed finite vertex chain into a Mathlib
`Path` by concatenating straight segment paths.  Its range theorem exposes
exactly the constituent edge segments, which is the bridge needed to combine
continuous planar crossing theorems with `IsSimplePolygon`.
-/

namespace Gluck.Forward

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- The piecewise-linear path through `p 0, p 1, …, p N`. -/
noncomputable def polygonalChainPath (p : ℕ → E) :
    (N : ℕ) → Path (p 0) (p N)
  | 0 => Path.refl (p 0)
  | N + 1 =>
      (polygonalChainPath p N).trans (Path.segment (p N) (p (N + 1)))


@[simp] theorem polygonalChainPath_succ (p : ℕ → E) (N : ℕ) :
    polygonalChainPath p (N + 1) =
      (polygonalChainPath p N).trans
        (Path.segment (p N) (p (N + 1))) := rfl

/-- A point is on a finite polygonal chain iff it is the initial vertex or
belongs to one of its edge segments. -/
theorem mem_range_polygonalChainPath_iff (p : ℕ → E) (x : E) :
    ∀ N : ℕ,
      x ∈ Set.range (polygonalChainPath p N) ↔
        x = p 0 ∨ ∃ k : ℕ, k < N ∧ x ∈ segment ℝ (p k) (p (k + 1)) := by
  intro N
  induction N with
  | zero =>
      simp [polygonalChainPath, Path.refl_range]
  | succ N ih =>
      rw [polygonalChainPath_succ, Path.trans_range]
      simp only [Set.mem_union, ih, Path.range_segment]
      constructor
      · rintro ((hx | ⟨k, hkN, hxk⟩) | hxlast)
        · exact Or.inl hx
        · exact Or.inr ⟨k, by omega, hxk⟩
        · exact Or.inr ⟨N, by omega, by simpa using hxlast⟩
      · rintro (hx | ⟨k, hk, hxk⟩)
        · exact Or.inl (Or.inl hx)
        · by_cases hkN : k < N
          · exact Or.inl (Or.inr ⟨k, hkN, hxk⟩)
          · have hkeq : k = N := by omega
            subst k
            exact Or.inr (by simpa using hxk)

/-- For a nontrivial chain, the initial vertex already belongs to its first
edge, so the path range is exactly the union of the constituent segments. -/
theorem mem_range_polygonalChainPath_iff_mem_edge
    (p : ℕ → E) (x : E) {N : ℕ} (hN : 0 < N) :
    x ∈ Set.range (polygonalChainPath p N) ↔
      ∃ k : ℕ, k < N ∧ x ∈ segment ℝ (p k) (p (k + 1)) := by
  rw [mem_range_polygonalChainPath_iff]
  constructor
  · rintro (rfl | hx)
    · exact ⟨0, hN, left_mem_segment ℝ _ _⟩
    · exact hx
  · exact Or.inr

/-- Every edge of a nonempty finite chain lies in the range of its bundled
polygonal path. -/
theorem segment_subset_range_polygonalChainPath
    (p : ℕ → E) {N k : ℕ} (hk : k < N) :
    segment ℝ (p k) (p (k + 1)) ⊆
      Set.range (polygonalChainPath p N) := by
  intro x hx
  exact (mem_range_polygonalChainPath_iff_mem_edge p x
    (Nat.zero_lt_of_lt hk)).2 ⟨k, hk, hx⟩

/-- An intersection of two nontrivial polygonal path ranges is witnessed by
an intersection of one edge from each chain. -/
theorem exists_intersecting_edges_of_polygonalChainPath_ranges
    {p q : ℕ → E} {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    {x : E}
    (hxp : x ∈ Set.range (polygonalChainPath p M))
    (hxq : x ∈ Set.range (polygonalChainPath q N)) :
    ∃ i j : ℕ, i < M ∧ j < N ∧
      x ∈ segment ℝ (p i) (p (i + 1)) ∧
      x ∈ segment ℝ (q j) (q (j + 1)) := by
  obtain ⟨i, hi, hxi⟩ :=
    (mem_range_polygonalChainPath_iff_mem_edge p x hM).1 hxp
  obtain ⟨j, hj, hxj⟩ :=
    (mem_range_polygonalChainPath_iff_mem_edge q x hN).1 hxq
  exact ⟨i, j, hi, hj, hxi, hxj⟩

/-- A polygonal chain whose vertices lie in a convex set has its entire range
in that set. -/
theorem range_polygonalChainPath_subset_of_convex
    {s : Set E} (hs : Convex ℝ s) {p : ℕ → E} {N : ℕ}
    (hp : ∀ k, k ≤ N → p k ∈ s) :
    Set.range (polygonalChainPath p N) ⊆ s := by
  intro x hx
  rw [mem_range_polygonalChainPath_iff] at hx
  rcases hx with rfl | ⟨k, hk, hx⟩
  · exact hp 0 (Nat.zero_le N)
  · exact hs.segment_subset (hp k hk.le) (hp (k + 1) hk) hx

/-- Two nontrivial polygonal chains have disjoint ranges exactly when every
edge of the first is disjoint from every edge of the second. -/
theorem disjoint_polygonalChainPath_ranges_iff
    {p q : ℕ → E} {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    Disjoint (Set.range (polygonalChainPath p M))
        (Set.range (polygonalChainPath q N)) ↔
      ∀ i, i < M → ∀ j, j < N →
        Disjoint (segment ℝ (p i) (p (i + 1)))
          (segment ℝ (q j) (q (j + 1))) := by
  constructor
  · intro h i hi j hj
    exact h.mono (segment_subset_range_polygonalChainPath p hi)
      (segment_subset_range_polygonalChainPath q hj)
  · intro h
    apply Set.disjoint_left.mpr
    intro x hxp hxq
    obtain ⟨i, hi, hxi⟩ :=
      (mem_range_polygonalChainPath_iff_mem_edge p x hM).mp hxp
    obtain ⟨j, hj, hxj⟩ :=
      (mem_range_polygonalChainPath_iff_mem_edge q x hN).mp hxq
    exact Set.disjoint_left.mp (h i hi j hj) hxi hxj

end Gluck.Forward
