/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.AlternatingDiskPathCrossing
import Gluck.Forward.Discrete.PolygonalChainPath
import Gluck.Discrete.PolygonConvexity

/-!
# Circle order of separated polygonal subchains

Two separated subchains of a simple cyclic polygon have disjoint ranges.
Consequently, if their four endpoints lie on one containing circle, those
endpoints cannot alternate around the circle: alternating disk paths must
intersect.

This is the finite crosscut ingredient in the global contact-order step of
Dahlberg's Section 4 argument.
-/

namespace Gluck.Forward

open Gluck.Discrete Metric Set
open scoped unitInterval

/-- Edges whose natural starts are strictly separated in one unwrapped
period are disjoint in a simple cyclic polygon. -/
theorem naturalPolygonEdges_disjoint_of_separated
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) {i j : ℕ}
    (hij : i + 1 < j) (hjn : j + 1 < n) :
    Disjoint
      (segment ℝ (v (i : ZMod n)) (v ((i + 1 : ℕ) : ZMod n)))
      (segment ℝ (v (j : ZMod n)) (v ((j + 1 : ℕ) : ZMod n))) := by
  simpa [cyclicVertex] using
    hsimple.natural_edges_disjoint_of_separated
      (i := i) (j := j) hij (by omega) (Or.inl hjn)

/-- Every bundled subchain of a polygon contained in a closed disk remains
inside that disk. -/
theorem polygonalChainPath_inside_closedDisk
    {O : ℂ} {R : ℝ} {p : ℕ → ℂ} {N : ℕ}
    (hvertices : ∀ k : ℕ, k ≤ N → dist O (p k) ≤ R)
    (s : I) :
    dist O (polygonalChainPath p N s) ≤ R := by
  have hrange : polygonalChainPath p N s ∈
      Set.range (polygonalChainPath p N) := ⟨s, rfl⟩
  have hmem := range_polygonalChainPath_subset_of_convex
    (convex_closedBall O R) (fun k hk ↦ by
      simpa [mem_closedBall, dist_comm] using hvertices k hk) hrange
  simpa [mem_closedBall, dist_comm] using hmem

private theorem exists_intersecting_edges_of_circle_alternating_polygonal_chains_aux
    {O : ℂ} {R : ℝ} {p q : ℕ → ℂ} {M N : ℕ}
    {θi θk θj θl : ℝ}
    (hM : 0 < M) (hN : 0 < N)
    (hp0 : p 0 = circlePoint O R θi)
    (hpM : p M = circlePoint O R θj)
    (hq0 : q 0 = circlePoint O R θk)
    (hqN : q N = circlePoint O R θl)
    (hpinside : ∀ a : ℕ, a ≤ M → dist O (p a) ≤ R)
    (hqinside : ∀ b : ℕ, b ≤ N → dist O (q b) ≤ R)
    (hR : 0 < R)
    (hik : θi < θk) (hkj : θk < θj)
    (hjl : θj < θl) (hspan : θl < θi + 2 * Real.pi) :
    ∃ (x : ℂ) (a b : ℕ), a < M ∧ b < N ∧
      x ∈ segment ℝ (p a) (p (a + 1)) ∧
      x ∈ segment ℝ (q b) (q (b + 1)) := by
  let γ₀ := polygonalChainPath p M
  let δ₀ := polygonalChainPath q N
  let γ : Path (circlePoint O R θi) (circlePoint O R θj) :=
    γ₀.cast hp0.symm hpM.symm
  let δ : Path (circlePoint O R θk) (circlePoint O R θl) :=
    δ₀.cast hq0.symm hqN.symm
  have hγinside : ∀ s : I, dist O (γ s) ≤ R := by
    intro s
    change dist O (γ₀ s) ≤ R
    exact polygonalChainPath_inside_closedDisk hpinside s
  have hδinside : ∀ t : I, dist O (δ t) ≤ R := by
    intro t
    change dist O (δ₀ t) ≤ R
    exact polygonalChainPath_inside_closedDisk hqinside t
  obtain ⟨s, t, hst⟩ := paths_intersect_of_circle_alternating
    hR hik hkj hjl hspan γ δ hγinside hδinside
  have hsγ₀ : γ s ∈ Set.range γ := ⟨s, rfl⟩
  have htδ₀ : γ s ∈ Set.range δ := ⟨t, hst.symm⟩
  have hsγ : γ s ∈ Set.range (polygonalChainPath p M) := by
    simpa only [γ, γ₀, Path.cast_coe] using hsγ₀
  have htδ : γ s ∈ Set.range (polygonalChainPath q N) := by
    simpa only [δ, δ₀, Path.cast_coe, γ, γ₀] using htδ₀
  obtain ⟨a, b, haM, hbN, hpa, hqb⟩ :=
    exists_intersecting_edges_of_polygonalChainPath_ranges hM hN hsγ htδ
  exact ⟨γ s, a, b, haM, hbN, hpa, hqb⟩

/-- Four alternating circle endpoints cannot occur on two separated pieces
of one simple disk-contained polygon. -/
theorem not_circle_alternating_of_separated_polygonSubchains
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {i j k l : ℕ}
    {θi θk θj θl : ℝ}
    (hsimple : IsSimplePolygon v)
    (hinside : ∀ z : ZMod n, dist O (v z) ≤ R)
    (hR : 0 < R)
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hln : l < n)
    (hi : v (i : ZMod n) = circlePoint O R θi)
    (hk : v (k : ZMod n) = circlePoint O R θk)
    (hj : v (j : ZMod n) = circlePoint O R θj)
    (hl : v (l : ZMod n) = circlePoint O R θl)
    (hik : θi < θk) (hkj : θk < θj)
    (hjl : θj < θl) (hspan : θl < θi + 2 * Real.pi) : False := by
  let p : ℕ → ℂ := fun a ↦ v ((i + a : ℕ) : ZMod n)
  let q : ℕ → ℂ := fun b ↦ v ((k + b : ℕ) : ZMod n)
  let M : ℕ := j - i
  let N : ℕ := l - k
  have hM : 0 < M := by dsimp [M]; omega
  have hN : 0 < N := by dsimp [N]; omega
  have hp0 : p 0 = circlePoint O R θi := by simpa [p] using hi
  have hpM : p M = circlePoint O R θj := by
    change v ((i + M : ℕ) : ZMod n) = circlePoint O R θj
    rw [show i + M = j by dsimp [M]; omega]
    exact hj
  have hq0 : q 0 = circlePoint O R θk := by simpa [q] using hk
  have hqN : q N = circlePoint O R θl := by
    change v ((k + N : ℕ) : ZMod n) = circlePoint O R θl
    rw [show k + N = l by dsimp [N]; omega]
    exact hl
  obtain ⟨_x, a, b, haM, hbN, hpa, hqb⟩ :=
    exists_intersecting_edges_of_circle_alternating_polygonal_chains_aux
      hM hN hp0 hpM hq0 hqN
      (by intro a _ha; exact hinside _)
      (by intro b _hb; exact hinside _)
      hR hik hkj hjl hspan
  have hstarts : i + a + 1 < k + b := by
    have hai : i + a < j := by dsimp [M] at haM; omega
    omega
  have hsecond : k + b + 1 < n := by
    have hbl : k + b < l := by dsimp [N] at hbN; omega
    omega
  have hdisjoint := naturalPolygonEdges_disjoint_of_separated
    hsimple hstarts hsecond
  apply Set.disjoint_left.mp hdisjoint
  · simpa [p, Nat.add_assoc] using hpa
  · simpa [q, Nat.add_assoc] using hqb

end Gluck.Forward
