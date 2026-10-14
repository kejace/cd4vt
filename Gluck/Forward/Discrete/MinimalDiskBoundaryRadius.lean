/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.MinimalDiskContacts

/-!
# Radius minimality on boundary contacts

A finite minimal enclosing disk is already radius-minimal among disks which
contain only its boundary-contact vertices.  The proof interpolates toward a
hypothetically smaller contact-containing disk.  Boundary contacts remain
inside by convexity of distance, while the positive minimum of the radial
slacks of the finitely many noncontacts keeps every other vertex inside.
-/

open Set Metric

namespace Gluck.Forward

/-- A minimal enclosing disk is already radius-minimal among nonnegative-radius
disks containing all of its boundary-contact vertices. -/
theorem minimalEnclosingDiskR2_le_of_boundaryContactsInClosedDiskR2
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O C : ℂ} {R ρ : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) (hρ : 0 ≤ ρ)
    (hcontains : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      InClosedDiskR2 C ρ (v i)) :
    R ≤ ρ := by
  classical
  by_contra hRρ
  have hρR : ρ < R := lt_of_not_ge hRρ
  let slack : ZMod n → ℝ := fun i =>
    if OnDiskBoundaryR2 v O R i then 1 else R - dist O (v i)
  have hslack_pos : ∀ i, 0 < slack i := by
    intro i
    by_cases hi : OnDiskBoundaryR2 v O R i
    · dsimp only [slack]
      rw [if_pos hi]
      norm_num
    · dsimp only [slack]
      rw [if_neg hi]
      have hle_i : dist O (v i) ≤ R := Metric.mem_closedBall'.mp (hΔ.2.1 i)
      have hne_i : dist O (v i) ≠ R := fun hdist ↦ hi (Metric.mem_sphere'.mpr hdist)
      have hlt_i : dist O (v i) < R := lt_of_le_of_ne hle_i hne_i
      linarith
  let ε : ℝ := (Finset.univ : Finset (ZMod n)).inf'
    Finset.univ_nonempty slack
  have hε_pos : 0 < ε := by
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).2
      (fun i _hi => hslack_pos i)
  have hε_le (i : ZMod n) : ε ≤ slack i := by
    exact Finset.inf'_le slack (Finset.mem_univ i)
  let d : ℝ := dist O C
  let g : ℝ := R - ρ
  have hd_nonneg : 0 ≤ d := by positivity
  have hg_pos : 0 < g := by dsimp [g]; linarith
  have hdg_pos : 0 < d + g := add_pos_of_nonneg_of_pos hd_nonneg hg_pos
  let t : ℝ := min (1 / 2 : ℝ) (ε / (2 * (d + g)))
  have ht_pos : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num)
      (div_pos hε_pos (mul_pos (by norm_num) hdg_pos))
  have ht_le_half : t ≤ 1 / 2 := min_le_left _ _
  have ht_le_one : t ≤ 1 := ht_le_half.trans (by norm_num)
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_dg : t * (d + g) ≤ ε / 2 := by
    have ht_ratio : t ≤ ε / (2 * (d + g)) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right ht_ratio hdg_pos.le
    calc
      t * (d + g) ≤ (ε / (2 * (d + g))) * (d + g) := hmul
      _ = ε / 2 := by field_simp [hdg_pos.ne']
  let O' : ℂ := AffineMap.lineMap O C t
  let R' : ℝ := (1 - t) * R + t * ρ
  have hR'_nonneg : 0 ≤ R' := by
    dsimp [R']
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht_le_one) hΔ.1)
      (mul_nonneg ht_nonneg hρ)
  have hR'_lt : R' < R := by
    dsimp [R', g] at *
    nlinarith
  have hdist_convex (X : ℂ) :
      dist O' X ≤ (1 - t) * dist O X + t * dist C X := by
    have h := (convexOn_univ_dist X).2
      (Set.mem_univ O) (Set.mem_univ C)
      (sub_nonneg.mpr ht_le_one) ht_nonneg (by ring)
    simpa [O', AffineMap.lineMap_apply_module] using h
  have hcontainsAll : PolygonInClosedDiskR2 v O' R' := by
    intro i
    by_cases hi : OnDiskBoundaryR2 v O R i
    · have hiC : dist C (v i) ≤ ρ := Metric.mem_closedBall'.mp (hcontains i hi)
      apply Metric.mem_closedBall'.mpr
      calc
        dist O' (v i) ≤
            (1 - t) * dist O (v i) + t * dist C (v i) :=
          hdist_convex (v i)
        _ ≤ (1 - t) * R + t * ρ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (le_of_eq (Metric.mem_sphere'.mp hi))
              (sub_nonneg.mpr ht_le_one))
            (mul_le_mul_of_nonneg_left hiC ht_nonneg)
        _ = R' := rfl
    · have hεi : ε ≤ R - dist O (v i) := by
        have hεi' := hε_le i
        dsimp only [slack] at hεi'
        rwa [if_neg hi] at hεi'
      have hdist_O'O : dist O' O = t * d := by
        dsimp [O', d]
        rw [dist_lineMap_left]
        simp [abs_of_nonneg ht_nonneg]
      have htri : dist O' (v i) ≤ dist O' O + dist O (v i) :=
        dist_triangle _ _ _
      apply Metric.mem_closedBall'.mpr
      dsimp [R']
      calc
        dist O' (v i) ≤ dist O' O + dist O (v i) := htri
        _ = t * d + dist O (v i) := by rw [hdist_O'O]
        _ ≤ (1 - t) * R + t * ρ := by
          have : t * (d + g) ≤ ε :=
            ht_dg.trans (by linarith [hε_pos])
          dsimp [g] at this
          nlinarith
  exact (not_lt_of_ge (minimalEnclosingDiskR2_le_of_polygonInClosedDiskR2
    hΔ hR'_nonneg hcontainsAll)) hR'_lt

end Gluck.Forward
