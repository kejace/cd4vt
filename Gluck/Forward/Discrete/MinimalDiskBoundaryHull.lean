/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.MinimalDiskBoundaryRadius
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Convex hull of minimal-disk boundary contacts

The center of a finite minimal enclosing disk belongs to the real convex hull
of its boundary-contact points.  First, a center perturbation and boundary
radius minimality show that the contacts cannot all lie in an open half-plane
through the center.  Strong separation of a point from the finite closed
convex hull then proves the result.
-/

open Set Metric

namespace Gluck.Forward


/-- A finite minimal enclosing disk has at least one boundary-contact
vertex. -/
theorem exists_onDiskBoundaryR2_of_minimalEnclosingDiskR2
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    ∃ i : ZMod n, OnDiskBoundaryR2 v O R i := by
  by_contra hnone
  push Not at hnone
  have hRle : R ≤ 0 :=
    minimalEnclosingDiskR2_le_of_boundaryContactsInClosedDiskR2
      (C := O) hΔ le_rfl (fun i hi => (hnone i hi).elim)
  have hRzero : R = 0 := le_antisymm hRle hΔ.1
  have hdist : dist O (v (0 : ZMod n)) = 0 := by
    apply le_antisymm
    · simpa [hRzero] using Metric.mem_closedBall'.mp (hΔ.2.1 (0 : ZMod n))
    · exact dist_nonneg
  exact hnone 0 (Metric.mem_sphere'.mpr (by simpa [hRzero] using hdist))

/-- In every direction from the center, some boundary contact has
nonpositive real inner product with that direction. -/
theorem exists_boundaryContact_real_inner_nonpos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) (u : ℂ) :
    ∃ i : ZMod n, OnDiskBoundaryR2 v O R i ∧
      inner ℝ u (v i - O) ≤ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hall : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      0 < inner ℝ u (v i - O) := by
    intro i hi
    exact hnone i hi
  obtain ⟨p, hp⟩ := exists_onDiskBoundaryR2_of_minimalEnclosingDiskR2 hΔ
  let margin : ZMod n → ℝ := fun i =>
    if OnDiskBoundaryR2 v O R i then inner ℝ u (v i - O) else 1
  have hmargin_pos : ∀ i, 0 < margin i := by
    intro i
    by_cases hi : OnDiskBoundaryR2 v O R i
    · dsimp only [margin]
      rw [if_pos hi]
      exact hall i hi
    · dsimp only [margin]
      rw [if_neg hi]
      norm_num
  let m : ℝ := (Finset.univ : Finset (ZMod n)).inf'
    Finset.univ_nonempty margin
  have hm_pos : 0 < m := by
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).2
      (fun i _hi => hmargin_pos i)
  have hm_le (i : ZMod n) : m ≤ margin i := by
    exact Finset.inf'_le margin (Finset.mem_univ i)
  let q : ℝ := ‖u‖ ^ 2 + 1
  have hq_pos : 0 < q := by dsimp [q]; positivity
  let t : ℝ := m / q
  have ht_pos : 0 < t := div_pos hm_pos hq_pos
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have htq : t * q = m := by
    dsimp [t]
    field_simp [hq_pos.ne']
  have ht_norm_sq : t * ‖u‖ ^ 2 < m := by
    have hnormq : ‖u‖ ^ 2 < q := by dsimp [q]; linarith
    have := mul_lt_mul_of_pos_left hnormq ht_pos
    rw [htq] at this
    exact this
  let C : ℂ := O + t • u
  have hcontactInside (i : ZMod n) (hi : OnDiskBoundaryR2 v O R i) :
      dist C (v i) < R := by
    have hmargin : m ≤ inner ℝ u (v i - O) := by
      have hmargin' := hm_le i
      dsimp only [margin] at hmargin'
      rwa [if_pos hi] at hmargin'
    have hxnorm : ‖v i - O‖ = R := by
      have hi0 : dist O (v i) = R := Metric.mem_sphere'.mp hi
      have hi' : dist (v i) O = R := by simpa [dist_comm] using hi0
      simpa [dist_eq_norm] using hi'
    have htmarg : t * m ≤ t * inner ℝ u (v i - O) :=
      mul_le_mul_of_nonneg_left hmargin ht_nonneg
    have hquad : t ^ 2 * ‖u‖ ^ 2 < t * m := by
      have hmul := mul_lt_mul_of_pos_left ht_norm_sq ht_pos
      nlinarith
    have hsq : ‖(v i - O) - t • u‖ ^ 2 < R ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht_nonneg, hxnorm]
      rw [real_inner_comm u (v i - O)]
      nlinarith
    have hdist : dist C (v i) = ‖(v i - O) - t • u‖ := by
      dsimp [C]
      rw [dist_comm, dist_eq_norm]
      congr 1
      module
    rw [hdist]
    nlinarith [norm_nonneg ((v i - O) - t • u), hΔ.1]
  let slack : ZMod n → ℝ := fun i =>
    if OnDiskBoundaryR2 v O R i then R - dist C (v i) else 1
  have hslack_pos : ∀ i, 0 < slack i := by
    intro i
    by_cases hi : OnDiskBoundaryR2 v O R i
    · dsimp only [slack]
      rw [if_pos hi]
      exact sub_pos.mpr (hcontactInside i hi)
    · dsimp only [slack]
      rw [if_neg hi]
      norm_num
  let ε : ℝ := (Finset.univ : Finset (ZMod n)).inf'
    Finset.univ_nonempty slack
  have hε_pos : 0 < ε := by
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).2
      (fun i _hi => hslack_pos i)
  have hε_le (i : ZMod n) : ε ≤ slack i := by
    exact Finset.inf'_le slack (Finset.mem_univ i)
  have hεR : ε ≤ R := by
    have hpε : ε ≤ R - dist C (v p) := by
      have hpε' := hε_le p
      dsimp only [slack] at hpε'
      rwa [if_pos hp] at hpε'
    exact hpε.trans (sub_le_self R dist_nonneg)
  let ρ : ℝ := R - ε / 2
  have hρ_nonneg : 0 ≤ ρ := by dsimp [ρ]; linarith
  have hρ_lt : ρ < R := by dsimp [ρ]; linarith
  have hcontactsρ : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      InClosedDiskR2 C ρ (v i) := by
    intro i hi
    have hiε : ε ≤ R - dist C (v i) := by
      have hiε' := hε_le i
      dsimp only [slack] at hiε'
      rwa [if_pos hi] at hiε'
    apply Metric.mem_closedBall'.mpr
    dsimp [ρ]
    linarith
  have hRρ := minimalEnclosingDiskR2_le_of_boundaryContactsInClosedDiskR2
    hΔ hρ_nonneg hcontactsρ
  exact (not_lt_of_ge hRρ) hρ_lt



end Gluck.Forward
