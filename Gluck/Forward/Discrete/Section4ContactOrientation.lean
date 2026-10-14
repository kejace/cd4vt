/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Dahlberg

/-!
# Orientation of minimal-disk contacts

This file isolates the local geometric part of the orientation bridge used in
Dahlberg's Section 4.  A contact with a minimal enclosing circle is an extreme
point of its closed ball.  Local regularity and polygon simplicity therefore
exclude a collinear turn at every contact.
-/

namespace Gluck.Forward

/-- A locally regular vertex on a minimal enclosing circle has nonzero
oriented area with its two neighbors.

If the triple were collinear, regularity would put the middle vertex in the
neighbor segment.  Simplicity makes it an open-segment point, while strict
convexity of the Euclidean closed ball puts every such point strictly inside
the minimal disk, contradicting boundary incidence. -/
theorem crossR2_ne_zero_of_minimalEnclosingDisk_boundary
    {n : ℕ} {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    {i : ZMod n} (hboundary : OnDiskBoundaryR2 v O R i) :
    Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) ≠ 0 := by
  intro hcross
  have hprevSelf : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  have hselfNext : v i ≠ v (i + 1) := hsimple.1 i
  have hprevNext : v (i - 1) ≠ v (i + 1) := by
    simpa [sub_eq_add_neg, add_assoc] using
      isSimplePolygon_two_step_ne hsimple (i - 1)
  have hsegment : v i ∈ segment ℝ (v (i - 1)) (v (i + 1)) :=
    dahlbergRegularAt_segment_of_cross_eq_zero
      hprevSelf hselfNext hprevNext (hregular i) hcross
  have hopen : v i ∈ openSegment ℝ (v (i - 1)) (v (i + 1)) :=
    mem_openSegment_of_ne_left_right hprevSelf hselfNext.symm hsegment
  have hprevBall : v (i - 1) ∈ Metric.closedBall O R := by
    exact hΔ.2.1 (i - 1)
  have hnextBall : v (i + 1) ∈ Metric.closedBall O R := by
    exact hΔ.2.1 (i + 1)
  have hiBall : v i ∈ Metric.ball O R :=
    openSegment_subset_ball_of_ne hprevBall hnextBall hprevNext hopen
  have hiLt : dist O (v i) < R := by
    simpa [Metric.mem_ball, dist_comm] using hiBall
  have hiEq : dist O (v i) = R := Metric.mem_sphere'.mp hboundary
  exact (ne_of_lt hiLt) hiEq

/-- A point of a boundary chord that remains in the closed disk has affine
parameter in the unit interval. -/
private theorem lineMap_parameter_mem_Icc_of_mem_closedBall_of_boundary
    {O A B Y : ℂ} {R s : ℝ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hY : Y = (AffineMap.lineMap A B) s)
    (hYmem : dist O Y ≤ R) :
    s ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · by_contra hs0
    have hsneg : s < 0 := lt_of_not_ge hs0
    let r : ℝ := -s / (1 - s)
    have hr0 : 0 < r := by
      exact div_pos (neg_pos.mpr hsneg) (sub_pos.mpr (by linarith))
    have hr1 : r < 1 := by
      apply (div_lt_one (sub_pos.mpr (by linarith))).mpr
      linarith
    have hAline : A = (AffineMap.lineMap Y B) r := by
      rw [hY]
      dsimp [r]
      rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
      apply Complex.ext
      all_goals simp only [vsub_eq_sub, vadd_eq_add, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
      all_goals field_simp [show 1 - s ≠ 0 by linarith]
      all_goals ring
    have hYneB : Y ≠ B := by
      intro hEq
      have hs1 : s = 1 := by
        apply (AffineMap.lineMap_injective ℝ hAB)
        rw [← hY, hEq]
        simp
      linarith
    have hYball : Y ∈ Metric.closedBall O R := by
      simpa [Metric.mem_closedBall, dist_comm] using hYmem
    have hBball : B ∈ Metric.closedBall O R := by
      simpa [Metric.mem_closedBall, dist_comm] using hB.le
    have hAopen : A ∈ openSegment ℝ Y B := by
      rw [hAline]
      exact lineMap_mem_openSegment ℝ Y B ⟨hr0, hr1⟩
    have hAball : A ∈ Metric.ball O R :=
      openSegment_subset_ball_of_ne hYball hBball hYneB hAopen
    have hAlt : dist O A < R := by
      simpa [Metric.mem_ball, dist_comm] using hAball
    linarith
  · by_contra hs1
    have hspos : 1 < s := lt_of_not_ge hs1
    let r : ℝ := 1 / s
    have hr0 : 0 < r := one_div_pos.mpr (by linarith)
    have hr1 : r < 1 := (div_lt_one (by linarith : 0 < s)).mpr (by linarith)
    have hBline : B = (AffineMap.lineMap A Y) r := by
      rw [hY]
      dsimp [r]
      rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
      apply Complex.ext
      all_goals simp only [vsub_eq_sub, vadd_eq_add, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
      all_goals field_simp [show s ≠ 0 by linarith]
      all_goals ring
    have hAneY : A ≠ Y := by
      intro hEq
      have hs0 : s = 0 := by
        apply (AffineMap.lineMap_injective ℝ hAB)
        rw [← hY, ← hEq]
        simp
      linarith
    have hAball : A ∈ Metric.closedBall O R := by
      simpa [Metric.mem_closedBall, dist_comm] using hA.le
    have hYball : Y ∈ Metric.closedBall O R := by
      simpa [Metric.mem_closedBall, dist_comm] using hYmem
    have hBopen : B ∈ openSegment ℝ A Y := by
      rw [hBline]
      exact lineMap_mem_openSegment ℝ A Y ⟨hr0, hr1⟩
    have hBball : B ∈ Metric.ball O R :=
      openSegment_subset_ball_of_ne hAball hYball hAneY hBopen
    have hBlt : dist O B < R := by
      simpa [Metric.mem_ball, dist_comm] using hBball
    linarith

/-- Opposite strict sides of a boundary chord force two disk-contained
segments to intersect. -/
private theorem not_crossR2_pos_neg_of_disjoint_segments_in_disk
    {O A B C D : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hC : dist O C ≤ R) (hD : dist O D ≤ R)
    (hdisjoint : Disjoint (segment ℝ A B) (segment ℝ C D)) :
    ¬ (0 < Gluck.Discrete.crossR2 A B C ∧
      Gluck.Discrete.crossR2 A B D < 0) := by
  rintro ⟨hCpos, hDneg⟩
  let α := Gluck.Discrete.crossR2 A B C
  let β := Gluck.Discrete.crossR2 A B D
  let t := α / (α - β)
  have hden : 0 < α - β := by dsimp [α, β]; linarith
  have ht0 : 0 < t := div_pos (by simpa [α] using hCpos) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by dsimp [α, β]; linarith)
  let Y := (AffineMap.lineMap C D) t
  have hcrossY : Gluck.Discrete.crossR2 A B Y = 0 := by
    dsimp [Y]
    rw [Gluck.Discrete.crossR2_lineMap]
    change (1 - t) * α + t * β = 0
    dsimp [t]
    field_simp [hden.ne']
    ring
  obtain ⟨s, hs⟩ := Gluck.Discrete.exists_lineMap_eq_of_crossR2_eq_zero hAB hcrossY
  have hCball : C ∈ Metric.closedBall O R := by
    simpa [Metric.mem_closedBall, dist_comm] using hC
  have hDball : D ∈ Metric.closedBall O R := by
    simpa [Metric.mem_closedBall, dist_comm] using hD
  have hYsegCD : Y ∈ segment ℝ C D := by
    exact lineMap_mem_segment ℝ C D ⟨ht0.le, ht1.le⟩
  have hYball : Y ∈ Metric.closedBall O R :=
    (convex_closedBall O R).segment_subset hCball hDball hYsegCD
  have hYdist : dist O Y ≤ R := by
    simpa [Metric.mem_closedBall, dist_comm] using hYball
  have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 :=
    lineMap_parameter_mem_Icc_of_mem_closedBall_of_boundary
      hAB hA hB hs.symm hYdist
  have hYsegAB : Y ∈ segment ℝ A B := by
    rw [← hs]
    exact lineMap_mem_segment ℝ A B hsIcc
  exact Set.disjoint_left.mp hdisjoint hYsegAB hYsegCD

/-- A segment in a closed disk whose endpoints lie on opposite strict sides
of a boundary chord must meet that chord.

This is the public edge-level crossing primitive extracted from the contact
orientation argument.  It is deliberately stated as failure of disjointness,
which is exactly the form consumed by polygonal-chain reductions. -/
theorem boundaryChord_not_disjoint_segment_of_cross_pos_neg
    {O A B C D : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hC : dist O C ≤ R) (hD : dist O D ≤ R)
    (hCpos : 0 < Gluck.Discrete.crossR2 A B C)
    (hDneg : Gluck.Discrete.crossR2 A B D < 0) :
    ¬ Disjoint (segment ℝ A B) (segment ℝ C D) := by
  intro hdisjoint
  exact not_crossR2_pos_neg_of_disjoint_segments_in_disk
    hAB hA hB hC hD hdisjoint ⟨hCpos, hDneg⟩

/-- A disk-contained point on the supporting line of a nondegenerate
boundary chord belongs to the chord itself. -/
theorem mem_boundaryChord_of_cross_eq_zero
    {O A B Y : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hY : dist O Y ≤ R)
    (hcross : Gluck.Discrete.crossR2 A B Y = 0) :
    Y ∈ segment ℝ A B := by
  obtain ⟨s, hs⟩ := Gluck.Discrete.exists_lineMap_eq_of_crossR2_eq_zero hAB hcross
  have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 :=
    lineMap_parameter_mem_Icc_of_mem_closedBall_of_boundary
      hAB hA hB hs.symm hY
  rw [← hs]
  exact lineMap_mem_segment ℝ A B hsIcc

private theorem zmod_natCast_ne_of_lt_disk {n : ℕ} [NeZero n] {a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (a : ZMod n) ≠ (b : ZMod n) := by
  rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]
  exact hab

private theorem first_lifted_edge_disjoint {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) {j : ℕ}
    (hj2 : 2 ≤ j) (hjn : j + 1 < n) :
    Disjoint
      (segment ℝ (v 0) (v 1))
      (segment ℝ (v (j : ZMod n)) (v (j + 1 : ZMod n))) := by
  have h0j : (0 : ZMod n) ≠ (j : ZMod n) := by
    have h := zmod_natCast_ne_of_lt_disk (n := n) (a := 0) (b := j)
      (by omega) (by omega) (by omega)
    simpa using h
  have h1j : (0 : ZMod n) + 1 ≠ (j : ZMod n) := by
    have h := zmod_natCast_ne_of_lt_disk (n := n) (a := 1) (b := j)
      (by omega) (by omega) (by omega)
    simpa using h
  have hj10 : (j : ZMod n) + 1 ≠ 0 := by
    have h := zmod_natCast_ne_of_lt_disk (n := n) (a := j + 1) (b := 0)
      hjn (by omega) (by omega)
    simpa [Nat.cast_add] using h
  apply Set.disjoint_iff_inter_eq_empty.mpr
  simpa [Nat.cast_add] using hsimple.2.2 (0 : ZMod n) (j : ZMod n)
    h0j h1j hj10

private theorem first_boundary_edge_other_vertex_cross_ne_zero
    {n : ℕ} [NeZero n] (_hn : 3 ≤ n) {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcontains : ∀ z : ZMod n, dist O (v z) ≤ R)
    (h0 : dist O (v 0) = R) (h1 : dist O (v 1) = R)
    {j : ℕ} (hj2 : 2 ≤ j) (hjn : j < n) :
    Gluck.Discrete.crossR2 (v 0) (v 1) (v (j : ZMod n)) ≠ 0 := by
  intro hcross
  have h01 : v 0 ≠ v 1 := by simpa using hsimple.1 (0 : ZMod n)
  obtain ⟨s, hs⟩ := Gluck.Discrete.exists_lineMap_eq_of_crossR2_eq_zero h01 hcross
  have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 :=
    lineMap_parameter_mem_Icc_of_mem_closedBall_of_boundary
      h01 h0 h1 hs.symm (hcontains (j : ZMod n))
  have hjseg : v (j : ZMod n) ∈ segment ℝ (v 0) (v 1) := by
    rw [← hs]
    exact lineMap_mem_segment ℝ _ _ hsIcc
  by_cases hjlast : j + 1 = n
  · have hjcast : (j : ZMod n) + 1 = 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add, hjlast, ZMod.natCast_self]
    have hjclosing : v (j : ZMod n) ∈
        segment ℝ (v (j : ZMod n)) (v 0) := left_mem_segment ℝ _ _
    have hjinter : v (j : ZMod n) ∈
        segment ℝ (v (j : ZMod n)) (v 0) ∩ segment ℝ (v 0) (v 1) :=
      ⟨hjclosing, hjseg⟩
    have hjzero : v (j : ZMod n) = v 0 := by
      have hcon := hsimple.2.1 (j : ZMod n)
      rw [hjcast] at hcon
      have hcon' : segment ℝ (v (j : ZMod n)) (v 0) ∩
          segment ℝ (v 0) (v 1) = {v 0} := by
        simpa using hcon
      rw [hcon'] at hjinter
      simpa using hjinter
    exact hsimple.1 (j : ZMod n) (by simpa [hjcast] using hjzero)
  · have hjn' : j + 1 < n := by omega
    have hdisj := first_lifted_edge_disjoint hsimple hj2 hjn'
    exact Set.disjoint_left.mp hdisj hjseg (left_mem_segment ℝ _ _)

/-- All nonendpoint vertices of a simple polygon lie on one strict side of
an edge whose endpoints lie on the same containing circle. -/
private theorem first_boundary_edge_other_vertices_same_side
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcontains : ∀ z : ZMod n, dist O (v z) ≤ R)
    (h0 : dist O (v 0) = R) (h1 : dist O (v 1) = R) :
    (∀ j : ℕ, 2 ≤ j → j < n →
        0 < Gluck.Discrete.crossR2 (v 0) (v 1) (v (j : ZMod n))) ∨
      (∀ j : ℕ, 2 ≤ j → j < n →
        Gluck.Discrete.crossR2 (v 0) (v 1) (v (j : ZMod n)) < 0) := by
  let f : ℕ → ℝ := fun j =>
    Gluck.Discrete.crossR2 (v 0) (v 1) (v (j : ZMod n))
  have h01 : v 0 ≠ v 1 := by simpa using hsimple.1 (0 : ZMod n)
  have hne : ∀ j : ℕ, 2 ≤ j → j < n → f j ≠ 0 := by
    intro j hj2 hjn
    exact first_boundary_edge_other_vertex_cross_ne_zero
      hn hsimple hcontains h0 h1 hj2 hjn
  have hstep : ∀ j : ℕ, 2 ≤ j → j + 1 < n →
      ¬ (0 < f j ∧ f (j + 1) < 0) ∧
      ¬ (f j < 0 ∧ 0 < f (j + 1)) := by
    intro j hj2 hjn
    have hdisjRaw := first_lifted_edge_disjoint hsimple hj2 hjn
    have hdisj : Disjoint
        (segment ℝ (v 0) (v 1))
        (segment ℝ (v (j : ZMod n)) (v ((j + 1 : ℕ) : ZMod n))) := by
      simpa [Nat.cast_add] using hdisjRaw
    constructor
    · exact not_crossR2_pos_neg_of_disjoint_segments_in_disk
        h01 h0 h1 (hcontains (j : ZMod n))
          (hcontains ((j + 1 : ℕ) : ZMod n)) hdisj
    · intro hnegpos
      have hdisj' : Disjoint
          (segment ℝ (v 0) (v 1))
          (segment ℝ (v ((j + 1 : ℕ) : ZMod n)) (v (j : ZMod n))) := by
        simpa [segment_symm] using hdisj
      exact not_crossR2_pos_neg_of_disjoint_segments_in_disk
        h01 h0 h1 (hcontains ((j + 1 : ℕ) : ZMod n))
          (hcontains (j : ZMod n)) hdisj' ⟨hnegpos.2, hnegpos.1⟩
  have hpos_of_h2 : 0 < f 2 →
      ∀ j : ℕ, 2 ≤ j → j < n → 0 < f j := by
    intro h2 j hj2 hjn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj2
    induction d with
    | zero => simpa using h2
    | succ d ih =>
        have hprev : 0 < f (2 + d) := ih (by omega) (by omega)
        have hcurNe : f (2 + (d + 1)) ≠ 0 := hne _ (by omega) (by omega)
        rcases lt_or_gt_of_ne hcurNe with hcurNeg | hcurPos
        · exfalso
          exact (hstep (2 + d) (by omega) (by omega)).1
            ⟨hprev, by simpa [Nat.add_assoc] using hcurNeg⟩
        · simpa [Nat.add_assoc] using hcurPos
  have hneg_of_h2 : f 2 < 0 →
      ∀ j : ℕ, 2 ≤ j → j < n → f j < 0 := by
    intro h2 j hj2 hjn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj2
    induction d with
    | zero => simpa using h2
    | succ d ih =>
        have hprev : f (2 + d) < 0 := ih (by omega) (by omega)
        have hcurNe : f (2 + (d + 1)) ≠ 0 := hne _ (by omega) (by omega)
        rcases lt_or_gt_of_ne hcurNe with hcurNeg | hcurPos
        · simpa [Nat.add_assoc] using hcurNeg
        · exfalso
          exact (hstep (2 + d) (by omega) (by omega)).2
            ⟨hprev, by simpa [Nat.add_assoc] using hcurPos⟩
  have h2ne : f 2 ≠ 0 := hne 2 (by omega) (by omega)
  rcases lt_or_gt_of_ne h2ne with h2neg | h2pos
  · exact Or.inr (hneg_of_h2 h2neg)
  · exact Or.inl (hpos_of_h2 h2pos)

/-- At consecutive contacts of a containing disk, the two local turns have
the same strict sign. -/
private theorem adjacent_boundary_cross_same_sign
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcontains : ∀ z : ZMod n, dist O (v z) ≤ R)
    {i : ZMod n}
    (hi : dist O (v i) = R) (hi1 : dist O (v (i + 1)) = R) :
    ((0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) ∧
        0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1))) ∨
      (Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0 ∧
        Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)) := by
  let w : ZMod n → ℂ := Gluck.Discrete.shiftPolygon v i
  have hsimpleW : Gluck.Discrete.IsSimplePolygon w :=
    Gluck.Discrete.isSimplePolygon_shift hsimple i
  have hcontainsW : ∀ z : ZMod n, dist O (w z) ≤ R := by
    intro z
    exact hcontains (i + z)
  have h0W : dist O (w 0) = R := by simpa [w, Gluck.Discrete.shiftPolygon] using hi
  have h1W : dist O (w 1) = R := by simpa [w, Gluck.Discrete.shiftPolygon] using hi1
  have hside := first_boundary_edge_other_vertices_same_side
    (show 3 ≤ n by omega) hsimpleW hcontainsW h0W h1W
  have hlastCast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    simp
  rcases hside with hpos | hneg
  · left
    have hprev := hpos (n - 1) (by omega) (by omega)
    have hnext := hpos 2 (by omega) (by omega)
    constructor
    · rw [polygonCross_eq_edgePrev]
      simpa [w, Gluck.Discrete.shiftPolygon, hlastCast, sub_eq_add_neg,
        add_assoc] using hprev
    · simpa [w, Gluck.Discrete.shiftPolygon,
        show (2 : ZMod n) = 1 + 1 by norm_num, add_assoc] using hnext
  · right
    have hprev := hneg (n - 1) (by omega) (by omega)
    have hnext := hneg 2 (by omega) (by omega)
    constructor
    · rw [polygonCross_eq_edgePrev]
      simpa [w, Gluck.Discrete.shiftPolygon, hlastCast, sub_eq_add_neg,
        add_assoc] using hprev
    · simpa [w, Gluck.Discrete.shiftPolygon,
        show (2 : ZMod n) = 1 + 1 by norm_num, add_assoc] using hnext

/-- If all minimal-disk contacts form one cyclic run, then their nonzero local
turns have one common sign.  This is the orientation bridge needed to reverse
the polygon in the negative case and reduce Section 4 to positive contact
turns. -/
theorem circleContactSet_cross_uniform_of_isCyclicInterval
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hinterval : Gluck.IsCyclicInterval (circleContactSet v O R)) :
    ((∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
        0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) ∨
      (∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
        Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0)) := by
  classical
  let turn : ZMod n → ℝ := fun i =>
    Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))
  rcases hinterval with ⟨c, a, b, hab, hbn, hcontacts⟩
  have hboundaryLift {k : ℕ} (hak : a ≤ k) (hkb : k ≤ b) :
      OnDiskBoundaryR2 v O R (Gluck.cyclicLift c k) := by
    apply Metric.mem_sphere'.mpr
    apply mem_circleContactSet.mp
    rw [hcontacts]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hak, hkb⟩, rfl⟩
  have hstep {k : ℕ} (hak : a ≤ k) (hkb : k < b) :
      ((0 < turn (Gluck.cyclicLift c k) ∧
          0 < turn (Gluck.cyclicLift c (k + 1))) ∨
        (turn (Gluck.cyclicLift c k) < 0 ∧
          turn (Gluck.cyclicLift c (k + 1)) < 0)) := by
    have hkBoundary := hboundaryLift hak hkb.le
    have hk1Boundary := hboundaryLift (k := k + 1) (by omega) (by omega)
    have hsucc : Gluck.cyclicLift c (k + 1) = Gluck.cyclicLift c k + 1 := by
      simp [Gluck.cyclicLift, Nat.cast_add, add_assoc]
    have hraw := adjacent_boundary_cross_same_sign hn hsimple
      (fun z => by
        exact Metric.mem_closedBall'.mp (hΔ.2.1 z))
      (by exact Metric.mem_sphere'.mp hkBoundary) (by
        rw [← hsucc]
        exact Metric.mem_sphere'.mp hk1Boundary)
    rcases hraw with hpos | hneg
    · left
      constructor
      · simpa [turn] using hpos.1
      · rw [hsucc]
        simpa [turn, sub_eq_add_neg, add_assoc] using hpos.2
    · right
      constructor
      · simpa [turn] using hneg.1
      · rw [hsucc]
        simpa [turn, sub_eq_add_neg, add_assoc] using hneg.2
  have hposFromA (haPos : 0 < turn (Gluck.cyclicLift c a)) :
      ∀ k : ℕ, a ≤ k → k ≤ b → 0 < turn (Gluck.cyclicLift c k) := by
    intro k hak hkb
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hak
    induction d with
    | zero => simpa using haPos
    | succ d ih =>
        have hprev : 0 < turn (Gluck.cyclicLift c (a + d)) :=
          ih (by omega) (by omega)
        rcases hstep (k := a + d) (by omega) (by omega) with hpos | hneg
        · simpa [Nat.add_assoc] using hpos.2
        · exact False.elim ((not_lt_of_ge hprev.le) hneg.1)
  have hnegFromA (haNeg : turn (Gluck.cyclicLift c a) < 0) :
      ∀ k : ℕ, a ≤ k → k ≤ b → turn (Gluck.cyclicLift c k) < 0 := by
    intro k hak hkb
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hak
    induction d with
    | zero => simpa using haNeg
    | succ d ih =>
        have hprev : turn (Gluck.cyclicLift c (a + d)) < 0 :=
          ih (by omega) (by omega)
        rcases hstep (k := a + d) (by omega) (by omega) with hpos | hneg
        · exact False.elim ((not_lt_of_ge hpos.1.le) hprev)
        · simpa [Nat.add_assoc] using hneg.2
  have haBoundary : OnDiskBoundaryR2 v O R (Gluck.cyclicLift c a) :=
    hboundaryLift le_rfl hab
  have haNe : turn (Gluck.cyclicLift c a) ≠ 0 := by
    exact crossR2_ne_zero_of_minimalEnclosingDisk_boundary
      hsimple hregular hΔ haBoundary
  rcases lt_or_gt_of_ne haNe with haNeg | haPos
  · right
    intro i hi
    have hiContact : i ∈ circleContactSet v O R :=
      mem_circleContactSet.mpr (Metric.mem_sphere'.mp hi)
    rw [hcontacts] at hiContact
    rcases Finset.mem_image.mp hiContact with ⟨k, hk, rfl⟩
    exact hnegFromA haNeg k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  · left
    intro i hi
    have hiContact : i ∈ circleContactSet v O R :=
      mem_circleContactSet.mpr (Metric.mem_sphere'.mp hi)
    rw [hcontacts] at hiContact
    rcases Finset.mem_image.mp hiContact with ⟨k, hk, rfl⟩
    exact hposFromA haPos k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2

end Gluck.Forward
