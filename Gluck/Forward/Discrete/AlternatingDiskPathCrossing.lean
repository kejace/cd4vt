/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Forward.Discrete.Section4AlternatingChordCrossing
public import Gluck.Topology.ChordDiskNormalization
public import ForMathlib.Analysis.Complex.PoincareMiranda

/-!
# Alternating disk paths cross

Two paths contained in a closed Euclidean disk, whose four distinct endpoints
occur alternately on the boundary circle, must intersect.  The proof uses the
project's source-free winding-number engine: under a disjointness assumption,
the path-difference loop on the parameter-square boundary contracts through
nonzero loops, but a homotopy to the two crossing chords identifies the same
loop with the boundary of a nonsingular affine parallelogram, whose winding is
`±1`.

Endpoint-avoidance hypotheses are explicit.  They are exactly what simple
polygonal subchains provide and are what makes the straight-line homotopy from
each path to its chord stay away from the opposite fixed boundary endpoint.
-/

@[expose] public section

namespace Gluck.Forward

open Gluck.Discrete Gluck.Topology
open Metric Set
open scoped Real unitInterval

private theorem left_eq_lineMap_add_neg_smul (A B : ℂ) (t : ℝ) :
    A = AffineMap.lineMap A B t + (-t) • (B - A) := by
  rw [AffineMap.lineMap_apply_module]
  module

private theorem right_eq_lineMap_add_one_sub_smul (A B : ℂ) (t : ℝ) :
    B = AffineMap.lineMap A B t + (1 - t) • (B - A) := by
  rw [AffineMap.lineMap_apply_module]
  module

private theorem crossR2_zero_sub_sub (A B C D : ℂ) :
    crossR2 0 (B - A) (D - C) = crossR2 A B D - crossR2 A B C := by
  unfold crossR2
  simp only [Complex.zero_re, Complex.zero_im, Complex.sub_re, Complex.sub_im]
  ring

private theorem chordDirections_linearIndependent
    {A B C D : ℂ}
    (hCneg : crossR2 A B C < 0) (hDpos : 0 < crossR2 A B D) :
    LinearIndependent ℝ ![B - A, D - C] := by
  have hdetpos : 0 < crossR2 0 (B - A) (D - C) := by
    rw [crossR2_zero_sub_sub]
    linarith
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hre := congrArg Complex.re hab
  have him := congrArg Complex.im hab
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im, Complex.sub_re, Complex.sub_im,
    zero_mul, sub_zero] at hre him
  have haDet : a * crossR2 0 (B - A) (D - C) = 0 := by
    unfold crossR2
    simp only [Complex.zero_re, Complex.zero_im, Complex.sub_re, Complex.sub_im]
    linear_combination (D.im - C.im) * hre - (D.re - C.re) * him
  have hbDet : b * crossR2 0 (B - A) (D - C) = 0 := by
    unfold crossR2
    simp only [Complex.zero_re, Complex.zero_im, Complex.sub_re, Complex.sub_im]
    linear_combination (B.re - A.re) * him - (B.im - A.im) * hre
  exact ⟨(mul_eq_zero.mp haDet).resolve_right hdetpos.ne',
    (mul_eq_zero.mp hbDet).resolve_right hdetpos.ne'⟩

/-- Opposite boundary chords have a common point with both affine parameters
strictly between `0` and `1`. -/
theorem exists_strict_chord_intersection_parameters
    {O A B C D : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hA : dist O A = R) (hB : dist O B = R)
    (hC : dist O C = R) (hD : dist O D = R)
    (hCneg : crossR2 A B C < 0) (hDpos : 0 < crossR2 A B D) :
    ∃ s t : ℝ, s ∈ Set.Ioo 0 1 ∧ t ∈ Set.Ioo 0 1 ∧
      AffineMap.lineMap A B s = AffineMap.lineMap C D t := by
  have hmeet : ¬ Disjoint (segment ℝ A B) (segment ℝ C D) := by
    simpa [segment_symm] using
      boundaryChord_not_disjoint_segment_of_cross_pos_neg
        hAB hA hB hD.le hC.le hDpos hCneg
  rw [Set.not_disjoint_iff] at hmeet
  obtain ⟨X, hXAB, hXCD⟩ := hmeet
  rw [segment_eq_image_lineMap] at hXAB hXCD
  obtain ⟨s, hs, hsX⟩ := hXAB
  obtain ⟨t, ht, htX⟩ := hXCD
  have hline : AffineMap.lineMap A B s = AffineMap.lineMap C D t :=
    hsX.trans htX.symm
  have ht0 : 0 < t := by
    have ht0le := ht.1
    refine lt_of_le_of_ne ht0le ?_
    intro htzero
    subst t
    have hzero : crossR2 A B C = 0 := by
      calc
        crossR2 A B C =
            crossR2 A B (AffineMap.lineMap C D (0 : ℝ)) := by simp
        _ = crossR2 A B (AffineMap.lineMap A B s) := by rw [hline]
        _ = 0 := crossR2_lineMap_self A B s
    linarith
  have ht1 : t < 1 := by
    have ht1le := ht.2
    refine lt_of_le_of_ne ht1le ?_
    intro htone
    subst t
    have hzero : crossR2 A B D = 0 := by
      calc
        crossR2 A B D =
            crossR2 A B (AffineMap.lineMap C D (1 : ℝ)) := by simp
        _ = crossR2 A B (AffineMap.lineMap A B s) := by rw [hline]
        _ = 0 := crossR2_lineMap_self A B s
    linarith
  have hXopen : X ∈ openSegment ℝ C D := by
    rw [← htX]
    exact lineMap_mem_openSegment ℝ C D ⟨ht0, ht1⟩
  have hCball : C ∈ closedBall O R := by
    simp [mem_closedBall, dist_comm, hC]
  have hDball : D ∈ closedBall O R := by
    simp [mem_closedBall, dist_comm, hD]
  have hXball : X ∈ ball O R :=
    openSegment_subset_ball_of_ne hCball hDball hCD hXopen
  have hXlt : dist O X < R := by
    simpa [mem_ball, dist_comm] using hXball
  have hs0 : 0 < s := by
    have hs0le := hs.1
    refine lt_of_le_of_ne hs0le ?_
    intro hszero
    subst s
    have hXA : X = A := by
      rw [← hsX]
      simp
    rw [hXA, hA] at hXlt
    exact (lt_irrefl R) hXlt
  have hs1 : s < 1 := by
    have hs1le := hs.2
    refine lt_of_le_of_ne hs1le ?_
    intro hsone
    subst s
    have hXB : X = B := by
      rw [← hsX]
      simp
    rw [hXB, hB] at hXlt
    exact (lt_irrefl R) hXlt
  exact ⟨s, t, ⟨hs0, hs1⟩, ⟨ht0, ht1⟩, hline⟩

/-- Two paths across opposite pairs of faces of a square intersect, provided
they are obtained by applying one injective planar map.  This is the exact
path-level corollary of Poincaré–Miranda used after chord normalization. -/
theorem paths_intersect_of_square_normalized
    {A B C D : ℂ} (E : ℂ ≃ₜ ℝ × ℝ)
    (γ : Path A B) (δ : Path C D)
    (hEA : E A = (-1, 0)) (hEB : E B = (1, 0))
    (hEC : E C = (0, -1)) (hED : E D = (0, 1))
    (hγbounds : ∀ s : I, |(E (γ s)).1| ≤ 1 ∧ |(E (γ s)).2| ≤ 1)
    (hδbounds : ∀ t : I, |(E (δ t)).1| ≤ 1 ∧ |(E (δ t)).2| ≤ 1) :
    ∃ s t : I, γ s = δ t := by
  let clamp : ℝ → I := Set.projIcc 0 1 zero_le_one
  let γE : ℝ → ℝ × ℝ := fun s ↦ E (γ (clamp s))
  let δE : ℝ → ℝ × ℝ := fun t ↦ E (δ (clamp t))
  let G : ℝ × ℝ → ℝ × ℝ := fun p ↦
    ((γE p.1).1 - (δE p.2).1,
      (δE p.2).2 - (γE p.1).2)
  have hclamp : Continuous clamp := by
    dsimp [clamp]
    exact continuous_projIcc (h := zero_le_one)
  have hγEc : Continuous γE := by
    exact E.continuous.comp (γ.continuous.comp hclamp)
  have hδEc : Continuous δE := by
    exact E.continuous.comp (δ.continuous.comp hclamp)
  have hGc : Continuous G := by
    exact ((continuous_fst.comp (hγEc.comp continuous_fst)).sub
      (continuous_fst.comp (hδEc.comp continuous_snd))).prodMk
      ((continuous_snd.comp (hδEc.comp continuous_snd)).sub
        (continuous_snd.comp (hγEc.comp continuous_fst)))
  have hleft : ∀ y ∈ Set.Icc (0 : ℝ) 1, (G (0, y)).1 ≤ 0 := by
    intro y hy
    have hδlo := (abs_le.mp (hδbounds (clamp y)).1).1
    have hγ0 : γE 0 = (-1, 0) := by
      simp [γE, clamp, hEA]
    simp only [G, hγ0, sub_nonpos]
    exact hδlo
  have hright : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (G (1, y)).1 := by
    intro y hy
    have hδhi := (abs_le.mp (hδbounds (clamp y)).1).2
    have hγ1 : γE 1 = (1, 0) := by
      simp [γE, clamp, hEB]
    simp only [G, hγ1, sub_nonneg]
    exact hδhi
  have hbot : ∀ x ∈ Set.Icc (0 : ℝ) 1, (G (x, 0)).2 ≤ 0 := by
    intro x hx
    have hγlo := (abs_le.mp (hγbounds (clamp x)).2).1
    have hδ0 : δE 0 = (0, -1) := by
      simp [δE, clamp, hEC]
    simp only [G, hδ0, sub_nonpos]
    exact hγlo
  have htop : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (G (x, 1)).2 := by
    intro x hx
    have hγhi := (abs_le.mp (hγbounds (clamp x)).2).2
    have hδ1 : δE 1 = (0, 1) := by
      simp [δE, clamp, hED]
    simp only [G, hδ1, sub_nonneg]
    exact hγhi
  obtain ⟨p, hp, hpzero⟩ :=
    poincare_miranda
      (a₁ := 0) (a₂ := 1) (b₁ := 0) (b₂ := 1)
      zero_le_one zero_le_one G hGc.continuousOn
      hleft hright hbot htop
  let s : I := clamp p.1
  let t : I := clamp p.2
  refine ⟨s, t, ?_⟩
  apply E.injective
  apply Prod.ext
  · have h := congrArg Prod.fst hpzero
    simpa [G, γE, δE, s, t] using sub_eq_zero.mp h
  · have h := congrArg Prod.snd hpzero
    have heq : (δE p.2).2 = (γE p.1).2 := by
      simpa [G] using sub_eq_zero.mp h
    simpa [γE, δE, s, t] using heq.symm

/-- **Disk crosscut theorem.**  If the endpoints of two disk-contained paths
lie on opposite sides of the other boundary chord, then the paths intersect.
The strict side conditions make the two chords transverse and put their
intersection in the open disk; chord coordinates and gauge rescaling reduce
the claim to `paths_intersect_of_square_normalized`. -/
theorem paths_intersect_of_opposite_boundary_chords
    {O A B C D : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hA : dist O A = R) (hB : dist O B = R)
    (hC : dist O C = R) (hD : dist O D = R)
    (hCneg : crossR2 A B C < 0) (hDpos : 0 < crossR2 A B D)
    (γ : Path A B) (δ : Path C D)
    (hγinside : ∀ s : I, dist O (γ s) ≤ R)
    (hδinside : ∀ t : I, dist O (δ t) ≤ R) :
    ∃ s t : I, γ s = δ t := by
  have hAB : A ≠ B := by
    intro h
    subst B
    simp [crossR2] at hDpos
  have hCD : C ≠ D := by
    intro h
    subst D
    linarith
  obtain ⟨s₀, t₀, hs₀, ht₀, hline⟩ :=
    exists_strict_chord_intersection_parameters
      hAB hCD hA hB hC hD hCneg hDpos
  let X : ℂ := AffineMap.lineMap A B s₀
  let u : ℂ := B - A
  let v : ℂ := D - C
  have hXlineCD : X = AffineMap.lineMap C D t₀ := by
    exact hline
  have hCball : C ∈ closedBall O R := by
    simp [mem_closedBall, dist_comm, hC]
  have hDball : D ∈ closedBall O R := by
    simp [mem_closedBall, dist_comm, hD]
  have hXopen : X ∈ openSegment ℝ C D := by
    rw [hXlineCD]
    exact lineMap_mem_openSegment ℝ C D ht₀
  have hXball : X ∈ ball O R :=
    openSegment_subset_ball_of_ne hCball hDball hCD hXopen
  have hXdist : dist O X < R := by
    simpa [mem_ball, dist_comm] using hXball
  have hli : LinearIndependent ℝ ![u, v] := by
    simpa [u, v] using chordDirections_linearIndependent hCneg hDpos
  have hXA : A = X + (-s₀) • u := by
    simpa [X, u] using left_eq_lineMap_add_neg_smul A B s₀
  have hXB : B = X + (1 - s₀) • u := by
    simpa [X, u] using right_eq_lineMap_add_one_sub_smul A B s₀
  have hXC : C = X + (-t₀) • v := by
    calc
      C = AffineMap.lineMap C D t₀ + (-t₀) • (D - C) :=
        left_eq_lineMap_add_neg_smul C D t₀
      _ = X + (-t₀) • v := by rw [← hXlineCD]
  have hXD : D = X + (1 - t₀) • v := by
    calc
      D = AffineMap.lineMap C D t₀ + (1 - t₀) • (D - C) :=
        right_eq_lineMap_add_one_sub_smul C D t₀
      _ = X + (1 - t₀) • v := by rw [← hXlineCD]
  have hA' : dist O (X + (-s₀) • u) = R := by rw [← hXA]; exact hA
  have hB' : dist O (X + (1 - s₀) • u) = R := by rw [← hXB]; exact hB
  have hC' : dist O (X + (-t₀) • v) = R := by rw [← hXC]; exact hC
  have hD' : dist O (X + (1 - t₀) • v) = R := by rw [← hXD]; exact hD
  let E : ℂ ≃ₜ ℝ × ℝ :=
    diskSquareHomeomorph O R X u v hli hXdist
  have hEA : E A = (-1, 0) := by
    change diskSquareHomeomorph O R X u v hli hXdist A = (-1, 0)
    rw [hXA]
    exact diskSquareHomeomorph_apply_neg_left_line hR.ne' hli hXdist
      (by linarith [hs₀.1]) hA'
  have hEB : E B = (1, 0) := by
    change diskSquareHomeomorph O R X u v hli hXdist B = (1, 0)
    rw [hXB]
    exact diskSquareHomeomorph_apply_pos_left_line hR.ne' hli hXdist
      (by linarith [hs₀.2]) hB'
  have hEC : E C = (0, -1) := by
    change diskSquareHomeomorph O R X u v hli hXdist C = (0, -1)
    rw [hXC]
    exact diskSquareHomeomorph_apply_neg_right_line hR.ne' hli hXdist
      (by linarith [ht₀.1]) hC'
  have hED : E D = (0, 1) := by
    change diskSquareHomeomorph O R X u v hli hXdist D = (0, 1)
    rw [hXD]
    exact diskSquareHomeomorph_apply_pos_right_line hR.ne' hli hXdist
      (by linarith [ht₀.2]) hD'
  apply paths_intersect_of_square_normalized E γ δ hEA hEB hEC hED
  · intro s
    apply diskSquareHomeomorph_coordinate_bounds hR hli hXdist
    simpa [mem_closedBall, dist_comm] using hγinside s
  · intro t
    apply diskSquareHomeomorph_coordinate_bounds hR hli hXdist
    simpa [mem_closedBall, dist_comm] using hδinside t

/-- Four cyclically alternating points on one circle are the endpoints of two
intersecting disk-contained paths.  No injectivity or endpoint-avoidance
hypothesis is needed. -/
theorem paths_intersect_of_circle_alternating
    {O : ℂ} {R θA θC θB θD : ℝ}
    (hR : 0 < R)
    (hAC : θA < θC) (hCB : θC < θB)
    (hBD : θB < θD) (hspan : θD < θA + 2 * Real.pi)
    (γ : Path (circlePoint O R θA) (circlePoint O R θB))
    (δ : Path (circlePoint O R θC) (circlePoint O R θD))
    (hγinside : ∀ s : I, dist O (γ s) ≤ R)
    (hδinside : ∀ t : I, dist O (δ t) ≤ R) :
    ∃ s t : I, γ s = δ t := by
  have hACB :
      0 < crossR2 (circlePoint O R θA) (circlePoint O R θC)
        (circlePoint O R θB) :=
    crossR2_circlePoint_pos_of_ordered O hR.ne' hAC hCB
      (by linarith)
  have hABCneg :
      crossR2 (circlePoint O R θA) (circlePoint O R θB)
          (circlePoint O R θC) < 0 := by
    rw [crossR2_swap]
    linarith
  have hABDpos :
      0 < crossR2 (circlePoint O R θA) (circlePoint O R θB)
        (circlePoint O R θD) :=
    crossR2_circlePoint_pos_of_ordered O hR.ne'
      (hAC.trans hCB) hBD hspan
  apply paths_intersect_of_opposite_boundary_chords hR
    (by simp [dist_circlePoint_center, abs_of_pos hR])
    (by simp [dist_circlePoint_center, abs_of_pos hR])
    (by simp [dist_circlePoint_center, abs_of_pos hR])
    (by simp [dist_circlePoint_center, abs_of_pos hR])
    hABCneg hABDpos γ δ hγinside hδinside

end Gluck.Forward
