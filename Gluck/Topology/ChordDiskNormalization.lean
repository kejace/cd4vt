/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-!
# Normalize two crossing disk chords to the coordinate axes

An affine coordinate change centered at the intersection of two transverse
chords sends the chord directions to the coordinate axes. The disk becomes a
bounded convex neighborhood of the origin. Gauge rescaling then gives a global
homeomorphism to the product unit ball, i.e. the open square. The four chord
endpoints land on the four opposite square faces.

This is the normalization needed before applying a rectangle crossing theorem
to paths with arbitrary alternating endpoints on a circle.
-/

noncomputable section

open Filter Metric Set Bornology

namespace Gluck.Topology

private theorem pair_span_eq_top {u v : ℂ}
    (hli : LinearIndependent ℝ ![u, v]) :
    Submodule.span ℝ (Set.range ![u, v]) = ⊤ := by
  apply hli.span_eq_top_of_card_eq_finrank
  simp [Complex.finrank_real_complex]

/-- Coordinates in a specified ordered real basis of `ℂ`. -/
def pairCoordEquiv (u v : ℂ) (hli : LinearIndependent ℝ ![u, v]) :
    ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  let b : Module.Basis (Fin 2) ℝ ℂ :=
    Module.Basis.mk hli (pair_span_eq_top hli).ge
  b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 2) ≪≫ₗ
    LinearEquiv.finTwoArrow ℝ ℝ

@[simp] theorem pairCoordEquiv_apply_left (u v : ℂ)
    (hli : LinearIndependent ℝ ![u, v]) :
    pairCoordEquiv u v hli u = (1, 0) := by
  let b : Module.Basis (Fin 2) ℝ ℂ :=
    Module.Basis.mk hli (pair_span_eq_top hli).ge
  have hbu : b 0 = u := by
    simp [b, Module.Basis.mk_apply]
  change (((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 2))
    (b.repr u)) 0, ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 2))
    (b.repr u)) 1) = (1, 0)
  rw [← hbu, b.repr_self]
  simp

@[simp] theorem pairCoordEquiv_apply_right (u v : ℂ)
    (hli : LinearIndependent ℝ ![u, v]) :
    pairCoordEquiv u v hli v = (0, 1) := by
  let b : Module.Basis (Fin 2) ℝ ℂ :=
    Module.Basis.mk hli (pair_span_eq_top hli).ge
  have hbv : b 1 = v := by
    simp [b, Module.Basis.mk_apply]
  change (((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 2))
    (b.repr v)) 0, ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 2))
    (b.repr v)) 1) = (0, 1)
  rw [← hbv, b.repr_self]
  simp

/-- Affine coordinates centered at `x`, in the ordered basis `(u,v)`. -/
def chordCoordHomeomorph (x u v : ℂ) (hli : LinearIndependent ℝ ![u, v]) :
    ℂ ≃ₜ ℝ × ℝ :=
  ((AffineEquiv.constVAdd ℝ ℂ (-x)).trans
    (pairCoordEquiv u v hli).toAffineEquiv).toHomeomorphOfFiniteDimensional

@[simp] theorem chordCoordHomeomorph_apply (x u v z : ℂ)
    (hli : LinearIndependent ℝ ![u, v]) :
    chordCoordHomeomorph x u v hli z = pairCoordEquiv u v hli (z - x) := by
  simp [chordCoordHomeomorph, sub_eq_add_neg, add_comm]

@[simp] theorem chordCoordHomeomorph_apply_center (x u v : ℂ)
    (hli : LinearIndependent ℝ ![u, v]) :
    chordCoordHomeomorph x u v hli x = 0 := by
  simp

theorem chordCoordHomeomorph_apply_left_line (x u v : ℂ)
    (hli : LinearIndependent ℝ ![u, v]) (a : ℝ) :
    chordCoordHomeomorph x u v hli (x + a • u) = (a, 0) := by
  rw [chordCoordHomeomorph_apply]
  simp only [add_sub_cancel_left]
  rw [map_smul]
  simp

theorem chordCoordHomeomorph_apply_right_line (x u v : ℂ)
    (hli : LinearIndependent ℝ ![u, v]) (a : ℝ) :
    chordCoordHomeomorph x u v hli (x + a • v) = (0, a) := by
  rw [chordCoordHomeomorph_apply]
  simp only [add_sub_cancel_left]
  rw [map_smul]
  simp

/-- The image of an open Euclidean disk under chord coordinates. -/
def chordDisk (O : ℂ) (R : ℝ) (x u v : ℂ)
    (hli : LinearIndependent ℝ ![u, v]) : Set (ℝ × ℝ) :=
  chordCoordHomeomorph x u v hli '' ball O R

theorem chordDisk_convex (O : ℂ) (R : ℝ) (x u v : ℂ)
    (hli : LinearIndependent ℝ ![u, v]) :
    Convex ℝ (chordDisk O R x u v hli) := by
  let e : ℂ ≃ᵃ[ℝ] ℝ × ℝ :=
    (AffineEquiv.constVAdd ℝ ℂ (-x)).trans
      (pairCoordEquiv u v hli).toAffineEquiv
  exact (convex_ball O R).affine_image e.toAffineMap

theorem chordDisk_mem_nhds_zero {O : ℂ} {R : ℝ} {x u v : ℂ}
    (hli : LinearIndependent ℝ ![u, v]) (hx : dist O x < R) :
    chordDisk O R x u v hli ∈ nhds 0 := by
  apply IsOpen.mem_nhds
  · exact (chordCoordHomeomorph x u v hli).isOpenMap _ isOpen_ball
  · refine ⟨x, ?_, chordCoordHomeomorph_apply_center x u v hli⟩
    change dist x O < R
    rw [dist_comm]
    exact hx

theorem chordDisk_isBounded (O : ℂ) (R : ℝ) (x u v : ℂ)
    (hli : LinearIndependent ℝ ![u, v]) :
    IsBounded (chordDisk O R x u v hli) := by
  apply ((isCompact_closedBall O R).image
    (chordCoordHomeomorph x u v hli).continuous).isBounded.subset
  exact Set.image_mono ball_subset_closedBall

theorem chordCoord_mem_frontier_chordDisk {O A : ℂ} {R : ℝ} {x u v : ℂ}
    (hR : R ≠ 0) (hli : LinearIndependent ℝ ![u, v])
    (hA : dist O A = R) :
    chordCoordHomeomorph x u v hli A ∈ frontier (chordDisk O R x u v hli) := by
  unfold chordDisk
  rw [← (chordCoordHomeomorph x u v hli).image_frontier, frontier_ball O hR]
  refine ⟨A, ?_, rfl⟩
  change dist A O = R
  simpa [dist_comm] using hA

private theorem gaugeRescale_unitBall_neg_fst {s : Set (ℝ × ℝ)}
    (hsconv : Convex ℝ s) (hs0 : s ∈ nhds 0) {a : ℝ} (ha : a < 0)
    (hfront : (a, 0) ∈ frontier s) :
    gaugeRescale s (ball 0 1) (a, 0) = (-1, 0) := by
  have hg : gauge s (a, 0) = 1 :=
    (gauge_eq_one_iff_mem_frontier hsconv hs0).2 hfront
  rw [gaugeRescale_def, hg, gauge_ball zero_le_one]
  ext <;> simp [Prod.norm_def, abs_of_neg ha,
    max_eq_left (by linarith : 0 ≤ -a), ha.ne]

private theorem gaugeRescale_unitBall_pos_fst {s : Set (ℝ × ℝ)}
    (hsconv : Convex ℝ s) (hs0 : s ∈ nhds 0) {a : ℝ} (ha : 0 < a)
    (hfront : (a, 0) ∈ frontier s) :
    gaugeRescale s (ball 0 1) (a, 0) = (1, 0) := by
  have hg : gauge s (a, 0) = 1 :=
    (gauge_eq_one_iff_mem_frontier hsconv hs0).2 hfront
  rw [gaugeRescale_def, hg, gauge_ball zero_le_one]
  ext <;> simp [Prod.norm_def, abs_of_pos ha,
    max_eq_left ha.le, ha.ne']

private theorem gaugeRescale_unitBall_neg_snd {s : Set (ℝ × ℝ)}
    (hsconv : Convex ℝ s) (hs0 : s ∈ nhds 0) {a : ℝ} (ha : a < 0)
    (hfront : (0, a) ∈ frontier s) :
    gaugeRescale s (ball 0 1) (0, a) = (0, -1) := by
  have hg : gauge s (0, a) = 1 :=
    (gauge_eq_one_iff_mem_frontier hsconv hs0).2 hfront
  rw [gaugeRescale_def, hg, gauge_ball zero_le_one]
  ext <;> simp [Prod.norm_def, abs_of_neg ha,
    max_eq_right (by linarith : 0 ≤ -a), ha.ne]

private theorem gaugeRescale_unitBall_pos_snd {s : Set (ℝ × ℝ)}
    (hsconv : Convex ℝ s) (hs0 : s ∈ nhds 0) {a : ℝ} (ha : 0 < a)
    (hfront : (0, a) ∈ frontier s) :
    gaugeRescale s (ball 0 1) (0, a) = (0, 1) := by
  have hg : gauge s (0, a) = 1 :=
    (gauge_eq_one_iff_mem_frontier hsconv hs0).2 hfront
  rw [gaugeRescale_def, hg, gauge_ball zero_le_one]
  ext <;> simp [Prod.norm_def, abs_of_pos ha,
    max_eq_right ha.le, ha.ne']

/-- A global homeomorphism that sends an open disk, in chord coordinates,
to the open unit ball of `ℝ × ℝ`, i.e. the open square `(-1,1)²`. -/
def diskSquareHomeomorph (O : ℂ) (R : ℝ) (x u v : ℂ)
    (hli : LinearIndependent ℝ ![u, v]) (hx : dist O x < R) :
    ℂ ≃ₜ ℝ × ℝ :=
  let K := chordDisk O R x u v hli
  let hKconv := chordDisk_convex O R x u v hli
  let hK0 := chordDisk_mem_nhds_zero hli hx
  let hKb := NormedSpace.isVonNBounded_of_isBounded ℝ
    (chordDisk_isBounded O R x u v hli)
  let hBconv := convex_ball (0 : ℝ × ℝ) 1
  let hB0 := Metric.ball_mem_nhds (0 : ℝ × ℝ) one_pos
  let hBb := NormedSpace.isVonNBounded_ball ℝ (ℝ × ℝ) 1
  (chordCoordHomeomorph x u v hli).trans
    (gaugeRescaleHomeomorph K (ball 0 1)
      hKconv hK0 hKb hBconv hB0 hBb)

theorem diskSquareHomeomorph_apply_neg_left_line
    {O : ℂ} {R : ℝ} {x u v : ℂ}
    (hR : R ≠ 0) (hli : LinearIndependent ℝ ![u, v])
    (hx : dist O x < R) {a : ℝ} (ha : a < 0)
    (hA : dist O (x + a • u) = R) :
    diskSquareHomeomorph O R x u v hli hx (x + a • u) = (-1, 0) := by
  change gaugeRescale (chordDisk O R x u v hli) (ball 0 1)
    (chordCoordHomeomorph x u v hli (x + a • u)) = (-1, 0)
  rw [chordCoordHomeomorph_apply_left_line]
  apply gaugeRescale_unitBall_neg_fst (ha := ha)
  · exact chordDisk_convex O R x u v hli
  · exact chordDisk_mem_nhds_zero hli hx
  · have hf := chordCoord_mem_frontier_chordDisk
      (O := O) (A := x + a • u) (R := R) (x := x) (u := u) (v := v)
      hR hli hA
    rw [chordCoordHomeomorph_apply_left_line] at hf
    exact hf

theorem diskSquareHomeomorph_apply_pos_left_line
    {O : ℂ} {R : ℝ} {x u v : ℂ}
    (hR : R ≠ 0) (hli : LinearIndependent ℝ ![u, v])
    (hx : dist O x < R) {a : ℝ} (ha : 0 < a)
    (hA : dist O (x + a • u) = R) :
    diskSquareHomeomorph O R x u v hli hx (x + a • u) = (1, 0) := by
  change gaugeRescale (chordDisk O R x u v hli) (ball 0 1)
    (chordCoordHomeomorph x u v hli (x + a • u)) = (1, 0)
  rw [chordCoordHomeomorph_apply_left_line]
  apply gaugeRescale_unitBall_pos_fst (ha := ha)
  · exact chordDisk_convex O R x u v hli
  · exact chordDisk_mem_nhds_zero hli hx
  · have hf := chordCoord_mem_frontier_chordDisk
      (O := O) (A := x + a • u) (R := R) (x := x) (u := u) (v := v)
      hR hli hA
    rw [chordCoordHomeomorph_apply_left_line] at hf
    exact hf

theorem diskSquareHomeomorph_apply_neg_right_line
    {O : ℂ} {R : ℝ} {x u v : ℂ}
    (hR : R ≠ 0) (hli : LinearIndependent ℝ ![u, v])
    (hx : dist O x < R) {a : ℝ} (ha : a < 0)
    (hA : dist O (x + a • v) = R) :
    diskSquareHomeomorph O R x u v hli hx (x + a • v) = (0, -1) := by
  change gaugeRescale (chordDisk O R x u v hli) (ball 0 1)
    (chordCoordHomeomorph x u v hli (x + a • v)) = (0, -1)
  rw [chordCoordHomeomorph_apply_right_line]
  apply gaugeRescale_unitBall_neg_snd (ha := ha)
  · exact chordDisk_convex O R x u v hli
  · exact chordDisk_mem_nhds_zero hli hx
  · have hf := chordCoord_mem_frontier_chordDisk
      (O := O) (A := x + a • v) (R := R) (x := x) (u := u) (v := v)
      hR hli hA
    rw [chordCoordHomeomorph_apply_right_line] at hf
    exact hf

theorem diskSquareHomeomorph_apply_pos_right_line
    {O : ℂ} {R : ℝ} {x u v : ℂ}
    (hR : R ≠ 0) (hli : LinearIndependent ℝ ![u, v])
    (hx : dist O x < R) {a : ℝ} (ha : 0 < a)
    (hA : dist O (x + a • v) = R) :
    diskSquareHomeomorph O R x u v hli hx (x + a • v) = (0, 1) := by
  change gaugeRescale (chordDisk O R x u v hli) (ball 0 1)
    (chordCoordHomeomorph x u v hli (x + a • v)) = (0, 1)
  rw [chordCoordHomeomorph_apply_right_line]
  apply gaugeRescale_unitBall_pos_snd (ha := ha)
  · exact chordDisk_convex O R x u v hli
  · exact chordDisk_mem_nhds_zero hli hx
  · have hf := chordCoord_mem_frontier_chordDisk
      (O := O) (A := x + a • v) (R := R) (x := x) (u := u) (v := v)
      hR hli hA
    rw [chordCoordHomeomorph_apply_right_line] at hf
    exact hf

/-- The normalization sends the closed Euclidean disk into the closed unit
ball of `ℝ × ℝ`, which is exactly the closed square `[-1,1]²`. -/
theorem diskSquareHomeomorph_mapsTo_closedBall
    {O : ℂ} {R : ℝ} {x u v : ℂ}
    (hR : 0 < R) (hli : LinearIndependent ℝ ![u, v])
    (hx : dist O x < R) :
    MapsTo (diskSquareHomeomorph O R x u v hli hx)
      (closedBall O R) (closedBall 0 1) := by
  intro z hz
  let K := chordDisk O R x u v hli
  let e := chordCoordHomeomorph x u v hli
  have hKconv : Convex ℝ K := chordDisk_convex O R x u v hli
  have hK0 : K ∈ nhds 0 := chordDisk_mem_nhds_zero hli hx
  have hKb : IsVonNBounded ℝ K :=
    NormedSpace.isVonNBounded_of_isBounded ℝ
      (chordDisk_isBounded O R x u v hli)
  have hBconv : Convex ℝ (ball (0 : ℝ × ℝ) 1) := convex_ball 0 1
  have hB0 : ball (0 : ℝ × ℝ) 1 ∈ nhds 0 :=
    Metric.ball_mem_nhds 0 one_pos
  have hBb : IsVonNBounded ℝ (ball (0 : ℝ × ℝ) 1) :=
    NormedSpace.isVonNBounded_ball ℝ (ℝ × ℝ) 1
  have hez : e z ∈ closure K := by
    change e z ∈ closure (e '' ball O R)
    rw [← e.image_closure, closure_ball O hR.ne']
    exact ⟨z, hz, rfl⟩
  have htarget :
      gaugeRescaleHomeomorph K (ball 0 1)
          hKconv hK0 hKb hBconv hB0 hBb (e z) ∈
        closure (ball (0 : ℝ × ℝ) 1) := by
    rw [← image_gaugeRescaleHomeomorph_closure
      hKconv hK0 hKb hBconv hB0 hBb]
    exact ⟨e z, hez, rfl⟩
  change gaugeRescaleHomeomorph K (ball 0 1)
      hKconv hK0 hKb hBconv hB0 hBb (e z) ∈ closedBall 0 1
  simpa [closure_ball (0 : ℝ × ℝ) one_ne_zero] using htarget

theorem diskSquareHomeomorph_coordinate_bounds
    {O z : ℂ} {R : ℝ} {x u v : ℂ}
    (hR : 0 < R) (hli : LinearIndependent ℝ ![u, v])
    (hx : dist O x < R) (hz : z ∈ closedBall O R) :
    |(diskSquareHomeomorph O R x u v hli hx z).1| ≤ 1 ∧
      |(diskSquareHomeomorph O R x u v hli hx z).2| ≤ 1 := by
  have hmem := diskSquareHomeomorph_mapsTo_closedBall hR hli hx hz
  rw [mem_closedBall_zero_iff, norm_prod_le_iff] at hmem
  simpa [Real.norm_eq_abs] using hmem

/-- Equality after normalization is equality before normalization; this is the
step that turns a Maehara intersection of transformed paths into an
intersection of the original paths. -/
theorem diskSquareHomeomorph_apply_eq_iff
    {O z w : ℂ} {R : ℝ} {x u v : ℂ}
    (hli : LinearIndependent ℝ ![u, v]) (hx : dist O x < R) :
    diskSquareHomeomorph O R x u v hli hx z =
        diskSquareHomeomorph O R x u v hli hx w ↔ z = w := by
  constructor
  · intro h
    exact (diskSquareHomeomorph O R x u v hli hx).injective h
  · rintro rfl
    rfl

end Gluck.Topology
