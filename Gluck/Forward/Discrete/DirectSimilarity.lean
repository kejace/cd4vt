/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Defs
import Gluck.Discrete.PolygonConvexity
import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Direct similarities of the Euclidean plane

The map `z ↦ a * z + w` packages rotations, positive homotheties, and
translations into one orientation-preserving similarity API.
-/

namespace Gluck.Forward

/-- An orientation-preserving similarity of the Euclidean plane, written in
complex coordinates. -/
def directSimilarityR2 (a w z : ℂ) : ℂ :=
  a * z + w

/-- Compatibility name for a direct similarity whose multiplier has norm one. -/
abbrev directIsometryR2 (u w z : ℂ) : ℂ :=
  u * z + w

/-- The explicit inverse similarity undoes a direct similarity. -/
@[simp]
theorem directSimilarityR2_inverse_apply {a : ℂ} (ha : a ≠ 0) (w z : ℂ) :
    directSimilarityR2 a⁻¹ (-(a⁻¹ * w)) (directSimilarityR2 a w z) = z := by
  unfold directSimilarityR2
  field_simp
  ring

/-- Applying a direct similarity after its explicit inverse returns the point. -/
@[simp]
theorem directSimilarityR2_apply_inverse {a : ℂ} (ha : a ≠ 0) (w z : ℂ) :
    directSimilarityR2 a w (directSimilarityR2 a⁻¹ (-(a⁻¹ * w)) z) = z := by
  unfold directSimilarityR2
  field_simp
  ring

/-- A direct similarity with nonzero multiplier is injective. -/
theorem directSimilarityR2_injective {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    Function.Injective (directSimilarityR2 a w) := by
  intro z₁ z₂ h
  unfold directSimilarityR2 at h
  exact mul_left_cancel₀ ha (add_right_cancel h)

/-- A direct similarity with nonzero multiplier is surjective. -/
theorem directSimilarityR2_surjective {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    Function.Surjective (directSimilarityR2 a w) := by
  intro z
  exact ⟨directSimilarityR2 a⁻¹ (-(a⁻¹ * w)) z,
    directSimilarityR2_apply_inverse ha w z⟩

/-- A direct similarity with nonzero multiplier is bijective. -/
theorem directSimilarityR2_bijective {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    Function.Bijective (directSimilarityR2 a w) :=
  ⟨directSimilarityR2_injective ha w, directSimilarityR2_surjective ha w⟩

/-- Direct similarities scale all distances by the norm of their multiplier. -/
theorem dist_directSimilarityR2 (a w z₁ z₂ : ℂ) :
    dist (directSimilarityR2 a w z₁) (directSimilarityR2 a w z₂) =
      ‖a‖ * dist z₁ z₂ := by
  rw [dist_eq_norm, dist_eq_norm]
  unfold directSimilarityR2
  have hsub : a * z₁ + w - (a * z₂ + w) = a * (z₁ - z₂) := by
    ring
  rw [hsub, norm_mul]

/-- Direct similarities commute with affine interpolation. -/
theorem directSimilarityR2_lineMap (a w A B : ℂ) (t : ℝ) :
    directSimilarityR2 a w (AffineMap.lineMap A B t) =
      AffineMap.lineMap (directSimilarityR2 a w A) (directSimilarityR2 a w B) t := by
  unfold directSimilarityR2
  simp [AffineMap.lineMap_apply_module]
  ring

/-- A nondegenerate direct similarity preserves closed-segment membership. -/
theorem mem_segment_directSimilarityR2 {a : ℂ} (ha : a ≠ 0) (w A B z : ℂ) :
    directSimilarityR2 a w z ∈
        segment ℝ (directSimilarityR2 a w A) (directSimilarityR2 a w B) ↔
      z ∈ segment ℝ A B := by
  constructor
  · intro hz
    rw [segment_eq_image_lineMap] at hz ⊢
    rcases hz with ⟨t, ht, hz⟩
    refine ⟨t, ht, ?_⟩
    apply directSimilarityR2_injective ha w
    rw [directSimilarityR2_lineMap]
    exact hz
  · intro hz
    rw [segment_eq_image_lineMap] at hz ⊢
    rcases hz with ⟨t, ht, hz⟩
    refine ⟨t, ht, ?_⟩
    rw [← directSimilarityR2_lineMap, hz]

/-- A nondegenerate direct similarity preserves simple cyclic polygons. -/
theorem isSimplePolygon_directSimilarityR2 {n : ℕ} {a : ℂ} (ha : a ≠ 0)
    (w : ℂ) {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (fun i ↦ directSimilarityR2 a w (v i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h
    exact hsimple.1 i (directSimilarityR2_injective ha w h)
  · intro i
    ext z
    constructor
    · intro hz
      let z₀ := directSimilarityR2 a⁻¹ (-(a⁻¹ * w)) z
      have hzimage : directSimilarityR2 a w z₀ = z := by
        exact directSimilarityR2_apply_inverse ha w z
      have hzleft : z₀ ∈ segment ℝ (v i) (v (i + 1)) := by
        apply (mem_segment_directSimilarityR2 ha w (v i) (v (i + 1)) z₀).mp
        simpa only [hzimage] using hz.1
      have hzright : z₀ ∈ segment ℝ (v (i + 1)) (v (i + 1 + 1)) := by
        apply (mem_segment_directSimilarityR2 ha w
          (v (i + 1)) (v (i + 1 + 1)) z₀).mp
        simpa only [hzimage] using hz.2
      have hz₀ := Set.mem_inter hzleft hzright
      rw [hsimple.2.1 i] at hz₀
      have hz₀eq : z₀ = v (i + 1) := by simpa using hz₀
      rw [← hzimage, hz₀eq]
      exact Set.mem_singleton _
    · intro hz
      have hz_eq : z = directSimilarityR2 a w (v (i + 1)) := by simpa using hz
      rw [hz_eq]
      exact ⟨
        (mem_segment_directSimilarityR2 ha w (v i) (v (i + 1)) (v (i + 1))).mpr
          (right_mem_segment ℝ (v i) (v (i + 1))),
        (mem_segment_directSimilarityR2 ha w (v (i + 1))
          (v (i + 1 + 1)) (v (i + 1))).mpr
            (left_mem_segment ℝ (v (i + 1)) (v (i + 1 + 1)))⟩
  · intro i j hij hij_next hji_next
    ext z
    constructor
    · intro hz
      let z₀ := directSimilarityR2 a⁻¹ (-(a⁻¹ * w)) z
      have hzimage : directSimilarityR2 a w z₀ = z := by
        exact directSimilarityR2_apply_inverse ha w z
      have hzleft : z₀ ∈ segment ℝ (v i) (v (i + 1)) := by
        apply (mem_segment_directSimilarityR2 ha w (v i) (v (i + 1)) z₀).mp
        simpa only [hzimage] using hz.1
      have hzright : z₀ ∈ segment ℝ (v j) (v (j + 1)) := by
        apply (mem_segment_directSimilarityR2 ha w (v j) (v (j + 1)) z₀).mp
        simpa only [hzimage] using hz.2
      have hz₀ := Set.mem_inter hzleft hzright
      rw [hsimple.2.2 i j hij hij_next hji_next] at hz₀
      exact hz₀.elim
    · intro hz
      exact hz.elim

/-- Nondegenerate direct similarities preserve simple cyclic polygons
exactly. -/
theorem isSimplePolygon_directSimilarityR2_iff {n : ℕ} {a : ℂ} (ha : a ≠ 0)
    (w : ℂ) (v : ZMod n → ℂ) :
    Gluck.Discrete.IsSimplePolygon (fun i ↦ directSimilarityR2 a w (v i)) ↔
      Gluck.Discrete.IsSimplePolygon v := by
  constructor
  · intro hsimple
    have hpre := isSimplePolygon_directSimilarityR2 (inv_ne_zero ha)
      (-(a⁻¹ * w)) hsimple
    simpa only [directSimilarityR2_inverse_apply ha] using hpre
  · exact isSimplePolygon_directSimilarityR2 ha w

/-- Sphere power scales quadratically under a direct similarity. -/
theorem sphere_power_directSimilarityR2 (a w c z : ℂ) (r : ℝ) :
    (⟨directSimilarityR2 a w c, ‖a‖ * r⟩ : EuclideanGeometry.Sphere ℂ).power
        (directSimilarityR2 a w z) =
      ‖a‖ ^ 2 * (⟨c, r⟩ : EuclideanGeometry.Sphere ℂ).power z := by
  unfold EuclideanGeometry.Sphere.power
  rw [dist_directSimilarityR2]
  ring

/-- A nondegenerate direct similarity carries a closed ball to the closed ball
whose radius is scaled by the multiplier norm. -/
theorem mem_closedBall_directSimilarityR2 {a : ℂ} (ha : a ≠ 0)
    (w c z : ℂ) (r : ℝ) :
    directSimilarityR2 a w z ∈
        Metric.closedBall (directSimilarityR2 a w c) (‖a‖ * r) ↔
      z ∈ Metric.closedBall c r := by
  simp only [Metric.mem_closedBall', dist_directSimilarityR2]
  exact mul_le_mul_iff_of_pos_left (norm_pos_iff.mpr ha)

/-- A nondegenerate direct similarity carries a sphere to the sphere whose
radius is scaled by the multiplier norm. -/
theorem mem_sphere_directSimilarityR2 {a : ℂ} (ha : a ≠ 0)
    (w c z : ℂ) (r : ℝ) :
    directSimilarityR2 a w z ∈
        Metric.sphere (directSimilarityR2 a w c) (‖a‖ * r) ↔
      z ∈ Metric.sphere c r := by
  simp only [Metric.mem_sphere', dist_directSimilarityR2]
  simp [mul_eq_mul_left_iff, norm_ne_zero_iff.mpr ha]

/-- Direct similarities preserve project disk containment after scaling the
radius. -/
theorem inClosedDiskR2_directSimilarityR2 {a : ℂ} (ha : a ≠ 0)
    (w O z : ℂ) (R : ℝ) :
    InClosedDiskR2 (directSimilarityR2 a w O) (‖a‖ * R)
        (directSimilarityR2 a w z) ↔
      InClosedDiskR2 O R z :=
  mem_closedBall_directSimilarityR2 ha w O z R

/-- Direct similarities preserve polygon containment after scaling the disk
radius. -/
theorem polygonInClosedDiskR2_directSimilarityR2 {n : ℕ} {a : ℂ}
    (ha : a ≠ 0) (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    PolygonInClosedDiskR2 (fun i ↦ directSimilarityR2 a w (v i))
        (directSimilarityR2 a w O) (‖a‖ * R) ↔
      PolygonInClosedDiskR2 v O R := by
  constructor <;> intro h i
  · exact (inClosedDiskR2_directSimilarityR2 ha w O (v i) R).mp (h i)
  · exact (inClosedDiskR2_directSimilarityR2 ha w O (v i) R).mpr (h i)

/-- A surjective map that scales every distance by the same positive factor
preserves minimal enclosing balls, with the radius scaled by that factor. -/
theorem isMinimalEnclosingBall_map_iff {ι α β : Type*}
    [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (s : ℝ)
    (hs : 0 < s) (hf : Function.Surjective f)
    (hscale : ∀ x y, dist (f x) (f y) = s * dist x y)
    (v : ι → α) (O : α) (R : ℝ) :
    IsMinimalEnclosingBall (fun i ↦ f (v i)) (f O) (s * R) ↔
      IsMinimalEnclosingBall v O R := by
  constructor
  · intro h
    refine ⟨(mul_nonneg_iff_of_pos_left hs).mp h.1, ?_, ?_⟩
    · intro i
      rw [Metric.mem_closedBall']
      apply (mul_le_mul_iff_of_pos_left hs).mp
      rw [← hscale]
      exact Metric.mem_closedBall'.mp (h.2.1 i)
    · intro O' R' hR' hcontains
      have hcontains' : ∀ i, f (v i) ∈ Metric.closedBall (f O') (s * R') := by
        intro i
        rw [Metric.mem_closedBall', hscale]
        exact (mul_le_mul_iff_of_pos_left hs).mpr
          (Metric.mem_closedBall'.mp (hcontains i))
      have hmin := h.2.2 (f O') (s * R') (mul_nonneg hs.le hR') hcontains'
      exact (mul_le_mul_iff_of_pos_left hs).mp hmin
  · intro h
    refine ⟨mul_nonneg hs.le h.1, ?_, ?_⟩
    · intro i
      rw [Metric.mem_closedBall', hscale]
      exact (mul_le_mul_iff_of_pos_left hs).mpr
        (Metric.mem_closedBall'.mp (h.2.1 i))
    · intro O' R' hR' hcontains
      obtain ⟨Opre, rfl⟩ := hf O'
      have hcontains' : ∀ i, v i ∈ Metric.closedBall Opre (s⁻¹ * R') := by
        intro i
        rw [Metric.mem_closedBall']
        apply (mul_le_mul_iff_of_pos_left hs).mp
        rw [← hscale]
        simpa [hs.ne'] using Metric.mem_closedBall'.mp (hcontains i)
      have hRpre : 0 ≤ s⁻¹ * R' := mul_nonneg (inv_nonneg.mpr hs.le) hR'
      have hmin := h.2.2 Opre (s⁻¹ * R') hRpre hcontains'
      apply (mul_le_mul_iff_of_pos_left hs).mpr at hmin
      simpa [hs.ne'] using hmin

/-- Direct similarities preserve minimal enclosing disks, scaling the radius
by the norm of the multiplier. -/
theorem minimalEnclosingDiskR2_directSimilarityR2_iff {n : ℕ} {a : ℂ}
    (ha : a ≠ 0) (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    MinimalEnclosingDiskR2 (fun i ↦ directSimilarityR2 a w (v i))
        (directSimilarityR2 a w O) (‖a‖ * R) ↔
      MinimalEnclosingDiskR2 v O R := by
  exact isMinimalEnclosingBall_map_iff (directSimilarityR2 a w) ‖a‖
    (norm_pos_iff.mpr ha) (directSimilarityR2_surjective ha w)
    (dist_directSimilarityR2 a w) v O R

/-- A nondegenerate direct similarity carries a concyclic family to a
concyclic family. -/
theorem concyclic_directSimilarityR2 {n : ℕ} {a : ℂ} (ha : a ≠ 0)
    (w : ℂ) (v : ZMod n → ℂ) (h : Concyclic v) :
    Concyclic (fun i ↦ directSimilarityR2 a w (v i)) := by
  obtain ⟨O, R, hR, hall⟩ := h
  refine ⟨directSimilarityR2 a w O, ‖a‖ * R,
    mul_pos (norm_pos_iff.mpr ha) hR, ?_⟩
  intro i
  rw [dist_directSimilarityR2, hall i]

/-- Nondegenerate direct similarities preserve concyclicity exactly. -/
theorem concyclic_directSimilarityR2_iff {n : ℕ} {a : ℂ} (ha : a ≠ 0)
    (w : ℂ) (v : ZMod n → ℂ) :
    Concyclic (fun i ↦ directSimilarityR2 a w (v i)) ↔ Concyclic v := by
  constructor
  · intro h
    have hpre := concyclic_directSimilarityR2 (inv_ne_zero ha)
      (-(a⁻¹ * w)) (fun i ↦ directSimilarityR2 a w (v i)) h
    simpa only [directSimilarityR2_inverse_apply ha] using hpre
  · exact concyclic_directSimilarityR2 ha w v

/-- Nondegenerate direct similarities preserve nonconcyclicity exactly. -/
theorem not_concyclic_directSimilarityR2_iff {n : ℕ} {a : ℂ} (ha : a ≠ 0)
    (w : ℂ) (v : ZMod n → ℂ) :
    (¬ Concyclic (fun i ↦ directSimilarityR2 a w (v i))) ↔ ¬ Concyclic v := by
  rw [concyclic_directSimilarityR2_iff ha w v]

/-- A nondegenerate direct similarity carries a circumcircle to the
circumcircle with scaled radius. -/
theorem circumcircleR2_directSimilarityR2 {a : ℂ} (ha : a ≠ 0)
    (w A B C O : ℂ) (R : ℝ) (h : CircumcircleR2 A B C O R) :
    CircumcircleR2 (directSimilarityR2 a w A) (directSimilarityR2 a w B)
      (directSimilarityR2 a w C) (directSimilarityR2 a w O) (‖a‖ * R) := by
  refine ⟨mul_pos (norm_pos_iff.mpr ha) h.1, ?_, ?_, ?_⟩
  · rw [dist_directSimilarityR2, h.2.1]
  · rw [dist_directSimilarityR2, h.2.2.1]
  · rw [dist_directSimilarityR2, h.2.2.2]

/-- Nondegenerate direct similarities preserve circumcircles exactly, with
the radius scaled by the multiplier norm. -/
theorem circumcircleR2_directSimilarityR2_iff {a : ℂ} (ha : a ≠ 0)
    (w A B C O : ℂ) (R : ℝ) :
    CircumcircleR2 (directSimilarityR2 a w A) (directSimilarityR2 a w B)
        (directSimilarityR2 a w C) (directSimilarityR2 a w O) (‖a‖ * R) ↔
      CircumcircleR2 A B C O R := by
  constructor
  · rintro ⟨hR, hA, hB, hC⟩
    have hs : 0 < ‖a‖ := norm_pos_iff.mpr ha
    refine ⟨(mul_pos_iff_of_pos_left hs).mp hR, ?_, ?_, ?_⟩
    · rw [dist_directSimilarityR2] at hA
      exact (mul_left_cancel₀ hs.ne' hA)
    · rw [dist_directSimilarityR2] at hB
      exact (mul_left_cancel₀ hs.ne' hB)
    · rw [dist_directSimilarityR2] at hC
      exact (mul_left_cancel₀ hs.ne' hC)
  · exact circumcircleR2_directSimilarityR2 ha w A B C O R

/-- Direct similarities carry vertex cones to vertex cones. -/
theorem inVertexCone_directSimilarityR2 (a w A B C O : ℂ)
    (h : InVertexCone A B C O) :
    InVertexCone (directSimilarityR2 a w A) (directSimilarityR2 a w B)
      (directSimilarityR2 a w C) (directSimilarityR2 a w O) := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := h
  refine ⟨α, β, hα, hβ, ?_⟩
  unfold directSimilarityR2
  linear_combination a * hcenter

/-- Nondegenerate direct similarities preserve vertex-cone membership
exactly. -/
theorem inVertexCone_directSimilarityR2_iff {a : ℂ} (ha : a ≠ 0)
    (w A B C O : ℂ) :
    InVertexCone (directSimilarityR2 a w A) (directSimilarityR2 a w B)
        (directSimilarityR2 a w C) (directSimilarityR2 a w O) ↔
      InVertexCone A B C O := by
  constructor
  · intro h
    have hpre := inVertexCone_directSimilarityR2 a⁻¹ (-(a⁻¹ * w))
      (directSimilarityR2 a w A) (directSimilarityR2 a w B)
      (directSimilarityR2 a w C) (directSimilarityR2 a w O) h
    simpa only [directSimilarityR2_inverse_apply ha] using hpre
  · exact inVertexCone_directSimilarityR2 a w A B C O

/-- Direct similarities preserve project disk-boundary incidence after
scaling the disk radius. -/
theorem onDiskBoundaryR2_directSimilarityR2 {n : ℕ} {a : ℂ}
    (ha : a ≠ 0) (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) (i : ZMod n) :
    OnDiskBoundaryR2 (fun j ↦ directSimilarityR2 a w (v j))
        (directSimilarityR2 a w O) (‖a‖ * R) i ↔
      OnDiskBoundaryR2 v O R i :=
  mem_sphere_directSimilarityR2 ha w O (v i) R

/-- Signed twice-area scales quadratically under a direct similarity. -/
theorem crossR2_directSimilarityR2 (a w A B C : ℂ) :
    Gluck.Discrete.crossR2 (directSimilarityR2 a w A)
        (directSimilarityR2 a w B) (directSimilarityR2 a w C) =
      ‖a‖ ^ 2 * Gluck.Discrete.crossR2 A B C := by
  unfold directSimilarityR2
  rw [Gluck.Discrete.crossR2_add_left]
  have h₁ : a * B - a * A = a * (B - A) := by ring
  have h₂ : a * C - a * A = a * (C - A) := by ring
  unfold Gluck.Discrete.crossR2
  simp only [h₁, h₂, Complex.mul_re, Complex.mul_im]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Signed Menger curvature scales inversely under a nondegenerate direct
similarity. -/
theorem signedMengerR2_directSimilarityR2 {a : ℂ} (ha : a ≠ 0) (w A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 (directSimilarityR2 a w A)
        (directSimilarityR2 a w B) (directSimilarityR2 a w C) =
      ‖a‖⁻¹ * Gluck.Discrete.signedMengerR2 A B C := by
  unfold Gluck.Discrete.signedMengerR2
  rw [crossR2_directSimilarityR2, dist_directSimilarityR2,
    dist_directSimilarityR2, dist_directSimilarityR2]
  have hnorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hden :
      (‖a‖ * dist A B) * (‖a‖ * dist B C) * (‖a‖ * dist C A) =
        ‖a‖ ^ 3 * (dist A B * dist B C * dist C A) := by
    ring
  rw [hden]
  by_cases hD : dist A B * dist B C * dist C A = 0
  · simp [hD]
  · field_simp

/-- Nondegenerate direct similarities preserve positive polygon orientation. -/
theorem positivePolygonOrientation_directSimilarityR2_iff {n : ℕ} {a : ℂ}
    (ha : a ≠ 0) (w : ℂ) (v : ZMod n → ℂ) :
    PositivePolygonOrientation (fun i ↦ directSimilarityR2 a w (v i)) ↔
      PositivePolygonOrientation v := by
  have hs : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  constructor
  · intro h i
    have hi := h i
    rw [crossR2_directSimilarityR2] at hi
    exact (mul_pos_iff_of_pos_left hs).mp hi
  · intro h i
    rw [crossR2_directSimilarityR2]
    exact mul_pos hs (h i)

/-- Nondegenerate direct similarities preserve negative polygon orientation. -/
theorem negativePolygonOrientation_directSimilarityR2_iff {n : ℕ} {a : ℂ}
    (ha : a ≠ 0) (w : ℂ) (v : ZMod n → ℂ) :
    NegativePolygonOrientation (fun i ↦ directSimilarityR2 a w (v i)) ↔
      NegativePolygonOrientation v := by
  have hs : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  constructor
  · intro h i
    have hi := h i
    rw [crossR2_directSimilarityR2] at hi
    exact neg_of_mul_neg_right hi hs.le
  · intro h i
    rw [crossR2_directSimilarityR2]
    exact mul_neg_of_pos_of_neg hs (h i)

/-- Nondegenerate direct similarities preserve strict polygon orientation in
either direction. -/
theorem strictPolygonOrientation_directSimilarityR2_iff {n : ℕ} {a : ℂ}
    (ha : a ≠ 0) (w : ℂ) (v : ZMod n → ℂ) :
    (PositivePolygonOrientation (fun i ↦ directSimilarityR2 a w (v i)) ∨
        NegativePolygonOrientation (fun i ↦ directSimilarityR2 a w (v i))) ↔
      PositivePolygonOrientation v ∨ NegativePolygonOrientation v := by
  rw [positivePolygonOrientation_directSimilarityR2_iff ha w v,
    negativePolygonOrientation_directSimilarityR2_iff ha w v]

/-- The signed-Menger profile scales by the reciprocal similarity factor. -/
theorem SignedMengerProfile_directSimilarityR2 {n : ℕ} {a : ℂ}
    (ha : a ≠ 0) (w : ℂ) (v : ZMod n → ℂ) :
    SignedMengerProfile (fun i ↦ directSimilarityR2 a w (v i)) =
      fun i ↦ ‖a‖⁻¹ * SignedMengerProfile v i := by
  funext i
  exact signedMengerR2_directSimilarityR2 ha w
    (v (i - 1)) (v i) (v (i + 1))

/-- A nondegenerate direct similarity preserves Dahlberg local regularity. -/
theorem dahlbergRegularAt_directSimilarityR2 {a : ℂ} (ha : a ≠ 0)
    (w A B C : ℂ) (h : DahlbergRegularAt A B C) :
    DahlbergRegularAt (directSimilarityR2 a w A) (directSimilarityR2 a w B)
      (directSimilarityR2 a w C) := by
  rcases h with hcollinear | hcircle
  · refine Or.inl ⟨?_, ?_⟩
    · rw [crossR2_directSimilarityR2, hcollinear.1, mul_zero]
    · exact (mem_segment_directSimilarityR2 ha w A C B).mpr hcollinear.2
  · obtain ⟨O, R, hcircle, hcone⟩ := hcircle
    exact Or.inr ⟨directSimilarityR2 a w O, ‖a‖ * R,
      circumcircleR2_directSimilarityR2 ha w A B C O R hcircle,
      inVertexCone_directSimilarityR2 a w A B C O hcone⟩

/-- Nondegenerate direct similarities preserve Dahlberg local regularity
exactly. -/
theorem dahlbergRegularAt_directSimilarityR2_iff {a : ℂ} (ha : a ≠ 0)
    (w A B C : ℂ) :
    DahlbergRegularAt (directSimilarityR2 a w A) (directSimilarityR2 a w B)
        (directSimilarityR2 a w C) ↔
      DahlbergRegularAt A B C := by
  constructor
  · intro h
    have hpre := dahlbergRegularAt_directSimilarityR2 (inv_ne_zero ha)
      (-(a⁻¹ * w)) (directSimilarityR2 a w A) (directSimilarityR2 a w B)
      (directSimilarityR2 a w C) h
    simpa only [directSimilarityR2_inverse_apply ha] using hpre
  · exact dahlbergRegularAt_directSimilarityR2 ha w A B C

/-- A nondegenerate direct similarity preserves Dahlberg regularity of a
cyclic polygon. -/
theorem dahlbergRegular_directSimilarityR2 {n : ℕ} {a : ℂ} (ha : a ≠ 0)
    (w : ℂ) (v : ZMod n → ℂ) (h : DahlbergRegular v) :
    DahlbergRegular (fun i ↦ directSimilarityR2 a w (v i)) := by
  intro i
  exact dahlbergRegularAt_directSimilarityR2 ha w
    (v (i - 1)) (v i) (v (i + 1)) (h i)

/-- Nondegenerate direct similarities preserve Dahlberg regularity of cyclic
polygons exactly. -/
theorem dahlbergRegular_directSimilarityR2_iff {n : ℕ} {a : ℂ}
    (ha : a ≠ 0) (w : ℂ) (v : ZMod n → ℂ) :
    DahlbergRegular (fun i ↦ directSimilarityR2 a w (v i)) ↔
      DahlbergRegular v := by
  constructor
  · intro h i
    exact (dahlbergRegularAt_directSimilarityR2_iff ha w
      (v (i - 1)) (v i) (v (i + 1))).mp (h i)
  · exact dahlbergRegular_directSimilarityR2 ha w v

end Gluck.Forward
