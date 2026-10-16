module

public import Gluck.Forward.Discrete.DirectSimilarity
public import Gluck.Forward.Discrete.ContactSets
public import Gluck.Forward.Discrete.CyclicChordGeometry
public import Gluck.Discrete.PolygonConvexity
public import Mathlib.Geometry.Euclidean.Sphere.Power

/-!
# Dahlberg's oriented circle regions

This file develops the comparison geometry used in Dahlberg's Lemma 8. The
first lemmas treat a shared horizontal chord in normalized coordinates. The
general Euclidean lemma will follow by an orientation-preserving isometry.
-/

@[expose] public section

namespace Gluck.Forward

/-- The power expression of `z` with respect to the circle of centre `c` and
radius `r`. Compatibility alias for `EuclideanGeometry.Sphere.power`. -/
noncomputable abbrev circlePowerR2 (c z : ℂ) (r : ℝ) : ℝ :=
  (⟨c, r⟩ : EuclideanGeometry.Sphere ℂ).power z

/-- Vanishing circle power gives metric incidence when the radius is
nonnegative. -/
theorem dist_eq_of_circlePowerR2_eq_zero {c z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hpower : circlePowerR2 c z r = 0) : dist c z = r := by
  have hz : z ∈ (⟨c, r⟩ : EuclideanGeometry.Sphere ℂ) :=
    (EuclideanGeometry.Sphere.power_eq_zero_iff_mem_sphere hr).mp hpower
  exact EuclideanGeometry.mem_sphere'.mp hz

/-- Circle power is invariant under a direct Euclidean isometry. -/
theorem circlePowerR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w c z : ℂ) (r : ℝ) :
    circlePowerR2 (directIsometryR2 u w c) (directIsometryR2 u w z) r =
      circlePowerR2 c z r := by
  simpa [circlePowerR2, directIsometryR2, directSimilarityR2, hu] using
    sphere_power_directSimilarityR2 u w c z r

/-- Direct Euclidean isometries preserve distance. -/
theorem dist_directIsometryR2 {u : ℂ} (hu : ‖u‖ = 1) (w z₁ z₂ : ℂ) :
    dist (directIsometryR2 u w z₁) (directIsometryR2 u w z₂) = dist z₁ z₂ := by
  simpa [directIsometryR2, directSimilarityR2, hu] using dist_directSimilarityR2 u w z₁ z₂

/-- Positive real homotheties scale distances linearly. -/
theorem dist_posRealHomothety {r : ℝ} (hr : 0 < r) (A B : ℂ) :
    dist ((r : ℂ) * A) ((r : ℂ) * B) = r * dist A B := by
  simpa [directSimilarityR2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
    dist_directSimilarityR2 (r : ℂ) 0 A B

/-- Direct Euclidean isometries preserve membership in a closed disk. -/
theorem inClosedDiskR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w O z : ℂ) (R : ℝ) :
    InClosedDiskR2 (directIsometryR2 u w O) R (directIsometryR2 u w z) ↔
      InClosedDiskR2 O R z := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2, hu] using
    inClosedDiskR2_directSimilarityR2 hu0 w O z R

/-- Direct Euclidean isometries preserve finite polygon containment in a
closed disk. -/
theorem polygonInClosedDiskR2_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    PolygonInClosedDiskR2 (fun i => directIsometryR2 u w (v i))
        (directIsometryR2 u w O) R ↔
      PolygonInClosedDiskR2 v O R := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2, hu] using
    polygonInClosedDiskR2_directSimilarityR2 hu0 w O R v

/-- Direct Euclidean isometries preserve disk-boundary incidence. -/
theorem onDiskBoundaryR2_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) (i : ZMod n) :
    OnDiskBoundaryR2 (fun j => directIsometryR2 u w (v j))
        (directIsometryR2 u w O) R i ↔
      OnDiskBoundaryR2 v O R i := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2, hu] using
    onDiskBoundaryR2_directSimilarityR2 hu0 w O R v i

/-- Positive real homotheties preserve membership in a closed disk, scaling
the radius by the same factor. -/
theorem inClosedDiskR2_posRealHomothety {r : ℝ} (hr : 0 < r)
    (O z : ℂ) (R : ℝ) :
    InClosedDiskR2 ((r : ℂ) * O) (r * R) ((r : ℂ) * z) ↔
      InClosedDiskR2 O R z := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simpa [directSimilarityR2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
    inClosedDiskR2_directSimilarityR2 hr0 0 O z R

/-- Positive real homotheties preserve finite polygon containment in a closed
disk, scaling the radius by the same factor. -/
theorem polygonInClosedDiskR2_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    PolygonInClosedDiskR2 (fun i => (r : ℂ) * v i) ((r : ℂ) * O) (r * R) ↔
      PolygonInClosedDiskR2 v O R := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simpa [directSimilarityR2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
    polygonInClosedDiskR2_directSimilarityR2 hr0 0 O R v

/-- Positive real homotheties preserve disk-boundary incidence, scaling the
radius by the same factor. -/
theorem onDiskBoundaryR2_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (O : ℂ) (R : ℝ) (v : ZMod n → ℂ) (i : ZMod n) :
    OnDiskBoundaryR2 (fun j => (r : ℂ) * v j) ((r : ℂ) * O) (r * R) i ↔
      OnDiskBoundaryR2 v O R i := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simpa [directSimilarityR2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
    onDiskBoundaryR2_directSimilarityR2 hr0 0 O R v i

/-- The explicit inverse centre for a direct Euclidean isometry. -/
theorem directIsometryR2_inverse_center {u : ℂ} (hu : ‖u‖ = 1) (w O' : ℂ) :
    directIsometryR2 u w (u⁻¹ * (O' - w)) = O' := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  unfold directIsometryR2
  rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
  ring

/-- The inverse direct isometry undoes a direct Euclidean isometry. -/
theorem directIsometryR2_inverse_apply {u : ℂ} (hu : ‖u‖ = 1) (w z : ℂ) :
    directIsometryR2 u⁻¹ (-(u⁻¹ * w)) (directIsometryR2 u w z) = z := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2] using
    directSimilarityR2_inverse_apply hu0 w z

/-- Direct Euclidean isometries preserve minimal enclosing disks. -/
theorem minimalEnclosingDiskR2_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    MinimalEnclosingDiskR2 (fun i => directIsometryR2 u w (v i))
        (directIsometryR2 u w O) R ↔
      MinimalEnclosingDiskR2 v O R := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2, hu] using
    minimalEnclosingDiskR2_directSimilarityR2_iff hu0 w O R v

/-- Positive real homotheties preserve minimal enclosing disks, scaling the
radius by the same factor. -/
theorem minimalEnclosingDiskR2_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (O : ℂ) (R : ℝ) (v : ZMod n → ℂ)
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    MinimalEnclosingDiskR2 (fun i => (r : ℂ) * v i) ((r : ℂ) * O) (r * R) := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have h := (minimalEnclosingDiskR2_directSimilarityR2_iff hr0 0 O R v).mpr hΔ
  simpa [directSimilarityR2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using h

/-- Positive real homotheties preserve minimal enclosing disks exactly,
scaling the radius by the same factor. -/
theorem minimalEnclosingDiskR2_posRealHomothety_iff {n : ℕ} {r : ℝ} (hr : 0 < r)
    (O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    MinimalEnclosingDiskR2 (fun i => (r : ℂ) * v i) ((r : ℂ) * O) (r * R) ↔
      MinimalEnclosingDiskR2 v O R := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simpa [directSimilarityR2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
    minimalEnclosingDiskR2_directSimilarityR2_iff hr0 0 O R v

/-- Direct Euclidean isometries preserve concyclicity. -/
theorem concyclic_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    Concyclic (fun i => directIsometryR2 u w (v i)) ↔ Concyclic v := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2] using concyclic_directSimilarityR2_iff hu0 w v

/-- Direct Euclidean isometries preserve nonconcyclicity. -/
theorem not_concyclic_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    (¬ Concyclic (fun i => directIsometryR2 u w (v i))) ↔ ¬ Concyclic v := by
  rw [concyclic_directIsometry hu w v]

/-- Positive real homotheties preserve concyclicity. -/
theorem concyclic_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    Concyclic v →
      Concyclic (fun i => (r : ℂ) * v i) := by
  intro h
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simpa [directSimilarityR2] using concyclic_directSimilarityR2 hr0 0 v h

/-- If a positive real homothety of a cyclic polygon is concyclic, then the
original polygon is concyclic. -/
theorem concyclic_of_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ)
    (hcircle : Concyclic (fun i => (r : ℂ) * v i)) :
    Concyclic v := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  apply (concyclic_directSimilarityR2_iff hr0 0 v).mp
  simpa [directSimilarityR2] using hcircle

/-- Positive real homotheties preserve concyclicity exactly. -/
theorem concyclic_posRealHomothety_iff {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    Concyclic (fun i => (r : ℂ) * v i) ↔ Concyclic v := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simpa [directSimilarityR2] using concyclic_directSimilarityR2_iff hr0 0 v

/-- Positive real homotheties preserve nonconcyclicity in the forward
direction needed for normalized source gates. -/
theorem not_concyclic_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    ¬ Concyclic v →
      ¬ Concyclic (fun i => (r : ℂ) * v i) := by
  intro hnon hcircle
  exact hnon (concyclic_of_posRealHomothety hr v hcircle)

/-- Positive real homotheties preserve nonconcyclicity exactly. -/
theorem not_concyclic_posRealHomothety_iff {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    (¬ Concyclic (fun i => (r : ℂ) * v i)) ↔ ¬ Concyclic v := by
  rw [concyclic_posRealHomothety_iff hr v]

/-- Direct Euclidean isometries carry circumcircles to circumcircles with the
same radius. -/
theorem circumcircleR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w A B C O : ℂ) (R : ℝ) (hcircle : CircumcircleR2 A B C O R) :
    CircumcircleR2 (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) (directIsometryR2 u w O) R := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2, hu] using
    circumcircleR2_directSimilarityR2 hu0 w A B C O R hcircle

/-- Direct Euclidean isometries preserve the signed twice-area. -/
theorem crossR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1) (w A B C : ℂ) :
    Gluck.Discrete.crossR2 (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) = Gluck.Discrete.crossR2 A B C := by
  simpa [directIsometryR2, directSimilarityR2, hu] using crossR2_directSimilarityR2 u w A B C

/-- Direct Euclidean isometries preserve positive polygon orientation. -/
theorem positivePolygonOrientation_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    PositivePolygonOrientation (fun i => directIsometryR2 u w (v i)) ↔
      PositivePolygonOrientation v := by
  simpa [directIsometryR2, directSimilarityR2] using
    positivePolygonOrientation_directSimilarityR2_iff
      (norm_ne_zero_iff.mp (by simp [hu])) w v

/-- Direct Euclidean isometries preserve negative polygon orientation. -/
theorem negativePolygonOrientation_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    NegativePolygonOrientation (fun i => directIsometryR2 u w (v i)) ↔
      NegativePolygonOrientation v := by
  simpa [directIsometryR2, directSimilarityR2] using
    negativePolygonOrientation_directSimilarityR2_iff
      (norm_ne_zero_iff.mp (by simp [hu])) w v

/-- Direct Euclidean isometries preserve having strict polygon orientation in
either direction. -/
theorem strictPolygonOrientation_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    (PositivePolygonOrientation (fun i => directIsometryR2 u w (v i)) ∨
        NegativePolygonOrientation (fun i => directIsometryR2 u w (v i))) ↔
      (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) := by
  rw [positivePolygonOrientation_directIsometry hu w v,
    negativePolygonOrientation_directIsometry hu w v]

/-- Direct Euclidean isometries preserve the non-strict orientation branch. -/
theorem not_strictPolygonOrientation_directIsometry {n : ℕ} {u : ℂ}
    (hu : ‖u‖ = 1) (w : ℂ) (v : ZMod n → ℂ) :
    (¬ (PositivePolygonOrientation (fun i => directIsometryR2 u w (v i)) ∨
        NegativePolygonOrientation (fun i => directIsometryR2 u w (v i)))) ↔
      ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) := by
  rw [strictPolygonOrientation_directIsometry hu w v]

/-- Direct Euclidean isometries preserve signed Menger curvature. -/
theorem signedMengerR2_directIsometry {u : ℂ} (hu : ‖u‖ = 1) (w A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) = Gluck.Discrete.signedMengerR2 A B C := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2, hu] using
    signedMengerR2_directSimilarityR2 hu0 w A B C

/-- Positive real homotheties scale signed twice-area quadratically. -/
theorem crossR2_posRealHomothety (r : ℝ) (A B C : ℂ) :
    Gluck.Discrete.crossR2 ((r : ℂ) * A) ((r : ℂ) * B) ((r : ℂ) * C) =
      r ^ 2 * Gluck.Discrete.crossR2 A B C := by
  simpa [directSimilarityR2, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    crossR2_directSimilarityR2 (r : ℂ) 0 A B C

/-- Positive real homotheties scale signed Menger curvature by the reciprocal
scale. -/
theorem signedMengerR2_posRealHomothety {r : ℝ} (hr : 0 < r) (A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 ((r : ℂ) * A) ((r : ℂ) * B) ((r : ℂ) * C) =
      r⁻¹ * Gluck.Discrete.signedMengerR2 A B C := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simpa [directSimilarityR2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
    signedMengerR2_directSimilarityR2 hr0 0 A B C

/-- Positive real homotheties scale signed-Menger profiles by the reciprocal
scale. -/
theorem SignedMengerProfile_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    SignedMengerProfile (fun i => (r : ℂ) * v i) =
      fun i => r⁻¹ * SignedMengerProfile v i := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simpa [directSimilarityR2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
    SignedMengerProfile_directSimilarityR2 hr0 0 v

/-- Direct Euclidean isometries preserve the signed-Menger profile. -/
theorem SignedMengerProfile_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    SignedMengerProfile (fun i => directIsometryR2 u w (v i)) =
      SignedMengerProfile v := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  simpa [directIsometryR2, directSimilarityR2, hu] using
    SignedMengerProfile_directSimilarityR2 hu0 w v

/-- Direct Euclidean isometries preserve the Dahlberg four-vertex conclusion
for the signed-Menger profile. -/
theorem dahlbergFourVertex_signedMengerProfile_directIsometry_iff {n : ℕ}
    {u : ℂ} (hu : ‖u‖ = 1) (w : ℂ) (v : ZMod n → ℂ) :
    DahlbergFourVertex (SignedMengerProfile (fun i => directIsometryR2 u w (v i))) ↔
      DahlbergFourVertex (SignedMengerProfile v) := by
  constructor
  · intro hfv
    exact dahlbergFourVertex_congr
      (fun i => (congrFun (SignedMengerProfile_directIsometry hu w v) i).symm) hfv
  · intro hfv
    exact dahlbergFourVertex_congr
      (fun i => congrFun (SignedMengerProfile_directIsometry hu w v) i) hfv

/-- Direct Euclidean isometries preserve nonconstancy of the signed-Menger
profile. -/
theorem not_constant_signedMengerProfile_directIsometry_iff {n : ℕ}
    {u : ℂ} (hu : ‖u‖ = 1) (w : ℂ) (v : ZMod n → ℂ) :
    (¬ ∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u w (v j)) i = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_congr_iff
    (fun i => congrFun (SignedMengerProfile_directIsometry hu w v) i)

/-- Cyclic permutations preserve the oriented twice-area. -/
theorem crossR2_cycle (A B C : ℂ) :
    Gluck.Discrete.crossR2 B C A = Gluck.Discrete.crossR2 A B C := by
  exact Gluck.Discrete.crossR2_cycle A B C

/-- Two cyclic steps also preserve oriented twice-area. -/
theorem crossR2_cycle_two (A B C : ℂ) :
    Gluck.Discrete.crossR2 C A B = Gluck.Discrete.crossR2 A B C := by
  exact Gluck.Discrete.crossR2_cycle_two A B C

/-- Swapping the last two vertices reverses the oriented twice-area. -/
theorem crossR2_swap (A B C : ℂ) :
    Gluck.Discrete.crossR2 A C B = -Gluck.Discrete.crossR2 A B C := by
  exact Gluck.Discrete.crossR2_swap A B C

/-- Reversing a triple reverses the oriented twice-area. -/
theorem crossR2_reverse (A B C : ℂ) :
    Gluck.Discrete.crossR2 C B A = -Gluck.Discrete.crossR2 A B C := by
  exact Gluck.Discrete.crossR2_reverse A B C

/-- The oriented twice-area vanishes when the third point is the left endpoint. -/
theorem crossR2_left_endpoint (A B : ℂ) :
    Gluck.Discrete.crossR2 A B A = 0 := by
  exact Gluck.Discrete.crossR2_left_endpoint A B

/-- The oriented twice-area vanishes when the third point is the right endpoint. -/
theorem crossR2_right_endpoint (A B : ℂ) :
    Gluck.Discrete.crossR2 A B B = 0 := by
  exact Gluck.Discrete.crossR2_right_endpoint A B

/-- Unnormalised scalar coordinate along the oriented base edge `A → B`. -/
def lineCoordR2 (A B Z : ℂ) : ℝ :=
  (Z.re - A.re) * (B.re - A.re) + (Z.im - A.im) * (B.im - A.im)

/-- Projection to an arbitrary edge coordinate sends a complex segment into the
unordered real interval joining the projected endpoint coordinates. -/
theorem lineCoordR2_mem_uIcc_of_mem_segment {A B X Y Z : ℂ}
    (hZ : Z ∈ segment ℝ X Y) :
    lineCoordR2 A B Z ∈ Set.uIcc (lineCoordR2 A B X) (lineCoordR2 A B Y) := by
  rw [segment_eq_image_lineMap] at hZ
  rcases hZ with ⟨t, ht, rfl⟩
  rw [← segment_eq_uIcc]
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  unfold lineCoordR2
  simp [AffineMap.lineMap_apply]
  ring

/-- On the line through a nondegenerate base edge, the edge coordinate is
injective. -/
theorem eq_of_crossR2_eq_zero_of_lineCoordR2_eq {A B C D : ℂ} (hAB : A ≠ B)
    (hC : Gluck.Discrete.crossR2 A B C = 0)
    (hD : Gluck.Discrete.crossR2 A B D = 0)
    (hcoord : lineCoordR2 A B C = lineCoordR2 A B D) :
    C = D := by
  have hABsq_pos : 0 < (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 := by
    have hABsq_ne : (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 ≠ 0 := by
      intro hsq
      apply hAB
      apply Complex.ext
      · nlinarith [sq_nonneg (B.re - A.re), sq_nonneg (B.im - A.im)]
      · nlinarith [sq_nonneg (B.re - A.re), sq_nonneg (B.im - A.im)]
    exact lt_of_le_of_ne' (add_nonneg (sq_nonneg _) (sq_nonneg _)) hABsq_ne
  unfold lineCoordR2 at hcoord
  unfold Gluck.Discrete.crossR2 at hC hD
  simp only [Complex.sub_re, Complex.sub_im] at hcoord hC hD
  ring_nf at hcoord hC hD
  have hdot :
      (C.re - D.re) * (B.re - A.re) + (C.im - D.im) * (B.im - A.im) = 0 := by
    linarith
  have hdet :
      (B.re - A.re) * (C.im - D.im) - (B.im - A.im) * (C.re - D.re) = 0 := by
    linarith
  apply Complex.ext
  · have hx :
        (C.re - D.re) * ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) =
          (B.re - A.re) *
              ((C.re - D.re) * (B.re - A.re) +
                (C.im - D.im) * (B.im - A.im)) -
            (B.im - A.im) *
              ((B.re - A.re) * (C.im - D.im) -
                (B.im - A.im) * (C.re - D.re)) := by
      ring
    rw [hdot, hdet, mul_zero, mul_zero, sub_zero] at hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right (ne_of_gt hABsq_pos))
  · have hy :
        (C.im - D.im) * ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) =
          (B.im - A.im) *
              ((C.re - D.re) * (B.re - A.re) +
                (C.im - D.im) * (B.im - A.im)) +
            (B.re - A.re) *
              ((B.re - A.re) * (C.im - D.im) -
                (B.im - A.im) * (C.re - D.re)) := by
      ring
    rw [hdot, hdet, mul_zero, mul_zero, zero_add] at hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right (ne_of_gt hABsq_pos))

/-- Consecutive collinear triples propagate collinearity across the shared
nondegenerate edge. -/
theorem crossR2_eq_zero_of_consecutive {A B C D : ℂ} (hBC : B ≠ C)
    (hABC : Gluck.Discrete.crossR2 A B C = 0)
    (hBCD : Gluck.Discrete.crossR2 B C D = 0) :
    Gluck.Discrete.crossR2 A B D = 0 := by
  have hBCsq_pos : 0 < (B.re - C.re) ^ 2 + (B.im - C.im) ^ 2 := by
    have hBCsq_ne : (B.re - C.re) ^ 2 + (B.im - C.im) ^ 2 ≠ 0 := by
      intro hsq
      apply hBC
      apply Complex.ext
      · nlinarith [sq_nonneg (B.re - C.re), sq_nonneg (B.im - C.im)]
      · nlinarith [sq_nonneg (B.re - C.re), sq_nonneg (B.im - C.im)]
    exact lt_of_le_of_ne' (add_nonneg (sq_nonneg _) (sq_nonneg _)) hBCsq_ne
  unfold Gluck.Discrete.crossR2 at hABC hBCD ⊢
  simp only [Complex.sub_re, Complex.sub_im] at hABC hBCD ⊢
  ring_nf at hABC hBCD ⊢
  have hdet :
      (-(B.re * A.im) + B.re * D.im + A.re * B.im - A.re * D.im +
            A.im * D.re - B.im * D.re) *
          ((B.re - C.re) ^ 2 + (B.im - C.im) ^ 2) =
        (B.re * C.im - B.re * A.im - A.re * C.im + A.re * B.im +
              A.im * C.re - B.im * C.re) *
            (((B.re - C.re) ^ 2 + (B.im - C.im) ^ 2) +
              ((D.re - C.re) * (C.re - B.re) +
                (D.im - C.im) * (C.im - B.im))) +
          (B.re * C.im - B.re * D.im - C.im * D.re - B.im * C.re +
                B.im * D.re + C.re * D.im) *
            ((B.re - A.re) * (C.re - B.re) +
              (B.im - A.im) * (C.im - B.im)) := by
    ring_nf
  rw [hABC, hBCD, zero_mul, zero_mul, zero_add] at hdet
  exact (mul_eq_zero.mp hdet).resolve_right (ne_of_gt hBCsq_pos)

/-- If two points lie on the same nondegenerate line through `A` and `B`, then
the triangle obtained by replacing `A` with one of those points is also
collinear. -/
theorem crossR2_eq_zero_of_same_line_right {A B C D : ℂ} (hAB : A ≠ B)
    (hABC : Gluck.Discrete.crossR2 A B C = 0)
    (hABD : Gluck.Discrete.crossR2 A B D = 0) :
    Gluck.Discrete.crossR2 B C D = 0 := by
  have hABsq_pos : 0 < (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 := by
    have hABsq_ne : (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 ≠ 0 := by
      intro hsq
      apply hAB
      apply Complex.ext
      · nlinarith [sq_nonneg (B.re - A.re), sq_nonneg (B.im - A.im)]
      · nlinarith [sq_nonneg (B.re - A.re), sq_nonneg (B.im - A.im)]
    exact lt_of_le_of_ne' (add_nonneg (sq_nonneg _) (sq_nonneg _)) hABsq_ne
  unfold Gluck.Discrete.crossR2 at hABC hABD ⊢
  simp only [Complex.sub_re, Complex.sub_im] at hABC hABD ⊢
  ring_nf at hABC hABD ⊢
  have hdet :
      (B.re * C.im - B.re * D.im - C.im * D.re - B.im * C.re +
            B.im * D.re + C.re * D.im) *
          ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) =
        (B.re * C.im - B.re * A.im - A.re * C.im + A.re * B.im +
              A.im * C.re - B.im * C.re) *
            (((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) -
              ((D.re - A.re) * (B.re - A.re) +
                (D.im - A.im) * (B.im - A.im))) +
          (-(B.re * A.im) + B.re * D.im + A.re * B.im - A.re * D.im +
                A.im * D.re - B.im * D.re) *
            (((C.re - A.re) * (B.re - A.re) +
                (C.im - A.im) * (B.im - A.im)) -
              ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2)) := by
    ring_nf
  rw [hABC, hABD, zero_mul, zero_mul, zero_add] at hdet
  exact (mul_eq_zero.mp hdet).resolve_right (ne_of_gt hABsq_pos)

/-- One-step propagation along a chain of collinear consecutive triples.  If
`C` and `D` are already on the nondegenerate base line `A B`, and `C,D,E` are
collinear, then `E` is on the same base line. -/
theorem crossR2_eq_zero_of_same_line_step {A B C D E : ℂ}
    (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D)
    (hABC : Gluck.Discrete.crossR2 A B C = 0)
    (hABD : Gluck.Discrete.crossR2 A B D = 0)
    (hCDE : Gluck.Discrete.crossR2 C D E = 0) :
    Gluck.Discrete.crossR2 A B E = 0 := by
  have hBCD : Gluck.Discrete.crossR2 B C D = 0 :=
    crossR2_eq_zero_of_same_line_right hAB hABC hABD
  have hBCE : Gluck.Discrete.crossR2 B C E = 0 :=
    crossR2_eq_zero_of_consecutive hCD hBCD hCDE
  exact crossR2_eq_zero_of_consecutive hBC hABC hBCE

/-- One-step line propagation without any nonincidence condition between the
fixed base edge and the moving edge.  If `C` and `D` are on the nondegenerate
line `A B`, the moving edge `C D` is nondegenerate, and `E` is collinear with
`C,D`, then `E` is on the base line `A B`. -/
theorem crossR2_eq_zero_of_same_line_step_of_moving_edge {A B C D E : ℂ}
    (hCD : C ≠ D)
    (hABC : Gluck.Discrete.crossR2 A B C = 0)
    (hABD : Gluck.Discrete.crossR2 A B D = 0)
    (hCDE : Gluck.Discrete.crossR2 C D E = 0) :
    Gluck.Discrete.crossR2 A B E = 0 := by
  have hCDsq_pos : 0 < (D.re - C.re) ^ 2 + (D.im - C.im) ^ 2 := by
    have hCDsq_ne : (D.re - C.re) ^ 2 + (D.im - C.im) ^ 2 ≠ 0 := by
      intro hsq
      apply hCD
      apply Complex.ext
      · nlinarith [sq_nonneg (D.re - C.re), sq_nonneg (D.im - C.im)]
      · nlinarith [sq_nonneg (D.re - C.re), sq_nonneg (D.im - C.im)]
    exact lt_of_le_of_ne' (add_nonneg (sq_nonneg _) (sq_nonneg _)) hCDsq_ne
  unfold Gluck.Discrete.crossR2 at hABC hABD hCDE ⊢
  simp only [Complex.sub_re, Complex.sub_im] at hABC hABD hCDE ⊢
  ring_nf at hABC hABD hCDE ⊢
  have hdet :
      (-(B.re * A.im) + B.re * E.im + A.re * B.im - A.re * E.im +
            A.im * E.re - B.im * E.re) *
          ((D.re - C.re) ^ 2 + (D.im - C.im) ^ 2) =
        (B.re * C.im - B.re * A.im - A.re * C.im + A.re * B.im +
              A.im * C.re - B.im * C.re) *
            ((D.re - C.re) ^ 2 + (D.im - C.im) ^ 2) +
          (-(C.im * D.re) + C.im * E.re + C.re * D.im - C.re * E.im -
                D.im * E.re + D.re * E.im) *
            ((B.re - A.re) * (D.re - C.re) +
              (B.im - A.im) * (D.im - C.im)) +
          ((-(B.re * A.im) + B.re * D.im + A.re * B.im - A.re * D.im +
                  A.im * D.re - B.im * D.re) -
                (B.re * C.im - B.re * A.im - A.re * C.im + A.re * B.im +
                  A.im * C.re - B.im * C.re)) *
            ((D.re - C.re) * (E.re - C.re) +
              (D.im - C.im) * (E.im - C.im)) := by
    ring_nf
  rw [hABC, hABD, hCDE, zero_mul, zero_mul, sub_self, zero_mul, zero_add,
    zero_add] at hdet
  exact (mul_eq_zero.mp hdet).resolve_right (ne_of_gt hCDsq_pos)

/-- Cyclic permutations preserve signed Menger curvature. -/
theorem signedMengerR2_cycle (A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 B C A =
      Gluck.Discrete.signedMengerR2 A B C := by
  unfold Gluck.Discrete.signedMengerR2
  rw [crossR2_cycle]
  ring

/-- Two cyclic steps also preserve signed Menger curvature. -/
theorem signedMengerR2_cycle_two (A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 C A B =
      Gluck.Discrete.signedMengerR2 A B C := by
  exact (signedMengerR2_cycle C A B).symm

/-- Swapping the last two vertices reverses signed Menger curvature. -/
theorem signedMengerR2_swap (A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 A C B =
      -Gluck.Discrete.signedMengerR2 A B C := by
  unfold Gluck.Discrete.signedMengerR2
  rw [crossR2_swap]
  rw [dist_comm A C, dist_comm C B, dist_comm B A]
  ring

/-- Reversing a triple reverses signed Menger curvature. -/
theorem signedMengerR2_reverse (A B C : ℂ) :
    Gluck.Discrete.signedMengerR2 C B A =
      -Gluck.Discrete.signedMengerR2 A B C := by
  rw [← signedMengerR2_cycle_two C B A, signedMengerR2_swap]

/-- Signed twice-area of a normalized triple. -/
theorem crossR2_normalized (a : ℝ) (z : ℂ) :
    Gluck.Discrete.crossR2 (-a : ℂ) (a : ℂ) z = 2 * a * z.im := by
  unfold Gluck.Discrete.crossR2
  simp only [sub_neg_eq_add, Complex.add_re, Complex.ofReal_re, Complex.add_im,
    Complex.ofReal_im, add_zero, zero_mul, sub_zero]
  ring

/-- A direct Euclidean isometry with unit multiplier is injective. -/
theorem directIsometryR2_injective {u : ℂ} (hu : ‖u‖ = 1) (w : ℂ) :
    Function.Injective (directIsometryR2 u w) := by
  intro z₁ z₂ h
  unfold directIsometryR2 at h
  exact mul_left_cancel₀ (norm_ne_zero_iff.mp (by simp [hu])) (add_right_cancel h)

/-- Direct Euclidean isometries commute with affine line interpolation. -/
theorem directIsometryR2_lineMap (u w A B : ℂ) (t : ℝ) :
    directIsometryR2 u w (AffineMap.lineMap A B t) =
      AffineMap.lineMap (directIsometryR2 u w A) (directIsometryR2 u w B) t :=
  by simpa [directIsometryR2, directSimilarityR2] using directSimilarityR2_lineMap u w A B t

/-- Direct Euclidean isometries preserve membership in a closed segment. -/
theorem mem_segment_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w A B z : ℂ) :
    directIsometryR2 u w z ∈ segment ℝ (directIsometryR2 u w A)
        (directIsometryR2 u w B) ↔
      z ∈ segment ℝ A B := by
  simpa [directIsometryR2, directSimilarityR2] using
    mem_segment_directSimilarityR2 (norm_ne_zero_iff.mp (by simp [hu])) w A B z

/-- Positive real homotheties are injective. -/
theorem posRealHomothety_injective {r : ℝ} (hr : 0 < r) :
    Function.Injective fun z : ℂ => (r : ℂ) * z := by
  intro z₁ z₂ h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') h

/-- Positive real homotheties commute with affine line interpolation. -/
theorem posRealHomothety_lineMap (r : ℝ) (A B : ℂ) (t : ℝ) :
    (r : ℂ) * AffineMap.lineMap A B t =
      AffineMap.lineMap ((r : ℂ) * A) ((r : ℂ) * B) t := by
  simpa [directSimilarityR2] using directSimilarityR2_lineMap (r : ℂ) 0 A B t

/-- Positive real homotheties preserve membership in a closed segment. -/
theorem mem_segment_posRealHomothety {r : ℝ} (hr : 0 < r) (A B z : ℂ) :
    (r : ℂ) * z ∈ segment ℝ ((r : ℂ) * A) ((r : ℂ) * B) ↔
      z ∈ segment ℝ A B := by
  simpa [directSimilarityR2] using
    mem_segment_directSimilarityR2 (Complex.ofReal_ne_zero.mpr hr.ne') 0 A B z

/-- Direct Euclidean isometries preserve simple cyclic polygons. -/
theorem isSimplePolygon_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (fun i => directIsometryR2 u w (v i)) := by
  simpa [directIsometryR2, directSimilarityR2] using
    isSimplePolygon_directSimilarityR2 (norm_ne_zero_iff.mp (by simp [hu])) w hsimple

/-- Direct Euclidean isometries preserve simple cyclic polygons exactly. -/
theorem isSimplePolygon_directIsometry_iff {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    Gluck.Discrete.IsSimplePolygon (fun i => directIsometryR2 u w (v i)) ↔
      Gluck.Discrete.IsSimplePolygon v := by
  simpa [directIsometryR2, directSimilarityR2] using
    isSimplePolygon_directSimilarityR2_iff (norm_ne_zero_iff.mp (by simp [hu])) w v

/-- Positive real homotheties preserve simple cyclic polygons. -/
theorem isSimplePolygon_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (fun i => (r : ℂ) * v i) := by
  simpa [directSimilarityR2] using
    isSimplePolygon_directSimilarityR2 (Complex.ofReal_ne_zero.mpr hr.ne') 0 hsimple

/-- Direct Euclidean isometries preserve membership of a circumcentre in a
vertex cone. -/
theorem inVertexCone_directIsometry (u w A B C O : ℂ)
    (hcone : InVertexCone A B C O) :
    InVertexCone (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) (directIsometryR2 u w O) := by
  simpa [directIsometryR2, directSimilarityR2] using
    inVertexCone_directSimilarityR2 u w A B C O hcone

/-- Positive real homotheties preserve membership of a circumcentre in a
vertex cone. -/
theorem inVertexCone_posRealHomothety (r : ℝ) (A B C O : ℂ)
    (hcone : InVertexCone A B C O) :
    InVertexCone ((r : ℂ) * A) ((r : ℂ) * B)
      ((r : ℂ) * C) ((r : ℂ) * O) := by
  simpa [directSimilarityR2] using inVertexCone_directSimilarityR2 (r : ℂ) 0 A B C O hcone

/-- Positive real homotheties carry circumcircles to circumcircles, scaling
the radius by the same positive factor. -/
theorem circumcircleR2_posRealHomothety {r : ℝ} (hr : 0 < r)
    (A B C O : ℂ) (R : ℝ) (hcircle : CircumcircleR2 A B C O R) :
    CircumcircleR2 ((r : ℂ) * A) ((r : ℂ) * B) ((r : ℂ) * C)
      ((r : ℂ) * O) (r * R) := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simpa [directSimilarityR2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
    circumcircleR2_directSimilarityR2 hr0 0 A B C O R hcircle

/-- Direct Euclidean isometries preserve Dahlberg local regularity. -/
theorem dahlbergRegularAt_directIsometry {u : ℂ} (hu : ‖u‖ = 1)
    (w A B C : ℂ) (hregular : DahlbergRegularAt A B C) :
    DahlbergRegularAt (directIsometryR2 u w A) (directIsometryR2 u w B)
      (directIsometryR2 u w C) := by
  simpa [directIsometryR2, directSimilarityR2] using
    dahlbergRegularAt_directSimilarityR2 (norm_ne_zero_iff.mp (by simp [hu])) w
      A B C hregular

/-- Direct Euclidean isometries preserve Dahlberg regularity of cyclic
polygons. -/
theorem dahlbergRegular_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) (hregular : DahlbergRegular v) :
    DahlbergRegular (fun i => directIsometryR2 u w (v i)) := by
  simpa [directIsometryR2, directSimilarityR2] using
    dahlbergRegular_directSimilarityR2 (norm_ne_zero_iff.mp (by simp [hu])) w
      v hregular

/-- Positive real homotheties preserve Dahlberg local regularity. -/
theorem dahlbergRegularAt_posRealHomothety {r : ℝ} (hr : 0 < r)
    (A B C : ℂ) (hregular : DahlbergRegularAt A B C) :
    DahlbergRegularAt ((r : ℂ) * A) ((r : ℂ) * B) ((r : ℂ) * C) := by
  simpa [directSimilarityR2] using
    dahlbergRegularAt_directSimilarityR2
      (Complex.ofReal_ne_zero.mpr hr.ne') 0 A B C hregular

/-- Positive real homotheties preserve Dahlberg regularity of cyclic
polygons. -/
theorem dahlbergRegular_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) (hregular : DahlbergRegular v) :
    DahlbergRegular (fun i => (r : ℂ) * v i) := by
  simpa [directSimilarityR2] using
    dahlbergRegular_directSimilarityR2 (Complex.ofReal_ne_zero.mpr hr.ne') 0
      v hregular

/-- Positive real homotheties preserve positive polygon orientation exactly. -/
theorem positivePolygonOrientation_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    PositivePolygonOrientation (fun i => (r : ℂ) * v i) ↔
      PositivePolygonOrientation v := by
  simpa [directSimilarityR2] using
    positivePolygonOrientation_directSimilarityR2_iff
      (Complex.ofReal_ne_zero.mpr hr.ne') 0 v

/-- Positive real homotheties preserve negative polygon orientation exactly. -/
theorem negativePolygonOrientation_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    NegativePolygonOrientation (fun i => (r : ℂ) * v i) ↔
      NegativePolygonOrientation v := by
  simpa [directSimilarityR2] using
    negativePolygonOrientation_directSimilarityR2_iff
      (Complex.ofReal_ne_zero.mpr hr.ne') 0 v

/-- Positive real homotheties preserve having strict polygon orientation in
either direction. -/
theorem strictPolygonOrientation_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    (PositivePolygonOrientation (fun i => (r : ℂ) * v i) ∨
        NegativePolygonOrientation (fun i => (r : ℂ) * v i)) ↔
      (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) := by
  rw [positivePolygonOrientation_posRealHomothety hr v,
    negativePolygonOrientation_posRealHomothety hr v]

/-- Positive real homotheties preserve the non-strict orientation branch. -/
theorem not_strictPolygonOrientation_posRealHomothety {n : ℕ} {r : ℝ}
    (hr : 0 < r) (v : ZMod n → ℂ) :
    (¬ (PositivePolygonOrientation (fun i => (r : ℂ) * v i) ∨
        NegativePolygonOrientation (fun i => (r : ℂ) * v i))) ↔
      ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v) := by
  rw [strictPolygonOrientation_posRealHomothety hr v]

/-- Direct Euclidean isometries preserve Dahlberg local regularity exactly. -/
theorem dahlbergRegularAt_directIsometry_iff {u : ℂ} (hu : ‖u‖ = 1)
    (w A B C : ℂ) :
    DahlbergRegularAt (directIsometryR2 u w A) (directIsometryR2 u w B)
        (directIsometryR2 u w C) ↔
      DahlbergRegularAt A B C := by
  simpa [directIsometryR2, directSimilarityR2] using
    dahlbergRegularAt_directSimilarityR2_iff (norm_ne_zero_iff.mp (by simp [hu]))
      w A B C

/-- Direct Euclidean isometries preserve Dahlberg regularity of cyclic
polygons exactly. -/
theorem dahlbergRegular_directIsometry_iff {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    DahlbergRegular (fun i => directIsometryR2 u w (v i)) ↔
      DahlbergRegular v := by
  simpa [directIsometryR2, directSimilarityR2] using
    dahlbergRegular_directSimilarityR2_iff (norm_ne_zero_iff.mp (by simp [hu]))
      w v

/-- Image of a planar region under a direct Euclidean isometry. -/
def directIsometryImage (u w : ℂ) (S : Set ℂ) : Set ℂ :=
  directIsometryR2 u w '' S

/-- Endpoints of a transported horizontal chord. -/
def transportedChordLeft (u w : ℂ) (a : ℝ) : ℂ := directIsometryR2 u w (-a : ℂ)
def transportedChordRight (u w : ℂ) (a : ℝ) : ℂ := directIsometryR2 u w (a : ℂ)

/-- Unit direction, midpoint, and half-length of a nondegenerate chord. -/
noncomputable def chordUnit (A B : ℂ) : ℂ := (B - A) / (‖B - A‖ : ℂ)
noncomputable def chordMidpoint (A B : ℂ) : ℂ := (A + B) / 2
noncomputable def chordHalfLength (A B : ℂ) : ℝ := ‖B - A‖ / 2

/-- Coordinates in which the chord `A–B` becomes horizontal and centred. -/
noncomputable def edgeCoordinates (A B z : ℂ) : ℂ :=
  (starRingEnd ℂ) (chordUnit A B) * (z - chordMidpoint A B)

/-- Passing to canonical edge coordinates preserves the vertex-cone
regularity condition. -/
theorem inVertexCone_edgeCoordinates (E₁ E₂ A B C O : ℂ)
    (hcone : InVertexCone A B C O) :
    InVertexCone (edgeCoordinates E₁ E₂ A) (edgeCoordinates E₁ E₂ B)
      (edgeCoordinates E₁ E₂ C) (edgeCoordinates E₁ E₂ O) := by
  have h := inVertexCone_directIsometry
    ((starRingEnd ℂ) (chordUnit E₁ E₂))
    (-((starRingEnd ℂ) (chordUnit E₁ E₂)) * chordMidpoint E₁ E₂) A B C O hcone
  convert h using 1 <;> simp only [edgeCoordinates, directIsometryR2] <;> ring

/-- The canonical chord direction has unit norm. -/
theorem norm_chordUnit {A B : ℂ} (hAB : A ≠ B) : ‖chordUnit A B‖ = 1 := by
  unfold chordUnit
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < ‖B - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  rw [abs_of_pos hpos, div_self hpos.ne']

/-- Canonical edge coordinates preserve a circumcircle and its radius. -/
theorem circumcircleR2_edgeCoordinates {E₁ E₂ A B C O : ℂ} {R : ℝ}
    (hE : E₁ ≠ E₂)
    (hcircle : CircumcircleR2 A B C O R) :
    CircumcircleR2 (edgeCoordinates E₁ E₂ A) (edgeCoordinates E₁ E₂ B)
      (edgeCoordinates E₁ E₂ C) (edgeCoordinates E₁ E₂ O) R := by
  have hu : ‖(starRingEnd ℂ) (chordUnit E₁ E₂)‖ = 1 := by
    simpa using norm_chordUnit hE
  have h := circumcircleR2_directIsometry hu
    (-((starRingEnd ℂ) (chordUnit E₁ E₂)) * chordMidpoint E₁ E₂) A B C O R hcircle
  convert h using 1 <;> simp only [edgeCoordinates, directIsometryR2] <;> ring

/-- Canonical edge coordinates invert the direct isometry. -/
theorem directIsometryR2_edgeCoordinates {A B : ℂ} (hAB : A ≠ B) (z : ℂ) :
    directIsometryR2 (chordUnit A B) (chordMidpoint A B) (edgeCoordinates A B z) = z := by
  unfold directIsometryR2 edgeCoordinates
  have hu := Complex.mul_conj (chordUnit A B)
  rw [Complex.normSq_eq_norm_sq, norm_chordUnit hAB, one_pow, Complex.ofReal_one] at hu
  rw [← mul_assoc, hu, one_mul]
  ring

/-- A nondegenerate chord has positive half-length. -/
theorem chordHalfLength_pos {A B : ℂ} (hAB : A ≠ B) : 0 < chordHalfLength A B := by
  unfold chordHalfLength
  have hpos : 0 < ‖B - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  positivity

/-- The canonical direct isometry sends the normalized chord endpoints exactly
to `A` and `B`. -/
theorem canonicalChord_endpoints {A B : ℂ} (hAB : A ≠ B) :
    transportedChordLeft (chordUnit A B) (chordMidpoint A B) (chordHalfLength A B) = A ∧
      transportedChordRight (chordUnit A B) (chordMidpoint A B) (chordHalfLength A B) = B := by
  constructor
  · unfold transportedChordLeft chordUnit chordMidpoint chordHalfLength directIsometryR2
    push_cast
    have hn : (↑‖B - A‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAB.symm))
    field_simp [hn]
    ring
  · unfold transportedChordRight chordUnit chordMidpoint chordHalfLength directIsometryR2
    push_cast
    have hn : (↑‖B - A‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAB.symm))
    field_simp [hn]
    ring

/-- In canonical coordinates the original edge endpoints are `−a` and `a`. -/
theorem edgeCoordinates_endpoints {A B : ℂ} (hAB : A ≠ B) :
    edgeCoordinates A B A = (-chordHalfLength A B : ℂ) ∧
      edgeCoordinates A B B = (chordHalfLength A B : ℂ) := by
  constructor
  · apply directIsometryR2_injective (norm_chordUnit hAB) (chordMidpoint A B)
    rw [directIsometryR2_edgeCoordinates hAB]
    exact (canonicalChord_endpoints hAB).1.symm
  · apply directIsometryR2_injective (norm_chordUnit hAB) (chordMidpoint A B)
    rw [directIsometryR2_edgeCoordinates hAB]
    exact (canonicalChord_endpoints hAB).2.symm

/-- Signed twice-area in canonical edge coordinates. -/
theorem crossR2_edgeCoordinates {A B : ℂ} (hAB : A ≠ B) (C : ℂ) :
    Gluck.Discrete.crossR2 (-chordHalfLength A B : ℂ) (chordHalfLength A B : ℂ)
      (edgeCoordinates A B C) = Gluck.Discrete.crossR2 A B C := by
  have h := crossR2_directIsometry (norm_chordUnit hAB) (chordMidpoint A B)
    (-chordHalfLength A B : ℂ) (chordHalfLength A B : ℂ) (edgeCoordinates A B C)
  have he := canonicalChord_endpoints hAB
  unfold transportedChordLeft transportedChordRight at he
  rw [he.1, he.2, directIsometryR2_edgeCoordinates hAB] at h
  exact h.symm

/-- A noncollinear third point has nonzero vertical coordinate in the
canonical edge frame. -/
theorem edgeCoordinates_im_ne_zero {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    (edgeCoordinates A B C).im ≠ 0 := by
  intro him
  have hnorm := crossR2_edgeCoordinates hAB C
  rw [crossR2_normalized, him, mul_zero] at hnorm
  exact hcross hnorm.symm

/-- Orientation is the sign of the vertical coordinate in the canonical edge
frame. -/
theorem crossR2_pos_iff_edgeCoordinates_im_pos {A B : ℂ} (hAB : A ≠ B) (C : ℂ) :
    0 < Gluck.Discrete.crossR2 A B C ↔ 0 < (edgeCoordinates A B C).im := by
  rw [← crossR2_edgeCoordinates hAB C, crossR2_normalized]
  have hcoef : 0 < 2 * chordHalfLength A B := mul_pos (by norm_num) (chordHalfLength_pos hAB)
  exact mul_pos_iff_of_pos_left hcoef

/-- Negative orientation is likewise the sign of the canonical vertical
coordinate. -/
theorem crossR2_neg_iff_edgeCoordinates_im_neg {A B : ℂ} (hAB : A ≠ B) (C : ℂ) :
    Gluck.Discrete.crossR2 A B C < 0 ↔ (edgeCoordinates A B C).im < 0 := by
  rw [← crossR2_edgeCoordinates hAB C, crossR2_normalized]
  have hcoef : 0 < 2 * chordHalfLength A B := mul_pos (by norm_num) (chordHalfLength_pos hAB)
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg hcoef.le (le_of_not_gt hn))) h
  · intro h
    exact mul_neg_of_pos_of_neg hcoef h

/-- Centre of the normalized coaxial family. -/
def normalizedCircleCenter (y : ℝ) : ℂ := ⟨0, y⟩

/-- Radius of the normalized circle through `−a` and `a`. -/
noncomputable def normalizedCircleRadius (a y : ℝ) : ℝ := Real.sqrt (a ^ 2 + y ^ 2)

/-- Positive Euclidean curvature of a member of the normalized circle family. -/
noncomputable def normalizedCircleCurvature (a y : ℝ) : ℝ :=
  1 / normalizedCircleRadius a y

/-- Coaxial-family parameter of the circle through `−a`, `a`, and a
noncollinear third point `z`. -/
noncomputable def normalizedCircumcenterParameter (a : ℝ) (z : ℂ) : ℝ :=
  (z.re ^ 2 + z.im ^ 2 - a ^ 2) / (2 * z.im)

/-- Expanded power equation for the normalized coaxial family. -/
theorem circlePowerR2_normalized (a y : ℝ) (z : ℂ) :
    circlePowerR2 (normalizedCircleCenter y) z (normalizedCircleRadius a y) =
      z.re ^ 2 + z.im ^ 2 - 2 * y * z.im - a ^ 2 := by
  unfold circlePowerR2 EuclideanGeometry.Sphere.power normalizedCircleCenter
    normalizedCircleRadius
  rw [dist_eq_norm]
  rw [Complex.sq_norm, Complex.normSq_apply, Real.sq_sqrt (by positivity)]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- The parameter formula puts the third point on the normalized circle. -/
theorem circlePowerR2_normalized_parameter {a : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    circlePowerR2 (normalizedCircleCenter (normalizedCircumcenterParameter a z)) z
      (normalizedCircleRadius a (normalizedCircumcenterParameter a z)) = 0 := by
  rw [circlePowerR2_normalized]
  unfold normalizedCircumcenterParameter
  field_simp [hz]
  ring

/-- A point equidistant from the endpoints and a noncollinear third point is
the canonical normalized circumcentre. -/
theorem eq_normalizedCircleCenter_of_equidistant {a : ℝ} (ha : a ≠ 0)
    {z O : ℂ} (hz : z.im ≠ 0)
    (hends : dist O (-a : ℂ) = dist O (a : ℂ))
    (hthird : dist O z = dist O (a : ℂ)) :
    O = normalizedCircleCenter (normalizedCircumcenterParameter a z) := by
  have hendsSq := congrArg (fun x : ℝ => x ^ 2) hends
  simp only [dist_eq_norm] at hendsSq
  rw [Complex.sq_norm, Complex.sq_norm] at hendsSq
  simp only [sub_neg_eq_add, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, add_zero, Complex.sub_re, Complex.sub_im,
    sub_zero, add_left_inj] at hendsSq
  have hOre : O.re = 0 := by
    have hprod : O.re * a = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_right ha
  have hthirdSq := congrArg (fun x : ℝ => x ^ 2) hthird
  simp only [dist_eq_norm] at hthirdSq
  rw [Complex.sq_norm, Complex.sq_norm] at hthirdSq
  simp [Complex.normSq_apply, hOre] at hthirdSq
  have hOim : O.im = normalizedCircumcenterParameter a z := by
    unfold normalizedCircumcenterParameter
    field_simp [hz]
    nlinarith
  apply Complex.ext <;> simp [normalizedCircleCenter, hOre, hOim]

/-- A circle through the normalized chord endpoints and a third point on the
same line must have that third point equal to one of the endpoints. -/
theorem normalized_collinear_circumcircle_third_eq_endpoint {a R : ℝ} (ha : a ≠ 0)
    {z O : ℂ} (hz : z.im = 0)
    (hcircle : CircumcircleR2 (-a : ℂ) (a : ℂ) z O R) :
    z = (-a : ℂ) ∨ z = (a : ℂ) := by
  have hendsSq := congrArg (fun x : ℝ => x ^ 2)
    (hcircle.2.1.trans hcircle.2.2.1.symm)
  simp only [dist_eq_norm] at hendsSq
  rw [Complex.sq_norm, Complex.sq_norm] at hendsSq
  simp only [sub_neg_eq_add, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, add_zero, Complex.sub_re, Complex.sub_im,
    sub_zero, add_left_inj] at hendsSq
  have hOre : O.re = 0 := by
    have hprod : O.re * a = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_right ha
  have hthirdSq := congrArg (fun x : ℝ => x ^ 2)
    (hcircle.2.2.2.trans hcircle.2.2.1.symm)
  simp only [dist_eq_norm] at hthirdSq
  rw [Complex.sq_norm, Complex.sq_norm] at hthirdSq
  simp [Complex.normSq_apply, hOre, hz] at hthirdSq
  have hzsq : z.re ^ 2 = a ^ 2 := by nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hzsq with hza | hza
  · right
    apply Complex.ext <;> simp [hza, hz]
  · left
    apply Complex.ext <;> simp [hza, hz]

/-- Algebraic circumradius identity for a normalized triple. -/
theorem normalized_circumradius_sq_identity {a : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    4 * z.im ^ 2 *
        (a ^ 2 + normalizedCircumcenterParameter a z ^ 2) =
      ((z.re - a) ^ 2 + z.im ^ 2) * ((z.re + a) ^ 2 + z.im ^ 2) := by
  unfold normalizedCircumcenterParameter
  field_simp [hz]
  ring

/-- Squared side lengths of a normalized triple. -/
theorem dist_sq_normalized_right (a : ℝ) (z : ℂ) :
    dist (a : ℂ) z ^ 2 = (z.re - a) ^ 2 + z.im ^ 2 := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  simp
  ring

theorem dist_sq_normalized_left (a : ℝ) (z : ℂ) :
    dist (-a : ℂ) z ^ 2 = (z.re + a) ^ 2 + z.im ^ 2 := by
  simpa using dist_sq_normalized_right (-a) z

theorem dist_normalized_endpoints {a : ℝ} (ha : 0 < a) :
    dist (-a : ℂ) (a : ℂ) = 2 * a := by
  rw [dist_eq_norm]
  have h : (-↑a : ℂ) - ↑a = (↑(-2 * a) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  ring

/-- Product of the two non-base side lengths in terms of circumradius. -/
theorem normalized_side_product {a : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    dist (a : ℂ) z * dist z (-a : ℂ) =
      2 * |z.im| * normalizedCircleRadius a (normalizedCircumcenterParameter a z) := by
  apply (sq_eq_sq₀ (mul_nonneg dist_nonneg dist_nonneg)
    (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (by
      unfold normalizedCircleRadius
      positivity))).mp
  simp only [mul_pow]
  rw [dist_comm z (-a : ℂ), dist_sq_normalized_right, dist_sq_normalized_left]
  rw [normalizedCircleRadius, Real.sq_sqrt (by positivity), sq_abs]
  norm_num
  exact (normalized_circumradius_sq_identity hz).symm

/-- Signed Menger curvature of a normalized noncollinear triple is the signed
reciprocal circumradius. -/
theorem signedMengerR2_normalized {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z.im ≠ 0) :
    Gluck.Discrete.signedMengerR2 (-a : ℂ) (a : ℂ) z =
      (z.im / |z.im|) *
        normalizedCircleCurvature a (normalizedCircumcenterParameter a z) := by
  unfold Gluck.Discrete.signedMengerR2
  rw [crossR2_normalized, dist_normalized_endpoints ha]
  rw [mul_assoc (2 * a) (dist (a : ℂ) z) (dist z (-a : ℂ))]
  rw [normalized_side_product hz]
  unfold normalizedCircleCurvature
  have habs : |z.im| ≠ 0 := abs_ne_zero.mpr hz
  have hr : normalizedCircleRadius a (normalizedCircumcenterParameter a z) ≠ 0 :=
    (by unfold normalizedCircleRadius; positivity)
  field_simp [ha.ne', habs, hr]

/-- The upper oriented cap bounded by the horizontal chord from `−a` to `a`
and the circle through its endpoints whose centre is `iy`. Expanding the
circle equation gives `x² + v² - 2yv ≤ a²`. -/
def normalizedUpperCap (a y : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2}

/-- Interior-side half-plane, closed disk, and closed exterior for the
normalized shared chord. -/
def normalizedEdgeHalfPlane : Set ℂ := {z | 0 ≤ z.im}

def normalizedClosedDisk (a y : ℝ) : Set ℂ :=
  {z | z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2}

def normalizedClosedExterior (a y : ℝ) : Set ℂ :=
  {z | a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im}

/-- Both normalized chord endpoints lie on the boundary of the normalized
interior-side half-plane. -/
theorem normalizedEdgeHalfPlane_endpoints (a : ℝ) :
    (a : ℂ) ∈ normalizedEdgeHalfPlane ∧ (-a : ℂ) ∈ normalizedEdgeHalfPlane := by
  constructor <;> simp [normalizedEdgeHalfPlane]

/-- Both normalized chord endpoints lie in every coaxial closed disk. -/
theorem normalizedClosedDisk_endpoints (a y : ℝ) :
    (a : ℂ) ∈ normalizedClosedDisk a y ∧
      (-a : ℂ) ∈ normalizedClosedDisk a y := by
  constructor
  · change (a : ℂ).re ^ 2 + (a : ℂ).im ^ 2 - 2 * y * (a : ℂ).im ≤ a ^ 2
    simp
  · change (-a : ℂ).re ^ 2 + (-a : ℂ).im ^ 2 - 2 * y * (-a : ℂ).im ≤ a ^ 2
    simp

/-- The normalized algebraic closed disk is the metric closed disk with centre
`normalizedCircleCenter y` and radius `normalizedCircleRadius a y`. -/
theorem mem_normalizedClosedDisk_iff_dist_le (a y : ℝ) (z : ℂ) :
    z ∈ normalizedClosedDisk a y ↔
      dist (normalizedCircleCenter y) z ≤ normalizedCircleRadius a y := by
  rw [dist_eq_norm]
  unfold normalizedClosedDisk normalizedCircleCenter normalizedCircleRadius
  have hnorm :
      ‖({ re := 0, im := y } : ℂ) - z‖ ^ 2 =
        z.re ^ 2 + z.im ^ 2 - 2 * y * z.im + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  constructor
  · intro h
    change z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2 at h
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [hnorm, Real.sq_sqrt (by positivity)]
    nlinarith
  · intro h
    have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr h
    rw [hnorm, Real.sq_sqrt (by positivity)] at hs
    change z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2
    nlinarith

/-- The normalized algebraic closed exterior is the metric closed exterior
with centre `normalizedCircleCenter y` and radius `normalizedCircleRadius a y`. -/
theorem mem_normalizedClosedExterior_iff_radius_le_dist (a y : ℝ) (z : ℂ) :
    z ∈ normalizedClosedExterior a y ↔
      normalizedCircleRadius a y ≤ dist (normalizedCircleCenter y) z := by
  rw [dist_eq_norm]
  unfold normalizedClosedExterior normalizedCircleCenter normalizedCircleRadius
  have hnorm :
      ‖({ re := 0, im := y } : ℂ) - z‖ ^ 2 =
        z.re ^ 2 + z.im ^ 2 - 2 * y * z.im + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  constructor
  · intro h
    change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im at h
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
    rw [hnorm, Real.sq_sqrt (by positivity)]
    nlinarith
  · intro h
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mpr h
    rw [hnorm, Real.sq_sqrt (by positivity)] at hs
    change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im
    nlinarith

/-- The noncollinear third point lies in the closed disk bounded by its
normalized circumcircle. -/
theorem normalizedCircumcenter_mem_closedDisk {a : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ normalizedClosedDisk a (normalizedCircumcenterParameter a z) := by
  have hzero := circlePowerR2_normalized_parameter (a := a) (z := z) hz
  rw [circlePowerR2_normalized] at hzero
  change z.re ^ 2 + z.im ^ 2 -
      2 * normalizedCircumcenterParameter a z * z.im ≤ a ^ 2
  linarith

/-- Dahlberg's exact oriented region `δ(P,e)` in normalized coordinates. -/
def normalizedDahlbergRegion (a y k : ℝ) : Set ℂ :=
  if 0 < k then normalizedClosedDisk a y ∩ normalizedEdgeHalfPlane
  else if k < 0 then
    normalizedClosedExterior a y ∪ (normalizedClosedDisk a y ∩ normalizedEdgeHalfPlane)
  else normalizedEdgeHalfPlane

/-- Positive curvature selects the disk-side cap. -/
theorem normalizedDahlbergRegion_eq_upperCap_of_pos {a y k : ℝ} (hk : 0 < k) :
    normalizedDahlbergRegion a y k = normalizedUpperCap a y := by
  ext z
  simp [normalizedDahlbergRegion, hk, normalizedClosedDisk,
    normalizedEdgeHalfPlane, normalizedUpperCap, and_comm]

/-- Dahlberg Lemma 8(1): a nonnegative-curvature region lies in the interior
half-plane. -/
theorem normalizedDahlbergRegion_subset_halfPlane {a y k : ℝ} (hk : 0 ≤ k) :
    normalizedDahlbergRegion a y k ⊆ normalizedEdgeHalfPlane := by
  rcases hk.eq_or_lt with rfl | hk
  · simp [normalizedDahlbergRegion]
  · rw [normalizedDahlbergRegion_eq_upperCap_of_pos hk]
    intro z hz
    exact hz.1

/-- On the positive branch, Dahlberg's exact region lies in the closed disk. -/
theorem normalizedDahlbergRegion_subset_closedDisk_of_pos {a y k : ℝ} (hk : 0 < k) :
    normalizedDahlbergRegion a y k ⊆ normalizedClosedDisk a y := by
  rw [normalizedDahlbergRegion_eq_upperCap_of_pos hk]
  intro z hz
  exact hz.2

/-- Dahlberg Lemma 8(2): the interior half-plane lies in every
nonpositive-curvature region. -/
theorem normalizedHalfPlane_subset_dahlbergRegion {a y k : ℝ} (hk : k ≤ 0) :
    normalizedEdgeHalfPlane ⊆ normalizedDahlbergRegion a y k := by
  rcases hk.eq_or_lt with rfl | hk
  · simp [normalizedDahlbergRegion]
  · intro z hz
    rw [normalizedDahlbergRegion, if_neg (not_lt_of_ge hk.le), if_pos hk]
    by_cases hd : z ∈ normalizedClosedDisk a y
    · exact Or.inr ⟨hd, hz⟩
    · apply Or.inl
      change ¬(z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2) at hd
      change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im
      exact (lt_of_not_ge hd).le

/-- Mixed-sign part of Dahlberg Lemma 8(3). -/
theorem normalizedDahlbergRegion_anti_of_nonpos_nonneg
    {a yP yQ kP kQ : ℝ} (hP : kP ≤ 0) (hQ : 0 ≤ kQ) :
    normalizedDahlbergRegion a yQ kQ ⊆ normalizedDahlbergRegion a yP kP := by
  exact (normalizedDahlbergRegion_subset_halfPlane hQ).trans
    (normalizedHalfPlane_subset_dahlbergRegion hP)

/-- On the negative branch, increasing the centre parameter enlarges
Dahlberg's oriented region. -/
theorem normalizedDahlbergRegion_mono_of_negative {a y₁ y₂ k₁ k₂ : ℝ}
    (hy : y₁ ≤ y₂) (hk₁ : k₁ < 0) (hk₂ : k₂ < 0) :
    normalizedDahlbergRegion a y₁ k₁ ⊆ normalizedDahlbergRegion a y₂ k₂ := by
  intro z hz
  rw [normalizedDahlbergRegion, if_neg (not_lt_of_ge hk₁.le), if_pos hk₁] at hz
  rw [normalizedDahlbergRegion, if_neg (not_lt_of_ge hk₂.le), if_pos hk₂]
  rcases hz with hext | hcap
  · by_cases him : 0 ≤ z.im
    · have hhalf : z ∈ normalizedEdgeHalfPlane := him
      have hr := normalizedHalfPlane_subset_dahlbergRegion
        (a := a) (y := y₂) (k := k₂) hk₂.le hhalf
      simpa [normalizedDahlbergRegion, not_lt_of_ge hk₂.le, hk₂] using hr
    · apply Or.inl
      change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y₁ * z.im at hext
      change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y₂ * z.im
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy)
        (lt_of_not_ge him).le]
  · have hr := normalizedHalfPlane_subset_dahlbergRegion
      (a := a) (y := y₂) (k := k₂) hk₂.le hcap.2
    simpa [normalizedDahlbergRegion, not_lt_of_ge hk₂.le, hk₂] using hr

/-- A normalized upper cap transported to arbitrary Euclidean coordinates. -/
def transportedUpperCap (u w : ℂ) (a y : ℝ) : Set ℂ :=
  directIsometryImage u w (normalizedUpperCap a y)

/-- A normalized closed disk transported to arbitrary Euclidean coordinates. -/
def transportedClosedDisk (u w : ℂ) (a y : ℝ) : Set ℂ :=
  directIsometryImage u w (normalizedClosedDisk a y)

/-- The normalized interior-side half-plane transported to arbitrary Euclidean
coordinates. -/
def transportedEdgeHalfPlane (u w : ℂ) : Set ℂ :=
  directIsometryImage u w normalizedEdgeHalfPlane

/-- Dahlberg's exact oriented region transported to arbitrary Euclidean
coordinates. -/
def transportedDahlbergRegion (u w : ℂ) (a y k : ℝ) : Set ℂ :=
  directIsometryImage u w (normalizedDahlbergRegion a y k)

/-- Centre of the transported coaxial family. -/
def transportedCircleCenter (u w : ℂ) (y : ℝ) : ℂ :=
  directIsometryR2 u w (normalizedCircleCenter y)

/-- The canonical circle centre and oriented cap attached to an arbitrary
nondegenerate chord. -/
noncomputable def edgeCircleCenter (A B : ℂ) (y : ℝ) : ℂ :=
  transportedCircleCenter (chordUnit A B) (chordMidpoint A B) y

/-- Coaxial parameter of the circumcircle through an arbitrary noncollinear
triple. -/
noncomputable def edgeCircumcenterParameter (A B C : ℂ) : ℝ :=
  normalizedCircumcenterParameter (chordHalfLength A B) (edgeCoordinates A B C)

noncomputable def edgeUpperCap (A B : ℂ) (y : ℝ) : Set ℂ :=
  transportedUpperCap (chordUnit A B) (chordMidpoint A B) (chordHalfLength A B) y

noncomputable def edgeClosedDisk (A B : ℂ) (y : ℝ) : Set ℂ :=
  transportedClosedDisk (chordUnit A B) (chordMidpoint A B) (chordHalfLength A B) y

noncomputable def edgeClosedExterior (A B : ℂ) (y : ℝ) : Set ℂ :=
  directIsometryImage (chordUnit A B) (chordMidpoint A B)
    (normalizedClosedExterior (chordHalfLength A B) y)

noncomputable def edgeHalfPlane (A B : ℂ) : Set ℂ :=
  transportedEdgeHalfPlane (chordUnit A B) (chordMidpoint A B)

noncomputable def edgeDahlbergRegion (A B : ℂ) (y k : ℝ) : Set ℂ :=
  transportedDahlbergRegion (chordUnit A B) (chordMidpoint A B)
    (chordHalfLength A B) y k

/-- Dahlberg's oriented region attached to a point and an oriented edge, using
the point's signed Menger curvature with that edge. -/
noncomputable def edgePointDahlbergRegion (A B C : ℂ) : Set ℂ :=
  edgeDahlbergRegion A B (edgeCircumcenterParameter A B C)
    (Gluck.Discrete.signedMengerR2 A B C)

/-- Every canonical edge disk contains both endpoints of the edge. -/
theorem edgeClosedDisk_endpoints {A B : ℂ} (hAB : A ≠ B) (y : ℝ) :
    A ∈ edgeClosedDisk A B y ∧ B ∈ edgeClosedDisk A B y := by
  have he := canonicalChord_endpoints hAB
  have hnorm := normalizedClosedDisk_endpoints (chordHalfLength A B) y
  constructor
  · unfold edgeClosedDisk transportedClosedDisk directIsometryImage
    exact ⟨(-chordHalfLength A B : ℂ), hnorm.2, by
      simpa [transportedChordLeft] using he.1⟩
  · unfold edgeClosedDisk transportedClosedDisk directIsometryImage
    exact ⟨(chordHalfLength A B : ℂ), hnorm.1, by
      simpa [transportedChordRight] using he.2⟩

/-- The transported edge closed disk is the metric closed disk with centre
`edgeCircleCenter A B y` and radius `normalizedCircleRadius
(chordHalfLength A B) y`. -/
theorem mem_edgeClosedDisk_iff_dist_le {A B z : ℂ} (hAB : A ≠ B) (y : ℝ) :
    z ∈ edgeClosedDisk A B y ↔
      dist (edgeCircleCenter A B y) z ≤
        normalizedCircleRadius (chordHalfLength A B) y := by
  constructor
  · intro hmem
    unfold edgeClosedDisk transportedClosedDisk directIsometryImage at hmem
    rcases hmem with ⟨z₀, hz₀, hzmap⟩
    have hdist₀ :=
      (mem_normalizedClosedDisk_iff_dist_le (chordHalfLength A B) y z₀).mp hz₀
    rw [← hzmap]
    simpa [edgeCircleCenter, transportedCircleCenter,
      dist_directIsometryR2 (norm_chordUnit hAB)] using hdist₀
  · intro hdist
    have hdist₀ :
        dist (normalizedCircleCenter y) (edgeCoordinates A B z) ≤
          normalizedCircleRadius (chordHalfLength A B) y := by
      have h := hdist
      rw [← directIsometryR2_edgeCoordinates hAB z] at h
      simpa [edgeCircleCenter, transportedCircleCenter,
        dist_directIsometryR2 (norm_chordUnit hAB)] using h
    unfold edgeClosedDisk transportedClosedDisk directIsometryImage
    exact ⟨edgeCoordinates A B z,
      (mem_normalizedClosedDisk_iff_dist_le (chordHalfLength A B) y
        (edgeCoordinates A B z)).mpr hdist₀,
      directIsometryR2_edgeCoordinates hAB z⟩

/-- The transported edge closed exterior is the metric closed exterior with
centre `edgeCircleCenter A B y` and radius `normalizedCircleRadius
(chordHalfLength A B) y`. -/
theorem mem_edgeClosedExterior_iff_radius_le_dist {A B z : ℂ} (hAB : A ≠ B)
    (y : ℝ) :
    z ∈ edgeClosedExterior A B y ↔
      normalizedCircleRadius (chordHalfLength A B) y ≤
        dist (edgeCircleCenter A B y) z := by
  constructor
  · intro hmem
    unfold edgeClosedExterior directIsometryImage at hmem
    rcases hmem with ⟨z₀, hz₀, hzmap⟩
    have hdist₀ :=
      (mem_normalizedClosedExterior_iff_radius_le_dist
        (chordHalfLength A B) y z₀).mp hz₀
    rw [← hzmap]
    simpa [edgeCircleCenter, transportedCircleCenter,
      dist_directIsometryR2 (norm_chordUnit hAB)] using hdist₀
  · intro hdist
    have hdist₀ :
        normalizedCircleRadius (chordHalfLength A B) y ≤
          dist (normalizedCircleCenter y) (edgeCoordinates A B z) := by
      have h := hdist
      rw [← directIsometryR2_edgeCoordinates hAB z] at h
      simpa [edgeCircleCenter, transportedCircleCenter,
        dist_directIsometryR2 (norm_chordUnit hAB)] using h
    unfold edgeClosedExterior directIsometryImage
    exact ⟨edgeCoordinates A B z,
      (mem_normalizedClosedExterior_iff_radius_le_dist (chordHalfLength A B) y
        (edgeCoordinates A B z)).mpr hdist₀,
      directIsometryR2_edgeCoordinates hAB z⟩

/-- Every canonical edge half-plane contains both endpoints of the edge. -/
theorem edgeHalfPlane_endpoints {A B : ℂ} (hAB : A ≠ B) :
    A ∈ edgeHalfPlane A B ∧ B ∈ edgeHalfPlane A B := by
  have he := canonicalChord_endpoints hAB
  have hnorm := normalizedEdgeHalfPlane_endpoints (chordHalfLength A B)
  constructor
  · unfold edgeHalfPlane transportedEdgeHalfPlane directIsometryImage
    exact ⟨(-chordHalfLength A B : ℂ), hnorm.2, by
      simpa [transportedChordLeft] using he.1⟩
  · unfold edgeHalfPlane transportedEdgeHalfPlane directIsometryImage
    exact ⟨(chordHalfLength A B : ℂ), hnorm.1, by
      simpa [transportedChordRight] using he.2⟩

/-- A noncollinear point lies in the canonical edge disk determined by its
circumcircle through the oriented edge. -/
theorem edgePoint_mem_own_edgeClosedDisk {A B C : ℂ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    C ∈ edgeClosedDisk A B (edgeCircumcenterParameter A B C) := by
  have hz := edgeCoordinates_im_ne_zero hAB hcross
  have hmem := normalizedCircumcenter_mem_closedDisk
    (a := chordHalfLength A B) (z := edgeCoordinates A B C) hz
  unfold edgeClosedDisk transportedClosedDisk directIsometryImage
  exact ⟨edgeCoordinates A B C, by simpa [edgeCircumcenterParameter] using hmem,
    directIsometryR2_edgeCoordinates hAB C⟩

/-- The normalized upper cap is the upper-half-plane part of the corresponding
closed Euclidean disk. -/
theorem mem_normalizedUpperCap_iff (a y : ℝ) (z : ℂ) :
    z ∈ normalizedUpperCap a y ↔
      0 ≤ z.im ∧
        circlePowerR2 (normalizedCircleCenter y) z (normalizedCircleRadius a y) ≤ 0 := by
  rw [circlePowerR2_normalized]
  change (0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2) ↔ _
  constructor
  · rintro ⟨him, hpower⟩
    exact ⟨him, by linarith⟩
  · rintro ⟨him, hpower⟩
    exact ⟨him, by linarith⟩

/-- Both endpoints of the normalized chord lie on every circle in the coaxial
family. -/
theorem normalizedCircle_endpoints (a y : ℝ) :
    circlePowerR2 (normalizedCircleCenter y) (a : ℂ) (normalizedCircleRadius a y) = 0 ∧
      circlePowerR2 (normalizedCircleCenter y) (-a : ℂ) (normalizedCircleRadius a y) = 0 := by
  constructor
  · rw [circlePowerR2_normalized]
    simp
  · rw [circlePowerR2_normalized]
    simp

/-- In a normalized regular vertex cone, a third point above the edge forces
the circumcentre above the edge. -/
theorem normalizedCenter_nonneg_of_inVertexCone {a y : ℝ} {z : ℂ}
    (hcone : InVertexCone z (-a : ℂ) (a : ℂ) (normalizedCircleCenter y))
    (hz : 0 < z.im) : 0 ≤ y := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := hcone
  have him := congrArg Complex.im hcenter
  simp [normalizedCircleCenter] at him
  nlinarith [mul_nonneg hα hz.le]

/-- In a normalized regular vertex cone, a third point below the edge forces
the circumcentre below the edge. -/
theorem normalizedCenter_nonpos_of_inVertexCone {a y : ℝ} {z : ℂ}
    (hcone : InVertexCone z (-a : ℂ) (a : ℂ) (normalizedCircleCenter y))
    (hz : z.im < 0) : y ≤ 0 := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := hcone
  have him := congrArg Complex.im hcenter
  simp [normalizedCircleCenter] at him
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hz.le]

/-- The right-endpoint version of the normalized vertex-cone sign statement. -/
theorem normalizedCenter_nonneg_of_inVertexCone_right {a y : ℝ} {z : ℂ}
    (hcone : InVertexCone (-a : ℂ) (a : ℂ) z (normalizedCircleCenter y))
    (hz : 0 < z.im) : 0 ≤ y := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := hcone
  have him := congrArg Complex.im hcenter
  simp [normalizedCircleCenter] at him
  nlinarith [mul_nonneg hβ hz.le]

/-- The right-endpoint version below the oriented edge. -/
theorem normalizedCenter_nonpos_of_inVertexCone_right {a y : ℝ} {z : ℂ}
    (hcone : InVertexCone (-a : ℂ) (a : ℂ) z (normalizedCircleCenter y))
    (hz : z.im < 0) : y ≤ 0 := by
  obtain ⟨α, β, hα, hβ, hcenter⟩ := hcone
  have him := congrArg Complex.im hcenter
  simp [normalizedCircleCenter] at him
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hz.le]

/-- Dahlberg regularity at the left endpoint of a normalized edge places its
circumcentre parameter on the interior side when the preceding vertex is
above the edge. -/
theorem normalizedCircumcenterParameter_nonneg_of_regular {a : ℝ} (ha : a ≠ 0)
    {z O : ℂ} {R : ℝ} (hz : 0 < z.im)
    (hcircle : CircumcircleR2 z (-a : ℂ) (a : ℂ) O R)
    (hcone : InVertexCone z (-a : ℂ) (a : ℂ) O) :
    0 ≤ normalizedCircumcenterParameter a z := by
  have hO := eq_normalizedCircleCenter_of_equidistant ha hz.ne'
    (hcircle.2.2.1.trans hcircle.2.2.2.symm)
    (hcircle.2.1.trans hcircle.2.2.2.symm)
  rw [hO] at hcone
  exact normalizedCenter_nonneg_of_inVertexCone hcone hz

/-- The corresponding regularity statement below the oriented edge. -/
theorem normalizedCircumcenterParameter_nonpos_of_regular {a : ℝ} (ha : a ≠ 0)
    {z O : ℂ} {R : ℝ} (hz : z.im < 0)
    (hcircle : CircumcircleR2 z (-a : ℂ) (a : ℂ) O R)
    (hcone : InVertexCone z (-a : ℂ) (a : ℂ) O) :
    normalizedCircumcenterParameter a z ≤ 0 := by
  have hO := eq_normalizedCircleCenter_of_equidistant ha hz.ne
    (hcircle.2.2.1.trans hcircle.2.2.2.symm)
    (hcircle.2.1.trans hcircle.2.2.2.symm)
  rw [hO] at hcone
  exact normalizedCenter_nonpos_of_inVertexCone hcone hz

/-- Dahlberg regularity at the right endpoint of a normalized edge gives the
same centre-side condition. -/
theorem normalizedCircumcenterParameter_nonneg_of_regular_right {a : ℝ} (ha : a ≠ 0)
    {z O : ℂ} {R : ℝ} (hz : 0 < z.im)
    (hcircle : CircumcircleR2 (-a : ℂ) (a : ℂ) z O R)
    (hcone : InVertexCone (-a : ℂ) (a : ℂ) z O) :
    0 ≤ normalizedCircumcenterParameter a z := by
  have hO := eq_normalizedCircleCenter_of_equidistant ha hz.ne'
    (hcircle.2.1.trans hcircle.2.2.1.symm)
    (hcircle.2.2.2.trans hcircle.2.2.1.symm)
  rw [hO] at hcone
  exact normalizedCenter_nonneg_of_inVertexCone_right hcone hz

/-- The right-endpoint regularity statement below the oriented edge. -/
theorem normalizedCircumcenterParameter_nonpos_of_regular_right {a : ℝ} (ha : a ≠ 0)
    {z O : ℂ} {R : ℝ} (hz : z.im < 0)
    (hcircle : CircumcircleR2 (-a : ℂ) (a : ℂ) z O R)
    (hcone : InVertexCone (-a : ℂ) (a : ℂ) z O) :
    normalizedCircumcenterParameter a z ≤ 0 := by
  have hO := eq_normalizedCircleCenter_of_equidistant ha hz.ne
    (hcircle.2.1.trans hcircle.2.2.1.symm)
    (hcircle.2.2.2.trans hcircle.2.2.1.symm)
  rw [hO] at hcone
  exact normalizedCenter_nonpos_of_inVertexCone_right hcone hz

/-- Dahlberg regularity at the left endpoint of an arbitrary oriented edge
places the canonical circumcentre parameter on the interior side. -/
theorem edgeCircumcenterParameter_nonneg_of_regular {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hcircle : CircumcircleR2 C A B O R) (hcone : InVertexCone C A B O) :
    0 ≤ edgeCircumcenterParameter A B C := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hcone' := inVertexCone_edgeCoordinates A B C A B O hcone
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcone'
  have hy := normalizedCircumcenterParameter_nonneg_of_regular
    (chordHalfLength_pos hAB).ne' hz hcircle' hcone'
  simpa [edgeCircumcenterParameter] using hy

/-- Negative Dahlberg regularity at the left endpoint of an arbitrary
oriented edge places the canonical circumcentre parameter on the opposite
side. -/
theorem edgeCircumcenterParameter_nonpos_of_regular {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C < 0)
    (hcircle : CircumcircleR2 C A B O R) (hcone : InVertexCone C A B O) :
    edgeCircumcenterParameter A B C ≤ 0 := by
  have hz := (crossR2_neg_iff_edgeCoordinates_im_neg hAB C).mp hcross
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hcone' := inVertexCone_edgeCoordinates A B C A B O hcone
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcone'
  have hy := normalizedCircumcenterParameter_nonpos_of_regular
    (chordHalfLength_pos hAB).ne' hz hcircle' hcone'
  simpa [edgeCircumcenterParameter] using hy

/-- Right-endpoint regularity for an arbitrary oriented edge also places the
canonical circumcentre parameter on the interior side. -/
theorem edgeCircumcenterParameter_nonneg_of_regular_right {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hcircle : CircumcircleR2 A B C O R) (hcone : InVertexCone A B C O) :
    0 ≤ edgeCircumcenterParameter A B C := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hcone' := inVertexCone_edgeCoordinates A B A B C O hcone
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcone'
  have hy := normalizedCircumcenterParameter_nonneg_of_regular_right
    (chordHalfLength_pos hAB).ne' hz hcircle' hcone'
  simpa [edgeCircumcenterParameter] using hy

/-- Right-endpoint regularity below the oriented edge. -/
theorem edgeCircumcenterParameter_nonpos_of_regular_right {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C < 0)
    (hcircle : CircumcircleR2 A B C O R) (hcone : InVertexCone A B C O) :
    edgeCircumcenterParameter A B C ≤ 0 := by
  have hz := (crossR2_neg_iff_edgeCoordinates_im_neg hAB C).mp hcross
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hcone' := inVertexCone_edgeCoordinates A B A B C O hcone
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcone'
  have hy := normalizedCircumcenterParameter_nonpos_of_regular_right
    (chordHalfLength_pos hAB).ne' hz hcircle' hcone'
  simpa [edgeCircumcenterParameter] using hy

/-- A nondegenerate normalized chord gives every member of the coaxial family
a positive radius. -/
theorem normalizedCircleRadius_pos {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    0 < normalizedCircleRadius a y := by
  rw [normalizedCircleRadius, Real.sqrt_pos]
  positivity

/-- Positive reciprocal radius for a nondegenerate chord. -/
theorem normalizedCircleCurvature_pos {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    0 < normalizedCircleCurvature a y := by
  unfold normalizedCircleCurvature
  exact one_div_pos.mpr (normalizedCircleRadius_pos ha y)

/-- Metric form of the endpoint incidence relation. -/
theorem dist_normalizedCircleCenter_right (a y : ℝ) :
    dist (normalizedCircleCenter y) (a : ℂ) = normalizedCircleRadius a y := by
  rw [dist_eq_norm, Complex.norm_eq_sqrt_sq_add_sq]
  unfold normalizedCircleCenter normalizedCircleRadius
  congr 1
  simp

/-- The left endpoint has the same incidence relation. -/
theorem dist_normalizedCircleCenter_left (a y : ℝ) :
    dist (normalizedCircleCenter y) (-a : ℂ) = normalizedCircleRadius a y := by
  simpa [normalizedCircleRadius] using dist_normalizedCircleCenter_right (-a) y

/-- Any normalized circumcircle through a noncollinear triple has the canonical
coaxial radius. -/
theorem normalizedCircumcircle_radius_eq {a R : ℝ} (ha : a ≠ 0) {z O : ℂ}
    (hz : z.im ≠ 0)
    (hcircle : CircumcircleR2 z (-a : ℂ) (a : ℂ) O R) :
    R = normalizedCircleRadius a (normalizedCircumcenterParameter a z) := by
  have hO := eq_normalizedCircleCenter_of_equidistant ha hz
    (hcircle.2.2.1.trans hcircle.2.2.2.symm)
    (hcircle.2.1.trans hcircle.2.2.2.symm)
  rw [← hcircle.2.2.2, hO, dist_normalizedCircleCenter_right]

/-- A nondegenerate normalized triple has the advertised circumcircle. -/
theorem circumcircleR2_normalized_parameter {a : ℝ} (ha : a ≠ 0) {z : ℂ}
    (hz : z.im ≠ 0) :
    CircumcircleR2 (-a : ℂ) (a : ℂ) z
      (normalizedCircleCenter (normalizedCircumcenterParameter a z))
      (normalizedCircleRadius a (normalizedCircumcenterParameter a z)) := by
  refine ⟨normalizedCircleRadius_pos ha _, ?_, ?_, ?_⟩
  · exact dist_normalizedCircleCenter_left _ _
  · exact dist_normalizedCircleCenter_right _ _
  · exact dist_eq_of_circlePowerR2_eq_zero (Real.sqrt_nonneg _)
      (circlePowerR2_normalized_parameter hz)

/-- Every transported member of the coaxial family passes through the two
transported chord endpoints. -/
theorem transportedCircle_incident {u : ℂ} (hu : ‖u‖ = 1) (w : ℂ) (a y : ℝ) :
    dist (transportedCircleCenter u w y) (transportedChordLeft u w a) =
        normalizedCircleRadius a y ∧
      dist (transportedCircleCenter u w y) (transportedChordRight u w a) =
        normalizedCircleRadius a y := by
  constructor
  · unfold transportedCircleCenter transportedChordLeft
    rw [dist_directIsometryR2 hu, dist_normalizedCircleCenter_left]
  · unfold transportedCircleCenter transportedChordRight
    rw [dist_directIsometryR2 hu, dist_normalizedCircleCenter_right]

/-- Every canonical edge circle passes through the original endpoints. -/
theorem edgeCircle_incident {A B : ℂ} (hAB : A ≠ B) (y : ℝ) :
    dist (edgeCircleCenter A B y) A = normalizedCircleRadius (chordHalfLength A B) y ∧
      dist (edgeCircleCenter A B y) B = normalizedCircleRadius (chordHalfLength A B) y := by
  have hi := transportedCircle_incident (norm_chordUnit hAB) (chordMidpoint A B)
    (chordHalfLength A B) y
  have he := canonicalChord_endpoints hAB
  unfold edgeCircleCenter
  simpa only [he.1, he.2] using hi

/-- The third point has zero power with respect to its canonical edge circle. -/
theorem circlePowerR2_edge_parameter {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    circlePowerR2 (edgeCircleCenter A B (edgeCircumcenterParameter A B C)) C
      (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) = 0 := by
  have hz := edgeCoordinates_im_ne_zero hAB hcross
  have hp := circlePowerR2_directIsometry (norm_chordUnit hAB) (chordMidpoint A B)
    (normalizedCircleCenter (edgeCircumcenterParameter A B C)) (edgeCoordinates A B C)
    (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C))
  have hzero := circlePowerR2_normalized_parameter
    (a := chordHalfLength A B) hz
  change circlePowerR2 (normalizedCircleCenter (edgeCircumcenterParameter A B C))
    (edgeCoordinates A B C)
    (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) = 0 at hzero
  rw [directIsometryR2_edgeCoordinates hAB, hzero] at hp
  simpa [edgeCircleCenter, transportedCircleCenter] using hp

/-- Every noncollinear Euclidean triple has the canonical circumcircle obtained
from its edge coordinates. -/
theorem circumcircleR2_edge_parameter {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    CircumcircleR2 A B C
      (edgeCircleCenter A B (edgeCircumcenterParameter A B C))
      (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) := by
  have hi := edgeCircle_incident hAB (edgeCircumcenterParameter A B C)
  have ha := chordHalfLength_pos hAB
  refine ⟨normalizedCircleRadius_pos ha.ne' _, hi.1, hi.2, ?_⟩
  exact dist_eq_of_circlePowerR2_eq_zero (Real.sqrt_nonneg _)
    (circlePowerR2_edge_parameter hAB hcross)

/-- Any Euclidean circumcircle through a noncollinear edge triple has the same
radius as the canonical edge-parameter circle. -/
theorem circumcircleR2_edge_radius_eq {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hcircle : CircumcircleR2 C A B O R) :
    R = normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hz := edgeCoordinates_im_ne_zero hAB hcross
  have hR := normalizedCircumcircle_radius_eq (chordHalfLength_pos hAB).ne' hz hcircle'
  simpa [edgeCircumcenterParameter] using hR

/-- A Euclidean circle through a collinear triple over a nondegenerate edge
forces the third point to be one of the edge endpoints. -/
theorem collinear_circumcircle_third_eq_endpoint {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C = 0)
    (hcircle : CircumcircleR2 A B C O R) :
    C = A ∨ C = B := by
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have him : (edgeCoordinates A B C).im = 0 := by
    have harea := crossR2_edgeCoordinates hAB C
    have hzero : 2 * chordHalfLength A B * (edgeCoordinates A B C).im = 0 := by
      simpa [crossR2_normalized, hcross] using harea
    have hcoef : 2 * chordHalfLength A B ≠ 0 := by
      nlinarith [chordHalfLength_pos hAB]
    exact (mul_eq_zero.mp hzero).resolve_left hcoef
  have hthird :=
    normalized_collinear_circumcircle_third_eq_endpoint
      (chordHalfLength_pos hAB).ne' him hcircle'
  rcases hthird with hleft | hright
  · left
    have himage :=
      congrArg (directIsometryR2 (chordUnit A B) (chordMidpoint A B)) hleft
    rw [directIsometryR2_edgeCoordinates hAB C] at himage
    exact himage.trans (canonicalChord_endpoints hAB).1
  · right
    have himage :=
      congrArg (directIsometryR2 (chordUnit A B) (chordMidpoint A B)) hright
    rw [directIsometryR2_edgeCoordinates hAB C] at himage
    exact himage.trans (canonicalChord_endpoints hAB).2

/-- Any Euclidean circumcircle through a noncollinear edge triple has the
canonical edge centre. -/
theorem circumcircleR2_edge_center_eq {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hcircle : CircumcircleR2 A B C O R) :
    O = edgeCircleCenter A B (edgeCircumcenterParameter A B C) := by
  have hcircle' := circumcircleR2_edgeCoordinates (E₁ := A) (E₂ := B) hAB hcircle
  rw [(edgeCoordinates_endpoints hAB).1, (edgeCoordinates_endpoints hAB).2] at hcircle'
  have hz := edgeCoordinates_im_ne_zero hAB hcross
  have hO := eq_normalizedCircleCenter_of_equidistant (chordHalfLength_pos hAB).ne' hz
    (hcircle'.2.1.trans hcircle'.2.2.1.symm)
    (hcircle'.2.2.2.trans hcircle'.2.2.1.symm)
  have hOimage :=
    congrArg (directIsometryR2 (chordUnit A B) (chordMidpoint A B)) hO
  rw [directIsometryR2_edgeCoordinates hAB O] at hOimage
  simpa [edgeCircleCenter, transportedCircleCenter, edgeCircumcenterParameter] using hOimage

/-- Right-endpoint order version of the canonical edge-radius uniqueness
statement. -/
theorem circumcircleR2_edge_radius_eq_right {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hcircle : CircumcircleR2 A B C O R) :
    R = normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  exact circumcircleR2_edge_radius_eq hAB hcross
    ⟨hcircle.1, hcircle.2.2.2, hcircle.2.1, hcircle.2.2.1⟩

/-- A noncollinear triple has the canonical edge centre and radius. -/
theorem circumcircleR2_edge_center_radius_eq {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hcircle : CircumcircleR2 A B C O R) :
    O = edgeCircleCenter A B (edgeCircumcenterParameter A B C) ∧
      R = normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  exact ⟨circumcircleR2_edge_center_eq hAB hcross hcircle,
    circumcircleR2_edge_radius_eq_right hAB hcross hcircle⟩

/-- Two Euclidean circumcircles through the same noncollinear triple have the
same centre and radius. -/
theorem circumcircleR2_unique_of_noncollinear {A B C O₁ O₂ : ℂ} {R₁ R₂ : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (h₁ : CircumcircleR2 A B C O₁ R₁) (h₂ : CircumcircleR2 A B C O₂ R₂) :
    O₁ = O₂ ∧ R₁ = R₂ := by
  have hcanon₁ := circumcircleR2_edge_center_radius_eq hAB hcross h₁
  have hcanon₂ := circumcircleR2_edge_center_radius_eq hAB hcross h₂
  exact ⟨hcanon₁.1.trans hcanon₂.1.symm, hcanon₁.2.trans hcanon₂.2.symm⟩

/-- Circumcircle uniqueness is insensitive to cyclic reordering of the same
noncollinear triple. -/
theorem circumcircleR2_unique_of_cyclic_reorder {A B C O₁ O₂ : ℂ} {R₁ R₂ : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (h₁ : CircumcircleR2 A B C O₁ R₁) (h₂ : CircumcircleR2 B C A O₂ R₂) :
    O₁ = O₂ ∧ R₁ = R₂ := by
  have h₂' : CircumcircleR2 A B C O₂ R₂ :=
    ⟨h₂.1, h₂.2.2.2, h₂.2.1, h₂.2.2.1⟩
  exact circumcircleR2_unique_of_noncollinear hAB hcross h₁ h₂'

/-- If the centre of a circumcircle is a convex combination of its three
vertices, then any closed disk containing the three vertices has radius at
least the circumradius.

This is the algebraic Euclidean core used when the regularity/convexity
hypotheses put the curvature-circle centre inside the relevant triangle: the
weighted variance identity gives
`R² + dist Δ O²` as the weighted average of the squared distances from `Δ` to
the three vertices. -/
theorem circumcircleR2_radius_le_of_center_convexCombo_three
    {A B C O Δ : ℂ} {R S α β γ : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hsum : α + β + γ = 1)
    (hO : O = (α : ℂ) * A + (β : ℂ) * B + (γ : ℂ) * C)
    (hS : 0 ≤ S)
    (hA : InClosedDiskR2 Δ S A) (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S := by
  have hγeq : γ = 1 - α - β := by linarith
  have hR : 0 ≤ R := hcircle.1.le
  have hOre := congrArg Complex.re hO
  have hOim := congrArg Complex.im hO
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hOre
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul] at hOim
  ring_nf at hOre hOim
  have hAO : (A.re - O.re) ^ 2 + (A.im - O.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simp only [Complex.sub_re, Complex.sub_im] at h
    have hre : (O.re - A.re) ^ 2 = (A.re - O.re) ^ 2 := by ring
    have him : (O.im - A.im) ^ 2 = (A.im - O.im) ^ 2 := by ring
    nlinarith
  have hBO : (B.re - O.re) ^ 2 + (B.im - O.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simp only [Complex.sub_re, Complex.sub_im] at h
    have hre : (O.re - B.re) ^ 2 = (B.re - O.re) ^ 2 := by ring
    have him : (O.im - B.im) ^ 2 = (B.im - O.im) ^ 2 := by ring
    nlinarith
  have hCO : (C.re - O.re) ^ 2 + (C.im - O.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.2
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simp only [Complex.sub_re, Complex.sub_im] at h
    have hre : (O.re - C.re) ^ 2 = (C.re - O.re) ^ 2 := by ring
    have him : (O.im - C.im) ^ 2 = (C.im - O.im) ^ 2 := by ring
    nlinarith
  have hAΔ : (A.re - Δ.re) ^ 2 + (A.im - Δ.im) ^ 2 ≤ S ^ 2 := by
    have hsq := (sq_le_sq₀ dist_nonneg hS).mpr hA
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at hsq
    simp only [Complex.sub_re, Complex.sub_im] at hsq
    have hre : (Δ.re - A.re) ^ 2 = (A.re - Δ.re) ^ 2 := by ring
    have him : (Δ.im - A.im) ^ 2 = (A.im - Δ.im) ^ 2 := by ring
    nlinarith
  have hBΔ : (B.re - Δ.re) ^ 2 + (B.im - Δ.im) ^ 2 ≤ S ^ 2 := by
    have hsq := (sq_le_sq₀ dist_nonneg hS).mpr hB
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at hsq
    simp only [Complex.sub_re, Complex.sub_im] at hsq
    have hre : (Δ.re - B.re) ^ 2 = (B.re - Δ.re) ^ 2 := by ring
    have him : (Δ.im - B.im) ^ 2 = (B.im - Δ.im) ^ 2 := by ring
    nlinarith
  have hCΔ : (C.re - Δ.re) ^ 2 + (C.im - Δ.im) ^ 2 ≤ S ^ 2 := by
    have hsq := (sq_le_sq₀ dist_nonneg hS).mpr hC
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at hsq
    simp only [Complex.sub_re, Complex.sub_im] at hsq
    have hre : (Δ.re - C.re) ^ 2 = (C.re - Δ.re) ^ 2 := by ring
    have him : (Δ.im - C.im) ^ 2 = (C.im - Δ.im) ^ 2 := by ring
    nlinarith
  have hweighted_le :
      α * ((A.re - Δ.re) ^ 2 + (A.im - Δ.im) ^ 2) +
          β * ((B.re - Δ.re) ^ 2 + (B.im - Δ.im) ^ 2) +
          γ * ((C.re - Δ.re) ^ 2 + (C.im - Δ.im) ^ 2) ≤ S ^ 2 := by
    have hαA :
        α * ((A.re - Δ.re) ^ 2 + (A.im - Δ.im) ^ 2) ≤ α * S ^ 2 :=
      mul_le_mul_of_nonneg_left hAΔ hα
    have hβB :
        β * ((B.re - Δ.re) ^ 2 + (B.im - Δ.im) ^ 2) ≤ β * S ^ 2 :=
      mul_le_mul_of_nonneg_left hBΔ hβ
    have hγC :
        γ * ((C.re - Δ.re) ^ 2 + (C.im - Δ.im) ^ 2) ≤ γ * S ^ 2 :=
      mul_le_mul_of_nonneg_left hCΔ hγ
    calc
      α * ((A.re - Δ.re) ^ 2 + (A.im - Δ.im) ^ 2) +
          β * ((B.re - Δ.re) ^ 2 + (B.im - Δ.im) ^ 2) +
          γ * ((C.re - Δ.re) ^ 2 + (C.im - Δ.im) ^ 2)
          ≤ α * S ^ 2 + β * S ^ 2 + γ * S ^ 2 := by
            exact add_le_add (add_le_add hαA hβB) hγC
      _ = S ^ 2 := by
        rw [hγeq]
        ring
  have hvariance :
      α * ((A.re - Δ.re) ^ 2 + (A.im - Δ.im) ^ 2) +
          β * ((B.re - Δ.re) ^ 2 + (B.im - Δ.im) ^ 2) +
          γ * ((C.re - Δ.re) ^ 2 + (C.im - Δ.im) ^ 2) =
        R ^ 2 + ((O.re - Δ.re) ^ 2 + (O.im - Δ.im) ^ 2) := by
    have hRweighted : R ^ 2 = α * R ^ 2 + β * R ^ 2 + γ * R ^ 2 := by
      rw [hγeq]
      ring
    have hRweighted' :
        R ^ 2 =
          α * ((A.re - O.re) ^ 2 + (A.im - O.im) ^ 2) +
          β * ((B.re - O.re) ^ 2 + (B.im - O.im) ^ 2) +
          γ * ((C.re - O.re) ^ 2 + (C.im - O.im) ^ 2) := by
      rw [hRweighted, hAO, hBO, hCO]
    have hreVariance :
        α * (A.re - Δ.re) ^ 2 + β * (B.re - Δ.re) ^ 2 +
            γ * (C.re - Δ.re) ^ 2 =
          α * (A.re - O.re) ^ 2 + β * (B.re - O.re) ^ 2 +
              γ * (C.re - O.re) ^ 2 + (O.re - Δ.re) ^ 2 := by
      rw [hOre]
      rw [hγeq]
      ring
    have himVariance :
        α * (A.im - Δ.im) ^ 2 + β * (B.im - Δ.im) ^ 2 +
            γ * (C.im - Δ.im) ^ 2 =
          α * (A.im - O.im) ^ 2 + β * (B.im - O.im) ^ 2 +
              γ * (C.im - O.im) ^ 2 + (O.im - Δ.im) ^ 2 := by
      rw [hOim]
      rw [hγeq]
      ring
    rw [hRweighted']
    linear_combination hreVariance + himVariance
  have hRsq : R ^ 2 ≤ S ^ 2 := by
    have hOD : 0 ≤ (O.re - Δ.re) ^ 2 + (O.im - Δ.im) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsum_le : R ^ 2 + ((O.re - Δ.re) ^ 2 + (O.im - Δ.im) ^ 2) ≤ S ^ 2 := by
      rw [← hvariance]
      exact hweighted_le
    exact le_trans (le_add_of_nonneg_right hOD) hsum_le
  exact (sq_le_sq₀ hR hS).mp hRsq

/-- Normalized version of
`circumcircleR2_radius_le_of_center_convexCombo_three`.

If a member of the normalized coaxial family has its centre in the convex hull
of the two chord endpoints and a third point on the circle, then any disk
containing those three points has radius at least the normalized circle
radius. -/
theorem normalizedCircleRadius_le_of_center_convexCombo_three
    {a y S α β γ : ℝ} {z Δ : ℂ}
    (ha : a ≠ 0)
    (hz : circlePowerR2 (normalizedCircleCenter y) z
      (normalizedCircleRadius a y) = 0)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hsum : α + β + γ = 1)
    (hcenter :
      normalizedCircleCenter y = (α : ℂ) * (-a : ℂ) +
        (β : ℂ) * (a : ℂ) + (γ : ℂ) * z)
    (hS : 0 ≤ S)
    (hleft : InClosedDiskR2 Δ S (-a : ℂ))
    (hright : InClosedDiskR2 Δ S (a : ℂ))
    (hzmem : InClosedDiskR2 Δ S z) :
    normalizedCircleRadius a y ≤ S := by
  have hcircle :
      CircumcircleR2 (-a : ℂ) (a : ℂ) z
        (normalizedCircleCenter y) (normalizedCircleRadius a y) := by
    refine ⟨normalizedCircleRadius_pos ha y, ?_, ?_, ?_⟩
    · exact dist_normalizedCircleCenter_left a y
    · exact dist_normalizedCircleCenter_right a y
    · exact dist_eq_of_circlePowerR2_eq_zero (Real.sqrt_nonneg _) hz
  exact circumcircleR2_radius_le_of_center_convexCombo_three
    hcircle hα hβ hγ hsum hcenter hS hleft hright hzmem

/-- Closed Euclidean triangle membership in explicit barycentric
coordinates. -/
def InClosedTriangleR2 (A B C P : ℂ) : Prop :=
  ∃ α β γ : ℝ,
    0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      P = (α : ℂ) * A + (β : ℂ) * B + (γ : ℂ) * C

/-- A circumcircle whose centre lies in the closed triangle has radius no
larger than any disk containing the three triangle vertices. -/
theorem circumcircleR2_radius_le_of_center_mem_closedTriangle
    {A B C O Δ : ℂ} {R S : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hcenter : InClosedTriangleR2 A B C O)
    (hS : 0 ≤ S)
    (hA : InClosedDiskR2 Δ S A) (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S := by
  rcases hcenter with ⟨α, β, γ, hα, hβ, hγ, hsum, hO⟩
  exact circumcircleR2_radius_le_of_center_convexCombo_three
    hcircle hα hβ hγ hsum hO hS hA hB hC

/-- Explicit vertex-cone coefficients with sum at most one put the point in
the closed triangle. -/
theorem inClosedTriangleR2_of_vertexCone_coeff_sum_le_one
    {A B C O : ℂ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hαγ : α + γ ≤ 1)
    (hcenter : O - B = (α : ℂ) * (A - B) + (γ : ℂ) * (C - B)) :
    InClosedTriangleR2 A B C O := by
  have hβ : 0 ≤ 1 - α - γ := by linarith
  have hsum : α + (1 - α - γ) + γ = 1 := by ring
  have hO : O = (α : ℂ) * A + ((1 - α - γ : ℝ) : ℂ) * B + (γ : ℂ) * C := by
    have hβcast : ((1 - α - γ : ℝ) : ℂ) = 1 - (α : ℂ) - (γ : ℂ) := by
      norm_num
    calc
      O = O - B + B := by abel
      _ = (α : ℂ) * A + ((1 - α - γ : ℝ) : ℂ) * B + (γ : ℂ) * C := by
        rw [hcenter, hβcast]
        ring
  exact ⟨α, 1 - α - γ, γ, hα, hβ, hγ, hsum, hO⟩

/-- If every vertex-cone representation of `O` has coefficient sum at most
one, then the bundled vertex-cone condition puts `O` in the closed triangle. -/
theorem inClosedTriangleR2_of_inVertexCone_coeff_sum_le_one
    {A B C O : ℂ}
    (hcone : InVertexCone A B C O)
    (hsum_le :
      ∀ {α γ : ℝ}, 0 ≤ α → 0 ≤ γ →
        O - B = (α : ℂ) * (A - B) + (γ : ℂ) * (C - B) →
        α + γ ≤ 1) :
    InClosedTriangleR2 A B C O := by
  rcases hcone with ⟨α, γ, hα, hγ, hcenter⟩
  exact inClosedTriangleR2_of_vertexCone_coeff_sum_le_one hα hγ
    (hsum_le hα hγ hcenter) hcenter

/-- The bundled `InVertexCone` condition is equivalently a barycentric
formula where the two outer coefficients are nonnegative and the three
coefficients sum to one.  The middle coefficient need not be nonnegative;
that extra condition is exactly the closed-triangle case. -/
theorem exists_barycentric_center_of_inVertexCone {A B C O : ℂ}
    (hcone : InVertexCone A B C O) :
    ∃ α β γ : ℝ,
      0 ≤ α ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
        O = (α : ℂ) * A + (β : ℂ) * B + (γ : ℂ) * C := by
  rcases hcone with ⟨α, γ, hα, hγ, hcenter⟩
  refine ⟨α, 1 - α - γ, γ, hα, hγ, by ring, ?_⟩
  have hβcast : ((1 - α - γ : ℝ) : ℂ) = 1 - (α : ℂ) - (γ : ℂ) := by
    norm_num
  calc
    O = O - B + B := by abel
    _ = (α : ℂ) * A + ((1 - α - γ : ℝ) : ℂ) * B + (γ : ℂ) * C := by
      rw [hcenter, hβcast]
      ring

/-- Vertex-cone coefficient form of the circumradius lower bound.

If the circumcentre is written as
`O - B = α(A-B) + γ(C-B)` with `α, γ ≥ 0` and `α + γ ≤ 1`, then the centre is
actually in the closed triangle `ABC`.  Therefore any closed disk containing
the three vertices has radius at least the circumradius. -/
theorem circumcircleR2_radius_le_of_center_vertexCone_coeff_sum_le_one
    {A B C O Δ : ℂ} {R S α γ : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hαγ : α + γ ≤ 1)
    (hcenter : O - B = (α : ℂ) * (A - B) + (γ : ℂ) * (C - B))
    (hS : 0 ≤ S)
    (hA : InClosedDiskR2 Δ S A) (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S := by
  exact circumcircleR2_radius_le_of_center_mem_closedTriangle hcircle
    (inClosedTriangleR2_of_vertexCone_coeff_sum_le_one hα hγ hαγ hcenter)
    hS hA hB hC

/-- Vertex-cone form of the circumradius lower bound using the bundled
`InVertexCone` witness plus an explicit bound on the chosen coefficients. -/
theorem circumcircleR2_radius_le_of_inVertexCone_coeff_sum_le_one
    {A B C O Δ : ℂ} {R S α γ : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hαγ : α + γ ≤ 1)
    (hcenter : O - B = (α : ℂ) * (A - B) + (γ : ℂ) * (C - B))
    (_hcone : InVertexCone A B C O)
    (hS : 0 ≤ S)
    (hA : InClosedDiskR2 Δ S A) (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S :=
  circumcircleR2_radius_le_of_center_vertexCone_coeff_sum_le_one
    hcircle hα hγ hαγ hcenter hS hA hB hC

/-- Bundled vertex-cone form of the circumradius lower bound.  The additional
side condition is exactly that the vertex-cone centre lies in the closed
triangle rather than beyond the opposite side. -/
theorem circumcircleR2_radius_le_of_inVertexCone_closedTriangle
    {A B C O Δ : ℂ} {R S : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hcone : InVertexCone A B C O)
    (hsum_le :
      ∀ {α γ : ℝ}, 0 ≤ α → 0 ≤ γ →
        O - B = (α : ℂ) * (A - B) + (γ : ℂ) * (C - B) →
        α + γ ≤ 1)
    (hS : 0 ≤ S)
    (hA : InClosedDiskR2 Δ S A) (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S := by
  exact circumcircleR2_radius_le_of_center_mem_closedTriangle hcircle
    (inClosedTriangleR2_of_inVertexCone_coeff_sum_le_one hcone hsum_le)
    hS hA hB hC

/-- Full radius inequality in Dahlberg's Lemma 10.

Let `A` be the distinguished triangle vertex.  If the circumcentre lies in
the closed cone at `A`, then every closed disk containing `A`, `B`, and `C`
and having `A` on its boundary has radius at least the circumradius.  No
second triangle vertex is assumed to lie on the disk boundary. -/
theorem circumcircleR2_radius_le_of_inVertexCone_of_boundary
    {A B C O Δ : ℂ} {R S : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hcone : InVertexCone B A C O)
    (hS : 0 ≤ S)
    (hA : dist Δ A = S)
    (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C) :
    R ≤ S := by
  rcases hcone with ⟨α, β, hα, hβ, hcenter⟩
  have hcenter_re := congrArg Complex.re hcenter
  have hcenter_im := congrArg Complex.im hcenter
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hcenter_re hcenter_im
  have hOA : (O.re - A.re) ^ 2 + (O.im - A.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOB : (O.re - B.re) ^ 2 + (O.im - B.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOC : (O.re - C.re) ^ 2 + (O.im - C.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.2
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔA : (Δ.re - A.re) ^ 2 + (Δ.im - A.im) ^ 2 = S ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hA
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔB : (Δ.re - B.re) ^ 2 + (Δ.im - B.im) ^ 2 ≤ S ^ 2 := by
    have h := (sq_le_sq₀ dist_nonneg hS).mpr (Metric.mem_closedBall'.mp hB)
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔC : (Δ.re - C.re) ^ 2 + (Δ.im - C.im) ^ 2 ≤ S ^ 2 := by
    have h := (sq_le_sq₀ dist_nonneg hS).mpr (Metric.mem_closedBall'.mp hC)
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOuB :
      (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 =
        2 * ((O.re - A.re) * (B.re - A.re) +
          (O.im - A.im) * (B.im - A.im)) := by
    nlinarith only [hOA, hOB]
  have hOuC :
      (C.re - A.re) ^ 2 + (C.im - A.im) ^ 2 =
        2 * ((O.re - A.re) * (C.re - A.re) +
          (O.im - A.im) * (C.im - A.im)) := by
    nlinarith only [hOA, hOC]
  have hΔuB :
      (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 ≤
        2 * ((Δ.re - A.re) * (B.re - A.re) +
          (Δ.im - A.im) * (B.im - A.im)) := by
    nlinarith only [hΔA, hΔB]
  have hΔuC :
      (C.re - A.re) ^ 2 + (C.im - A.im) ^ 2 ≤
        2 * ((Δ.re - A.re) * (C.re - A.re) +
          (Δ.im - A.im) * (C.im - A.im)) := by
    nlinarith only [hΔA, hΔC]
  have hαB := mul_le_mul_of_nonneg_left hΔuB hα
  have hβC := mul_le_mul_of_nonneg_left hΔuC hβ
  have hcenter_im' :
      O.im - A.im = α * (B.im - A.im) + β * (C.im - A.im) := by
    simpa only [add_zero] using hcenter_im
  have hweightedCirc :
      α * ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) +
          β * ((C.re - A.re) ^ 2 + (C.im - A.im) ^ 2) =
        2 * R ^ 2 := by
    rw [hOuB, hOuC]
    calc
      α * (2 * ((O.re - A.re) * (B.re - A.re) +
            (O.im - A.im) * (B.im - A.im))) +
          β * (2 * ((O.re - A.re) * (C.re - A.re) +
            (O.im - A.im) * (C.im - A.im))) =
          2 * ((O.re - A.re) *
              (α * (B.re - A.re) + β * (C.re - A.re)) +
            (O.im - A.im) *
              (α * (B.im - A.im) + β * (C.im - A.im))) := by ring
      _ = 2 * ((O.re - A.re) ^ 2 + (O.im - A.im) ^ 2) := by
        rw [← hcenter_re, ← hcenter_im']
        ring
      _ = 2 * R ^ 2 := by rw [hOA]
  have hweightedDisk :
      α * (2 * ((Δ.re - A.re) * (B.re - A.re) +
            (Δ.im - A.im) * (B.im - A.im))) +
          β * (2 * ((Δ.re - A.re) * (C.re - A.re) +
            (Δ.im - A.im) * (C.im - A.im))) =
        2 * ((Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im)) := by
    rw [hcenter_re, hcenter_im']
    ring
  have hweighted := add_le_add hαB hβC
  rw [hweightedCirc, hweightedDisk] at hweighted
  have hRdot :
      R ^ 2 ≤
        (Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im) := by
    nlinarith only [hweighted]
  have hcauchy :
      ((Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im)) ^ 2 ≤
        ((Δ.re - A.re) ^ 2 + (Δ.im - A.im) ^ 2) *
          ((O.re - A.re) ^ 2 + (O.im - A.im) ^ 2) := by
    nlinarith only [sq_nonneg
      ((Δ.re - A.re) * (O.im - A.im) -
        (Δ.im - A.im) * (O.re - A.re))]
  have hR2nonneg : 0 ≤ R ^ 2 := sq_nonneg R
  have hdot_nonneg :
      0 ≤ (Δ.re - A.re) * (O.re - A.re) +
        (Δ.im - A.im) * (O.im - A.im) :=
    hR2nonneg.trans hRdot
  have hsq_lower :
      (R ^ 2) ^ 2 ≤
        ((Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im)) ^ 2 :=
    (sq_le_sq₀ hR2nonneg hdot_nonneg).mpr hRdot
  have hmul : R ^ 2 * R ^ 2 ≤ S ^ 2 * R ^ 2 := by
    calc
      R ^ 2 * R ^ 2 = (R ^ 2) ^ 2 := by ring
      _ ≤ ((Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im)) ^ 2 := hsq_lower
      _ ≤ ((Δ.re - A.re) ^ 2 + (Δ.im - A.im) ^ 2) *
          ((O.re - A.re) ^ 2 + (O.im - A.im) ^ 2) := hcauchy
      _ = S ^ 2 * R ^ 2 := by rw [hΔA, hOA]
  have hR2pos : 0 < R ^ 2 := sq_pos_of_pos hcircle.1
  have hRsq : R ^ 2 ≤ S ^ 2 :=
    (mul_le_mul_iff_right₀ hR2pos).mp (by simpa [mul_comm] using hmul)
  exact (sq_le_sq₀ hcircle.1.le hS).mp hRsq

/-- Equality case of the radius inequality in Dahlberg's Lemma 10.

Under the same vertex-cone and boundary hypotheses, a containing disk with
the circumradius has the circumcenter as its center. -/
theorem eq_circumcenter_of_inVertexCone_of_boundary_of_radius_eq
    {A B C O Δ : ℂ} {R S : ℝ}
    (hcircle : CircumcircleR2 A B C O R)
    (hcone : InVertexCone B A C O)
    (hS : 0 ≤ S)
    (hA : dist Δ A = S)
    (hB : InClosedDiskR2 Δ S B)
    (hC : InClosedDiskR2 Δ S C)
    (hRS : R = S) :
    Δ = O := by
  rcases hcone with ⟨α, β, hα, hβ, hcenter⟩
  have hcenter_re := congrArg Complex.re hcenter
  have hcenter_im := congrArg Complex.im hcenter
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hcenter_re hcenter_im
  have hcenter_im' :
      O.im - A.im = α * (B.im - A.im) + β * (C.im - A.im) := by
    simpa only [add_zero] using hcenter_im
  have hOA : (O.re - A.re) ^ 2 + (O.im - A.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOB : (O.re - B.re) ^ 2 + (O.im - B.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.1
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOC : (O.re - C.re) ^ 2 + (O.im - C.im) ^ 2 = R ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hcircle.2.2.2
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔA : (Δ.re - A.re) ^ 2 + (Δ.im - A.im) ^ 2 = S ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hA
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔB : (Δ.re - B.re) ^ 2 + (Δ.im - B.im) ^ 2 ≤ S ^ 2 := by
    have h := (sq_le_sq₀ dist_nonneg hS).mpr (Metric.mem_closedBall'.mp hB)
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hΔC : (Δ.re - C.re) ^ 2 + (Δ.im - C.im) ^ 2 ≤ S ^ 2 := by
    have h := (sq_le_sq₀ dist_nonneg hS).mpr (Metric.mem_closedBall'.mp hC)
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply] at h
    simpa only [Complex.sub_re, Complex.sub_im, pow_two] using h
  have hOuB :
      (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 =
        2 * ((O.re - A.re) * (B.re - A.re) +
          (O.im - A.im) * (B.im - A.im)) := by
    nlinarith only [hOA, hOB]
  have hOuC :
      (C.re - A.re) ^ 2 + (C.im - A.im) ^ 2 =
        2 * ((O.re - A.re) * (C.re - A.re) +
          (O.im - A.im) * (C.im - A.im)) := by
    nlinarith only [hOA, hOC]
  have hΔuB :
      (B.re - A.re) ^ 2 + (B.im - A.im) ^ 2 ≤
        2 * ((Δ.re - A.re) * (B.re - A.re) +
          (Δ.im - A.im) * (B.im - A.im)) := by
    nlinarith only [hΔA, hΔB]
  have hΔuC :
      (C.re - A.re) ^ 2 + (C.im - A.im) ^ 2 ≤
        2 * ((Δ.re - A.re) * (C.re - A.re) +
          (Δ.im - A.im) * (C.im - A.im)) := by
    nlinarith only [hΔA, hΔC]
  have hαB := mul_le_mul_of_nonneg_left hΔuB hα
  have hβC := mul_le_mul_of_nonneg_left hΔuC hβ
  have hweightedCirc :
      α * ((B.re - A.re) ^ 2 + (B.im - A.im) ^ 2) +
          β * ((C.re - A.re) ^ 2 + (C.im - A.im) ^ 2) =
        2 * R ^ 2 := by
    rw [hOuB, hOuC]
    calc
      α * (2 * ((O.re - A.re) * (B.re - A.re) +
            (O.im - A.im) * (B.im - A.im))) +
          β * (2 * ((O.re - A.re) * (C.re - A.re) +
            (O.im - A.im) * (C.im - A.im))) =
          2 * ((O.re - A.re) *
              (α * (B.re - A.re) + β * (C.re - A.re)) +
            (O.im - A.im) *
              (α * (B.im - A.im) + β * (C.im - A.im))) := by ring
      _ = 2 * ((O.re - A.re) ^ 2 + (O.im - A.im) ^ 2) := by
        rw [← hcenter_re, ← hcenter_im']
        ring
      _ = 2 * R ^ 2 := by rw [hOA]
  have hweightedDisk :
      α * (2 * ((Δ.re - A.re) * (B.re - A.re) +
            (Δ.im - A.im) * (B.im - A.im))) +
          β * (2 * ((Δ.re - A.re) * (C.re - A.re) +
            (Δ.im - A.im) * (C.im - A.im))) =
        2 * ((Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im)) := by
    rw [hcenter_re, hcenter_im']
    ring
  have hweighted := add_le_add hαB hβC
  rw [hweightedCirc, hweightedDisk] at hweighted
  have hRdot :
      R ^ 2 ≤
        (Δ.re - A.re) * (O.re - A.re) +
          (Δ.im - A.im) * (O.im - A.im) := by
    nlinarith only [hweighted]
  have hΔA' : (Δ.re - A.re) ^ 2 + (Δ.im - A.im) ^ 2 = R ^ 2 := by
    simpa only [← hRS] using hΔA
  have hdist_sq :
      (Δ.re - O.re) ^ 2 + (Δ.im - O.im) ^ 2 ≤ 0 := by
    nlinarith only [hΔA', hOA, hRdot]
  apply Complex.ext
  · nlinarith only [hdist_sq, sq_nonneg (Δ.re - O.re), sq_nonneg (Δ.im - O.im)]
  · nlinarith only [hdist_sq, sq_nonneg (Δ.re - O.re), sq_nonneg (Δ.im - O.im)]

/-- Propagation primitive: two adjacent four-point windows whose common
circles overlap in a noncollinear triple determine the same circle. -/
theorem edgeCommonCircumcircle_overlap_unique {A B C P Q O₁ O₂ : ℂ} {R₁ R₂ : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hleft : CircumcircleR2 A B P O₁ R₁ ∧ CircumcircleR2 A B C O₁ R₁)
    (hright : CircumcircleR2 B C A O₂ R₂ ∧ CircumcircleR2 B C Q O₂ R₂) :
    O₁ = O₂ ∧ R₁ = R₂ := by
  exact circumcircleR2_unique_of_cyclic_reorder hAB hcross hleft.2 hright.1

/-- Signed Menger curvature of an arbitrary noncollinear triple, expressed by
its canonical edge-circle radius and orientation. -/
theorem signedMengerR2_edge_parameter {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    Gluck.Discrete.signedMengerR2 A B C =
      ((edgeCoordinates A B C).im / |(edgeCoordinates A B C).im|) *
        normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  have hz := edgeCoordinates_im_ne_zero hAB hcross
  have hi := signedMengerR2_directIsometry (norm_chordUnit hAB) (chordMidpoint A B)
    (-chordHalfLength A B : ℂ) (chordHalfLength A B : ℂ) (edgeCoordinates A B C)
  have he := canonicalChord_endpoints hAB
  unfold transportedChordLeft transportedChordRight at he
  rw [he.1, he.2, directIsometryR2_edgeCoordinates hAB] at hi
  have hn := signedMengerR2_normalized (chordHalfLength_pos hAB) hz
  simpa [edgeCircumcenterParameter] using hi.trans hn

/-- Positive orientation removes the sign quotient from the edge-parameter
formula. -/
theorem signedMengerR2_edge_parameter_of_pos {A B C : ℂ} (hAB : A ≠ B)
    (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    Gluck.Discrete.signedMengerR2 A B C =
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  have h := signedMengerR2_edge_parameter hAB hcross.ne'
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hsign : (edgeCoordinates A B C).im / |(edgeCoordinates A B C).im| = 1 := by
    rw [abs_of_pos hz]
    field_simp [hz.ne']
  rw [h, hsign, one_mul]

/-- Negative orientation removes the sign quotient from the edge-parameter
formula. -/
theorem signedMengerR2_edge_parameter_of_neg {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C < 0) :
    Gluck.Discrete.signedMengerR2 A B C =
      -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  have h := signedMengerR2_edge_parameter hAB hcross.ne
  have hz := (crossR2_neg_iff_edgeCoordinates_im_neg hAB C).mp hcross
  have hsign : (edgeCoordinates A B C).im / |(edgeCoordinates A B C).im| = -1 := by
    rw [abs_of_neg hz]
    field_simp [hz.ne]
  rw [h, hsign]
  ring

/-- The positive signed Menger curvature of a noncollinear triple is the
reciprocal of any Euclidean circumcircle radius for the same triple. -/
theorem signedMengerR2_eq_inv_circumradius_of_pos {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hcircle : CircumcircleR2 C A B O R) :
    Gluck.Discrete.signedMengerR2 A B C = 1 / R := by
  rw [signedMengerR2_edge_parameter_of_pos hAB hcross]
  have hR := circumcircleR2_edge_radius_eq hAB hcross.ne' hcircle
  rw [hR]
  rfl

/-- The negative signed Menger curvature of a noncollinear triple is the
negative reciprocal of any Euclidean circumcircle radius for the same triple. -/
theorem signedMengerR2_eq_neg_inv_circumradius_of_neg {A B C O : ℂ} {R : ℝ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C < 0)
    (hcircle : CircumcircleR2 C A B O R) :
    Gluck.Discrete.signedMengerR2 A B C = -(1 / R) := by
  rw [signedMengerR2_edge_parameter_of_neg hAB hcross]
  have hR := circumcircleR2_edge_radius_eq hAB hcross.ne hcircle
  rw [hR]
  rfl

/-! ### Curvature at contacts of a minimal enclosing disk -/

/-- At a positive-turn boundary vertex of a minimal enclosing disk, signed
Menger curvature is at least the reciprocal enclosing radius. -/
theorem signedMengerProfile_inv_radius_le_of_minimal_boundary_of_cross_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {OΔ : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hΔ : MinimalEnclosingDiskR2 v OΔ R)
    {i : ZMod n} (hboundary : OnDiskBoundaryR2 v OΔ R i)
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    1 / R ≤ SignedMengerProfile v i := by
  rcases hregular i with hcol | ⟨O, ρ, hcircle, hcone⟩
  · exact False.elim ((ne_of_gt hcross) hcol.1)
  · have hcircle' : CircumcircleR2 (v i) (v (i - 1)) (v (i + 1)) O ρ :=
      ⟨hcircle.1, hcircle.2.2.1, hcircle.2.1, hcircle.2.2.2⟩
    have hρR : ρ ≤ R :=
      circumcircleR2_radius_le_of_inVertexCone_of_boundary
        hcircle' hcone hΔ.1 (Metric.mem_sphere'.mp hboundary)
          (hΔ.2.1 (i - 1)) (hΔ.2.1 (i + 1))
    have hAB : v (i - 1) ≠ v i := by
      simpa using hsimple.1 (i - 1)
    have hcircle'' : CircumcircleR2 (v (i + 1)) (v (i - 1)) (v i) O ρ :=
      ⟨hcircle.1, hcircle.2.2.2, hcircle.2.1, hcircle.2.2.1⟩
    have hκ : SignedMengerProfile v i = 1 / ρ := by
      simpa [SignedMengerProfile] using
        signedMengerR2_eq_inv_circumradius_of_pos hAB hcross hcircle''
    rw [hκ]
    exact one_div_le_one_div_of_le hcircle.1 hρR

/-- The preceding curvature bound is strict if either neighboring vertex is
strictly inside the minimal enclosing disk. -/
theorem signedMengerProfile_inv_radius_lt_of_minimal_boundary_of_cross_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {OΔ : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hΔ : MinimalEnclosingDiskR2 v OΔ R)
    {i : ZMod n} (hboundary : OnDiskBoundaryR2 v OΔ R i)
    (hinterior : dist OΔ (v (i - 1)) < R ∨ dist OΔ (v (i + 1)) < R)
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    1 / R < SignedMengerProfile v i := by
  rcases hregular i with hcol | ⟨O, ρ, hcircle, hcone⟩
  · exact False.elim ((ne_of_gt hcross) hcol.1)
  · have hcircle' : CircumcircleR2 (v i) (v (i - 1)) (v (i + 1)) O ρ :=
      ⟨hcircle.1, hcircle.2.2.1, hcircle.2.1, hcircle.2.2.2⟩
    have hρR : ρ ≤ R :=
      circumcircleR2_radius_le_of_inVertexCone_of_boundary
        hcircle' hcone hΔ.1 (Metric.mem_sphere'.mp hboundary)
          (hΔ.2.1 (i - 1)) (hΔ.2.1 (i + 1))
    have hρne : ρ ≠ R := by
      intro hρeq
      have hcenters : OΔ = O :=
        eq_circumcenter_of_inVertexCone_of_boundary_of_radius_eq
          hcircle' hcone hΔ.1 (Metric.mem_sphere'.mp hboundary)
            (hΔ.2.1 (i - 1)) (hΔ.2.1 (i + 1)) hρeq
      rcases hinterior with hprev | hnext
      · rw [hcenters, ← hρeq, hcircle.2.1] at hprev
        exact (lt_irrefl ρ) hprev
      · rw [hcenters, ← hρeq, hcircle.2.2.2] at hnext
        exact (lt_irrefl ρ) hnext
    have hρR' : ρ < R := lt_of_le_of_ne hρR hρne
    have hAB : v (i - 1) ≠ v i := by
      simpa using hsimple.1 (i - 1)
    have hcircle'' : CircumcircleR2 (v (i + 1)) (v (i - 1)) (v i) O ρ :=
      ⟨hcircle.1, hcircle.2.2.2, hcircle.2.1, hcircle.2.2.1⟩
    have hκ : SignedMengerProfile v i = 1 / ρ := by
      simpa [SignedMengerProfile] using
        signedMengerR2_eq_inv_circumradius_of_pos hAB hcross hcircle''
    rw [hκ]
    exact one_div_lt_one_div_of_lt hcircle.1 hρR'

/-- Three consecutive contacts with a positive-radius circle determine
signed Menger curvature exactly as its reciprocal radius. -/
theorem signedMengerProfile_eq_inv_radius_of_three_boundaries_of_cross_pos
    {n : ℕ} {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hR : 0 < R)
    {i : ZMod n}
    (hprev : OnDiskBoundaryR2 v O R (i - 1))
    (hself : OnDiskBoundaryR2 v O R i)
    (hnext : OnDiskBoundaryR2 v O R (i + 1))
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    SignedMengerProfile v i = 1 / R := by
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  have hcircle : CircumcircleR2 (v (i + 1)) (v (i - 1)) (v i) O R :=
    ⟨hR, Metric.mem_sphere'.mp hnext, Metric.mem_sphere'.mp hprev,
      Metric.mem_sphere'.mp hself⟩
  simpa [SignedMengerProfile] using
    signedMengerR2_eq_inv_circumradius_of_pos hAB hcross hcircle

/-- Positive orientation rewrites the point-edge Dahlberg region using the
positive normalized curvature of its canonical circle. -/
theorem edgePointDahlbergRegion_eq_of_pos {A B C : ℂ} (hAB : A ≠ B)
    (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    edgePointDahlbergRegion A B C =
      edgeDahlbergRegion A B (edgeCircumcenterParameter A B C)
        (normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B C)) := by
  unfold edgePointDahlbergRegion
  rw [signedMengerR2_edge_parameter_of_pos hAB hcross]

/-- On the positive branch, the third point belongs to its own Dahlberg
edge-region. -/
theorem edgePoint_mem_own_dahlbergRegion_of_pos {A B C : ℂ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    C ∈ edgePointDahlbergRegion A B C := by
  rw [edgePointDahlbergRegion_eq_of_pos hAB hcross]
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hdisk := normalizedCircumcenter_mem_closedDisk
    (a := chordHalfLength A B) (z := edgeCoordinates A B C) hz.ne'
  unfold edgeDahlbergRegion transportedDahlbergRegion directIsometryImage
  refine ⟨edgeCoordinates A B C, ?_, directIsometryR2_edgeCoordinates hAB C⟩
  rw [normalizedDahlbergRegion_eq_upperCap_of_pos
    (normalizedCircleCurvature_pos (chordHalfLength_pos hAB).ne' _)]
  change 0 ≤ (edgeCoordinates A B C).im ∧
    (edgeCoordinates A B C).re ^ 2 + (edgeCoordinates A B C).im ^ 2 -
        2 * edgeCircumcenterParameter A B C * (edgeCoordinates A B C).im ≤
      chordHalfLength A B ^ 2
  constructor
  · exact hz.le
  · simpa [normalizedClosedDisk, edgeCircumcenterParameter] using hdisk

/-- Negative orientation rewrites the point-edge Dahlberg region using the
negative normalized curvature of its canonical circle. -/
theorem edgePointDahlbergRegion_eq_of_neg {A B C : ℂ} (hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C < 0) :
    edgePointDahlbergRegion A B C =
      edgeDahlbergRegion A B (edgeCircumcenterParameter A B C)
        (-normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B C)) := by
  unfold edgePointDahlbergRegion
  rw [signedMengerR2_edge_parameter_of_neg hAB hcross]

/-- On the negative branch, the third point belongs to its own Dahlberg
edge-region via the exterior side of the oriented disk. -/
theorem edgePoint_mem_own_dahlbergRegion_of_neg {A B C : ℂ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C < 0) :
    C ∈ edgePointDahlbergRegion A B C := by
  rw [edgePointDahlbergRegion_eq_of_neg hAB hcross]
  have hz := (crossR2_neg_iff_edgeCoordinates_im_neg hAB C).mp hcross
  have hzero := circlePowerR2_normalized_parameter
    (a := chordHalfLength A B) (z := edgeCoordinates A B C) hz.ne
  change circlePowerR2 (normalizedCircleCenter (edgeCircumcenterParameter A B C))
    (edgeCoordinates A B C)
    (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) = 0 at hzero
  unfold edgeDahlbergRegion transportedDahlbergRegion directIsometryImage
  refine ⟨edgeCoordinates A B C, ?_, directIsometryR2_edgeCoordinates hAB C⟩
  have hneg : -normalizedCircleCurvature (chordHalfLength A B)
      (edgeCircumcenterParameter A B C) < 0 :=
    neg_lt_zero.mpr (normalizedCircleCurvature_pos (chordHalfLength_pos hAB).ne' _)
  rw [normalizedDahlbergRegion, if_neg (not_lt_of_ge hneg.le), if_pos hneg]
  apply Or.inl
  rw [circlePowerR2_normalized] at hzero
  change chordHalfLength A B ^ 2 ≤
    (edgeCoordinates A B C).re ^ 2 + (edgeCoordinates A B C).im ^ 2 -
      2 * edgeCircumcenterParameter A B C * (edgeCoordinates A B C).im
  linarith

/-- Every noncollinear point belongs to its own Dahlberg edge-region. -/
theorem edgePoint_mem_own_dahlbergRegion {A B C : ℂ}
    (hAB : A ≠ B) (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    C ∈ edgePointDahlbergRegion A B C := by
  rcases lt_or_gt_of_ne hcross with hneg | hpos
  · exact edgePoint_mem_own_dahlbergRegion_of_neg hAB hneg
  · exact edgePoint_mem_own_dahlbergRegion_of_pos hAB hpos

/-- Collinear triples have zero signed Menger curvature. -/
theorem signedMengerR2_eq_zero_of_cross_eq_zero {A B C : ℂ}
    (hcross : Gluck.Discrete.crossR2 A B C = 0) :
    Gluck.Discrete.signedMengerR2 A B C = 0 := by
  exact Gluck.Discrete.signedMengerR2_eq_zero_iff_crossR2_eq_zero.mpr hcross

/-- Positive orientation gives positive signed Menger curvature. -/
theorem signedMengerR2_pos_of_cross_pos {A B C : ℂ} (_hAB : A ≠ B)
    (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    0 < Gluck.Discrete.signedMengerR2 A B C := by
  exact Gluck.Discrete.signedMengerR2_pos_iff_crossR2_pos.mpr hcross

/-- Negative orientation gives negative signed Menger curvature. -/
theorem signedMengerR2_neg_of_cross_neg {A B C : ℂ} (_hAB : A ≠ B)
    (hcross : Gluck.Discrete.crossR2 A B C < 0) :
    Gluck.Discrete.signedMengerR2 A B C < 0 := by
  exact Gluck.Discrete.signedMengerR2_neg_iff_crossR2_neg.mpr hcross

/-- Positive signed Menger curvature forces positive orientation over a
nondegenerate oriented edge. -/
theorem crossR2_pos_of_signedMengerR2_pos {A B C : ℂ} (_hAB : A ≠ B)
    (hκ : 0 < Gluck.Discrete.signedMengerR2 A B C) :
    0 < Gluck.Discrete.crossR2 A B C := by
  exact Gluck.Discrete.signedMengerR2_pos_iff_crossR2_pos.mp hκ

/-- Negative signed Menger curvature forces negative orientation over a
nondegenerate oriented edge. -/
theorem crossR2_neg_of_signedMengerR2_neg {A B C : ℂ} (_hAB : A ≠ B)
    (hκ : Gluck.Discrete.signedMengerR2 A B C < 0) :
    Gluck.Discrete.crossR2 A B C < 0 := by
  exact Gluck.Discrete.signedMengerR2_neg_iff_crossR2_neg.mp hκ

/-- Nonzero signed Menger curvature forces nonzero oriented area. -/
theorem crossR2_ne_zero_of_signedMengerR2_ne_zero {A B C : ℂ}
    (hκ : Gluck.Discrete.signedMengerR2 A B C ≠ 0) :
    Gluck.Discrete.crossR2 A B C ≠ 0 := by
  exact mt Gluck.Discrete.signedMengerR2_eq_zero_iff_crossR2_eq_zero.mpr hκ

/-- Zero signed Menger curvature forces zero oriented area over a
nondegenerate edge. -/
theorem crossR2_eq_zero_of_signedMengerR2_eq_zero {A B C : ℂ} (_hAB : A ≠ B)
    (hκ : Gluck.Discrete.signedMengerR2 A B C = 0) :
    Gluck.Discrete.crossR2 A B C = 0 := by
  exact Gluck.Discrete.signedMengerR2_eq_zero_iff_crossR2_eq_zero.mp hκ

/-- For a nondegenerate edge, zero signed Menger curvature is equivalent to
zero oriented area. -/
theorem signedMengerR2_eq_zero_iff_crossR2_eq_zero {A B C : ℂ} (_hAB : A ≠ B) :
    Gluck.Discrete.signedMengerR2 A B C = 0 ↔
      Gluck.Discrete.crossR2 A B C = 0 := by
  exact Gluck.Discrete.signedMengerR2_eq_zero_iff_crossR2_eq_zero

/-- A point with nonzero signed Menger curvature belongs to its own Dahlberg
edge-region. -/
theorem edgePoint_mem_own_dahlbergRegion_of_signedMenger_ne_zero {A B C : ℂ}
    (hAB : A ≠ B) (hκ : Gluck.Discrete.signedMengerR2 A B C ≠ 0) :
    C ∈ edgePointDahlbergRegion A B C := by
  exact edgePoint_mem_own_dahlbergRegion hAB
    (crossR2_ne_zero_of_signedMengerR2_ne_zero hκ)

/-- In a simple polygon, vertices two steps apart are distinct. -/
theorem isSimplePolygon_two_step_ne {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n) :
    v i ≠ v (i + 1 + 1) := by
  intro h
  have hmem :
      v i ∈ segment ℝ (v i) (v (i + 1)) ∩
        segment ℝ (v (i + 1)) (v (i + 1 + 1)) := by
    constructor
    · exact left_mem_segment ℝ (v i) (v (i + 1))
    · simpa [← h] using right_mem_segment ℝ (v (i + 1)) (v (i + 1 + 1))
  have hsingleton : v i ∈ ({v (i + 1)} : Set ℂ) := by
    simpa [hsimple.2.1 i] using hmem
  have hvi : v i = v (i + 1) := by
    simpa using hsingleton
  exact hsimple.1 i hvi

/-- A noncollinear Dahlberg-regular vertex is in the circle/cone branch. -/
theorem dahlbergRegularAt_circle_of_cross_ne_zero {A B C : ℂ}
    (hreg : DahlbergRegularAt C A B)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    ∃ O R, CircumcircleR2 C A B O R ∧ InVertexCone C A B O := by
  rcases hreg with hcol | hcircle
  · exfalso
    apply hcross
    calc
      Gluck.Discrete.crossR2 A B C = Gluck.Discrete.crossR2 C A B :=
        (crossR2_cycle_two A B C).symm
      _ = 0 := hcol.1
  · exact hcircle

/-- A noncollinear right-endpoint Dahlberg-regular vertex is in the
circle/cone branch. -/
theorem dahlbergRegularAt_circle_of_cross_ne_zero_right {A B C : ℂ}
    (hreg : DahlbergRegularAt A B C)
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0) :
    ∃ O R, CircumcircleR2 A B C O R ∧ InVertexCone A B C O := by
  rcases hreg with hcol | hcircle
  · exact False.elim (hcross hcol.1)
  · exact hcircle

/-- In the collinear case, Dahlberg regularity over a genuinely three-point
triple is exactly the segment/subdivision branch. -/
theorem dahlbergRegularAt_segment_of_cross_eq_zero {A B C : ℂ}
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hreg : DahlbergRegularAt A B C)
    (hcross : Gluck.Discrete.crossR2 A B C = 0) :
    B ∈ segment ℝ A C := by
  rcases hreg with hcol | hcircle
  · exact hcol.2
  · rcases hcircle with ⟨O, R, hcircle, _hcone⟩
    rcases collinear_circumcircle_third_eq_endpoint hAB hcross hcircle with hCA | hCB
    · exact False.elim (hAC hCA.symm)
    · exact False.elim (hBC hCB.symm)

/-- Polygon-indexed collinear regularity: if the signed-Menger profile
vanishes at a vertex of a simple locally regular polygon, then that vertex
lies on the segment joining its neighbors. -/
theorem vertex_mem_neighbor_segment_of_signedMengerProfile_eq_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) {i : ZMod n}
    (hκ : SignedMengerProfile v i = 0) :
    v i ∈ segment ℝ (v (i - 1)) (v (i + 1)) := by
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  have hcross : Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) = 0 :=
    crossR2_eq_zero_of_signedMengerR2_eq_zero hAB
      (by simpa [SignedMengerProfile] using hκ)
  have hBC : v i ≠ v (i + 1) := hsimple.1 i
  have hAC : v (i - 1) ≠ v (i + 1) := by
    simpa [sub_eq_add_neg, add_assoc] using isSimplePolygon_two_step_ne hsimple (i - 1)
  exact dahlbergRegularAt_segment_of_cross_eq_zero hAB hBC hAC (hregular i) hcross

/-- The disk-side cap in the lower half-plane. -/
def normalizedLowerCap (a y : ℝ) : Set ℂ :=
  {z | z.im ≤ 0 ∧ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2}

/-- Increasing the centre parameter shrinks the lower disk-side cap. -/
theorem normalizedLowerCap_antitone {a y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    normalizedLowerCap a y₂ ⊆ normalizedLowerCap a y₁ := by
  intro z hz
  change (z.im ≤ 0 ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₂ * z.im ≤ a ^ 2) at hz
  change z.im ≤ 0 ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₁ * z.im ≤ a ^ 2
  constructor
  · exact hz.1
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) hz.1]

/-- On the nonnegative-centre branch, circle radius is monotone in the centre
parameter. -/
theorem normalizedCircleRadius_mono_of_nonneg {a y₁ y₂ : ℝ}
    (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂) :
    normalizedCircleRadius a y₁ ≤ normalizedCircleRadius a y₂ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (sub_nonneg.mpr hy) (add_nonneg hy₁ (hy₁.trans hy))]

/-- Normalized radius comparison behind Dahlberg Lemma 10.  If the circle
through the shared chord and `z` has centre on the interior side, then any
other coaxial circle whose closed disk contains `z` has at least as large a
radius. -/
theorem normalizedCircleRadius_le_of_mem_closedDisk {a yρ yΔ : ℝ} {z : ℂ}
    (hyρ : 0 ≤ yρ) (hz : 0 < z.im)
    (hρ : circlePowerR2 (normalizedCircleCenter yρ) z
      (normalizedCircleRadius a yρ) = 0)
    (hΔ : z ∈ normalizedClosedDisk a yΔ) :
    normalizedCircleRadius a yρ ≤ normalizedCircleRadius a yΔ := by
  rw [circlePowerR2_normalized] at hρ
  change z.re ^ 2 + z.im ^ 2 - 2 * yΔ * z.im ≤ a ^ 2 at hΔ
  have hy : yρ ≤ yΔ := by
    nlinarith [hz]
  exact normalizedCircleRadius_mono_of_nonneg hyρ hy

/-- Exterior-side normalized radius comparison: if `z` lies on the circle with
centre parameter `yρ` and outside the closed disk with centre parameter `yΔ`,
then the latter circle has no larger radius, on the nonnegative-centre branch. -/
theorem normalizedCircleRadius_le_of_mem_closedExterior {a yρ yΔ : ℝ} {z : ℂ}
    (hyΔ : 0 ≤ yΔ) (hz : 0 < z.im)
    (hρ : circlePowerR2 (normalizedCircleCenter yρ) z
      (normalizedCircleRadius a yρ) = 0)
    (hΔ : z ∈ normalizedClosedExterior a yΔ) :
    normalizedCircleRadius a yΔ ≤ normalizedCircleRadius a yρ := by
  rw [circlePowerR2_normalized] at hρ
  change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * yΔ * z.im at hΔ
  have hy : yΔ ≤ yρ := by
    nlinarith [hz]
  exact normalizedCircleRadius_mono_of_nonneg hyΔ hy

/-- Strict radius monotonicity on the nonnegative-centre branch. -/
theorem normalizedCircleRadius_strictMono_of_nonneg {a y₁ y₂ : ℝ}
    (hy₁ : 0 ≤ y₁) (hy : y₁ < y₂) :
    normalizedCircleRadius a y₁ < normalizedCircleRadius a y₂ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_lt_sqrt (by positivity)
  have hy₂ : 0 < y₂ := lt_of_le_of_lt hy₁ hy
  nlinarith [mul_pos (sub_pos.mpr hy) (add_pos_of_pos_of_nonneg hy₂ hy₁)]

/-- On the nonpositive-centre branch, circle radius is antitone in the centre
parameter. -/
theorem normalizedCircleRadius_antitone_of_nonpos {a y₁ y₂ : ℝ}
    (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleRadius a y₂ ≤ normalizedCircleRadius a y₁ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hy)
    (add_nonpos (hy.trans hy₂) hy₂)]

/-- Strict radius antitonicity on the nonpositive-centre branch. -/
theorem normalizedCircleRadius_strictAnti_of_nonpos {a y₁ y₂ : ℝ}
    (hy : y₁ < y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleRadius a y₂ < normalizedCircleRadius a y₁ := by
  unfold normalizedCircleRadius
  apply Real.sqrt_lt_sqrt (by positivity)
  have hy₁ : y₁ < 0 := lt_of_lt_of_le hy hy₂
  nlinarith [mul_pos_of_neg_of_neg (sub_neg.mpr hy)
    (add_neg_of_neg_of_nonpos hy₁ hy₂)]

/-- On the nonnegative-centre branch, positive circle curvature is antitone. -/
theorem normalizedCircleCurvature_antitone_of_nonneg {a y₁ y₂ : ℝ}
    (ha : a ≠ 0) (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂) :
    normalizedCircleCurvature a y₂ ≤ normalizedCircleCurvature a y₁ := by
  unfold normalizedCircleCurvature
  exact one_div_le_one_div_of_le (normalizedCircleRadius_pos ha y₁)
    (normalizedCircleRadius_mono_of_nonneg hy₁ hy)

/-- Strict curvature antitonicity on the nonnegative-centre branch. -/
theorem normalizedCircleCurvature_strictAnti_of_nonneg {a y₁ y₂ : ℝ}
    (ha : a ≠ 0) (hy₁ : 0 ≤ y₁) (hy : y₁ < y₂) :
    normalizedCircleCurvature a y₂ < normalizedCircleCurvature a y₁ := by
  unfold normalizedCircleCurvature
  exact one_div_lt_one_div_of_lt (normalizedCircleRadius_pos ha y₁)
    (normalizedCircleRadius_strictMono_of_nonneg hy₁ hy)

/-- Strict radius order is the opposite of positive curvature order in the
normalized coaxial family. -/
theorem normalizedCircleCurvature_lt_of_radius_lt {a yP yQ : ℝ} (ha : a ≠ 0)
    (hR : normalizedCircleRadius a yQ < normalizedCircleRadius a yP) :
    normalizedCircleCurvature a yP < normalizedCircleCurvature a yQ := by
  unfold normalizedCircleCurvature
  exact one_div_lt_one_div_of_lt (normalizedCircleRadius_pos ha yQ) hR

/-- Curvature order reverses the centre-parameter order on the positive
regular branch. -/
theorem parameter_le_of_curvature_le_nonneg {a yP yQ : ℝ} (ha : a ≠ 0)
    (hyP : 0 ≤ yP) (hκ : normalizedCircleCurvature a yP ≤ normalizedCircleCurvature a yQ) :
    yQ ≤ yP := by
  by_contra horder
  have hlt : yP < yQ := lt_of_not_ge horder
  exact (not_lt_of_ge hκ) (normalizedCircleCurvature_strictAnti_of_nonneg ha hyP hlt)

/-- On the nonpositive-centre branch, positive circle curvature is monotone. -/
theorem normalizedCircleCurvature_mono_of_nonpos {a y₁ y₂ : ℝ}
    (ha : a ≠ 0) (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleCurvature a y₁ ≤ normalizedCircleCurvature a y₂ := by
  unfold normalizedCircleCurvature
  exact one_div_le_one_div_of_le (normalizedCircleRadius_pos ha y₂)
    (normalizedCircleRadius_antitone_of_nonpos hy hy₂)

/-- Strict curvature monotonicity on the nonpositive-centre branch. -/
theorem normalizedCircleCurvature_strictMono_of_nonpos {a y₁ y₂ : ℝ}
    (ha : a ≠ 0) (hy : y₁ < y₂) (hy₂ : y₂ ≤ 0) :
    normalizedCircleCurvature a y₁ < normalizedCircleCurvature a y₂ := by
  unfold normalizedCircleCurvature
  exact one_div_lt_one_div_of_lt (normalizedCircleRadius_pos ha y₂)
    (normalizedCircleRadius_strictAnti_of_nonpos hy hy₂)

/-- Reverse curvature order gives parameter order on the negative regular
branch. -/
theorem parameter_le_of_curvature_ge_nonpos {a yP yQ : ℝ} (ha : a ≠ 0)
    (hyQ : yQ ≤ 0) (hκ : normalizedCircleCurvature a yQ ≤ normalizedCircleCurvature a yP) :
    yQ ≤ yP := by
  by_contra horder
  have hlt : yP < yQ := lt_of_not_ge horder
  exact (not_lt_of_ge hκ) (normalizedCircleCurvature_strictMono_of_nonpos ha hlt hyQ)

/-- Negative same-sign part of Dahlberg Lemma 8(3). -/
theorem normalizedDahlbergRegion_anti_of_negative {a yP yQ : ℝ} (ha : a ≠ 0)
    (hyQ : yQ ≤ 0)
    (hκ : -normalizedCircleCurvature a yP ≤ -normalizedCircleCurvature a yQ) :
    normalizedDahlbergRegion a yQ (-normalizedCircleCurvature a yQ) ⊆
      normalizedDahlbergRegion a yP (-normalizedCircleCurvature a yP) := by
  have hκ' : normalizedCircleCurvature a yQ ≤ normalizedCircleCurvature a yP := by
    linarith
  have hy := parameter_le_of_curvature_ge_nonpos ha hyQ hκ'
  exact normalizedDahlbergRegion_mono_of_negative hy
    (neg_lt_zero.mpr (normalizedCircleCurvature_pos ha yQ))
    (neg_lt_zero.mpr (normalizedCircleCurvature_pos ha yP))

/-- Moving the centre upward enlarges the disk-side upper cap. This elementary
order statement is the normalized algebraic core of Dahlberg's nesting
lemma. -/
theorem normalizedUpperCap_mono {a y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    normalizedUpperCap a y₁ ⊆ normalizedUpperCap a y₂ := by
  intro z hz
  change (0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₁ * z.im ≤ a ^ 2) at hz
  change 0 ≤ z.im ∧ z.re ^ 2 + z.im ^ 2 - 2 * y₂ * z.im ≤ a ^ 2
  constructor
  · exact hz.1
  · nlinarith [mul_nonneg (sub_nonneg.mpr hy) hz.1]

/-- Positive same-sign part of Dahlberg Lemma 8(3). -/
theorem normalizedDahlbergRegion_anti_of_positive {a yP yQ : ℝ} (ha : a ≠ 0)
    (hyP : 0 ≤ yP)
    (hκ : normalizedCircleCurvature a yP ≤ normalizedCircleCurvature a yQ) :
    normalizedDahlbergRegion a yQ (normalizedCircleCurvature a yQ) ⊆
      normalizedDahlbergRegion a yP (normalizedCircleCurvature a yP) := by
  have hy := parameter_le_of_curvature_le_nonneg ha hyP hκ
  rw [normalizedDahlbergRegion_eq_upperCap_of_pos (normalizedCircleCurvature_pos ha yQ),
    normalizedDahlbergRegion_eq_upperCap_of_pos (normalizedCircleCurvature_pos ha yP)]
  exact normalizedUpperCap_mono hy

/-- Dahlberg cap nesting after any orientation-preserving Euclidean isometry. -/
theorem transportedUpperCap_mono (u w : ℂ) {a y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    transportedUpperCap u w a y₁ ⊆ transportedUpperCap u w a y₂ := by
  unfold transportedUpperCap directIsometryImage
  exact Set.image_mono (normalizedUpperCap_mono hy)

/-- Normalized Dahlberg-region inclusions transport through the same direct
Euclidean isometry. -/
theorem transportedDahlbergRegion_mono (u w : ℂ) {a yP yQ kP kQ : ℝ}
    (h : normalizedDahlbergRegion a yQ kQ ⊆ normalizedDahlbergRegion a yP kP) :
    transportedDahlbergRegion u w a yQ kQ ⊆ transportedDahlbergRegion u w a yP kP := by
  unfold transportedDahlbergRegion directIsometryImage
  exact Set.image_mono h

/-- Transported form of Dahlberg Lemma 8(1). -/
theorem transportedDahlbergRegion_subset_halfPlane (u w : ℂ) {a y k : ℝ}
    (hk : 0 ≤ k) :
    transportedDahlbergRegion u w a y k ⊆ transportedEdgeHalfPlane u w := by
  unfold transportedDahlbergRegion transportedEdgeHalfPlane directIsometryImage
  exact Set.image_mono (normalizedDahlbergRegion_subset_halfPlane hk)

/-- Transported form of Dahlberg Lemma 8(2). -/
theorem transportedHalfPlane_subset_dahlbergRegion (u w : ℂ) {a y k : ℝ}
    (hk : k ≤ 0) :
    transportedEdgeHalfPlane u w ⊆ transportedDahlbergRegion u w a y k := by
  unfold transportedDahlbergRegion transportedEdgeHalfPlane directIsometryImage
  exact Set.image_mono (normalizedHalfPlane_subset_dahlbergRegion hk)

/-- Positive transported Dahlberg regions lie in their transported closed disk. -/
theorem transportedDahlbergRegion_subset_closedDisk_of_pos (u w : ℂ) {a y k : ℝ}
    (hk : 0 < k) :
    transportedDahlbergRegion u w a y k ⊆ transportedClosedDisk u w a y := by
  unfold transportedDahlbergRegion transportedClosedDisk directIsometryImage
  exact Set.image_mono (normalizedDahlbergRegion_subset_closedDisk_of_pos hk)

/-- Nonnegative edge Dahlberg regions lie in the corresponding edge half-plane. -/
theorem edgeDahlbergRegion_subset_halfPlane (A B : ℂ) {y k : ℝ} (hk : 0 ≤ k) :
    edgeDahlbergRegion A B y k ⊆ edgeHalfPlane A B := by
  unfold edgeDahlbergRegion edgeHalfPlane
  exact transportedDahlbergRegion_subset_halfPlane _ _ hk

/-- The edge half-plane lies in every nonpositive edge Dahlberg region. -/
theorem edgeHalfPlane_subset_dahlbergRegion (A B : ℂ) {y k : ℝ} (hk : k ≤ 0) :
    edgeHalfPlane A B ⊆ edgeDahlbergRegion A B y k := by
  unfold edgeDahlbergRegion edgeHalfPlane
  exact transportedHalfPlane_subset_dahlbergRegion _ _ hk

/-- Positive edge Dahlberg regions lie in the corresponding edge disk. -/
theorem edgeDahlbergRegion_subset_closedDisk_of_pos (A B : ℂ) {y k : ℝ}
    (hk : 0 < k) :
    edgeDahlbergRegion A B y k ⊆ edgeClosedDisk A B y := by
  unfold edgeDahlbergRegion edgeClosedDisk
  exact transportedDahlbergRegion_subset_closedDisk_of_pos _ _ hk

/-- Point-edge form of Dahlberg Lemma 8(1). -/
theorem edgePointDahlbergRegion_subset_edgeHalfPlane_of_nonneg {A B C : ℂ}
    (hk : 0 ≤ Gluck.Discrete.signedMengerR2 A B C) :
    edgePointDahlbergRegion A B C ⊆ edgeHalfPlane A B := by
  unfold edgePointDahlbergRegion
  exact edgeDahlbergRegion_subset_halfPlane A B hk

/-- Point-edge form of Dahlberg Lemma 8(2). -/
theorem edgeHalfPlane_subset_edgePointDahlbergRegion_of_nonpos {A B C : ℂ}
    (hk : Gluck.Discrete.signedMengerR2 A B C ≤ 0) :
    edgeHalfPlane A B ⊆ edgePointDahlbergRegion A B C := by
  unfold edgePointDahlbergRegion
  exact edgeHalfPlane_subset_dahlbergRegion A B hk

/-- On the positive branch, a point-edge Dahlberg region is contained in the
ordinary curvature disk for that point and edge. -/
theorem edgePointDahlbergRegion_subset_edgeClosedDisk_of_pos {A B C : ℂ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    edgePointDahlbergRegion A B C ⊆
      edgeClosedDisk A B (edgeCircumcenterParameter A B C) := by
  rw [edgePointDahlbergRegion_eq_of_pos hAB hcross]
  exact edgeDahlbergRegion_subset_closedDisk_of_pos A B
    (normalizedCircleCurvature_pos (chordHalfLength_pos hAB).ne' _)

/-- Membership in an arbitrary edge disk is membership in the normalized disk
after passing to canonical edge coordinates. -/
theorem edgeCoordinates_mem_normalizedClosedDisk_of_mem_edgeClosedDisk {A B C : ℂ}
    {y : ℝ} (hAB : A ≠ B) (hmem : C ∈ edgeClosedDisk A B y) :
    edgeCoordinates A B C ∈ normalizedClosedDisk (chordHalfLength A B) y := by
  unfold edgeClosedDisk transportedClosedDisk directIsometryImage at hmem
  rcases hmem with ⟨z, hz, hzC⟩
  have hz_eq : z = edgeCoordinates A B C := by
    apply directIsometryR2_injective (norm_chordUnit hAB) (chordMidpoint A B)
    rw [hzC, directIsometryR2_edgeCoordinates hAB]
  simpa [← hz_eq] using hz

/-- Membership in an arbitrary edge exterior is membership in the normalized
exterior after passing to canonical edge coordinates. -/
theorem edgeCoordinates_mem_normalizedClosedExterior_of_mem_edgeClosedExterior
    {A B C : ℂ} {y : ℝ} (hAB : A ≠ B)
    (hmem : C ∈ edgeClosedExterior A B y) :
    edgeCoordinates A B C ∈ normalizedClosedExterior (chordHalfLength A B) y := by
  unfold edgeClosedExterior directIsometryImage at hmem
  rcases hmem with ⟨z, hz, hzC⟩
  have hz_eq : z = edgeCoordinates A B C := by
    apply directIsometryR2_injective (norm_chordUnit hAB) (chordMidpoint A B)
    rw [hzC, directIsometryR2_edgeCoordinates hAB]
  simpa [← hz_eq] using hz

/-! ### Coaxial edge envelopes for strictly convex polygons -/

/-- A point strictly above the normalized chord belongs to the coaxial closed
disk with centre parameter `y` exactly when its own circumcentre parameter is
at most `y`. -/
theorem mem_normalizedClosedDisk_circumcenterParameter_iff
    {a y : ℝ} {z : ℂ} (hz : 0 < z.im) :
    z ∈ normalizedClosedDisk a y ↔
      normalizedCircumcenterParameter a z ≤ y := by
  have hzero := circlePowerR2_normalized_parameter (a := a) (z := z) hz.ne'
  rw [circlePowerR2_normalized] at hzero
  constructor
  · intro hmem
    change z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2 at hmem
    nlinarith
  · intro hy
    change z.re ^ 2 + z.im ^ 2 - 2 * y * z.im ≤ a ^ 2
    nlinarith

/-- The corresponding closed-exterior criterion has the reverse parameter
order. -/
theorem mem_normalizedClosedExterior_circumcenterParameter_iff
    {a y : ℝ} {z : ℂ} (hz : 0 < z.im) :
    z ∈ normalizedClosedExterior a y ↔
      y ≤ normalizedCircumcenterParameter a z := by
  have hzero := circlePowerR2_normalized_parameter (a := a) (z := z) hz.ne'
  rw [circlePowerR2_normalized] at hzero
  constructor
  · intro hmem
    change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im at hmem
    nlinarith
  · intro hy
    change a ^ 2 ≤ z.re ^ 2 + z.im ^ 2 - 2 * y * z.im
    nlinarith

/-- Transported coaxial disk criterion for a point strictly left of the
oriented edge `A → B`. -/
theorem mem_edgeClosedDisk_circumcenterParameter_iff
    {A B C : ℂ} {y : ℝ} (hAB : A ≠ B)
    (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    C ∈ edgeClosedDisk A B y ↔ edgeCircumcenterParameter A B C ≤ y := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  constructor
  · intro hmem
    have hnorm := edgeCoordinates_mem_normalizedClosedDisk_of_mem_edgeClosedDisk
      hAB hmem
    exact (mem_normalizedClosedDisk_circumcenterParameter_iff hz).mp hnorm
  · intro hy
    unfold edgeClosedDisk transportedClosedDisk directIsometryImage
    refine ⟨edgeCoordinates A B C, ?_, directIsometryR2_edgeCoordinates hAB C⟩
    exact (mem_normalizedClosedDisk_circumcenterParameter_iff hz).mpr hy

/-- Transported coaxial exterior criterion for a point strictly left of the
oriented edge `A → B`. -/
theorem mem_edgeClosedExterior_circumcenterParameter_iff
    {A B C : ℂ} {y : ℝ} (hAB : A ≠ B)
    (hcross : 0 < Gluck.Discrete.crossR2 A B C) :
    C ∈ edgeClosedExterior A B y ↔ y ≤ edgeCircumcenterParameter A B C := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  constructor
  · intro hmem
    have hnorm := edgeCoordinates_mem_normalizedClosedExterior_of_mem_edgeClosedExterior
      hAB hmem
    exact (mem_normalizedClosedExterior_circumcenterParameter_iff hz).mp hnorm
  · intro hy
    unfold edgeClosedExterior directIsometryImage
    refine ⟨edgeCoordinates A B C, ?_, directIsometryR2_edgeCoordinates hAB C⟩
    exact (mem_normalizedClosedExterior_circumcenterParameter_iff hz).mpr hy

/-- Both normalized chord endpoints belong to every coaxial closed exterior,
on its boundary. -/
theorem normalizedClosedExterior_endpoints (a y : ℝ) :
    (a : ℂ) ∈ normalizedClosedExterior a y ∧
      (-a : ℂ) ∈ normalizedClosedExterior a y := by
  constructor
  · change a ^ 2 ≤ (a : ℂ).re ^ 2 + (a : ℂ).im ^ 2 - 2 * y * (a : ℂ).im
    simp
  · change a ^ 2 ≤ (-a : ℂ).re ^ 2 + (-a : ℂ).im ^ 2 - 2 * y * (-a : ℂ).im
    simp

/-- Both endpoints of an arbitrary edge belong to every coaxial closed
exterior, on its boundary. -/
theorem edgeClosedExterior_endpoints {A B : ℂ} (hAB : A ≠ B) (y : ℝ) :
    A ∈ edgeClosedExterior A B y ∧ B ∈ edgeClosedExterior A B y := by
  have he := canonicalChord_endpoints hAB
  have hnorm := normalizedClosedExterior_endpoints (chordHalfLength A B) y
  constructor
  · unfold edgeClosedExterior directIsometryImage
    exact ⟨(-chordHalfLength A B : ℂ), hnorm.2, by
      simpa [transportedChordLeft] using he.1⟩
  · unfold edgeClosedExterior directIsometryImage
    exact ⟨(chordHalfLength A B : ℂ), hnorm.1, by
      simpa [transportedChordRight] using he.2⟩

/-- Every vertex not on an oriented edge lies strictly to its left.  This is
the explicit global support property needed by the finite part of Dahlberg's
strictly convex argument. -/
def StrictConvexEdgeSupport {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 →
    0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j)

/-- The arbitrary-chord cyclic-order geometry consumed by Dahlberg's Lemmas
4 and 6.  For a lifted gap `p < k < q`, orient the endpoint chord from `q`
back to `p`.  The gap lies on its positive side, that closed side contains
only the endpoint-closed gap, and every segment from the gap to a vertex
outside it crosses the endpoint chord.

This structure isolates the precise downstream consequence of strict convex
cyclic order; it contains no circle-theorem assumption. -/
structure StrictConvexCyclicChordGeometry {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) : Prop where
  noncollinear : ∀ a b d : ZMod n,
    a ≠ b → d ≠ a → d ≠ b →
      Gluck.Discrete.crossR2 (v a) (v b) (v d) ≠ 0
  gap : ∀ (c : ZMod n) (p k q : ℕ),
    p < k → k < q → q < n →
    let a := Gluck.cyclicLift c q
    let b := Gluck.cyclicLift c p
    let z := Gluck.cyclicLift c k
    let E := Gluck.mapCut c (Finset.Icc p q)
    v a ≠ v b ∧
      0 < Gluck.Discrete.crossR2 (v a) (v b) (v z) ∧
      (∀ x : ZMod n,
        0 ≤ Gluck.Discrete.crossR2 (v a) (v b) (v x) → x ∈ E) ∧
      (∀ x : ZMod n, x ∉ E →
        ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1,
          (AffineMap.lineMap (v z) (v x)) t =
            (AffineMap.lineMap (v a) (v b)) s)

/-- Strict support by every oriented polygon edge implies the full
arbitrary-chord cyclic geometry used by Dahlberg's Lemmas 4 and 6. -/
theorem strictConvexCyclicChordGeometry_of_edgeSupport
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) :
    StrictConvexCyclicChordGeometry v := by
  let hfields :=
    Gluck.Forward.CyclicChordGeometry.strictConvexCyclicChordGeometryFields_of_edgeSupport
      (v := v)
      (show Gluck.Forward.CyclicChordGeometry.CyclicChordStrictConvexEdgeSupport v
        from hsupport)
  exact ⟨hfields.noncollinear, hfields.gap⟩

/-- Indices of vertices other than the endpoints of an oriented edge. -/
def edgeThirdVertexIndices {n : ℕ} [NeZero n] (i : ZMod n) :
    Finset (ZMod n) :=
  (Finset.univ.erase i).erase (i + 1)

theorem mem_edgeThirdVertexIndices_iff {n : ℕ} [NeZero n]
    {i j : ZMod n} :
    j ∈ edgeThirdVertexIndices i ↔ j ≠ i ∧ j ≠ i + 1 := by
  simp [edgeThirdVertexIndices, and_comm]

/-- For a polygon with at least four vertices, every edge has a third vertex. -/
theorem edgeThirdVertexIndices_nonempty {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (i : ZMod n) :
    (edgeThirdVertexIndices i).Nonempty := by
  letI : Fact (1 < n) := ⟨by omega⟩
  have hsucc : i + 1 ≠ i := by
    intro h
    have h10 : (1 : ZMod n) = 0 := calc
      (1 : ZMod n) = (i + 1) - i := by ring
      _ = i - i := congrArg (fun z : ZMod n ↦ z - i) h
      _ = 0 := sub_self i
    exact one_ne_zero h10
  rw [← Finset.card_pos]
  unfold edgeThirdVertexIndices
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hsucc, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, ZMod.card]
  omega

/-- Global strict edge support forces every edge to be nondegenerate. -/
theorem strictConvexEdgeSupport_edge_ne {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) {v : ZMod n → ℂ} (hsupport : StrictConvexEdgeSupport v)
    (i : ZMod n) : v i ≠ v (i + 1) := by
  rcases edgeThirdVertexIndices_nonempty hn i with ⟨j, hj⟩
  have hjne := mem_edgeThirdVertexIndices_iff.mp hj
  have hcross := hsupport i j hjne.1 hjne.2
  intro hAB
  have hzero : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j) = 0 := by
    rw [hAB]
    unfold Gluck.Discrete.crossR2
    simp
  linarith

/-- The maximum coaxial parameter among the third vertices gives a circle
through the edge and a third vertex whose closed disk contains every vertex. -/
theorem exists_edgeThirdVertex_circle_containsAll_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) (i : ZMod n) :
    ∃ j : ZMod n,
      j ≠ i ∧ j ≠ i + 1 ∧
      (∀ k : ZMod n,
        v k ∈ edgeClosedDisk (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j))) ∧
      CircumcircleR2 (v i) (v (i + 1)) (v j)
        (edgeCircleCenter (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j)))
        (normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j))) := by
  let s := edgeThirdVertexIndices i
  have hs : s.Nonempty := edgeThirdVertexIndices_nonempty hn i
  obtain ⟨j, hjs, hsup⟩ := Finset.exists_mem_eq_sup' hs
    (fun k : ZMod n ↦ edgeCircumcenterParameter (v i) (v (i + 1)) (v k))
  have hjne : j ≠ i ∧ j ≠ i + 1 := mem_edgeThirdVertexIndices_iff.mp hjs
  have hAB : v i ≠ v (i + 1) := strictConvexEdgeSupport_edge_ne hn hsupport i
  have hjcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j) :=
    hsupport i j hjne.1 hjne.2
  have hmax : ∀ k ∈ s,
      edgeCircumcenterParameter (v i) (v (i + 1)) (v k) ≤
        edgeCircumcenterParameter (v i) (v (i + 1)) (v j) := by
    intro k hk
    rw [← hsup]
    exact Finset.le_sup'
      (fun q : ZMod n ↦ edgeCircumcenterParameter (v i) (v (i + 1)) (v q)) hk
  refine ⟨j, hjne.1, hjne.2, ?_, circumcircleR2_edge_parameter hAB hjcross.ne'⟩
  intro k
  by_cases hki : k = i
  · subst k
    exact (edgeClosedDisk_endpoints hAB _).1
  by_cases hksucc : k = i + 1
  · subst k
    exact (edgeClosedDisk_endpoints hAB _).2
  · have hkcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v k) :=
      hsupport i k hki hksucc
    apply (mem_edgeClosedDisk_circumcenterParameter_iff hAB hkcross).mpr
    exact hmax k (mem_edgeThirdVertexIndices_iff.mpr ⟨hki, hksucc⟩)

/-- The minimum coaxial parameter among the third vertices gives a circle
through the edge and a third vertex whose open interior contains no vertex. -/
theorem exists_edgeThirdVertex_circle_interiorMissesAll_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) (i : ZMod n) :
    ∃ j : ZMod n,
      j ≠ i ∧ j ≠ i + 1 ∧
      (∀ k : ZMod n,
        v k ∈ edgeClosedExterior (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j))) ∧
      CircumcircleR2 (v i) (v (i + 1)) (v j)
        (edgeCircleCenter (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j)))
        (normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v j))) := by
  let s := edgeThirdVertexIndices i
  have hs : s.Nonempty := edgeThirdVertexIndices_nonempty hn i
  obtain ⟨j, hjs, hinf⟩ := Finset.exists_mem_eq_inf' hs
    (fun k : ZMod n ↦ edgeCircumcenterParameter (v i) (v (i + 1)) (v k))
  have hjne : j ≠ i ∧ j ≠ i + 1 := mem_edgeThirdVertexIndices_iff.mp hjs
  have hAB : v i ≠ v (i + 1) := strictConvexEdgeSupport_edge_ne hn hsupport i
  have hjcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j) :=
    hsupport i j hjne.1 hjne.2
  have hmin : ∀ k ∈ s,
      edgeCircumcenterParameter (v i) (v (i + 1)) (v j) ≤
        edgeCircumcenterParameter (v i) (v (i + 1)) (v k) := by
    intro k hk
    rw [← hinf]
    exact Finset.inf'_le
      (fun q : ZMod n ↦ edgeCircumcenterParameter (v i) (v (i + 1)) (v q)) hk
  refine ⟨j, hjne.1, hjne.2, ?_, circumcircleR2_edge_parameter hAB hjcross.ne'⟩
  intro k
  by_cases hki : k = i
  · subst k
    exact (edgeClosedExterior_endpoints hAB _).1
  by_cases hksucc : k = i + 1
  · subst k
    exact (edgeClosedExterior_endpoints hAB _).2
  · have hkcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v k) :=
      hsupport i k hki hksucc
    apply (mem_edgeClosedExterior_circumcenterParameter_iff hAB hkcross).mpr
    exact hmin k (mem_edgeThirdVertexIndices_iff.mpr ⟨hki, hksucc⟩)

/-! ### Dahlberg's finite three-contact disk families -/

/-- A closed disk in Dahlberg's family `F`: it contains every polygon vertex
and has at least three boundary contacts. -/
structure DahlbergContainingThreeContactDiskR2 {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  contains : PolygonInClosedDiskR2 v center radius
  three_contacts : 3 ≤ (circleContactSet v center radius).card

/-- An open disk in Dahlberg's family `G`, represented by its closed
exterior: no polygon vertex is in its interior, and at least three vertices
are on its boundary. -/
structure DahlbergInteriorMissingThreeContactDiskR2 {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  misses : ∀ k : ZMod n, radius ≤ dist center (v k)
  three_contacts : 3 ≤ (circleContactSet v center radius).card

/-- Dahlberg §3 Lemma 3 for the containing family `F`: the finite coaxial
maximum through the outgoing edge at `i` gives a member of `F(i)`. -/
theorem exists_dahlbergContainingThreeContactDiskR2_at_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) (i : ZMod n) :
    ∃ U : DahlbergContainingThreeContactDiskR2 v,
      i ∈ circleContactSet v U.center U.radius := by
  rcases exists_edgeThirdVertex_circle_containsAll_of_strictConvexEdgeSupport
      hn hsupport i with ⟨j, hji, hjnext, hall, hcircle⟩
  have hAB : v i ≠ v (i + 1) :=
    strictConvexEdgeSupport_edge_ne hn hsupport i
  let y := edgeCircumcenterParameter (v i) (v (i + 1)) (v j)
  let O := edgeCircleCenter (v i) (v (i + 1)) y
  let R := normalizedCircleRadius (chordHalfLength (v i) (v (i + 1))) y
  have hcontains : PolygonInClosedDiskR2 v O R := by
    intro k
    exact Metric.mem_closedBall'.mpr ((mem_edgeClosedDisk_iff_dist_le hAB y).mp (hall k))
  have hiNext : i ≠ i + 1 := by
    intro h
    exact hAB (congrArg v h)
  have hthree : 3 ≤ (circleContactSet v O R).card := by
    apply three_le_card_circleContactSet hiNext hji.symm hjnext.symm
    · exact hcircle.2.1
    · exact hcircle.2.2.1
    · exact hcircle.2.2.2
  let U : DahlbergContainingThreeContactDiskR2 v :=
    { center := O
      radius := R
      radius_pos := hcircle.1
      contains := hcontains
      three_contacts := hthree }
  refine ⟨U, ?_⟩
  exact mem_circleContactSet.mpr hcircle.2.1

/-- Dahlberg §3 Lemma 3 for the interior-missing family `G`: the finite
coaxial minimum through the outgoing edge at `i` gives a member of `G(i)`. -/
theorem exists_dahlbergInteriorMissingThreeContactDiskR2_at_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsupport : StrictConvexEdgeSupport v) (i : ZMod n) :
    ∃ U : DahlbergInteriorMissingThreeContactDiskR2 v,
      i ∈ circleContactSet v U.center U.radius := by
  rcases exists_edgeThirdVertex_circle_interiorMissesAll_of_strictConvexEdgeSupport
      hn hsupport i with ⟨j, hji, hjnext, hall, hcircle⟩
  have hAB : v i ≠ v (i + 1) :=
    strictConvexEdgeSupport_edge_ne hn hsupport i
  let y := edgeCircumcenterParameter (v i) (v (i + 1)) (v j)
  let O := edgeCircleCenter (v i) (v (i + 1)) y
  let R := normalizedCircleRadius (chordHalfLength (v i) (v (i + 1))) y
  have hmisses : ∀ k : ZMod n, R ≤ dist O (v k) := by
    intro k
    exact (mem_edgeClosedExterior_iff_radius_le_dist hAB y).mp (hall k)
  have hiNext : i ≠ i + 1 := by
    intro h
    exact hAB (congrArg v h)
  have hthree : 3 ≤ (circleContactSet v O R).card := by
    apply three_le_card_circleContactSet hiNext hji.symm hjnext.symm
    · exact hcircle.2.1
    · exact hcircle.2.2.1
    · exact hcircle.2.2.2
  let U : DahlbergInteriorMissingThreeContactDiskR2 v :=
    { center := O
      radius := R
      radius_pos := hcircle.1
      misses := hmisses
      three_contacts := hthree }
  refine ⟨U, ?_⟩
  exact mem_circleContactSet.mpr hcircle.2.1

/-- Two named contacts and any third noncollinear contact put a three-contact
circle into the canonical coaxial family of the named chord. -/
theorem exists_contact_edgeCircle_parameter
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {a b : ZMod n}
    (hAB : v a ≠ v b) (hR : 0 < R)
    (hthree : 3 ≤ (circleContactSet v O R).card)
    (ha : a ∈ circleContactSet v O R)
    (hb : b ∈ circleContactSet v O R)
    (hnocol : ∀ c : ZMod n,
      c ∈ circleContactSet v O R → c ≠ a → c ≠ b →
        Gluck.Discrete.crossR2 (v a) (v b) (v c) ≠ 0) :
    ∃ c : ZMod n,
      c ∈ circleContactSet v O R ∧ c ≠ a ∧ c ≠ b ∧
      O = edgeCircleCenter (v a) (v b)
        (edgeCircumcenterParameter (v a) (v b) (v c)) ∧
      R = normalizedCircleRadius (chordHalfLength (v a) (v b))
        (edgeCircumcenterParameter (v a) (v b) (v c)) := by
  obtain ⟨c, hc, hca, hcb⟩ :=
    exists_circleContact_ne_two_of_three_le_card hthree
  have hcircle : CircumcircleR2 (v a) (v b) (v c) O R :=
    ⟨hR, mem_circleContactSet.mp ha, mem_circleContactSet.mp hb,
      mem_circleContactSet.mp hc⟩
  have heq := circumcircleR2_edge_center_radius_eq hAB
    (hnocol c hc hca hcb) hcircle
  exact ⟨c, hc, hca, hcb, heq.1, heq.2⟩

/-! ### Two-circle chord separation -/

/-- A normalized coaxial closed disk is convex. -/
theorem convex_normalizedClosedDisk (a y : ℝ) :
    Convex ℝ (normalizedClosedDisk a y) := by
  rw [show normalizedClosedDisk a y =
      Metric.closedBall (normalizedCircleCenter y) (normalizedCircleRadius a y) by
    ext z
    simpa [Metric.mem_closedBall, dist_comm] using
      mem_normalizedClosedDisk_iff_dist_le a y z]
  exact convex_closedBall _ _

/-- The difference of two circle-power functions is affine.  This identity is
the algebraic radical-axis input used in Dahlberg's Lemmas 4 and 6. -/
theorem circlePowerR2_sub_lineMap (O₁ O₂ X Z : ℂ) (R₁ R₂ t : ℝ) :
    circlePowerR2 O₁ ((AffineMap.lineMap X Z) t) R₁ -
        circlePowerR2 O₂ ((AffineMap.lineMap X Z) t) R₂ =
      (1 - t) * (circlePowerR2 O₁ X R₁ - circlePowerR2 O₂ X R₂) +
        t * (circlePowerR2 O₁ Z R₁ - circlePowerR2 O₂ Z R₂) := by
  have hline : (AffineMap.lineMap X Z) t = (1 - t) • X + t • Z := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [hline]
  unfold circlePowerR2 EuclideanGeometry.Sphere.power
  simp only [dist_eq_norm]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im]
  ring

/-- Exterior-circle chord crossing is impossible under Dahlberg's Lemma 6
power inequalities.  The segment from `Q` to `X` would make the difference
of the two circle powers positive at its crossing with `AB`, while the same
affine difference is nonpositive throughout the chord `AB`. -/
theorem circleExterior_chord_crossing_false
    {Oᵤ O𝓌 A B Q X : ℂ} {Rᵤ R𝓌 t s : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hs : s ∈ Set.Icc 0 1)
    (hcrossing : (AffineMap.lineMap Q X) t = (AffineMap.lineMap A B) s)
    (hAᵤ : circlePowerR2 Oᵤ A Rᵤ = 0)
    (hBᵤ : circlePowerR2 Oᵤ B Rᵤ = 0)
    (hA𝓌 : 0 ≤ circlePowerR2 O𝓌 A R𝓌)
    (hB𝓌 : 0 ≤ circlePowerR2 O𝓌 B R𝓌)
    (hQᵤ : 0 < circlePowerR2 Oᵤ Q Rᵤ)
    (hQ𝓌 : circlePowerR2 O𝓌 Q R𝓌 = 0)
    (hXᵤ : 0 ≤ circlePowerR2 Oᵤ X Rᵤ)
    (hX𝓌 : circlePowerR2 O𝓌 X R𝓌 = 0) : False := by
  have hQdiff : 0 <
      circlePowerR2 Oᵤ Q Rᵤ - circlePowerR2 O𝓌 Q R𝓌 := by
    linarith
  have hXdiff : 0 ≤
      circlePowerR2 Oᵤ X Rᵤ - circlePowerR2 O𝓌 X R𝓌 := by
    linarith
  have hYpos : 0 <
      circlePowerR2 Oᵤ ((AffineMap.lineMap Q X) t) Rᵤ -
        circlePowerR2 O𝓌 ((AffineMap.lineMap Q X) t) R𝓌 := by
    rw [circlePowerR2_sub_lineMap]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr ht.2) hQdiff)
      (mul_nonneg ht.1.le hXdiff)
  have hAdiff :
      circlePowerR2 Oᵤ A Rᵤ - circlePowerR2 O𝓌 A R𝓌 ≤ 0 := by
    linarith
  have hBdiff :
      circlePowerR2 Oᵤ B Rᵤ - circlePowerR2 O𝓌 B R𝓌 ≤ 0 := by
    linarith
  have hYnonpos :
      circlePowerR2 Oᵤ ((AffineMap.lineMap A B) s) Rᵤ -
        circlePowerR2 O𝓌 ((AffineMap.lineMap A B) s) R𝓌 ≤ 0 := by
    rw [circlePowerR2_sub_lineMap]
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs.2) hAdiff)
      (mul_nonpos_of_nonneg_of_nonpos hs.1 hBdiff)
  rw [hcrossing] at hYpos
  exact (not_lt_of_ge hYnonpos) hYpos

/-- Normalized two-circle chord separation, the geometric core of Dahlberg's
Lemmas 4 and 6.

Let `U` be the coaxial disk through `−a` and `a`, and let `W` be the disk
with centre `O` and radius `R`.  Suppose `W` contains both chord endpoints,
while a point `Q` above the chord lies on `∂W` and strictly inside `U`.
Then every point `X` of `∂W ∩ U` lies in the closed half-plane on the
`Q`-side of the chord. -/
theorem normalized_circleBoundary_mem_closedDisk_im_nonneg
    {a y R : ℝ} {O Q X : ℂ}
    (ha : 0 < a) (hQim : 0 < Q.im)
    (hQint : circlePowerR2 (normalizedCircleCenter y) Q
      (normalizedCircleRadius a y) < 0)
    (hQboundary : circlePowerR2 O Q R = 0)
    (hleft : circlePowerR2 O (-a : ℂ) R ≤ 0)
    (hright : circlePowerR2 O (a : ℂ) R ≤ 0)
    (hXboundary : circlePowerR2 O X R = 0)
    (hXmem : X ∈ normalizedClosedDisk a y) :
    0 ≤ X.im := by
  by_contra hXnonneg
  have hXneg : X.im < 0 := lt_of_not_ge hXnonneg
  let t : ℝ := Q.im / (Q.im - X.im)
  have hden : 0 < Q.im - X.im := by linarith
  have htpos : 0 < t := div_pos hQim hden
  have htlt : t < 1 := (div_lt_one hden).2 (by linarith)
  let Y : ℂ := (AffineMap.lineMap Q X) t
  have hlineQX : Y = (1 - t) • Q + t • X := by
    change (AffineMap.lineMap Q X) t = (1 - t) • Q + t • X
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hYim : Y.im = 0 := by
    rw [hlineQX]
    simp only [Complex.add_im, Complex.smul_im]
    dsimp [t]
    field_simp [hden.ne']
    ring
  have hQmem : Q ∈ normalizedClosedDisk a y := by
    rw [circlePowerR2_normalized] at hQint
    change Q.re ^ 2 + Q.im ^ 2 - 2 * y * Q.im ≤ a ^ 2
    linarith
  have hYmem : Y ∈ normalizedClosedDisk a y := by
    exact (convex_normalizedClosedDisk a y).lineMap_mem hQmem hXmem
      ⟨htpos.le, htlt.le⟩
  have hYsq : Y.re ^ 2 ≤ a ^ 2 := by
    change Y.re ^ 2 + Y.im ^ 2 - 2 * y * Y.im ≤ a ^ 2 at hYmem
    rw [hYim] at hYmem
    simpa using hYmem
  have hYlower : -a ≤ Y.re := by
    nlinarith [sq_nonneg (Y.re + a)]
  have hYupper : Y.re ≤ a := by
    nlinarith [sq_nonneg (Y.re - a)]
  let s : ℝ := (Y.re + a) / (2 * a)
  have hs0 : 0 ≤ s := div_nonneg (by linarith) (by positivity)
  have hs1 : s ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hlineEnds : (AffineMap.lineMap (-a : ℂ) (a : ℂ)) s = Y := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, Complex.sub_re]
      dsimp [s]
      field_simp [ha.ne']
      ring
    · simp only [Complex.add_im, Complex.smul_im, Complex.sub_im]
      simp [hYim]
  have hUends := normalizedCircle_endpoints a y
  have hDleft : 0 ≤
      circlePowerR2 (normalizedCircleCenter y) (-a : ℂ)
          (normalizedCircleRadius a y) - circlePowerR2 O (-a : ℂ) R := by
    linarith [hUends.2]
  have hDright : 0 ≤
      circlePowerR2 (normalizedCircleCenter y) (a : ℂ)
          (normalizedCircleRadius a y) - circlePowerR2 O (a : ℂ) R := by
    linarith [hUends.1]
  have hDYnonneg : 0 ≤
      circlePowerR2 (normalizedCircleCenter y) Y (normalizedCircleRadius a y) -
        circlePowerR2 O Y R := by
    rw [← hlineEnds, circlePowerR2_sub_lineMap]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hs1) hDleft)
      (mul_nonneg hs0 hDright)
  have hXpower : circlePowerR2 (normalizedCircleCenter y) X
      (normalizedCircleRadius a y) ≤ 0 := by
    rw [circlePowerR2_normalized]
    change X.re ^ 2 + X.im ^ 2 - 2 * y * X.im ≤ a ^ 2 at hXmem
    linarith
  have hDXnonpos :
      circlePowerR2 (normalizedCircleCenter y) X (normalizedCircleRadius a y) -
        circlePowerR2 O X R ≤ 0 := by
    linarith
  have hDQneg :
      circlePowerR2 (normalizedCircleCenter y) Q (normalizedCircleRadius a y) -
        circlePowerR2 O Q R < 0 := by
    linarith
  have hDYneg :
      circlePowerR2 (normalizedCircleCenter y) Y (normalizedCircleRadius a y) -
        circlePowerR2 O Y R < 0 := by
    rw [show Y = (AffineMap.lineMap Q X) t by rfl,
      circlePowerR2_sub_lineMap]
    exact add_neg_of_neg_of_nonpos
      (mul_neg_of_pos_of_neg (sub_pos.mpr htlt) hDQneg)
      (mul_nonpos_of_nonneg_of_nonpos htpos.le hDXnonpos)
  exact (not_lt_of_ge hDYnonneg) hDYneg

/-- Circle power is unchanged by passage to canonical edge coordinates. -/
theorem circlePowerR2_edgeCoordinates {A B O X : ℂ} (hAB : A ≠ B) (R : ℝ) :
    circlePowerR2 (edgeCoordinates A B O) (edgeCoordinates A B X) R =
      circlePowerR2 O X R := by
  have h := circlePowerR2_directIsometry (norm_chordUnit hAB) (chordMidpoint A B)
    (edgeCoordinates A B O) (edgeCoordinates A B X) R
  simpa [directIsometryR2_edgeCoordinates hAB] using h.symm

/-- The canonical edge-circle power becomes normalized circle power in edge
coordinates. -/
theorem circlePowerR2_edgeCircleCenter_edgeCoordinates
    {A B X : ℂ} (hAB : A ≠ B) (y : ℝ) :
    circlePowerR2 (normalizedCircleCenter y) (edgeCoordinates A B X)
        (normalizedCircleRadius (chordHalfLength A B) y) =
      circlePowerR2 (edgeCircleCenter A B y) X
        (normalizedCircleRadius (chordHalfLength A B) y) := by
  have h := circlePowerR2_directIsometry (norm_chordUnit hAB) (chordMidpoint A B)
    (normalizedCircleCenter y) (edgeCoordinates A B X)
    (normalizedCircleRadius (chordHalfLength A B) y)
  simpa [edgeCircleCenter, transportedCircleCenter,
    directIsometryR2_edgeCoordinates hAB] using h.symm

/-- Membership in the interior-side edge half-plane is nonnegative height in
canonical edge coordinates. -/
theorem mem_edgeHalfPlane_iff_edgeCoordinates_im_nonneg
    {A B X : ℂ} (hAB : A ≠ B) :
    X ∈ edgeHalfPlane A B ↔ 0 ≤ (edgeCoordinates A B X).im := by
  constructor
  · intro hmem
    unfold edgeHalfPlane transportedEdgeHalfPlane directIsometryImage at hmem
    rcases hmem with ⟨z, hz, hzX⟩
    have hz_eq : z = edgeCoordinates A B X := by
      apply directIsometryR2_injective (norm_chordUnit hAB) (chordMidpoint A B)
      rw [hzX, directIsometryR2_edgeCoordinates hAB]
    simpa [normalizedEdgeHalfPlane, ← hz_eq] using hz
  · intro him
    unfold edgeHalfPlane transportedEdgeHalfPlane directIsometryImage
    exact ⟨edgeCoordinates A B X, him,
      directIsometryR2_edgeCoordinates hAB X⟩

/-- The canonical interior-side edge half-plane is equivalently the
nonnegative oriented-area side of the edge. -/
theorem mem_edgeHalfPlane_iff_crossR2_nonneg
    {A B X : ℂ} (hAB : A ≠ B) :
    X ∈ edgeHalfPlane A B ↔ 0 ≤ Gluck.Discrete.crossR2 A B X := by
  rw [mem_edgeHalfPlane_iff_edgeCoordinates_im_nonneg hAB,
    ← crossR2_edgeCoordinates hAB X, crossR2_normalized]
  exact (mul_nonneg_iff_of_pos_left
    (mul_pos (by norm_num) (chordHalfLength_pos hAB))).symm

/-- Edge-coordinate form of the two-circle contact localization theorem.

If a disk `W` contains both endpoints of `A → B`, and a point `Q` on
`∂W` lies strictly inside a coaxial edge disk on the positive side, then
every point where `∂W` meets that edge disk lies in `edgeHalfPlane A B`. -/
theorem circleBoundary_mem_edgeHalfPlane_of_mem_edgeClosedDisk
    {A B O Q X : ℂ} {y R : ℝ}
    (hAB : A ≠ B)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hQint : circlePowerR2 (edgeCircleCenter A B y) Q
      (normalizedCircleRadius (chordHalfLength A B) y) < 0)
    (hQboundary : circlePowerR2 O Q R = 0)
    (hA : circlePowerR2 O A R ≤ 0)
    (hB : circlePowerR2 O B R ≤ 0)
    (hXboundary : circlePowerR2 O X R = 0)
    (hXmem : X ∈ edgeClosedDisk A B y) :
    X ∈ edgeHalfPlane A B := by
  apply (mem_edgeHalfPlane_iff_edgeCoordinates_im_nonneg hAB).mpr
  apply normalized_circleBoundary_mem_closedDisk_im_nonneg
    (a := chordHalfLength A B) (y := y) (R := R)
    (O := edgeCoordinates A B O) (Q := edgeCoordinates A B Q)
    (X := edgeCoordinates A B X)
  · exact chordHalfLength_pos hAB
  · exact (crossR2_pos_iff_edgeCoordinates_im_pos hAB Q).mp hQcross
  · rwa [circlePowerR2_edgeCircleCenter_edgeCoordinates hAB]
  · rwa [circlePowerR2_edgeCoordinates hAB]
  · have hA' :
        circlePowerR2 (edgeCoordinates A B O) (edgeCoordinates A B A) R ≤ 0 := by
      rwa [circlePowerR2_edgeCoordinates hAB]
    simpa [(edgeCoordinates_endpoints hAB).1] using hA'
  · have hB' :
        circlePowerR2 (edgeCoordinates A B O) (edgeCoordinates A B B) R ≤ 0 := by
      rwa [circlePowerR2_edgeCoordinates hAB]
    simpa [(edgeCoordinates_endpoints hAB).2] using hB'
  · rwa [circlePowerR2_edgeCoordinates hAB]
  · exact edgeCoordinates_mem_normalizedClosedDisk_of_mem_edgeClosedDisk hAB hXmem

/-- Metric circle incidence implies zero circle power. -/
theorem circlePowerR2_eq_zero_of_dist_eq {O X : ℂ} {R : ℝ}
    (h : dist O X = R) : circlePowerR2 O X R = 0 := by
  have hR : 0 ≤ R := by rw [← h]; positivity
  apply (EuclideanGeometry.Sphere.power_eq_zero_iff_mem_sphere hR).mpr
  exact EuclideanGeometry.mem_sphere'.mpr h

/-- Metric membership in a disk of nonnegative radius implies nonpositive
circle power. -/
theorem circlePowerR2_nonpos_of_dist_le {O X : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (h : dist O X ≤ R) : circlePowerR2 O X R ≤ 0 := by
  apply (EuclideanGeometry.Sphere.power_nonpos_iff_dist_center_le_radius hR).mpr
  simpa [dist_comm] using h

/-- Strict metric membership in a disk of nonnegative radius implies negative
circle power. -/
theorem circlePowerR2_neg_of_dist_lt {O X : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (h : dist O X < R) : circlePowerR2 O X R < 0 := by
  apply (EuclideanGeometry.Sphere.power_neg_iff_dist_center_lt_radius hR).mpr
  simpa [dist_comm] using h

/-- Metric membership in the closed exterior of a nonnegative-radius disk
implies nonnegative circle power. -/
theorem circlePowerR2_nonneg_of_radius_le_dist {O X : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (h : R ≤ dist O X) : 0 ≤ circlePowerR2 O X R := by
  apply (EuclideanGeometry.Sphere.power_nonneg_iff_radius_le_dist_center hR).mpr
  simpa [dist_comm] using h

/-- Strict metric exterior membership for a nonnegative-radius disk implies
positive circle power. -/
theorem circlePowerR2_pos_of_radius_lt_dist {O X : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (h : R < dist O X) : 0 < circlePowerR2 O X R := by
  apply (EuclideanGeometry.Sphere.power_pos_iff_radius_lt_dist_center hR).mpr
  simpa [dist_comm] using h

/-- Metric, disk-language form of circle-contact localization.  This is the
reusable form consumed by the finite boundary-contact arguments in
Dahlberg's Lemmas 4 and 6. -/
theorem circleContact_mem_edgeHalfPlane_of_mem_edgeClosedDisk
    {A B O Q X : ℂ} {y R : ℝ}
    (hAB : A ≠ B)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hQint : dist (edgeCircleCenter A B y) Q <
      normalizedCircleRadius (chordHalfLength A B) y)
    (hR : 0 ≤ R)
    (hQboundary : dist O Q = R)
    (hA : InClosedDiskR2 O R A)
    (hB : InClosedDiskR2 O R B)
    (hXboundary : dist O X = R)
    (hXmem : X ∈ edgeClosedDisk A B y) :
    X ∈ edgeHalfPlane A B := by
  apply circleBoundary_mem_edgeHalfPlane_of_mem_edgeClosedDisk hAB hQcross
  · exact circlePowerR2_neg_of_dist_lt (Real.sqrt_nonneg _) hQint
  · exact circlePowerR2_eq_zero_of_dist_eq hQboundary
  · exact circlePowerR2_nonpos_of_dist_le hR (Metric.mem_closedBall'.mp hA)
  · exact circlePowerR2_nonpos_of_dist_le hR (Metric.mem_closedBall'.mp hB)
  · exact circlePowerR2_eq_zero_of_dist_eq hXboundary
  · exact hXmem

/-- Finite contact-set form of the containing-disk localization in Dahlberg
§3 Lemma 4.  If the contact chord of an old containing disk cuts out an
index envelope `E`, every contact of a new containing disk through a vertex
strictly inside the old disk belongs to `E`. -/
theorem circleContactSet_subset_of_containingDisk_chord_localization
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {a b q : ZMod n} {E : Finset (ZMod n)} {y : ℝ}
    (hAB : v a ≠ v b)
    (hqcross : 0 < Gluck.Discrete.crossR2 (v a) (v b) (v q))
    (hqU : dist (edgeCircleCenter (v a) (v b) y) (v q) <
      normalizedCircleRadius (chordHalfLength (v a) (v b)) y)
    (hUcontains : ∀ k : ZMod n,
      v k ∈ edgeClosedDisk (v a) (v b) y)
    (W : DahlbergContainingThreeContactDiskR2 v)
    (hqW : q ∈ circleContactSet v W.center W.radius)
    (hside : ∀ k : ZMod n,
      v k ∈ edgeHalfPlane (v a) (v b) → k ∈ E) :
    circleContactSet v W.center W.radius ⊆ E := by
  intro x hx
  apply hside x
  apply circleContact_mem_edgeHalfPlane_of_mem_edgeClosedDisk
    hAB hqcross hqU W.radius_pos.le
  · exact mem_circleContactSet.mp hqW
  · exact W.contains a
  · exact W.contains b
  · exact mem_circleContactSet.mp hx
  · exact hUcontains x

/-- Dahlberg Lemma 4 after packaging the old and new members of `F`.  The old
circle is automatically rewritten in the coaxial family of its two gap
endpoints; only the convex cyclic-order facts for that chord remain as
explicit hypotheses. -/
theorem circleContactSet_subset_of_containingDisk_gap
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {a b q : ZMod n} {E : Finset (ZMod n)}
    (U W : DahlbergContainingThreeContactDiskR2 v)
    (haU : a ∈ circleContactSet v U.center U.radius)
    (hbU : b ∈ circleContactSet v U.center U.radius)
    (hqNotU : q ∉ circleContactSet v U.center U.radius)
    (hqW : q ∈ circleContactSet v W.center W.radius)
    (hAB : v a ≠ v b)
    (hnocol : ∀ c : ZMod n,
      c ∈ circleContactSet v U.center U.radius → c ≠ a → c ≠ b →
        Gluck.Discrete.crossR2 (v a) (v b) (v c) ≠ 0)
    (hqcross : 0 < Gluck.Discrete.crossR2 (v a) (v b) (v q))
    (hside : ∀ k : ZMod n,
      v k ∈ edgeHalfPlane (v a) (v b) → k ∈ E) :
    circleContactSet v W.center W.radius ⊆ E := by
  obtain ⟨c, _hc, _hca, _hcb, hcenter, hradius⟩ :=
    exists_contact_edgeCircle_parameter hAB U.radius_pos U.three_contacts
      haU hbU hnocol
  let y := edgeCircumcenterParameter (v a) (v b) (v c)
  have hUcontains : ∀ k : ZMod n,
      v k ∈ edgeClosedDisk (v a) (v b) y := by
    intro k
    apply (mem_edgeClosedDisk_iff_dist_le hAB y).mpr
    rw [← hcenter, ← hradius]
    exact Metric.mem_closedBall'.mp (U.contains k)
  have hqdist : dist U.center (v q) < U.radius :=
    lt_of_le_of_ne (Metric.mem_closedBall'.mp (U.contains q))
      (fun h => hqNotU (mem_circleContactSet.mpr h))
  have hqU : dist (edgeCircleCenter (v a) (v b) y) (v q) <
      normalizedCircleRadius (chordHalfLength (v a) (v b)) y := by
    rw [show edgeCircleCenter (v a) (v b) y = U.center by
        simpa [y] using hcenter.symm,
      show normalizedCircleRadius (chordHalfLength (v a) (v b)) y = U.radius by
        simpa [y] using hradius.symm]
    exact hqdist
  exact circleContactSet_subset_of_containingDisk_chord_localization
    hAB hqcross hqU hUcontains W hqW hside

/-- Finite contact-set form of the interior-missing localization in Dahlberg
§3 Lemma 6.  The only polygon-specific input left explicit is the strict
convex chord-crossing fact for a purported contact outside `E`; the circle
geometry is discharged by `circleExterior_chord_crossing_false`. -/
theorem circleContactSet_subset_of_missingDisk_chord_localization
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {a b q : ZMod n} {E : Finset (ZMod n)}
    (U W : DahlbergInteriorMissingThreeContactDiskR2 v)
    (haU : a ∈ circleContactSet v U.center U.radius)
    (hbU : b ∈ circleContactSet v U.center U.radius)
    (hqNotU : q ∉ circleContactSet v U.center U.radius)
    (hqW : q ∈ circleContactSet v W.center W.radius)
    (hcrossing : ∀ x : ZMod n,
      x ∈ circleContactSet v W.center W.radius → x ∉ E →
      ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1,
        (AffineMap.lineMap (v q) (v x)) t =
          (AffineMap.lineMap (v a) (v b)) s) :
    circleContactSet v W.center W.radius ⊆ E := by
  intro x hxW
  by_contra hxE
  obtain ⟨t, ht, s, hs, hline⟩ := hcrossing x hxW hxE
  apply circleExterior_chord_crossing_false ht hs hline
  · exact circlePowerR2_eq_zero_of_dist_eq (mem_circleContactSet.mp haU)
  · exact circlePowerR2_eq_zero_of_dist_eq (mem_circleContactSet.mp hbU)
  · exact circlePowerR2_nonneg_of_radius_le_dist W.radius_pos.le (W.misses a)
  · exact circlePowerR2_nonneg_of_radius_le_dist W.radius_pos.le (W.misses b)
  · apply circlePowerR2_pos_of_radius_lt_dist U.radius_pos.le
    exact lt_of_le_of_ne (U.misses q)
      (fun h => hqNotU (mem_circleContactSet.mpr h.symm))
  · exact circlePowerR2_eq_zero_of_dist_eq (mem_circleContactSet.mp hqW)
  · exact circlePowerR2_nonneg_of_radius_le_dist U.radius_pos.le (U.misses x)
  · exact circlePowerR2_eq_zero_of_dist_eq (mem_circleContactSet.mp hxW)

/-- Cut-coordinate form of Dahlberg Lemma 4.  Under the isolated cyclic chord
geometry, replacing a containing disk through a vertex in an internal gap
forces all new contacts into the endpoint-closed gap. -/
theorem circleContactSet_subset_of_containingDisk_cutGap
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hgeom : StrictConvexCyclicChordGeometry v)
    (U W : DahlbergContainingThreeContactDiskR2 v)
    (c : ZMod n) {p k q : ℕ}
    (hpk : p < k) (hkq : k < q) (hqn : q < n)
    (hpU : Gluck.cyclicLift c p ∈ circleContactSet v U.center U.radius)
    (hqU : Gluck.cyclicLift c q ∈ circleContactSet v U.center U.radius)
    (hkNotU : Gluck.cyclicLift c k ∉ circleContactSet v U.center U.radius)
    (hkW : Gluck.cyclicLift c k ∈ circleContactSet v W.center W.radius) :
    circleContactSet v W.center W.radius ⊆
      Gluck.mapCut c (Finset.Icc p q) := by
  have hgap := hgeom.gap c p k q hpk hkq hqn
  let a := Gluck.cyclicLift c q
  let b := Gluck.cyclicLift c p
  let z := Gluck.cyclicLift c k
  let E := Gluck.mapCut c (Finset.Icc p q)
  have habIndex : a ≠ b := by
    intro h
    have hcast : (q : ZMod n) = (p : ZMod n) := by
      exact add_left_cancel h
    have hmod : q ≡ p [MOD n] :=
      (ZMod.natCast_eq_natCast_iff q p n).mp hcast
    exact (Nat.ne_of_gt (lt_trans hpk hkq))
      (hmod.eq_of_lt_of_lt hqn (lt_trans (lt_trans hpk hkq) hqn))
  apply circleContactSet_subset_of_containingDisk_gap U W hqU hpU hkNotU hkW
    hgap.1
  · intro d hdU hda hdb
    exact hgeom.noncollinear a b d habIndex hda hdb
  · exact hgap.2.1
  · intro x hx
    exact hgap.2.2.1 x ((mem_edgeHalfPlane_iff_crossR2_nonneg hgap.1).mp hx)

/-- Cut-coordinate form of Dahlberg Lemma 6.  The exterior-circle power
argument and strict chord crossing force all contacts of the replacement
interior-missing disk into the endpoint-closed gap. -/
theorem circleContactSet_subset_of_missingDisk_cutGap
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hgeom : StrictConvexCyclicChordGeometry v)
    (U W : DahlbergInteriorMissingThreeContactDiskR2 v)
    (c : ZMod n) {p k q : ℕ}
    (hpk : p < k) (hkq : k < q) (hqn : q < n)
    (hpU : Gluck.cyclicLift c p ∈ circleContactSet v U.center U.radius)
    (hqU : Gluck.cyclicLift c q ∈ circleContactSet v U.center U.radius)
    (hkNotU : Gluck.cyclicLift c k ∉ circleContactSet v U.center U.radius)
    (hkW : Gluck.cyclicLift c k ∈ circleContactSet v W.center W.radius) :
    circleContactSet v W.center W.radius ⊆
      Gluck.mapCut c (Finset.Icc p q) := by
  have hgap := hgeom.gap c p k q hpk hkq hqn
  apply circleContactSet_subset_of_missingDisk_chord_localization
    U W hqU hpU hkNotU hkW
  intro x hxW hxE
  exact hgap.2.2.2 x hxE

/-- The endpoint hull of a finite natural contact set, with the empty set
sent to the empty hull. -/
noncomputable def finiteNatHull (C : Finset ℕ) : Finset ℕ :=
  if hC : C.Nonempty then Finset.Icc (C.min' hC) (C.max' hC) else ∅

/-- Strong generic well-founded engine behind Dahlberg's Lemmas 5 and 7.
Starting from an explicit noncontact cut, it returns a terminal cyclic contact
interval and remembers that every terminal contact remains inside the initial
natural contact hull. -/
theorem exists_cyclicInterval_contacts_subset_hull_of_cutGap_shrink
    {n : ℕ} [NeZero n] {Disk : Type*}
    (contacts : Disk → Finset (ZMod n))
    (hthree : ∀ U : Disk, 3 ≤ (contacts U).card)
    (hchoose : ∀ i : ZMod n, ∃ W : Disk, i ∈ contacts W)
    (hlocalize : ∀ (U W : Disk) (c : ZMod n) {p k q : ℕ},
      p < k → k < q → q < n →
      Gluck.cyclicLift c p ∈ contacts U →
      Gluck.cyclicLift c q ∈ contacts U →
      Gluck.cyclicLift c k ∉ contacts U →
      Gluck.cyclicLift c k ∈ contacts W →
      contacts W ⊆ Gluck.mapCut c (Finset.Icc p q))
    (c₀ : ZMod n) (U₀ : Disk) (hc₀ : c₀ ∉ contacts U₀) :
    ∃ U : Disk,
      Gluck.IsCyclicInterval (contacts U) ∧
      contacts U ⊆ Gluck.mapCut c₀
        (finiteNatHull (Gluck.cutFinset c₀ (contacts U₀))) := by
  classical
  let P : Finset ℕ → Prop := fun H =>
    ∀ (c : ZMod n) (U : Disk)
      (hc : c ∉ contacts U)
      (hC : (Gluck.cutFinset c (contacts U)).Nonempty),
      H = finiteNatHull (Gluck.cutFinset c (contacts U)) →
      ∃ W : Disk,
        Gluck.IsCyclicInterval (contacts W) ∧ contacts W ⊆ Gluck.mapCut c H
  have hP : ∀ H : Finset ℕ, P H := by
    intro H
    refine Finset.strongInductionOn H ?_
    intro H ih c U hc hC hH
    let C := Gluck.cutFinset c (contacts U)
    have hCcard : 3 ≤ C.card := by
      dsimp [C]
      rw [Gluck.card_cutFinset]
      exact hthree U
    have hHform : H = Finset.Icc (C.min' hC) (C.max' hC) := by
      rw [hH]
      exact dif_pos hC
    by_cases hinterval : Gluck.IsNatInterval C
    · refine ⟨U, Gluck.isCyclicInterval_of_isNatInterval_cutFinset c hinterval, ?_⟩
      have hHrange : H ⊆ Finset.range n := by
        rw [hHform]
        intro r hr
        rw [Finset.mem_Icc] at hr
        exact Finset.mem_range.mpr
          (lt_of_le_of_lt hr.2 (Gluck.mem_cutFinset.mp (C.max'_mem hC)).1)
      apply (Gluck.cutFinset_subset_iff c hHrange).mp
      intro r hrC
      rw [hHform, Finset.mem_Icc]
      exact ⟨C.min'_le r hrC, C.le_max' r hrC⟩
    · obtain ⟨p, q, hpC, hqC, hpq, hgap, hpqH⟩ :=
        Gluck.exists_internal_gap_with_strict_hull hC hCcard hinterval
      have hpqH' : Finset.Icc p q ⊂ H := by
        simpa [hHform] using hpqH
      let k := p + 1
      have hpk : p < k := Nat.lt_succ_self p
      have hkq : k < q := by simpa [k] using hpq
      have hkNotC : k ∉ C := hgap k hpk hkq
      have hqn : q < n := (Gluck.mem_cutFinset.mp hqC).1
      have hpU : Gluck.cyclicLift c p ∈ contacts U :=
        (Gluck.mem_cutFinset.mp hpC).2
      have hqU : Gluck.cyclicLift c q ∈ contacts U :=
        (Gluck.mem_cutFinset.mp hqC).2
      have hkNotU : Gluck.cyclicLift c k ∉ contacts U := by
        intro hkU
        exact hkNotC (Gluck.mem_cutFinset.mpr ⟨lt_trans hkq hqn, hkU⟩)
      obtain ⟨W, hkW⟩ := hchoose (Gluck.cyclicLift c k)
      have hWsub : contacts W ⊆ Gluck.mapCut c (Finset.Icc p q) :=
        hlocalize U W c hpk hkq hqn hpU hqU hkNotU hkW
      have hIr : Finset.Icc p q ⊆ Finset.range n := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        exact Finset.mem_range.mpr (lt_of_le_of_lt hr.2 hqn)
      have hcutWsub : Gluck.cutFinset c (contacts W) ⊆ Finset.Icc p q :=
        (Gluck.cutFinset_subset_iff c hIr).mpr hWsub
      have hp0 : 0 < p := by
        by_contra hpnonpos
        have hpzero : p = 0 := Nat.eq_zero_of_not_pos hpnonpos
        apply hc
        simpa [Gluck.cyclicLift, hpzero] using hpU
      have hcW : c ∉ contacts W := by
        intro hcW
        have hzeroCut : 0 ∈ Gluck.cutFinset c (contacts W) := by
          exact Gluck.mem_cutFinset.mpr ⟨Nat.pos_of_ne_zero (NeZero.ne n), by
            simpa [Gluck.cyclicLift] using hcW⟩
        have hzeroI := Finset.mem_Icc.mp (hcutWsub hzeroCut)
        omega
      have hCW : (Gluck.cutFinset c (contacts W)).Nonempty := by
        rw [Gluck.cutFinset_nonempty_iff]
        exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hthree W))
      let CW := Gluck.cutFinset c (contacts W)
      let HW := Finset.Icc (CW.min' hCW) (CW.max' hCW)
      have hHWsubI : HW ⊆ Finset.Icc p q := by
        apply Finset.Icc_subset_Icc
        · exact (Finset.mem_Icc.mp (hcutWsub (CW.min'_mem hCW))).1
        · exact (Finset.mem_Icc.mp (hcutWsub (CW.max'_mem hCW))).2
      have hHWH : HW ⊂ H :=
        Finset.ssubset_of_subset_of_ssubset hHWsubI hpqH'
      have hHWhull : HW = finiteNatHull CW := by
        change Finset.Icc (CW.min' hCW) (CW.max' hCW) = finiteNatHull CW
        unfold finiteNatHull
        rw [dif_pos hCW]
      obtain ⟨Z, hZinterval, hZsub⟩ := ih HW hHWH c W hcW hCW hHWhull
      refine ⟨Z, hZinterval, ?_⟩
      exact hZsub.trans (by
        simpa [Gluck.mapCut] using
          (Finset.image_mono (Gluck.cyclicLift c) hHWH.1))
  have hC₀ : (Gluck.cutFinset c₀ (contacts U₀)).Nonempty := by
    rw [Gluck.cutFinset_nonempty_iff]
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hthree U₀))
  simpa using hP _ c₀ U₀ hc₀ hC₀ rfl

/-- Unconstrained terminal form of the generic shrink engine. -/
theorem exists_cyclicInterval_contacts_of_cutGap_shrink
    {n : ℕ} [NeZero n] {Disk : Type*}
    (contacts : Disk → Finset (ZMod n))
    (hthree : ∀ U : Disk, 3 ≤ (contacts U).card)
    (hproper : ∀ U : Disk, contacts U ≠ Finset.univ)
    (hchoose : ∀ i : ZMod n, ∃ W : Disk, i ∈ contacts W)
    (hlocalize : ∀ (U W : Disk) (c : ZMod n) {p k q : ℕ},
      p < k → k < q → q < n →
      Gluck.cyclicLift c p ∈ contacts U →
      Gluck.cyclicLift c q ∈ contacts U →
      Gluck.cyclicLift c k ∉ contacts U →
      Gluck.cyclicLift c k ∈ contacts W →
      contacts W ⊆ Gluck.mapCut c (Finset.Icc p q))
    (U₀ : Disk) :
    ∃ U : Disk, Gluck.IsCyclicInterval (contacts U) := by
  obtain ⟨c, hc⟩ := Gluck.exists_not_mem_of_ne_univ (hproper U₀)
  obtain ⟨U, hinterval, _hsub⟩ :=
    exists_cyclicInterval_contacts_subset_hull_of_cutGap_shrink
      contacts hthree hchoose hlocalize c U₀ hc
  exact ⟨U, hinterval⟩

/-- Localized terminal form of the generic cut-gap descent.  Starting from
one explicit complementary gap of `U`, choose a disk through an interior
noncontact and run the well-founded descent without ever leaving the closed
gap.  The positive lower endpoint ensures that the cut base is outside every
subsequent contact set. -/
theorem exists_cyclicInterval_contacts_subset_cutGap_of_shrink
    {n : ℕ} [NeZero n] {Disk : Type*}
    (contacts : Disk → Finset (ZMod n))
    (hthree : ∀ U : Disk, 3 ≤ (contacts U).card)
    (hchoose : ∀ i : ZMod n, ∃ W : Disk, i ∈ contacts W)
    (hlocalize : ∀ (U W : Disk) (c : ZMod n) {p k q : ℕ},
      p < k → k < q → q < n →
      Gluck.cyclicLift c p ∈ contacts U →
      Gluck.cyclicLift c q ∈ contacts U →
      Gluck.cyclicLift c k ∉ contacts U →
      Gluck.cyclicLift c k ∈ contacts W →
      contacts W ⊆ Gluck.mapCut c (Finset.Icc p q))
    (U : Disk) (c : ZMod n) {p k q : ℕ}
    (hp0 : 0 < p) (hpk : p < k) (hkq : k < q) (hqn : q < n)
    (hpU : Gluck.cyclicLift c p ∈ contacts U)
    (hqU : Gluck.cyclicLift c q ∈ contacts U)
    (hkNotU : Gluck.cyclicLift c k ∉ contacts U) :
    ∃ W : Disk,
      Gluck.IsCyclicInterval (contacts W) ∧
      contacts W ⊆ Gluck.mapCut c (Finset.Icc p q) := by
  classical
  obtain ⟨W, hkW⟩ := hchoose (Gluck.cyclicLift c k)
  have hWsub : contacts W ⊆ Gluck.mapCut c (Finset.Icc p q) :=
    hlocalize U W c hpk hkq hqn hpU hqU hkNotU hkW
  have hIr : Finset.Icc p q ⊆ Finset.range n := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    exact Finset.mem_range.mpr (lt_of_le_of_lt hr.2 hqn)
  have hcutWsub : Gluck.cutFinset c (contacts W) ⊆ Finset.Icc p q :=
    (Gluck.cutFinset_subset_iff c hIr).mpr hWsub
  have hcW : c ∉ contacts W := by
    intro hcW
    have hzeroCut : 0 ∈ Gluck.cutFinset c (contacts W) := by
      exact Gluck.mem_cutFinset.mpr
        ⟨Nat.pos_of_ne_zero (NeZero.ne n), by simpa [Gluck.cyclicLift] using hcW⟩
    have hzeroI := Finset.mem_Icc.mp (hcutWsub hzeroCut)
    omega
  obtain ⟨Z, hZinterval, hZsub⟩ :=
    exists_cyclicInterval_contacts_subset_hull_of_cutGap_shrink
      contacts hthree hchoose hlocalize c W hcW
  have hCW : (Gluck.cutFinset c (contacts W)).Nonempty := by
    rw [Gluck.cutFinset_nonempty_iff]
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hthree W))
  have hHullSub :
      finiteNatHull (Gluck.cutFinset c (contacts W)) ⊆ Finset.Icc p q := by
    unfold finiteNatHull
    rw [dif_pos hCW]
    apply Finset.Icc_subset_Icc
    · exact (Finset.mem_Icc.mp
        (hcutWsub ((Gluck.cutFinset c (contacts W)).min'_mem hCW))).1
    · exact (Finset.mem_Icc.mp
        (hcutWsub ((Gluck.cutFinset c (contacts W)).max'_mem hCW))).2
  refine ⟨Z, hZinterval, hZsub.trans ?_⟩
  exact Finset.image_mono (Gluck.cyclicLift c) hHullSub

/-- The generic descent produces two terminal disks with different contact
sets.  First obtain any terminal contact interval.  Three consecutive
contacts let us cut at its middle contact; the proper complementary gap is
then strictly separated from that basepoint.  Descending inside that gap
produces a second terminal contact interval which omits the basepoint and is
therefore different from the first one.

This is the finite common core of Dahlberg's Lemmas 5 and 7. -/
theorem exists_two_cyclicInterval_contacts_ne_of_cutGap_shrink
    {n : ℕ} [NeZero n] {Disk : Type*}
    (contacts : Disk → Finset (ZMod n))
    (hthree : ∀ U : Disk, 3 ≤ (contacts U).card)
    (hproper : ∀ U : Disk, contacts U ≠ Finset.univ)
    (hchoose : ∀ i : ZMod n, ∃ W : Disk, i ∈ contacts W)
    (hlocalize : ∀ (U W : Disk) (c : ZMod n) {p k q : ℕ},
      p < k → k < q → q < n →
      Gluck.cyclicLift c p ∈ contacts U →
      Gluck.cyclicLift c q ∈ contacts U →
      Gluck.cyclicLift c k ∉ contacts U →
      Gluck.cyclicLift c k ∈ contacts W →
      contacts W ⊆ Gluck.mapCut c (Finset.Icc p q))
    (U₀ : Disk) :
    ∃ U W : Disk,
      Gluck.IsCyclicInterval (contacts U) ∧
      Gluck.IsCyclicInterval (contacts W) ∧
      contacts U ≠ contacts W := by
  classical
  obtain ⟨U, hUinterval⟩ :=
    exists_cyclicInterval_contacts_of_cutGap_shrink
      contacts hthree hproper hchoose hlocalize U₀
  obtain ⟨c, p, k, q, hcU, hp0, hpk, hkq, hqn, hpU, hqU, hkNotU⟩ :=
    hUinterval.exists_cutGap_in_complement (hthree U) (hproper U)
  obtain ⟨W, hWinterval, hWsub⟩ :=
    exists_cyclicInterval_contacts_subset_cutGap_of_shrink
      contacts hthree hchoose hlocalize U c hp0 hpk hkq hqn hpU hqU hkNotU
  have hIr : Finset.Icc p q ⊆ Finset.range n := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    exact Finset.mem_range.mpr (lt_of_le_of_lt hr.2 hqn)
  have hcNotW : c ∉ contacts W := by
    intro hcW
    have hzeroCut : 0 ∈ Gluck.cutFinset c (contacts W) := by
      exact Gluck.mem_cutFinset.mpr
        ⟨Nat.pos_of_ne_zero (NeZero.ne n), by simpa [Gluck.cyclicLift] using hcW⟩
    have hcutWsub : Gluck.cutFinset c (contacts W) ⊆ Finset.Icc p q :=
      (Gluck.cutFinset_subset_iff c hIr).mpr hWsub
    have hzeroI := Finset.mem_Icc.mp (hcutWsub hzeroCut)
    omega
  refine ⟨U, W, hUinterval, hWinterval, ?_⟩
  intro hUW
  exact hcNotW (hUW ▸ hcU)

/-- Arbitrary-edge form of the normalized radius comparison behind Dahlberg
Lemma 10. -/
theorem edgeCircleRadius_le_of_mem_edgeClosedDisk {A B C : ℂ} {yΔ : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hyρ : 0 ≤ edgeCircumcenterParameter A B C)
    (hmem : C ∈ edgeClosedDisk A B yΔ) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) ≤
      normalizedCircleRadius (chordHalfLength A B) yΔ := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hρ := circlePowerR2_normalized_parameter
    (a := chordHalfLength A B) (z := edgeCoordinates A B C) hz.ne'
  change circlePowerR2 (normalizedCircleCenter (edgeCircumcenterParameter A B C))
    (edgeCoordinates A B C)
    (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) = 0 at hρ
  have hmem' := edgeCoordinates_mem_normalizedClosedDisk_of_mem_edgeClosedDisk hAB hmem
  exact normalizedCircleRadius_le_of_mem_closedDisk hyρ hz hρ hmem'

/-- Arbitrary-edge exterior form of the normalized radius comparison: if the
point `C` lies outside the coaxial disk with parameter `yΔ`, then that disk's
radius is no larger than the canonical circle through `A`, `B`, and `C`, on
the positive/nonnegative branch. -/
theorem edgeCircleRadius_le_of_mem_edgeClosedExterior {A B C : ℂ} {yΔ : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hyΔ : 0 ≤ yΔ)
    (hmem : C ∈ edgeClosedExterior A B yΔ) :
    normalizedCircleRadius (chordHalfLength A B) yΔ ≤
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) := by
  have hz := (crossR2_pos_iff_edgeCoordinates_im_pos hAB C).mp hcross
  have hρ := circlePowerR2_normalized_parameter
    (a := chordHalfLength A B) (z := edgeCoordinates A B C) hz.ne'
  change circlePowerR2 (normalizedCircleCenter (edgeCircumcenterParameter A B C))
    (edgeCoordinates A B C)
    (normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C)) = 0 at hρ
  have hmem' :=
    edgeCoordinates_mem_normalizedClosedExterior_of_mem_edgeClosedExterior hAB hmem
  exact normalizedCircleRadius_le_of_mem_closedExterior hyΔ hz hρ hmem'

/-- Regular point-edge form of the radius comparison behind Dahlberg Lemma 10. -/
theorem edgeRegularCircleRadius_le_of_mem_edgeClosedDisk {A B C O : ℂ} {R yΔ : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hcircle : CircumcircleR2 C A B O R) (hcone : InVertexCone C A B O)
    (hmem : C ∈ edgeClosedDisk A B yΔ) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) ≤
      normalizedCircleRadius (chordHalfLength A B) yΔ := by
  have hyρ := edgeCircumcenterParameter_nonneg_of_regular hAB hcross hcircle hcone
  exact edgeCircleRadius_le_of_mem_edgeClosedDisk hAB hcross hyρ hmem

/-- Arbitrary-edge form of the disk-side nesting statement in Dahlberg's
Lemma 8. -/
theorem edgeUpperCap_mono (A B : ℂ) {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    edgeUpperCap A B y₁ ⊆ edgeUpperCap A B y₂ := by
  unfold edgeUpperCap
  exact transportedUpperCap_mono _ _ hy

/-- Arbitrary-edge mixed-sign part of Dahlberg Lemma 8. -/
theorem edgeDahlbergRegion_anti_of_nonpos_nonneg (A B : ℂ) {yP yQ kP kQ : ℝ}
    (hP : kP ≤ 0) (hQ : 0 ≤ kQ) :
    edgeDahlbergRegion A B yQ kQ ⊆ edgeDahlbergRegion A B yP kP := by
  unfold edgeDahlbergRegion
  exact transportedDahlbergRegion_mono _ _
    (normalizedDahlbergRegion_anti_of_nonpos_nonneg hP hQ)

/-- Arbitrary-edge positive same-sign part of Dahlberg Lemma 8. -/
theorem edgeDahlbergRegion_anti_of_positive {A B : ℂ} (hAB : A ≠ B) {yP yQ : ℝ}
    (hyP : 0 ≤ yP)
    (hκ : normalizedCircleCurvature (chordHalfLength A B) yP ≤
      normalizedCircleCurvature (chordHalfLength A B) yQ) :
    edgeDahlbergRegion A B yQ
        (normalizedCircleCurvature (chordHalfLength A B) yQ) ⊆
      edgeDahlbergRegion A B yP
        (normalizedCircleCurvature (chordHalfLength A B) yP) := by
  unfold edgeDahlbergRegion
  exact transportedDahlbergRegion_mono _ _
    (normalizedDahlbergRegion_anti_of_positive (chordHalfLength_pos hAB).ne' hyP hκ)

/-- Arbitrary-edge negative same-sign part of Dahlberg Lemma 8. -/
theorem edgeDahlbergRegion_anti_of_negative {A B : ℂ} (hAB : A ≠ B) {yP yQ : ℝ}
    (hyQ : yQ ≤ 0)
    (hκ : -normalizedCircleCurvature (chordHalfLength A B) yP ≤
      -normalizedCircleCurvature (chordHalfLength A B) yQ) :
    edgeDahlbergRegion A B yQ
        (-normalizedCircleCurvature (chordHalfLength A B) yQ) ⊆
      edgeDahlbergRegion A B yP
        (-normalizedCircleCurvature (chordHalfLength A B) yP) := by
  unfold edgeDahlbergRegion
  exact transportedDahlbergRegion_mono _ _
    (normalizedDahlbergRegion_anti_of_negative (chordHalfLength_pos hAB).ne' hyQ hκ)

/-- Point-edge mixed-sign form of Dahlberg Lemma 8. -/
theorem edgePointDahlbergRegion_anti_of_nonpos_nonneg (A B P Q : ℂ)
    (hP : Gluck.Discrete.signedMengerR2 A B P ≤ 0)
    (hQ : 0 ≤ Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  unfold edgePointDahlbergRegion
  exact edgeDahlbergRegion_anti_of_nonpos_nonneg A B hP hQ

/-- Point-edge positive same-sign form of Dahlberg Lemma 8, with Dahlberg
regularity supplying the centre-side condition for the lower-curvature point. -/
theorem edgePointDahlbergRegion_anti_of_positive {A B P Q O : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hcircleP : CircumcircleR2 P A B O R) (hconeP : InVertexCone P A B O)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rw [edgePointDahlbergRegion_eq_of_pos hAB hQcross,
    edgePointDahlbergRegion_eq_of_pos hAB hPcross]
  apply edgeDahlbergRegion_anti_of_positive hAB
  · exact edgeCircumcenterParameter_nonneg_of_regular hAB hPcross hcircleP hconeP
  · simpa [signedMengerR2_edge_parameter_of_pos hAB hPcross,
      signedMengerR2_edge_parameter_of_pos hAB hQcross] using hκ

/-- Positive same-sign nesting using right-endpoint Dahlberg regularity for the
lower-curvature point. -/
theorem edgePointDahlbergRegion_anti_of_positive_right {A B P Q O : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hcircleP : CircumcircleR2 A B P O R) (hconeP : InVertexCone A B P O)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rw [edgePointDahlbergRegion_eq_of_pos hAB hQcross,
    edgePointDahlbergRegion_eq_of_pos hAB hPcross]
  apply edgeDahlbergRegion_anti_of_positive hAB
  · exact edgeCircumcenterParameter_nonneg_of_regular_right hAB hPcross hcircleP hconeP
  · simpa [signedMengerR2_edge_parameter_of_pos hAB hPcross,
      signedMengerR2_edge_parameter_of_pos hAB hQcross] using hκ

/-- Point-edge negative same-sign form of Dahlberg Lemma 8, with Dahlberg
regularity supplying the centre-side condition for the higher-curvature point. -/
theorem edgePointDahlbergRegion_anti_of_negative {A B P Q O : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hcircleQ : CircumcircleR2 Q A B O R) (hconeQ : InVertexCone Q A B O)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rw [edgePointDahlbergRegion_eq_of_neg hAB hQcross,
    edgePointDahlbergRegion_eq_of_neg hAB hPcross]
  apply edgeDahlbergRegion_anti_of_negative hAB
  · exact edgeCircumcenterParameter_nonpos_of_regular hAB hQcross hcircleQ hconeQ
  · simpa [signedMengerR2_edge_parameter_of_neg hAB hPcross,
      signedMengerR2_edge_parameter_of_neg hAB hQcross] using hκ

/-- Negative same-sign nesting using right-endpoint Dahlberg regularity for the
higher-curvature point. -/
theorem edgePointDahlbergRegion_anti_of_negative_right {A B P Q O : ℂ} {R : ℝ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hcircleQ : CircumcircleR2 A B Q O R) (hconeQ : InVertexCone A B Q O)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rw [edgePointDahlbergRegion_eq_of_neg hAB hQcross,
    edgePointDahlbergRegion_eq_of_neg hAB hPcross]
  apply edgeDahlbergRegion_anti_of_negative hAB
  · exact edgeCircumcenterParameter_nonpos_of_regular_right hAB hQcross hcircleQ hconeQ
  · simpa [signedMengerR2_edge_parameter_of_neg hAB hPcross,
      signedMengerR2_edge_parameter_of_neg hAB hQcross] using hκ

/-- Dahlberg Lemma 8 for two locally regular points over the same oriented
edge, expressed with the actual signed Menger curvatures. -/
theorem edgePointDahlbergRegion_anti_of_regular {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt Q A B)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rcases lt_trichotomy (Gluck.Discrete.crossR2 A B P) 0 with hPneg | hPzero | hPpos
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · obtain ⟨O, R, hcircleQ, hconeQ⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero hQreg hQneg.ne
      exact edgePointDahlbergRegion_anti_of_negative hAB hPneg hQneg hcircleQ hconeQ hκ
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_eq_zero_of_cross_eq_zero hPzero
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_eq_zero_of_cross_eq_zero hQzero
      nlinarith
    · obtain ⟨O, R, hcircleP, hconeP⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPpos.ne'
      exact edgePointDahlbergRegion_anti_of_positive hAB hPpos hQpos hcircleP hconeP hκ

/-- Dahlberg Lemma 8 with right-endpoint local regularity over the same
oriented edge. This is the form supplied directly by polygon vertex regularity
for triples `(A,B,C)`. -/
theorem edgePointDahlbergRegion_anti_of_regular_right {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt A B P) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rcases lt_trichotomy (Gluck.Discrete.crossR2 A B P) 0 with hPneg | hPzero | hPpos
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · obtain ⟨O, R, hcircleQ, hconeQ⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQneg.ne
      exact edgePointDahlbergRegion_anti_of_negative_right hAB hPneg hQneg hcircleQ hconeQ hκ
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_eq_zero_of_cross_eq_zero hPzero
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_eq_zero_of_cross_eq_zero hQzero
      nlinarith
    · obtain ⟨O, R, hcircleP, hconeP⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero_right hPreg hPpos.ne'
      exact edgePointDahlbergRegion_anti_of_positive_right hAB hPpos hQpos hcircleP hconeP hκ

/-- Dahlberg Lemma 8 for the two endpoints of an oriented polygon edge. The
left endpoint supplies regularity from the preceding triple `(P,A,B)`, while
the right endpoint supplies regularity from the following triple `(A,B,Q)`. -/
theorem edgePointDahlbergRegion_anti_of_endpoint_regular {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgePointDahlbergRegion A B Q ⊆ edgePointDahlbergRegion A B P := by
  rcases lt_trichotomy (Gluck.Discrete.crossR2 A B P) 0 with hPneg | hPzero | hPpos
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · obtain ⟨O, R, hcircleQ, hconeQ⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQneg.ne
      exact edgePointDahlbergRegion_anti_of_negative_right hAB hPneg hQneg hcircleQ hconeQ hκ
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · exact (signedMengerR2_neg_of_cross_neg hAB hPneg).le
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_eq_zero_of_cross_eq_zero hPzero
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hQzero]
    · apply edgePointDahlbergRegion_anti_of_nonpos_nonneg
      · rw [signedMengerR2_eq_zero_of_cross_eq_zero hPzero]
      · exact (signedMengerR2_pos_of_cross_pos hAB hQpos).le
  · rcases lt_trichotomy (Gluck.Discrete.crossR2 A B Q) 0 with hQneg | hQzero | hQpos
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_neg_of_cross_neg hAB hQneg
      nlinarith
    · exfalso
      have hPκ := signedMengerR2_pos_of_cross_pos hAB hPpos
      have hQκ := signedMengerR2_eq_zero_of_cross_eq_zero hQzero
      nlinarith
    · obtain ⟨O, R, hcircleP, hconeP⟩ :=
        dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPpos.ne'
      exact edgePointDahlbergRegion_anti_of_positive hAB hPpos hQpos hcircleP hconeP hκ

/-- The actual signed-Menger curvature at vertex `i` is the same cyclic
orientation as the endpoint-edge curvature over edge `i → i+1` with the
previous vertex as third point. -/
theorem polygonSignedMenger_eq_edgePrev {n : ℕ} {v : ZMod n → ℂ} (i : ZMod n) :
    Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
  exact (signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))).symm

/-- The corresponding cyclic rewrite for oriented twice-area. -/
theorem polygonCross_eq_edgePrev {n : ℕ} {v : ZMod n → ℂ} (i : ZMod n) :
    Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) := by
  exact (crossR2_cycle (v (i - 1)) (v i) (v (i + 1))).symm

/-- Reversing the consecutive triple at a polygon vertex negates its oriented
twice-area. -/
theorem polygonCross_reverse_vertex {n : ℕ} {v : ZMod n → ℂ} (i : ZMod n) :
    Gluck.Discrete.crossR2 (v (i + 1)) (v i) (v (i - 1)) =
      -Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) := by
  exact crossR2_reverse (v (i - 1)) (v i) (v (i + 1))

/-- Reversing the consecutive triple at a polygon vertex negates its
signed-Menger curvature. -/
theorem polygonSignedMenger_reverse_vertex {n : ℕ} {v : ZMod n → ℂ} (i : ZMod n) :
    Gluck.Discrete.signedMengerR2 (v (i + 1)) (v i) (v (i - 1)) =
      -SignedMengerProfile v i := by
  exact signedMengerR2_reverse (v (i - 1)) (v i) (v (i + 1))

/-- The signed-Menger profile of the reversed cyclic polygon is the negated
profile of the original polygon, reindexed by `i ↦ -i`. -/
theorem SignedMengerProfile_reverseCyclicPolygon {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) :
    SignedMengerProfile (ReverseCyclicPolygon v) i =
      -SignedMengerProfile v (-i) := by
  change Gluck.Discrete.signedMengerR2
      (v (-(i - 1))) (v (-i)) (v (-(i + 1))) =
    -SignedMengerProfile v (-i)
  convert polygonSignedMenger_reverse_vertex (v := v) (-i) using 1
  abel_nf

/-- Reversing the cyclic order turns negative orientation into positive
orientation. -/
theorem positiveOrientation_reverseCyclicPolygon_of_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (horient : NegativePolygonOrientation v) :
    PositivePolygonOrientation (ReverseCyclicPolygon v) := by
  intro i
  change 0 < Gluck.Discrete.crossR2 (v (-(i - 1))) (v (-i)) (v (-(i + 1)))
  rw [show (-(i - 1) : ZMod n) = -i + 1 by abel,
    show (-(i + 1) : ZMod n) = -i - 1 by abel,
    polygonCross_reverse_vertex (v := v) (-i)]
  exact neg_pos.mpr (horient (-i))

/-- Reversing the cyclic order turns positive orientation into negative
orientation. -/
theorem negativeOrientation_reverseCyclicPolygon_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (horient : PositivePolygonOrientation v) :
    NegativePolygonOrientation (ReverseCyclicPolygon v) := by
  intro i
  change Gluck.Discrete.crossR2 (v (-(i - 1))) (v (-i)) (v (-(i + 1))) < 0
  rw [show (-(i - 1) : ZMod n) = -i + 1 by abel,
    show (-(i + 1) : ZMod n) = -i - 1 by abel,
    polygonCross_reverse_vertex (v := v) (-i)]
  exact neg_neg_of_pos (horient (-i))

/-- If the reversed cyclic polygon is positively oriented, the original is
negatively oriented. -/
theorem negativeOrientation_of_positiveOrientation_reverseCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ}
    (horient : PositivePolygonOrientation (ReverseCyclicPolygon v)) :
    NegativePolygonOrientation v := by
  intro i
  have hrev : 0 < Gluck.Discrete.crossR2 (v (i + 1)) (v i) (v (i - 1)) := by
    have h := horient (-i)
    change 0 < Gluck.Discrete.crossR2 (v (-(-i - 1))) (v (-(-i)))
      (v (-(-i + 1))) at h
    convert h using 1
    abel_nf
  rw [crossR2_reverse] at hrev
  exact neg_pos.mp hrev

/-- If the reversed cyclic polygon is negatively oriented, the original is
positively oriented. -/
theorem positiveOrientation_of_negativeOrientation_reverseCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ}
    (horient : NegativePolygonOrientation (ReverseCyclicPolygon v)) :
    PositivePolygonOrientation v := by
  intro i
  have hrev : Gluck.Discrete.crossR2 (v (i + 1)) (v i) (v (i - 1)) < 0 := by
    have h := horient (-i)
    change Gluck.Discrete.crossR2 (v (-(-i - 1))) (v (-(-i)))
      (v (-(-i + 1))) < 0 at h
    convert h using 1
    abel_nf
  rw [crossR2_reverse] at hrev
  linarith

/-- Non-strict global orientation is invariant under reversing cyclic order. -/
theorem not_strictPolygonOrientation_reverseCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ}
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) :
    ¬ (PositivePolygonOrientation (ReverseCyclicPolygon v) ∨
      NegativePolygonOrientation (ReverseCyclicPolygon v)) := by
  intro horient
  rcases horient with hpos | hneg
  · exact hnonstrict
      (Or.inr (negativeOrientation_of_positiveOrientation_reverseCyclicPolygon hpos))
  · exact hnonstrict
      (Or.inl (positiveOrientation_of_negativeOrientation_reverseCyclicPolygon hneg))

/-- Reversing a strictly positively oriented conformal-Menger triple negates
the realized curvature.  The noncollinearity hypothesis is essential because
`ConformalMenger` chooses sign by `if 0 < cross then 1 else -1`. -/
theorem conformalMenger_reverse_of_cross_pos {ε : ℝ} {A B C : ℂ} {κ : ℝ}
    (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hκ : ConformalMenger ε A B C κ) :
    ConformalMenger ε C B A (-κ) := by
  rcases hκ with ⟨O, R, hR, hA, hB, hC, hκ⟩
  refine ⟨O, R, hR, hC, hB, hA, ?_⟩
  have hrev : ¬ 0 < Gluck.Discrete.crossR2 C B A := by
    rw [crossR2_reverse]
    exact not_lt_of_gt (neg_neg_of_pos hcross)
  rw [hκ, if_pos hcross, if_neg hrev]
  ring

/-- Reversing a strictly negatively oriented conformal-Menger triple negates
the realized curvature. -/
theorem conformalMenger_reverse_of_cross_neg {ε : ℝ} {A B C : ℂ} {κ : ℝ}
    (hcross : Gluck.Discrete.crossR2 A B C < 0)
    (hκ : ConformalMenger ε A B C κ) :
    ConformalMenger ε C B A (-κ) := by
  rcases hκ with ⟨O, R, hR, hA, hB, hC, hκ⟩
  refine ⟨O, R, hR, hC, hB, hA, ?_⟩
  have hrev : 0 < Gluck.Discrete.crossR2 C B A := by
    rw [crossR2_reverse]
    exact neg_pos.mpr hcross
  rw [hκ, if_neg (not_lt_of_gt hcross), if_pos hrev]
  ring

/-- Reversing a noncollinear conformal-Menger triple negates the realized
curvature. -/
theorem conformalMenger_reverse_of_cross_ne_zero {ε : ℝ} {A B C : ℂ} {κ : ℝ}
    (hcross : Gluck.Discrete.crossR2 A B C ≠ 0)
    (hκ : ConformalMenger ε A B C κ) :
    ConformalMenger ε C B A (-κ) := by
  rcases lt_or_gt_of_ne hcross with hneg | hpos
  · exact conformalMenger_reverse_of_cross_neg hneg hκ
  · exact conformalMenger_reverse_of_cross_pos hpos hκ

/-- Reversing a positively oriented cyclic polygon negates and reverses a
space-form conformal-Menger realization. -/
theorem realizesConformalMenger_reverseCyclicPolygon_of_positiveOrientation
    {n : ℕ} {ε : ℝ} {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (horient : PositivePolygonOrientation v)
    (hκ : RealizesConformalMenger ε v κ) :
    RealizesConformalMenger ε (ReverseCyclicPolygon v) (fun i => -κ (-i)) := by
  intro i
  change ConformalMenger ε (v (-(i - 1))) (v (-i)) (v (-(i + 1))) (-κ (-i))
  convert conformalMenger_reverse_of_cross_pos (horient (-i)) (hκ (-i)) using 1
  · congr 1
    abel
  · congr 1
    abel

/-- Reversing a negatively oriented cyclic polygon negates and reverses a
space-form conformal-Menger realization. -/
theorem realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation
    {n : ℕ} {ε : ℝ} {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (horient : NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger ε v κ) :
    RealizesConformalMenger ε (ReverseCyclicPolygon v) (fun i => -κ (-i)) := by
  intro i
  change ConformalMenger ε (v (-(i - 1))) (v (-i)) (v (-(i + 1))) (-κ (-i))
  convert conformalMenger_reverse_of_cross_neg (horient (-i)) (hκ (-i)) using 1
  · congr 1
    abel
  · congr 1
    abel

/-- Reversing a strictly oriented cyclic polygon negates and reverses a
space-form conformal-Menger realization. -/
theorem realizesConformalMenger_reverseCyclicPolygon_of_strict_orientation
    {n : ℕ} {ε : ℝ} {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hκ : RealizesConformalMenger ε v κ) :
    RealizesConformalMenger ε (ReverseCyclicPolygon v) (fun i => -κ (-i)) := by
  rcases horient with hpos | hneg
  · exact realizesConformalMenger_reverseCyclicPolygon_of_positiveOrientation hpos hκ
  · exact realizesConformalMenger_reverseCyclicPolygon_of_negativeOrientation hneg hκ

/-- Reversing the endpoints of a circumcircle triple preserves the
circumcircle. -/
theorem CircumcircleR2_reverse {A B C O : ℂ} {R : ℝ}
    (hcircle : CircumcircleR2 A B C O R) :
    CircumcircleR2 C B A O R := by
  rcases hcircle with ⟨hR, hA, hB, hC⟩
  exact ⟨hR, hC, hB, hA⟩

/-- Reversing the endpoints of a vertex cone preserves membership in the
cone. -/
theorem InVertexCone_reverse {A B C O : ℂ}
    (hcone : InVertexCone A B C O) :
    InVertexCone C B A O := by
  rcases hcone with ⟨a, b, ha, hb, hO⟩
  refine ⟨b, a, hb, ha, ?_⟩
  simpa [add_comm] using hO

/-- Dahlberg local regularity is invariant under reversing the two outer
vertices of the local triple. -/
theorem DahlbergRegularAt_reverse {A B C : ℂ}
    (hreg : DahlbergRegularAt A B C) :
    DahlbergRegularAt C B A := by
  rcases hreg with hcol | hcircle
  · left
    refine ⟨?_, ?_⟩
    · rw [crossR2_reverse, hcol.1, neg_zero]
    · simpa [segment_symm ℝ A C] using hcol.2
  · right
    rcases hcircle with ⟨O, R, hcirc, hcone⟩
    exact ⟨O, R, CircumcircleR2_reverse hcirc, InVertexCone_reverse hcone⟩

/-- Reversing cyclic order preserves Dahlberg regularity. -/
theorem dahlbergRegular_reverseCyclicPolygon {n : ℕ} {v : ZMod n → ℂ}
    (hregular : DahlbergRegular v) :
    DahlbergRegular (ReverseCyclicPolygon v) := by
  intro i
  change DahlbergRegularAt (v (-(i - 1))) (v (-i)) (v (-(i + 1)))
  convert DahlbergRegularAt_reverse (hregular (-i)) using 1
  · congr 1
    abel
  · congr 1
    abel

/-- Reversing cyclic order preserves concyclicity. -/
theorem concyclic_reverseCyclicPolygon {n : ℕ} {v : ZMod n → ℂ}
    (hcyc : Concyclic v) :
    Concyclic (ReverseCyclicPolygon v) := by
  rcases hcyc with ⟨O, R, hR, hdist⟩
  exact ⟨O, R, hR, fun i => by simpa [ReverseCyclicPolygon] using hdist (-i)⟩

/-- Reversing cyclic order preserves concyclicity exactly. -/
theorem concyclic_reverseCyclicPolygon_iff {n : ℕ} {v : ZMod n → ℂ} :
    Concyclic (ReverseCyclicPolygon v) ↔ Concyclic v := by
  constructor
  · intro hcyc
    rcases hcyc with ⟨O, R, hR, hdist⟩
    exact ⟨O, R, hR, fun i => by
      simpa [ReverseCyclicPolygon] using hdist (-i)⟩
  · exact concyclic_reverseCyclicPolygon

/-- Reversing cyclic order preserves polygon simplicity. -/
theorem isSimplePolygon_reverseCyclicPolygon {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change v (-i) ≠ v (-(i + 1))
    intro h
    have hedge := hsimple.1 (-(i + 1))
    apply hedge
    rw [show (-(i + 1) + 1 : ZMod n) = -i by abel]
    exact h.symm
  · intro i
    change
      segment ℝ (v (-i)) (v (-(i + 1))) ∩
          segment ℝ (v (-(i + 1))) (v (-((i + 1) + 1))) =
        {v (-(i + 1))}
    rw [segment_symm ℝ (v (-i)) (v (-(i + 1))),
      segment_symm ℝ (v (-(i + 1))) (v (-((i + 1) + 1))), Set.inter_comm]
    convert hsimple.2.1 (-(i + 1 + 1)) using 1
    · abel_nf
    · abel_nf
  · intro i j hij hij_next hji_next
    change
      segment ℝ (v (-i)) (v (-(i + 1))) ∩
          segment ℝ (v (-j)) (v (-(j + 1))) =
        ∅
    have hIJ : -(i + 1) ≠ -(j + 1) := by
      intro h
      apply hij
      have h' := congrArg Neg.neg h
      simpa [sub_eq_add_neg, add_assoc] using congrArg (fun x : ZMod n => x - 1) h'
    have hIJs : -(i + 1) + 1 ≠ -(j + 1) := by
      intro h
      apply hji_next
      have h' := congrArg Neg.neg h
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h'.symm
    have hJIs : -(j + 1) + 1 ≠ -(i + 1) := by
      intro h
      apply hij_next
      have h' := congrArg Neg.neg h
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h'.symm
    rw [segment_symm ℝ (v (-i)) (v (-(i + 1))),
      segment_symm ℝ (v (-j)) (v (-(j + 1)))]
    convert hsimple.2.2 (-(i + 1)) (-(j + 1)) hIJ hIJs hJIs using 1
    abel_nf

/-- Cyclic translation of a polygon's index origin. -/
def TranslateCyclicPolygon {n : ℕ} (v : ZMod n → ℂ) (a : ZMod n) :
    ZMod n → ℂ :=
  fun i => v (i + a)

/-- Signed Menger curvature is translated with the cyclic index origin. -/
theorem SignedMengerProfile_translateCyclicPolygon {n : ℕ} (v : ZMod n → ℂ)
    (a i : ZMod n) :
    SignedMengerProfile (TranslateCyclicPolygon v a) i =
      SignedMengerProfile v (i + a) := by
  simp [SignedMengerProfile, TranslateCyclicPolygon, sub_eq_add_neg, add_assoc,
    add_comm]

/-- Cyclic translation preserves a chosen minimal enclosing disk exactly. -/
theorem minimalEnclosingDiskR2_translateCyclicPolygon_iff {n : ℕ}
    {v : ZMod n → ℂ} {a : ZMod n} {O : ℂ} {R : ℝ} :
    MinimalEnclosingDiskR2 (TranslateCyclicPolygon v a) O R ↔
      MinimalEnclosingDiskR2 v O R := by
  constructor
  · intro hΔ
    refine ⟨hΔ.1, ?_, ?_⟩
    · intro i
      simpa [TranslateCyclicPolygon] using hΔ.2.1 (i - a)
    · intro O' R' hR' hcontains
      exact hΔ.2.2 O' R' hR' (fun i => by
        simpa [TranslateCyclicPolygon] using hcontains (i + a))
  · intro hΔ
    refine ⟨hΔ.1, ?_, ?_⟩
    · intro i
      exact hΔ.2.1 (i + a)
    · intro O' R' hR' hcontains
      exact hΔ.2.2 O' R' hR' (fun i => by
        simpa [TranslateCyclicPolygon] using hcontains (i - a))

/-- Cyclic translation preserves simplicity. -/
theorem isSimplePolygon_translateCyclicPolygon {n : ℕ} {v : ZMod n → ℂ}
    (a : ZMod n) (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.IsSimplePolygon (TranslateCyclicPolygon v a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    convert hsimple.1 (i + a) using 1
    all_goals simp [TranslateCyclicPolygon]
    all_goals abel_nf
  · intro i
    convert hsimple.2.1 (i + a) using 1
    all_goals simp [TranslateCyclicPolygon]
    all_goals abel_nf
  · intro i j hij hij_next hji_next
    have hij' : i + a ≠ j + a := by
      intro h
      apply hij
      exact add_right_cancel h
    have hij_next' : i + a + 1 ≠ j + a := by
      intro h
      apply hij_next
      have h' := congrArg (fun x : ZMod n => x - a) h
      convert h' using 1
      all_goals abel_nf
    have hji_next' : j + a + 1 ≠ i + a := by
      intro h
      apply hji_next
      have h' := congrArg (fun x : ZMod n => x - a) h
      convert h' using 1
      all_goals abel_nf
    convert hsimple.2.2 (i + a) (j + a) hij' hij_next' hji_next' using 1
    all_goals simp [TranslateCyclicPolygon]
    all_goals abel_nf

/-- Cyclic translation preserves positive orientation. -/
theorem positivePolygonOrientation_translateCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ} (a : ZMod n)
    (horient : PositivePolygonOrientation v) :
    PositivePolygonOrientation (TranslateCyclicPolygon v a) := by
  intro i
  convert horient (i + a) using 1
  all_goals simp [TranslateCyclicPolygon]
  all_goals abel_nf

/-- Cyclic translation preserves negative orientation. -/
theorem negativePolygonOrientation_translateCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ} (a : ZMod n)
    (horient : NegativePolygonOrientation v) :
    NegativePolygonOrientation (TranslateCyclicPolygon v a) := by
  intro i
  convert horient (i + a) using 1
  all_goals simp [TranslateCyclicPolygon]
  all_goals abel_nf

/-- Non-strict global orientation is invariant under cyclic translation. -/
theorem not_strictPolygonOrientation_translateCyclicPolygon {n : ℕ}
    {v : ZMod n → ℂ} (a : ZMod n)
    (hnonstrict : ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) :
    ¬ (PositivePolygonOrientation (TranslateCyclicPolygon v a) ∨
      NegativePolygonOrientation (TranslateCyclicPolygon v a)) := by
  intro horient
  rcases horient with hpos | hneg
  · apply hnonstrict
    left
    intro i
    convert hpos (i - a) using 1
    all_goals simp [TranslateCyclicPolygon]
    all_goals abel_nf
  · apply hnonstrict
    right
    intro i
    convert hneg (i - a) using 1
    all_goals simp [TranslateCyclicPolygon]
    all_goals abel_nf

/-- Cyclic translation preserves Dahlberg regularity. -/
theorem dahlbergRegular_translateCyclicPolygon {n : ℕ} {v : ZMod n → ℂ}
    (a : ZMod n) (hregular : DahlbergRegular v) :
    DahlbergRegular (TranslateCyclicPolygon v a) := by
  intro i
  convert hregular (i + a) using 1
  all_goals simp [TranslateCyclicPolygon, sub_eq_add_neg]
  all_goals abel_nf

/-- Cyclic translation preserves concyclicity. -/
theorem concyclic_translateCyclicPolygon_iff {n : ℕ} {v : ZMod n → ℂ}
    {a : ZMod n} :
    Concyclic (TranslateCyclicPolygon v a) ↔ Concyclic v := by
  constructor
  · intro hcyc
    rcases hcyc with ⟨O, R, hR, hdist⟩
    exact ⟨O, R, hR, fun i => by
      simpa [TranslateCyclicPolygon] using hdist (i - a)⟩
  · intro hcyc
    rcases hcyc with ⟨O, R, hR, hdist⟩
    exact ⟨O, R, hR, fun i => by
      simpa [TranslateCyclicPolygon] using hdist (i + a)⟩

/-- Reversing cyclic order preserves a chosen minimal enclosing disk exactly. -/
theorem minimalEnclosingDiskR2_reverseCyclicPolygon_iff {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ} :
    MinimalEnclosingDiskR2 (ReverseCyclicPolygon v) O R ↔
      MinimalEnclosingDiskR2 v O R := by
  constructor
  · intro hΔ
    refine ⟨hΔ.1, ?_, ?_⟩
    · intro i
      simpa [ReverseCyclicPolygon] using hΔ.2.1 (-i)
    · intro O' R' hR' hcontains
      exact hΔ.2.2 O' R' hR' (fun i => by
        simpa [ReverseCyclicPolygon] using hcontains (-i))
  · intro hΔ
    refine ⟨hΔ.1, ?_, ?_⟩
    · intro i
      simpa [ReverseCyclicPolygon] using hΔ.2.1 (-i)
    · intro O' R' hR' hcontains
      exact hΔ.2.2 O' R' hR' (fun i => by
        simpa [ReverseCyclicPolygon] using hcontains (-i))

/-- Positive oriented area at the actual vertex is positive over the outgoing
edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_pos_of_vertex_cross_pos {n : ℕ} {v : ZMod n → ℂ}
    {i : ZMod n}
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) := by
  rwa [← polygonCross_eq_edgePrev i]

/-- Negative oriented area at the actual vertex is negative over the outgoing
edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_neg_of_vertex_cross_neg {n : ℕ} {v : ZMod n → ℂ}
    {i : ZMod n}
    (hcross : Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0 := by
  rwa [← polygonCross_eq_edgePrev i]

/-- Positive signed Menger curvature at a polygon vertex gives positive
orientation over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : 0 < Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) := by
  have hκ' :
      0 < Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact crossR2_pos_of_signedMengerR2_pos (hsimple.1 i) hκ'

/-- Negative signed Menger curvature at a polygon vertex gives negative
orientation over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0 := by
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) < 0 := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact crossR2_neg_of_signedMengerR2_neg (hsimple.1 i) hκ'

/-- Zero signed Menger curvature at a polygon vertex gives zero oriented area
over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_eq_zero_of_vertex_signedMenger_eq_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = 0) :
    Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) = 0 := by
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) = 0 := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact crossR2_eq_zero_of_signedMengerR2_eq_zero (hsimple.1 i) hκ'

/-- Zero signed-Menger profile at a polygon vertex gives zero oriented area
over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_eq_zero_of_signedMengerProfile_eq_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : SignedMengerProfile v i = 0) :
    Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) = 0 := by
  exact polygonEdgePrev_cross_eq_zero_of_vertex_signedMenger_eq_zero hsimple
    (by simpa [SignedMengerProfile] using hκ)

/-- Zero signed-Menger profile at a polygon vertex is equivalent to zero
oriented area at that vertex. -/
theorem signedMengerProfile_eq_zero_iff_vertex_cross_eq_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n) :
    SignedMengerProfile v i = 0 ↔
      Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) = 0 := by
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact signedMengerR2_eq_zero_iff_crossR2_eq_zero hAB

/-- A constant-zero signed-Menger profile makes every consecutive triple
collinear in oriented-area form. -/
theorem vertex_cross_eq_zero_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) = 0 := by
  intro i
  exact (signedMengerProfile_eq_zero_iff_vertex_cross_eq_zero hsimple i).mp (hκ i)

/-- Zero signed-Menger profile at two adjacent vertices propagates collinearity
across the four consecutive vertices. -/
theorem four_consecutive_cross_eq_zero_of_signedMengerProfile_eq_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκi : SignedMengerProfile v i = 0)
    (hκs : SignedMengerProfile v (i + 1) = 0) :
    Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1 + 1)) = 0 := by
  have hleft :
      Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) = 0 :=
    (signedMengerProfile_eq_zero_iff_vertex_cross_eq_zero hsimple i).mp hκi
  have hright :
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) = 0 := by
    simpa [sub_eq_add_neg, add_assoc] using
      (signedMengerProfile_eq_zero_iff_vertex_cross_eq_zero hsimple (i + 1)).mp hκs
  exact crossR2_eq_zero_of_consecutive (hsimple.1 i) hleft hright

/-- A constant-zero signed-Menger profile propagates collinearity across every
four consecutive vertices. -/
theorem four_consecutive_cross_eq_zero_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n,
      Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1 + 1)) = 0 := by
  intro i
  exact four_consecutive_cross_eq_zero_of_signedMengerProfile_eq_zero
    hsimple (hκ i) (hκ (i + 1))

/-- A constant-zero signed-Menger profile propagates one step further: five
consecutive vertices are collinear with the first edge. -/
theorem five_consecutive_cross_eq_zero_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n,
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1 + 1 + 1)) = 0 := by
  intro i
  have hAB : v i ≠ v (i + 1) := hsimple.1 i
  have hBC : v (i + 1) ≠ v (i + 1 + 1) := by
    simpa [add_assoc] using hsimple.1 (i + 1)
  have hCD : v (i + 1 + 1) ≠ v (i + 1 + 1 + 1) := by
    simpa [add_assoc] using hsimple.1 (i + 1 + 1)
  have hABC : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) = 0 := by
    simpa [sub_eq_add_neg, add_assoc] using
      (vertex_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ (i + 1))
  have hABD : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1 + 1)) = 0 := by
    simpa [sub_eq_add_neg, add_assoc] using
      (four_consecutive_cross_eq_zero_of_constant_signedMengerProfile_zero
        hsimple hκ (i + 1))
  have hCDE :
      Gluck.Discrete.crossR2 (v (i + 1 + 1)) (v (i + 1 + 1 + 1))
        (v (i + 1 + 1 + 1 + 1)) = 0 := by
    simpa [sub_eq_add_neg, add_assoc] using
      (vertex_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ
        (i + 1 + 1 + 1))
  exact crossR2_eq_zero_of_same_line_step hAB hBC hCD hABC hABD hCDE

/-- A constant-zero signed-Menger profile propagates along every natural
forward offset from any fixed base edge. -/
theorem forward_chain_cross_eq_zero_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) (i : ZMod n) :
    ∀ k : ℕ, Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + (k : ZMod n))) = 0 := by
  have hpair :
      ∀ k : ℕ,
        Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + (k : ZMod n))) = 0 ∧
          Gluck.Discrete.crossR2 (v i) (v (i + 1))
            (v (i + ((k + 1 : ℕ) : ZMod n))) = 0 := by
    intro k
    induction k with
    | zero =>
        constructor
        · simp
        · simp
    | succ k ih =>
        constructor
        · exact ih.2
        · have hCD : v (i + (k : ZMod n)) ≠ v (i + ((k + 1 : ℕ) : ZMod n)) := by
            simpa [Nat.cast_add, add_assoc] using hsimple.1 (i + (k : ZMod n))
          have hCDE :
              Gluck.Discrete.crossR2 (v (i + (k : ZMod n)))
                (v (i + ((k + 1 : ℕ) : ZMod n)))
                (v (i + ((k : ZMod n) + (1 + 1)))) = 0 := by
            simpa [Nat.cast_add, sub_eq_add_neg, add_assoc] using
              (vertex_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ
                (i + ((k + 1 : ℕ) : ZMod n)))
          have htwo : ((1 : ZMod n) + 1) = 2 := by norm_num
          simpa [Nat.cast_add, add_assoc, htwo] using
            crossR2_eq_zero_of_same_line_step_of_moving_edge hCD ih.1 ih.2 hCDE
  intro k
  exact (hpair k).1

/-- A constant-zero signed-Menger profile puts every vertex on the line through
any chosen oriented edge. -/
theorem all_vertices_cross_eq_zero_of_constant_signedMengerProfile_zero {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i j : ZMod n, Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j) = 0 := by
  intro i j
  have hchain :=
    forward_chain_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ i
      (j - i).val
  have hcast : (((j + -i).val : ℕ) : ZMod n) = j + -i :=
    ZMod.natCast_rightInverse (j + -i)
  simpa [hcast, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hchain

/-- Projection to real parts sends a complex segment into the unordered real
interval joining the endpoint real parts. -/
theorem re_mem_uIcc_of_mem_segment {A B C : ℂ} (hB : B ∈ segment ℝ A C) :
    B.re ∈ Set.uIcc A.re C.re := by
  rw [segment_eq_image_lineMap] at hB
  rcases hB with ⟨t, ht, rfl⟩
  rw [← segment_eq_uIcc]
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply]

/-- A constant-zero signed-Menger profile on a simple locally regular polygon
makes every vertex a segment subdivision point between its two neighbors. -/
theorem vertex_mem_neighbor_segment_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n, v i ∈ segment ℝ (v (i - 1)) (v (i + 1)) := by
  intro i
  exact vertex_mem_neighbor_segment_of_signedMengerProfile_eq_zero hsimple hregular (hκ i)

/-- The zero-profile segment-subdivision condition descends to a real
between-neighbours condition on real parts. -/
theorem re_mem_uIcc_neighbors_of_constant_signedMengerProfile_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    ∀ i : ZMod n, (v i).re ∈ Set.uIcc (v (i - 1)).re (v (i + 1)).re := by
  intro i
  exact re_mem_uIcc_of_mem_segment
    (vertex_mem_neighbor_segment_of_constant_signedMengerProfile_zero hsimple hregular hκ i)

/-- In edge coordinates, the zero-profile segment-subdivision condition has an
adjacent plateau. -/
theorem exists_adjacent_equal_lineCoordR2_of_constant_signedMengerProfile_zero
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) (base : ZMod n) :
    ∃ i : ZMod n,
      lineCoordR2 (v base) (v (base + 1)) (v i) =
        lineCoordR2 (v base) (v (base + 1)) (v (i + 1)) := by
  apply exists_eq_succ_of_forall_mem_uIcc_neighbors
  intro i
  exact lineCoordR2_mem_uIcc_of_mem_segment
    (vertex_mem_neighbor_segment_of_constant_signedMengerProfile_zero hsimple hregular hκ i)

/-- A constant-zero signed-Menger profile is impossible on a simple
Dahlberg-regular polygon: the segment branch would make the polygon a
one-dimensional cyclic chain with no possible adjacent strict movement. -/
theorem not_constant_signedMengerProfile_zero_of_isSimplePolygon {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i = 0) :
    False := by
  obtain ⟨i, hcoord⟩ :=
    exists_adjacent_equal_lineCoordR2_of_constant_signedMengerProfile_zero
      hsimple hregular hκ (0 : ZMod n)
  have hbase : v (0 : ZMod n) ≠ v ((0 : ZMod n) + 1) := hsimple.1 0
  have hC :
      Gluck.Discrete.crossR2 (v (0 : ZMod n)) (v ((0 : ZMod n) + 1)) (v i) = 0 :=
    all_vertices_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ 0 i
  have hD :
      Gluck.Discrete.crossR2 (v (0 : ZMod n)) (v ((0 : ZMod n) + 1)) (v (i + 1)) = 0 :=
    all_vertices_cross_eq_zero_of_constant_signedMengerProfile_zero hsimple hκ 0 (i + 1)
  have hvi : v i = v (i + 1) :=
    eq_of_crossR2_eq_zero_of_lineCoordR2_eq hbase hC hD hcoord
  exact hsimple.1 i hvi

/-- A simple Dahlberg-regular polygon has some nonzero signed-Menger value.
Otherwise the zero-profile subdivision branch contradicts simplicity. -/
theorem exists_signedMengerProfile_ne_zero_of_isSimplePolygon {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) :
    ∃ i : ZMod n, SignedMengerProfile v i ≠ 0 := by
  by_contra hnone
  have hκzero : ∀ i : ZMod n, SignedMengerProfile v i = 0 := by
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  exact not_constant_signedMengerProfile_zero_of_isSimplePolygon hsimple hregular hκzero

/-- Polygon-indexed own-region membership over the outgoing edge from nonzero
signed Menger curvature at the left endpoint. -/
theorem polygonEdgePrev_mem_own_dahlbergRegion_of_vertex_menger_ne_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≠ 0) :
    v (i - 1) ∈ edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) ≠ 0 := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact edgePoint_mem_own_dahlbergRegion_of_signedMenger_ne_zero (hsimple.1 i) hκ'

/-- Polygon-indexed form of Dahlberg Lemma 8(1) for the left endpoint of the
edge `i → i+1`. -/
theorem polygonEdgePrev_region_subset_halfPlane_of_nonneg {n : ℕ} {v : ZMod n → ℂ}
    {i : ZMod n}
    (hk : 0 ≤ Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) ⊆
      edgeHalfPlane (v i) (v (i + 1)) := by
  have hk' :
      0 ≤ Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact edgePointDahlbergRegion_subset_edgeHalfPlane_of_nonneg hk'

/-- Polygon-indexed form of Dahlberg Lemma 8(2) for the left endpoint of the
edge `i → i+1`. -/
theorem polygonEdgePrev_halfPlane_subset_region_of_nonpos {n : ℕ} {v : ZMod n → ℂ}
    {i : ZMod n}
    (hk : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤ 0) :
    edgeHalfPlane (v i) (v (i + 1)) ⊆
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  have hk' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) ≤ 0 := by
    rwa [← polygonSignedMenger_eq_edgePrev i]
  exact edgeHalfPlane_subset_edgePointDahlbergRegion_of_nonpos hk'

/-- Polygon-indexed endpoint form of Dahlberg Lemma 8 for the oriented edge
from `v i` to `v (i+1)`. The curvature at the left endpoint is cyclically
rewritten to use the same oriented edge. -/
theorem polygonEdgeDahlbergRegion_anti_of_endpoint_order {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    edgePointDahlbergRegion (v i) (v (i + 1)) (v (i + 1 + 1)) ⊆
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  have hAB : v i ≠ v (i + 1) := hsimple.1 i
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) ≤
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgePointDahlbergRegion_anti_of_endpoint_regular hAB hPreg hQreg hκ'

/-- Polygon-indexed incidence corollary of endpoint nesting: under the adjacent
curvature order, the next vertex lies in the Dahlberg region attached to the
previous vertex over the same edge. -/
theorem polygonEdgePoint_mem_region_of_endpoint_order {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) ≠ 0) :
    v (i + 1 + 1) ∈
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  have hAB : v i ≠ v (i + 1) := hsimple.1 i
  have hQmem := edgePoint_mem_own_dahlbergRegion hAB hQcross
  exact polygonEdgeDahlbergRegion_anti_of_endpoint_order hsimple hregular i hκ hQmem

/-- Polygon-indexed endpoint incidence using nonzero signed Menger curvature
at the next vertex. -/
theorem polygonEdgePoint_mem_region_of_endpoint_order_menger_ne_zero {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hQκ : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) ≠ 0) :
    v (i + 1 + 1) ∈
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgePoint_mem_region_of_endpoint_order hsimple hregular i hκ
    (crossR2_ne_zero_of_signedMengerR2_ne_zero hQκ)

/-- Positive polygon-indexed incidence into the ordinary curvature disk. -/
theorem polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) ≠ 0) :
    v (i + 1 + 1) ∈
      edgeClosedDisk (v i) (v (i + 1))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hregion :=
    polygonEdgePoint_mem_region_of_endpoint_order hsimple hregular i hκ hQcross
  exact edgePointDahlbergRegion_subset_edgeClosedDisk_of_pos
    (hsimple.1 i) hPcross hregion

/-- Positive polygon-indexed incidence into the ordinary curvature disk, using
the actual cross sign at the left endpoint vertex. -/
theorem polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos_of_vertex_cross_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) ≠ 0) :
    v (i + 1 + 1) ∈
      edgeClosedDisk (v i) (v (i + 1))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos hsimple hregular i
    (polygonEdgePrev_cross_pos_of_vertex_cross_pos hPcross) hκ hQcross

/-- Positive polygon-indexed incidence into the ordinary curvature disk, using
only signed-Menger positivity at the left endpoint and the adjacent curvature
order. -/
theorem polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos_of_vertex_menger_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    v (i + 1 + 1) ∈
      edgeClosedDisk (v i) (v (i + 1))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple hPκpos
  have hQκpos : 0 <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    lt_of_lt_of_le hPκpos hκ
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    crossR2_pos_of_signedMengerR2_pos (hsimple.1 i) hQκpos
  exact polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos hsimple hregular i
    hPcross hκ hQcross.ne'

/-- If two locally regular points over an oriented edge are ordered by signed
Menger curvature, then the higher-curvature point lies in the lower-curvature
point's Dahlberg edge-region. -/
theorem edgePoint_mem_region_of_regular_order {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt Q A B)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgePointDahlbergRegion A B P := by
  have hQmem := edgePoint_mem_own_dahlbergRegion hAB hQcross
  exact edgePointDahlbergRegion_anti_of_regular hAB hPreg hQreg hκ hQmem

/-- Right-endpoint version of ordered regular incidence into a Dahlberg
edge-region. -/
theorem edgePoint_mem_region_of_regular_order_right {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt A B P) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgePointDahlbergRegion A B P := by
  have hQmem := edgePoint_mem_own_dahlbergRegion hAB hQcross
  exact edgePointDahlbergRegion_anti_of_regular_right hAB hPreg hQreg hκ hQmem

/-- Endpoint form of ordered regular incidence into a Dahlberg edge-region. -/
theorem edgePoint_mem_region_of_endpoint_regular_order {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgePointDahlbergRegion A B P := by
  have hQmem := edgePoint_mem_own_dahlbergRegion hAB hQcross
  exact edgePointDahlbergRegion_anti_of_endpoint_regular hAB hPreg hQreg hκ hQmem

/-- Endpoint ordered regular incidence using nonzero signed Menger curvature
for the higher-curvature endpoint. -/
theorem edgePoint_mem_region_of_endpoint_regular_order_menger_ne_zero {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQκ : Gluck.Discrete.signedMengerR2 A B Q ≠ 0) :
    Q ∈ edgePointDahlbergRegion A B P := by
  exact edgePoint_mem_region_of_endpoint_regular_order hAB hPreg hQreg hκ
    (crossR2_ne_zero_of_signedMengerR2_ne_zero hQκ)

/-- Positive ordered regular incidence into the ordinary curvature disk. -/
theorem edgePoint_mem_edgeClosedDisk_of_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt Q A B)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgeClosedDisk A B (edgeCircumcenterParameter A B P) := by
  have hregion := edgePoint_mem_region_of_regular_order hAB hPreg hQreg hκ hQcross
  exact edgePointDahlbergRegion_subset_edgeClosedDisk_of_pos hAB hPcross hregion

/-- Right-endpoint positive ordered regular incidence into the ordinary
curvature disk. -/
theorem edgePoint_mem_edgeClosedDisk_of_regular_order_pos_right {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hPreg : DahlbergRegularAt A B P) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgeClosedDisk A B (edgeCircumcenterParameter A B P) := by
  have hregion := edgePoint_mem_region_of_regular_order_right hAB hPreg hQreg hκ hQcross
  exact edgePointDahlbergRegion_subset_edgeClosedDisk_of_pos hAB hPcross hregion

/-- Endpoint positive ordered regular incidence into the ordinary curvature
disk. -/
theorem edgePoint_mem_edgeClosedDisk_of_endpoint_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0) :
    Q ∈ edgeClosedDisk A B (edgeCircumcenterParameter A B P) := by
  have hregion := edgePoint_mem_region_of_endpoint_regular_order hAB hPreg hQreg hκ hQcross
  exact edgePointDahlbergRegion_subset_edgeClosedDisk_of_pos hAB hPcross hregion

/-- Right-endpoint regular point-edge form of the radius comparison behind
Dahlberg Lemma 10. -/
theorem edgeRegularCircleRadius_le_of_mem_edgeClosedDisk_right {A B C O : ℂ} {R yΔ : ℝ}
    (hAB : A ≠ B) (hcross : 0 < Gluck.Discrete.crossR2 A B C)
    (hcircle : CircumcircleR2 A B C O R) (hcone : InVertexCone A B C O)
    (hmem : C ∈ edgeClosedDisk A B yΔ) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B C) ≤
      normalizedCircleRadius (chordHalfLength A B) yΔ := by
  have hyρ := edgeCircumcenterParameter_nonneg_of_regular_right hAB hcross hcircle hcone
  exact edgeCircleRadius_le_of_mem_edgeClosedDisk hAB hcross hyρ hmem

/-- Positive ordered regular vertices compare their canonical circle radii:
higher signed Menger curvature gives no larger positive-branch radius. -/
theorem edgeCircleRadius_antitone_of_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt Q A B)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) ≤
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
  have hmem := edgePoint_mem_edgeClosedDisk_of_regular_order_pos
    hAB hPcross hPreg hQreg hκ hQcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hQreg hQcross.ne'
  exact edgeRegularCircleRadius_le_of_mem_edgeClosedDisk
    hAB hQcross hcircleQ hconeQ hmem

/-- Right-endpoint version of the positive ordered regular radius comparison. -/
theorem edgeCircleRadius_antitone_of_regular_order_pos_right {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt A B P) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) ≤
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
  have hmem := edgePoint_mem_edgeClosedDisk_of_regular_order_pos_right
    hAB hPcross hPreg hQreg hκ hQcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne'
  exact edgeRegularCircleRadius_le_of_mem_edgeClosedDisk_right
    hAB hQcross hcircleQ hconeQ hmem

/-- Endpoint version of the positive ordered regular radius comparison. -/
theorem edgeCircleRadius_antitone_of_endpoint_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) ≤
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
  have hmem := edgePoint_mem_edgeClosedDisk_of_endpoint_regular_order_pos
    hAB hPcross hPreg hQreg hκ hQcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne'
  exact edgeRegularCircleRadius_le_of_mem_edgeClosedDisk_right
    hAB hQcross hcircleQ hconeQ hmem

/-- Strict endpoint version of the positive ordered regular radius comparison. -/
theorem edgeCircleRadius_strictAnti_of_endpoint_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P <
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne'
  have hyP : 0 ≤ edgeCircumcenterParameter A B P :=
    edgeCircumcenterParameter_nonneg_of_regular hAB hPcross hcircleP hconeP
  have hyQ : 0 ≤ edgeCircumcenterParameter A B Q :=
    edgeCircumcenterParameter_nonneg_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P)
          = Gluck.Discrete.signedMengerR2 A B P :=
            (signedMengerR2_edge_parameter_of_pos hAB hPcross).symm
      _ < Gluck.Discrete.signedMengerR2 A B Q := hκ
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) :=
            signedMengerR2_edge_parameter_of_pos hAB hQcross
  have hyQPle : edgeCircumcenterParameter A B Q ≤ edgeCircumcenterParameter A B P :=
    parameter_le_of_curvature_le_nonneg
      (a := chordHalfLength A B)
      (yP := edgeCircumcenterParameter A B P)
      (yQ := edgeCircumcenterParameter A B Q)
      (chordHalfLength_pos hAB).ne' hyP hcurv.le
  have hyne : edgeCircumcenterParameter A B Q ≠ edgeCircumcenterParameter A B P := by
    intro hy
    rw [hy] at hcurv
    exact (lt_irrefl _) hcurv
  have hyQP : edgeCircumcenterParameter A B Q < edgeCircumcenterParameter A B P :=
    lt_of_le_of_ne hyQPle hyne
  exact normalizedCircleRadius_strictMono_of_nonneg hyQ hyQP

/-- Reverse strict endpoint version of the positive ordered regular radius
comparison.  If the right endpoint has smaller positive signed Menger
curvature, then its canonical radius is larger. -/
theorem edgeCircleRadius_strictAnti_rev_of_endpoint_regular_order_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B Q <
      Gluck.Discrete.signedMengerR2 A B P) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne'
  have hyP : 0 ≤ edgeCircumcenterParameter A B P :=
    edgeCircumcenterParameter_nonneg_of_regular hAB hPcross hcircleP hconeP
  have hyQ : 0 ≤ edgeCircumcenterParameter A B Q :=
    edgeCircumcenterParameter_nonneg_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q)
          = Gluck.Discrete.signedMengerR2 A B Q :=
            (signedMengerR2_edge_parameter_of_pos hAB hQcross).symm
      _ < Gluck.Discrete.signedMengerR2 A B P := hκ
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) :=
            signedMengerR2_edge_parameter_of_pos hAB hPcross
  have hyPQle : edgeCircumcenterParameter A B P ≤ edgeCircumcenterParameter A B Q :=
    parameter_le_of_curvature_le_nonneg
      (a := chordHalfLength A B)
      (yP := edgeCircumcenterParameter A B Q)
      (yQ := edgeCircumcenterParameter A B P)
      (chordHalfLength_pos hAB).ne' hyQ hcurv.le
  have hyne : edgeCircumcenterParameter A B P ≠ edgeCircumcenterParameter A B Q := by
    intro hy
    rw [hy] at hcurv
    exact (lt_irrefl _) hcurv
  have hyPQ : edgeCircumcenterParameter A B P < edgeCircumcenterParameter A B Q :=
    lt_of_le_of_ne hyPQle hyne
  exact normalizedCircleRadius_strictMono_of_nonneg hyP hyPQ

/-- Positive-side converse: a strict radius drop over a shared oriented edge
gives a strict signed-Menger increase. -/
theorem signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_pos {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hR : normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P)) :
    Gluck.Discrete.signedMengerR2 A B P <
      Gluck.Discrete.signedMengerR2 A B Q := by
  calc
    Gluck.Discrete.signedMengerR2 A B P
        = normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) :=
          signedMengerR2_edge_parameter_of_pos hAB hPcross
    _ < normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) :=
      normalizedCircleCurvature_lt_of_radius_lt (chordHalfLength_pos hAB).ne' hR
    _ = Gluck.Discrete.signedMengerR2 A B Q :=
      (signedMengerR2_edge_parameter_of_pos hAB hQcross).symm

/-- Positive-side converse in the reverse adjacent direction. -/
theorem signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_pos_rev {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hR : normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q)) :
    Gluck.Discrete.signedMengerR2 A B Q <
      Gluck.Discrete.signedMengerR2 A B P := by
  calc
    Gluck.Discrete.signedMengerR2 A B Q
        = normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) :=
          signedMengerR2_edge_parameter_of_pos hAB hQcross
    _ < normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) :=
      normalizedCircleCurvature_lt_of_radius_lt (chordHalfLength_pos hAB).ne' hR
    _ = Gluck.Discrete.signedMengerR2 A B P :=
      (signedMengerR2_edge_parameter_of_pos hAB hPcross).symm

/-- Endpoint version of the negative ordered regular radius comparison.  On
the negative branch `κ = -1 / R`, so the signed-curvature order makes the
canonical radius monotone rather than antitone. -/
theorem edgeCircleRadius_mono_of_endpoint_regular_order_neg {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P ≤
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) ≤
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne
  have hyP : edgeCircumcenterParameter A B P ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular hAB hPcross hcircleP hconeP
  have hyQ : edgeCircumcenterParameter A B Q ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) ≤
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q)
          = -Gluck.Discrete.signedMengerR2 A B Q := by
            have hQeq := signedMengerR2_edge_parameter_of_neg hAB hQcross
            linarith
      _ ≤ -Gluck.Discrete.signedMengerR2 A B P := by linarith
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) := by
            have hPeq := signedMengerR2_edge_parameter_of_neg hAB hPcross
            linarith
  have hyQP : edgeCircumcenterParameter A B Q ≤ edgeCircumcenterParameter A B P :=
    parameter_le_of_curvature_ge_nonpos
      (a := chordHalfLength A B)
      (yP := edgeCircumcenterParameter A B P)
      (yQ := edgeCircumcenterParameter A B Q)
      (chordHalfLength_pos hAB).ne' hyQ hcurv
  exact normalizedCircleRadius_antitone_of_nonpos hyQP hyP

/-- Strict endpoint version of the negative ordered regular radius comparison. -/
theorem edgeCircleRadius_strictMono_of_endpoint_regular_order_neg {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P <
      Gluck.Discrete.signedMengerR2 A B Q) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne
  have hyP : edgeCircumcenterParameter A B P ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular hAB hPcross hcircleP hconeP
  have hyQ : edgeCircumcenterParameter A B Q ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q)
          = -Gluck.Discrete.signedMengerR2 A B Q := by
            have hQeq := signedMengerR2_edge_parameter_of_neg hAB hQcross
            linarith
      _ < -Gluck.Discrete.signedMengerR2 A B P := by linarith
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) := by
            have hPeq := signedMengerR2_edge_parameter_of_neg hAB hPcross
            linarith
  have hyQPle : edgeCircumcenterParameter A B Q ≤ edgeCircumcenterParameter A B P :=
    parameter_le_of_curvature_ge_nonpos
      (a := chordHalfLength A B)
      (yP := edgeCircumcenterParameter A B P)
      (yQ := edgeCircumcenterParameter A B Q)
      (chordHalfLength_pos hAB).ne' hyQ hcurv.le
  have hyne : edgeCircumcenterParameter A B Q ≠ edgeCircumcenterParameter A B P := by
    intro hy
    rw [hy] at hcurv
    exact (lt_irrefl _) hcurv
  have hyQP : edgeCircumcenterParameter A B Q < edgeCircumcenterParameter A B P :=
    lt_of_le_of_ne hyQPle hyne
  exact normalizedCircleRadius_strictAnti_of_nonpos hyQP hyP

/-- Reverse strict endpoint version of the negative ordered regular radius
comparison. -/
theorem edgeCircleRadius_strictMono_rev_of_endpoint_regular_order_neg {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B Q <
      Gluck.Discrete.signedMengerR2 A B P) :
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne
  have hyP : edgeCircumcenterParameter A B P ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular hAB hPcross hcircleP hconeP
  have hyQ : edgeCircumcenterParameter A B Q ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P)
          = -Gluck.Discrete.signedMengerR2 A B P := by
            have hPeq := signedMengerR2_edge_parameter_of_neg hAB hPcross
            linarith
      _ < -Gluck.Discrete.signedMengerR2 A B Q := by linarith
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) := by
            have hQeq := signedMengerR2_edge_parameter_of_neg hAB hQcross
            linarith
  have hyPQle : edgeCircumcenterParameter A B P ≤ edgeCircumcenterParameter A B Q :=
    parameter_le_of_curvature_ge_nonpos
      (a := chordHalfLength A B)
      (yP := edgeCircumcenterParameter A B Q)
      (yQ := edgeCircumcenterParameter A B P)
      (chordHalfLength_pos hAB).ne' hyP hcurv.le
  have hyne : edgeCircumcenterParameter A B P ≠ edgeCircumcenterParameter A B Q := by
    intro hy
    rw [hy] at hcurv
    exact (lt_irrefl _) hcurv
  have hyPQ : edgeCircumcenterParameter A B P < edgeCircumcenterParameter A B Q :=
    lt_of_le_of_ne hyPQle hyne
  exact normalizedCircleRadius_strictAnti_of_nonpos hyPQ hyQ

/-- Negative-side converse: a strict radius increase over a shared oriented
edge gives a strict signed-Menger increase. -/
theorem signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_neg {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hR : normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q)) :
    Gluck.Discrete.signedMengerR2 A B P <
      Gluck.Discrete.signedMengerR2 A B Q := by
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B P) :=
    normalizedCircleCurvature_lt_of_radius_lt
      (chordHalfLength_pos hAB).ne' hR
  calc
    Gluck.Discrete.signedMengerR2 A B P
        = -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
          have hPeq := signedMengerR2_edge_parameter_of_neg hAB hPcross
          linarith
    _ < -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) := by
      linarith
    _ = Gluck.Discrete.signedMengerR2 A B Q := by
      have hQeq := signedMengerR2_edge_parameter_of_neg hAB hQcross
      linarith

/-- Negative-side converse in the reverse adjacent direction. -/
theorem signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_neg_rev {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hR : normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B Q) <
      normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P)) :
    Gluck.Discrete.signedMengerR2 A B Q <
      Gluck.Discrete.signedMengerR2 A B P := by
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) <
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) :=
    normalizedCircleCurvature_lt_of_radius_lt
      (chordHalfLength_pos hAB).ne' hR
  calc
    Gluck.Discrete.signedMengerR2 A B Q
        = -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B Q) := by
          have hQeq := signedMengerR2_edge_parameter_of_neg hAB hQcross
          linarith
    _ < -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) := by
      linarith
    _ = Gluck.Discrete.signedMengerR2 A B P := by
      have hPeq := signedMengerR2_edge_parameter_of_neg hAB hPcross
      linarith

/-- Polygon-indexed positive endpoint radius comparison along one oriented
edge. -/
theorem polygonEdgeCircleRadius_antitone_of_endpoint_order_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) ≤
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_antitone_of_endpoint_regular_order_pos
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed positive endpoint radius comparison, using the actual cross
sign at the left endpoint vertex. -/
theorem polygonEdgeCircleRadius_antitone_of_endpoint_order_pos_of_vertex_cross_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgeCircleRadius_antitone_of_endpoint_order_pos hsimple hregular i
    (polygonEdgePrev_cross_pos_of_vertex_cross_pos hPcross) hQcross hκ

/-- Polygon-indexed positive endpoint radius comparison, using only
signed-Menger positivity at the left endpoint and the adjacent curvature order. -/
theorem polygonEdgeCircleRadius_antitone_of_endpoint_order_pos_of_vertex_menger_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple hPκpos
  have hQκpos : 0 <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    lt_of_lt_of_le hPκpos hκ
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    crossR2_pos_of_signedMengerR2_pos (hsimple.1 i) hQκpos
  exact polygonEdgeCircleRadius_antitone_of_endpoint_order_pos hsimple hregular i
    hPcross hQcross hκ

/-- Polygon-indexed strict positive endpoint radius comparison along one
oriented edge. -/
theorem polygonEdgeCircleRadius_strictAnti_of_endpoint_order_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_strictAnti_of_endpoint_regular_order_pos
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed strict positive endpoint radius comparison, using only
signed-Menger positivity at the left endpoint and the adjacent strict curvature
order. -/
theorem polygonEdgeCircleRadius_strictAnti_of_endpoint_order_pos_of_vertex_menger_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple hPκpos
  have hQκpos : 0 <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    lt_trans hPκpos hκ
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    crossR2_pos_of_signedMengerR2_pos (hsimple.1 i) hQκpos
  exact polygonEdgeCircleRadius_strictAnti_of_endpoint_order_pos hsimple hregular i
    hPcross hQcross hκ

/-- Polygon-indexed reverse strict positive endpoint radius comparison along
one oriented edge. -/
theorem polygonEdgeCircleRadius_strictAnti_rev_of_endpoint_order_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_strictAnti_rev_of_endpoint_regular_order_pos
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed reverse strict positive endpoint radius comparison, using
signed-Menger positivity at the right endpoint and the adjacent reverse strict
curvature order. -/
theorem polygonEdgeCircleRadius_strictAnti_rev_of_endpoint_order_pos_of_vertex_menger_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hQκpos : 0 < Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPκpos : 0 <
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) :=
    lt_trans hQκpos hκ
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple hPκpos
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) :=
    crossR2_pos_of_signedMengerR2_pos (hsimple.1 i) hQκpos
  exact polygonEdgeCircleRadius_strictAnti_rev_of_endpoint_order_pos hsimple hregular i
    hPcross hQcross hκ

/-- Polygon-indexed negative endpoint radius comparison along one oriented
edge.  For negative signed Menger curvature, the adjacent curvature order
gives the corresponding monotone radius order. -/
theorem polygonEdgeCircleRadius_mono_of_endpoint_order_neg {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) ≤
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_mono_of_endpoint_regular_order_neg
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed negative endpoint radius comparison, using the actual
cross sign at the left endpoint vertex. -/
theorem polygonEdgeCircleRadius_mono_of_endpoint_order_neg_of_vertex_cross_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  exact polygonEdgeCircleRadius_mono_of_endpoint_order_neg hsimple hregular i
    (polygonEdgePrev_cross_neg_of_vertex_cross_neg hPcross) hQcross hκ

/-- Polygon-indexed negative endpoint radius comparison, using signed-Menger
negativity at both adjacent endpoint vertices and the adjacent curvature order. -/
theorem polygonEdgeCircleRadius_mono_of_endpoint_order_neg_of_vertex_menger_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) < 0)
    (hQκneg : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) ≤
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPcross := polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple hPκneg
  have hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 :=
    crossR2_neg_of_signedMengerR2_neg (hsimple.1 i) hQκneg
  exact polygonEdgeCircleRadius_mono_of_endpoint_order_neg hsimple hregular i
    hPcross hQcross hκ

/-- Polygon-indexed strict negative endpoint radius comparison along one
oriented edge. -/
theorem polygonEdgeCircleRadius_strictMono_of_endpoint_order_neg {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_strictMono_of_endpoint_regular_order_neg
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed strict negative endpoint radius comparison, using
signed-Menger negativity at both adjacent endpoint vertices and the adjacent
strict curvature order. -/
theorem polygonEdgeCircleRadius_strictMono_of_endpoint_order_neg_of_vertex_menger_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) < 0)
    (hQκneg : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) <
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hPcross := polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple hPκneg
  have hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 :=
    crossR2_neg_of_signedMengerR2_neg (hsimple.1 i) hQκneg
  exact polygonEdgeCircleRadius_strictMono_of_endpoint_order_neg hsimple hregular i
    hPcross hQcross hκ

/-- Polygon-indexed reverse strict negative endpoint radius comparison along
one oriented edge. -/
theorem polygonEdgeCircleRadius_strictMono_rev_of_endpoint_order_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
    rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))]
    exact hκ
  exact edgeCircleRadius_strictMono_rev_of_endpoint_regular_order_neg
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Polygon-indexed reverse strict negative endpoint radius comparison, using
signed-Menger negativity at both adjacent endpoint vertices and the adjacent
reverse strict curvature order. -/
theorem polygonEdgeCircleRadius_strictMono_rev_of_endpoint_order_neg_of_vertex_menger_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) < 0)
    (hQκneg : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hPcross := polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple hPκneg
  have hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 :=
    crossR2_neg_of_signedMengerR2_neg (hsimple.1 i) hQκneg
  exact polygonEdgeCircleRadius_strictMono_rev_of_endpoint_order_neg hsimple hregular i
    hPcross hQcross hκ

end Gluck.Forward
