module

public import Gluck.Discrete.SideTangentSquareFan
public import Gluck.Discrete.SideTangentCircle
public import ForMathlib.Analysis.InnerProductSpace.ProjectiveOrientation

/-!
# Strict tangent geometry after projective balancing

Positive denominators at the tangent vertices preserve the positive order of
adjacent normals. The balanced vertices retain their strict supporting lines,
interior unit-circle contacts, and positively oriented nonzero edges.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Gluck.Discrete.SideTangent

lemma cross_transform (a x y z : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) (hx : ProjectiveBall.denominator a x ≠ 0)
    (hy : ProjectiveBall.denominator a y ≠ 0)
    (hz : ProjectiveBall.denominator a z ≠ 0) :
    crossR2 (ProjectiveBall.transform a σ x) (ProjectiveBall.transform a σ y)
        (ProjectiveBall.transform a σ z) =
      σ ^ 3 * crossR2 x y z / (ProjectiveBall.denominator a x *
        ProjectiveBall.denominator a y * ProjectiveBall.denominator a z) := by
  simpa only [ProjectiveBall.area, crossR2, Complex.sub_re, Complex.sub_im] using
    ProjectiveBall.area_transform_sub a x y z hσ hsq hx hy hz

/-- The orientation factor for a pair of tangent normals includes the
projective denominator at their common tangent vertex. -/
lemma cross_transform_normals {a u v : ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hd : 1 + ⟪u, v⟫_ℝ ≠ 0) :
    crossR2 0 (ProjectiveBall.transform a σ u) (ProjectiveBall.transform a σ v) =
      σ * crossR2 0 u v * ProjectiveBall.denominator a (tangentIntersection u v) /
        (ProjectiveBall.denominator a u * ProjectiveBall.denominator a v) := by
  have he : ProjectiveBall.area u v + ProjectiveBall.area a (u - v) =
      crossR2 u v a := by
    simp only [ProjectiveBall.area, crossR2, Complex.sub_re, Complex.sub_im]
    ring
  have h := ProjectiveBall.area_transform a u v hσ hsq
  rw [he, cross_eq_tangent_support hu hv hd a] at h
  simpa only [crossR2, Complex.zero_re, Complex.zero_im, sub_zero,
    ProjectiveBall.area, ProjectiveBall.denominator, mul_assoc] using h

/-- Unit normals with positive determinant cannot be antipodal. -/
lemma normal_pair_denominator_pos {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hc : 0 < crossR2 0 u v) : 0 < 1 + ⟪u, v⟫_ℝ := by
  have huv : u + v ≠ 0 := by
    intro he
    have hvu : v = -u := eq_neg_of_add_eq_zero_right he
    rw [hvu] at hc
    simp [crossR2, mul_comm] at hc
  have h := norm_add_sq_real u v
  rw [hu, hv] at h
  have hp := sq_pos_of_pos (norm_pos_iff.mpr huv)
  nlinarith

lemma cross_transform_normals_pos {a u v : ℂ} {σ : ℝ} (ha : ‖a‖ < 1)
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hc : 0 < crossR2 0 u v)
    (hx : 0 < ProjectiveBall.denominator a (tangentIntersection u v)) :
    0 < crossR2 0 (ProjectiveBall.transform a σ u) (ProjectiveBall.transform a σ v) := by
  rw [cross_transform_normals hσ hsq hu hv (normal_pair_denominator_pos hu hv hc).ne']
  exact div_pos (mul_pos (mul_pos hσ hc) hx)
    (mul_pos (ProjectiveBall.denominator_pos_of_norm_le_one ha hu.le)
      (ProjectiveBall.denominator_pos_of_norm_le_one ha hv.le))

/-- Positive-chart normalization commutes with taking an adjacent tangent vertex. -/
lemma transform_tangentIntersection {a u v : ℂ} {σ : ℝ} (ha : ‖a‖ < 1)
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hc : 0 < crossR2 0 u v)
    (hx : 0 < ProjectiveBall.denominator a (tangentIntersection u v)) :
    ProjectiveBall.transform a σ (tangentIntersection u v) =
      tangentIntersection (ProjectiveBall.transform a σ u) (ProjectiveBall.transform a σ v) := by
  have hdu := ProjectiveBall.denominator_pos_of_norm_le_one ha hu.le
  have hdv := ProjectiveBall.denominator_pos_of_norm_le_one ha hv.le
  have hu' := ProjectiveBall.norm_transform_eq_one hσ hsq hu hdu.ne'
  have hv' := ProjectiveBall.norm_transform_eq_one hσ hsq hv hdv.ne'
  have hc' := cross_transform_normals_pos ha hσ hsq hu hv hc hx
  have hd := (normal_pair_denominator_pos hu hv hc).ne'
  have hd' := (normal_pair_denominator_pos hu' hv' hc').ne'
  apply sub_eq_zero.mp
  apply eq_zero_of_two_inner_eq_zero hc'.ne'
  · rw [inner_sub_right, ProjectiveBall.inner_transform_eq_one hσ hsq hdu.ne' hx.ne'
      (inner_tangentIntersection_left hu hd), inner_tangentIntersection_left hu' hd']
    exact sub_self 1
  · rw [inner_sub_right, ProjectiveBall.inner_transform_eq_one hσ hsq hdv.ne' hx.ne'
      (inner_tangentIntersection_right hv hd), inner_tangentIntersection_right hv' hd']
    exact sub_self 1

/-- The central edge is a positive multiple of the counterclockwise unit tangent. -/
lemma tangent_edge_eq_pos_smul {u v w : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) (h₁ : 0 < crossR2 0 u v) (h₂ : 0 < crossR2 0 v w) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ tangentIntersection v w - tangentIntersection u v =
      ℓ • (Complex.I * v) := by
  have hd₁ := normal_pair_denominator_pos hu hv h₁
  have hd₂ := normal_pair_denominator_pos hv hw h₂
  refine ⟨crossR2 0 u v / (1 + ⟪u, v⟫_ℝ) +
    crossR2 0 v w / (1 + ⟪v, w⟫_ℝ), add_pos (div_pos h₁ hd₁) (div_pos h₂ hd₂), ?_⟩
  rw [tangentIntersection_eq_sub hv hd₁.ne', tangentIntersection_eq_add hv hd₂.ne', add_smul]
  abel

/-- The finite successor normal agrees with the angle-lift successor,
including the closing angle `2π`. -/
lemma normal_fanAngle_succ {n p q r : ℕ} [NeZero n] (hn : 4 ≤ n)
    (hpq : p < q) (hqr : q < r) (hr : r < n) (η : ℝ) (i : Fin n) :
    normal (fanAngle n p q r η (i + 1 : Fin n)) =
      normal (fanAngle n p q r η ((i : ℕ) + 1)) := by
  have h_one : (1 : Fin n).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  by_cases hi : (i : ℕ) + 1 < n
  · rw [Fin.val_add, h_one, Nat.mod_eq_of_lt hi]
  · have he : (i : ℕ) + 1 = n := by omega
    rw [Fin.val_add, h_one, he, Nat.mod_self, fanAngle_zero,
      fanAngle_end (by omega) hr hpq hqr]
    apply Complex.ext <;> simp

lemma fanVertex_eq_cyclic {n p q r : ℕ} [NeZero n] (hn : 4 ≤ n)
    (hpq : p < q) (hqr : q < r) (hr : r < n) (η : ℝ) (i : Fin n) :
    fanVertex n p q r η i = tangentIntersection (normal (fanAngle n p q r η i))
      (normal (fanAngle n p q r η (i + 1 : Fin n))) := by
  rw [normal_fanAngle_succ hn hpq hqr hr]
  rfl

lemma fan_normal_cross_pos {n p q r : ℕ} [NeZero n] (hn : 4 ≤ n) (hp : 0 < p)
    (hpq : p < q) (hqr : q < r) (hr : r < n) {η : ℝ}
    (hη : 0 < η) (hη₁ : η ≤ 1) (i : Fin n) :
    0 < crossR2 0 (normal (fanAngle n p q r η i))
      (normal (fanAngle n p q r η (i + 1 : Fin n))) := by
  rw [normal_fanAngle_succ hn hpq hqr hr, cross_normal]
  exact Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr (fanAngle_strictMono (by omega) hη hη₁ (Nat.lt_succ_self _)))
    (fanAngle_step_lt_pi hn hp hpq hqr hη.le hη₁ i)

lemma cross_of_tangent_edge {u x y z : ℂ} {ℓ : ℝ}
    (hedge : y - x = ℓ • (Complex.I * u)) (hux : ⟪u, x⟫_ℝ = 1) :
    crossR2 x y z = ℓ * (1 - ⟪u, z⟫_ℝ) := by
  change (y - x).re * (z - x).im - (y - x).im * (z - x).re = _
  rw [hedge]
  simp only [Complex.smul_re, Complex.smul_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add,
    Complex.sub_re, Complex.sub_im, smul_eq_mul, Complex.inner,
    Complex.conj_re, Complex.conj_im]
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hux
  linear_combination ℓ * hux

/-- Geometry of a strictly ordered tangential polygon, with incoming-edge
normals. The edge from `i` to `i+1` has normal `U (i+1)`. -/
structure IsStrictTangentialFan {n : ℕ} [NeZero n] (U Y : Fin n → ℂ) : Prop where
  unit_normal : ∀ i, ‖U i‖ = 1
  normal_cross_pos : ∀ i, 0 < crossR2 0 (U i) (U (i + 1))
  vertex_eq : ∀ i, Y i = tangentIntersection (U i) (U (i + 1))
  strict_support : ∀ i j, j ≠ i → j ≠ i + 1 → ⟪U j, Y i⟫_ℝ < 1
  contact_interior : ∀ i, U (i + 1) ∈ openSegment ℝ (Y i) (Y (i + 1))
  edge_pos : ∀ i, ∃ ℓ : ℝ, 0 < ℓ ∧ Y (i + 1) - Y i = ℓ • (Complex.I * U (i + 1))
  edge_ne : ∀ i, Y (i + 1) ≠ Y i
  cross_support : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < crossR2 (Y i) (Y (i + 1)) (Y j)

/-- Unit normals, positive successive determinants and strict nonincident
support already imply all contact and edge properties in the fan interface. -/
theorem isStrictTangentialFan_of_geometry {n : ℕ} [NeZero n] {U Y : Fin n → ℂ}
    (hu : ∀ i, ‖U i‖ = 1) (hc : ∀ i, 0 < crossR2 0 (U i) (U (i + 1)))
    (hy : ∀ i, Y i = tangentIntersection (U i) (U (i + 1)))
    (hs : ∀ i j, j ≠ i → j ≠ i + 1 → ⟪U j, Y i⟫_ℝ < 1) :
    IsStrictTangentialFan U Y := by
  have he : ∀ i, ∃ ℓ : ℝ, 0 < ℓ ∧ Y (i + 1) - Y i = ℓ • (Complex.I * U (i + 1)) := by
    intro i
    rw [hy i, hy (i + 1)]
    exact tangent_edge_eq_pos_smul (hu i) (hu (i + 1)) (hu (i + 1 + 1)) (hc i) (hc (i + 1))
  refine ⟨hu, hc, hy, hs, ?_, he, ?_, ?_⟩
  · intro i
    rw [hy i, hy (i + 1)]
    exact contact_mem_openSegment (hu (i + 1))
      (normal_pair_denominator_pos (hu i) (hu (i + 1)) (hc i))
      (normal_pair_denominator_pos (hu (i + 1)) (hu (i + 1 + 1)) (hc (i + 1)))
      (hc i) (hc (i + 1))
  · intro i hzero
    obtain ⟨ℓ, hℓ, heq⟩ := he i
    have hu₀ : U (i + 1) ≠ 0 := by
      intro h
      simpa [h] using hu (i + 1)
    have hn := smul_ne_zero hℓ.ne' (mul_ne_zero Complex.I_ne_zero hu₀)
    apply hn
    rw [← heq, hzero, sub_self]
  · intro i j hji hjnext
    obtain ⟨ℓ, hℓ, heq⟩ := he i
    have hi : ⟪U (i + 1), Y i⟫_ℝ = 1 := by
      rw [hy i]
      exact inner_tangentIntersection_right (hu (i + 1))
        (normal_pair_denominator_pos (hu i) (hu (i + 1)) (hc i)).ne'
    rw [cross_of_tangent_edge heq hi]
    exact mul_pos hℓ (sub_pos.mpr (hs j (i + 1) hjnext.symm
      (fun h ↦ hji (add_right_cancel h).symm)))

/-- The actual balanced square perturbation lies in the strict tangential-fan
class. Every hypothesis concerns the explicit normalization parameters. -/
theorem projective_squareFan_isStrictTangentialFan {n p q r : ℕ} [NeZero n]
    (hn : 4 ≤ n) (hp : 0 < p) (hpq : p < q) (hqr : q < r) (hr : r < n)
    {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) {a : ℂ} {σ : ℝ} (ha : ‖a‖ < 1)
    (hσ : 0 < σ) (hsq : σ ^ 2 + ‖a‖ ^ 2 = 1)
    (hd : ∀ i : Fin n, 0 < ProjectiveBall.denominator a (fanVertex n p q r η i)) :
    IsStrictTangentialFan
      (fun i : Fin n ↦ ProjectiveBall.transform a σ (normal (fanAngle n p q r η i)))
      (fun i : Fin n ↦ ProjectiveBall.transform a σ (fanVertex n p q r η i)) := by
  have hnorm : ∀ i : Fin n, ‖normal (fanAngle n p q r η i)‖ = 1 := fun i ↦ norm_normal _
  have hdn : ∀ i : Fin n, 0 < ProjectiveBall.denominator a (normal (fanAngle n p q r η i)) :=
    fun i ↦ ProjectiveBall.denominator_pos_of_norm_le_one ha (hnorm i).le
  have hc := fan_normal_cross_pos hn hp hpq hqr hr hη hη₁
  have hy := fanVertex_eq_cyclic hn hpq hqr hr η
  apply isStrictTangentialFan_of_geometry
  · intro i
    exact ProjectiveBall.norm_transform_eq_one hσ hsq (hnorm i) (hdn i).ne'
  · intro i
    exact cross_transform_normals_pos ha hσ hsq (hnorm i) (hnorm (i + 1)) (hc i)
      (by rw [← hy i]; exact hd i)
  · intro i
    rw [hy i]
    exact transform_tangentIntersection ha hσ hsq (hnorm i) (hnorm (i + 1)) (hc i)
      (by rw [← hy i]; exact hd i)
  · intro i j hji hjnext
    exact (ProjectiveBall.inner_transform_lt_one_iff hσ hsq (hdn j) (hd i)).mpr
      (fanVertex_strict_support hn hp hpq hqr hr hη hη₁ i j hji hjnext)

/-- Four alternating coefficient witnesses produce a genuinely strict,
projectively balanced tangential polygon with all its original labels. -/
theorem exists_balanced_strictTangentialFan {n p q r : ℕ} [NeZero n]
    (hn : 4 ≤ n) (hp : 0 < p) (hpq : p < q) (hqr : q < r) (hr : r < n)
    (c : Fin n → ℝ) (hsum : ∑ i, c i = 0)
    (h₀ : 0 < c ⟨0, by omega⟩) (h₁ : c ⟨p, by omega⟩ < 0)
    (h₂ : 0 < c ⟨q, by omega⟩) (h₃ : c ⟨r, hr⟩ < 0) :
    ∃ U Y : Fin n → ℂ, IsStrictTangentialFan U Y ∧ ∑ i, c i • Y i = 0 := by
  obtain ⟨η, hη, hη₁, a, σ, ha, hσ, hsq, hd, hb⟩ :=
    exists_balanced_squareFan hn hp hpq hqr hr c hsum h₀ h₁ h₂ h₃
  exact ⟨fun i ↦ ProjectiveBall.transform a σ (normal (fanAngle n p q r η i)),
    fun i ↦ ProjectiveBall.transform a σ (fanVertex n p q r η i),
    projective_squareFan_isStrictTangentialFan hn hp hpq hqr hr hη hη₁.le ha hσ hsq hd, hb⟩

end Gluck.Discrete.SideTangent
