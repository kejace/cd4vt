import Gluck.Discrete.SideTangentScaledPolygon
import Gluck.Discrete.SideTangentRegularFan

/-!
# The converse for inward circles tangent to three consecutive supporting lines

The normals below are outward unit normals of the polygon. Thus the equation
`⟪N, A - C⟫ = r > 0` places a radius-r circle center C on the inward side of
the line through A with normal N. Contacts on the neighboring line extensions
are allowed; the central contact is required to lie in its open edge segment.
-/

open scoped BigOperators InnerProductSpace

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- The three inward signed-distance equations at a given central edge. -/
def ThreeLineCircle (P N : ZMod n → ℂ) (i : ZMod n) (C : ℂ) (r : ℝ) : Prop :=
  ⟪N (i - 1), P i - C⟫_ℝ = r ∧ ⟪N i, P i - C⟫_ℝ = r ∧
    ⟪N (i + 1), P (i + 1) - C⟫_ℝ = r

/-- Exact supporting-line realization of the prescribed cyclic radii. -/
structure IsSideTangentRealization [NeZero n] (ρ : ZMod n → ℝ)
    (P N C : ZMod n → ℂ) : Prop where
  radius_pos : ∀ i, 0 < ρ i
  simple : IsSimplePolygon P
  strict_convex : StrictConvexEdgeSupport P
  unit_normal : ∀ i, ‖N i‖ = 1
  oriented_edge : ∀ i, ∃ ℓ : ℝ, 0 < ℓ ∧ P (i + 1) - P i = ℓ • (Complex.I * N i)
  supporting : ∀ i j, ⟪N i, P j - P i⟫_ℝ ≤ 0
  circles : ∀ i, ThreeLineCircle P N i (C i) (ρ i)
  unique_circle : ∀ i D r, ThreeLineCircle P N i D r → D = C i ∧ r = ρ i
  central_contact : ∀ i, C i + ρ i • N i ∈ openSegment ℝ (P i) (P (i + 1))

/-- A simple strictly convex polygon with the exact three-line radius at every edge. -/
def RealizesSideTangent [NeZero n] (ρ : ZMod n → ℝ) : Prop :=
  ∃ P N C : ZMod n → ℂ, IsSideTangentRealization ρ P N C

/-- Original constant-or-four-sign-change admissibility, with zero differences retained. -/
def SideTangentAdmissible (ρ : ZMod n → ℝ) : Prop :=
  (∀ i, 0 < ρ i) ∧ ((∃ r, ∀ i, ρ i = r) ∨ DFV (radiusDifference ρ) 0)

lemma IsCyclicStrictTangentialFan.inner_left [NeZero n] {U Y : ZMod n → ℂ}
    (h : IsCyclicStrictTangentialFan U Y) (i : ZMod n) : ⟪U i, Y i⟫_ℝ = 1 := by
  rw [h.vertex_eq i]
  exact inner_tangentIntersection_left (h.unit_normal i)
    (normal_pair_denominator_pos (h.unit_normal i) (h.unit_normal (i + 1))
      (h.normal_cross_pos i)).ne'

lemma IsCyclicStrictTangentialFan.inner_right [NeZero n] {U Y : ZMod n → ℂ}
    (h : IsCyclicStrictTangentialFan U Y) (i : ZMod n) : ⟪U (i + 1), Y i⟫_ℝ = 1 := by
  rw [h.vertex_eq i]
  exact inner_tangentIntersection_right (h.unit_normal (i + 1))
    (normal_pair_denominator_pos (h.unit_normal i) (h.unit_normal (i + 1))
      (h.normal_cross_pos i)).ne'

lemma IsCyclicStrictTangentialFan.next_strict [NeZero n] (hn : 3 ≤ n)
    {U Y : ZMod n → ℂ} (h : IsCyclicStrictTangentialFan U Y) (i : ZMod n) :
    ⟪U (i + 1 + 1), Y i⟫_ℝ < 1 := by
  have : Fact (1 < n) := ⟨by omega⟩
  have h₁ : (1 : ZMod n) ≠ 0 := one_ne_zero
  have h₂ : (2 : ZMod n) ≠ 0 := by
    intro he
    have := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 n).mp he)
    omega
  exact h.strict_support i (i + 1 + 1) (fun he ↦ h₂ (by linear_combination he))
    (fun he ↦ h₁ (by linear_combination he))

lemma crossR2_tangent_edge {A B C u : ℂ} {ℓ : ℝ}
    (he : B - A = ℓ • (Complex.I * u)) :
    crossR2 A B C = -ℓ * ⟪u, C - A⟫_ℝ := by
  rw [crossR2, he]
  simp only [Complex.smul_re, Complex.smul_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add,
    Complex.inner, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

/-- Unit normals perpendicular to positively oriented supported edges point outward. -/
lemma normal_support_of_strictSupport [NeZero n] {P N : ZMod n → ℂ}
    (hs : StrictConvexEdgeSupport P)
    (he : ∀ i, ∃ ℓ : ℝ, 0 < ℓ ∧ P (i + 1) - P i = ℓ • (Complex.I * N i)) :
    ∀ i j, ⟪N i, P j - P i⟫_ℝ ≤ 0 := by
  intro i j
  obtain ⟨ℓ, hℓ, hedge⟩ := he i
  have hc := crossR2_tangent_edge (C := P j) hedge
  by_cases hji : j = i
  · simp [hji]
  by_cases hjs : j = i + 1
  · have hz : crossR2 (P i) (P (i + 1)) (P j) = 0 := by simp [hjs, crossR2, mul_comm]
    nlinarith
  · have hp := hs i j hji hjs
    nlinarith

/-- Positive scaling identifies the exact inward circle at every edge, including its unique
radius and its contact in the open central segment. -/
theorem realizesSideTangent_of_scaledFan [NeZero n] (hn : 3 ≤ n)
    (ρ : ZMod n → ℝ) (hρ : ∀ i, 0 < ρ i) {U Y P : ZMod n → ℂ}
    (hf : IsCyclicStrictTangentialFan U Y)
    (hedge : ∀ i, P (i + 1) - P i = ρ i • (Y (i + 1) - Y i))
    (hs : StrictConvexEdgeSupport P) (hp : IsSimplePolygon P) : RealizesSideTangent ρ := by
  let N : ZMod n → ℂ := fun i ↦ U (i + 1)
  let C : ZMod n → ℂ := fun i ↦ P i - ρ i • Y i
  have he : ∀ i, ∃ ℓ : ℝ, 0 < ℓ ∧ P (i + 1) - P i = ℓ • (Complex.I * N i) := by
    intro i
    obtain ⟨ℓ, hℓ, heq⟩ := hf.edge_pos i
    exact ⟨ρ i * ℓ, mul_pos (hρ i) hℓ, by rw [hedge i, heq, smul_smul]⟩
  refine ⟨P, N, C, hρ, hp, hs, fun i ↦ hf.unit_normal (i + 1), he,
    normal_support_of_strictSupport hs he, ?_, ?_, ?_⟩
  · intro i
    simpa only [ThreeLineCircle, N, C, sub_add_cancel] using
      threeLineCircle_equations (hf.inner_left i) (hf.inner_right i) (hf.inner_right (i + 1))
        (hedge i)
  · intro i D r hD
    have heq : ⟪U i, P i - D⟫_ℝ = r ∧ ⟪U (i + 1), P i - D⟫_ℝ = r ∧
        ⟪U (i + 1 + 1), P (i + 1) - D⟫_ℝ = r := by
      simpa only [ThreeLineCircle, N, sub_add_cancel] using hD
    exact threeLineCircle_unique (hf.normal_cross_pos i).ne'
      (hf.inner_left i) (hf.inner_right i) (hf.inner_right (i + 1)) (hf.next_strict hn i)
      (hedge i) heq.1 heq.2.1 heq.2.2
  · intro i
    have hc := prescribedContact_mem_openSegment (ρ i) (hedge i) (hf.contact_interior i)
    simpa only [C, N, smul_sub, sub_add_eq_add_sub, add_sub_assoc] using hc

/-- The full nonconstant converse with exact original radii, including plateaus. -/
theorem sideTangentConverse_of_dfv [NeZero n] (ρ : ZMod n → ℝ)
    (hρ : ∀ i, 0 < ρ i) (h : DFV (radiusDifference ρ) 0) : RealizesSideTangent ρ := by
  obtain ⟨U, Y, P, hf, he, hs, hp⟩ := exists_sideTangent_scaledPolygon ρ hρ h
  exact realizesSideTangent_of_scaledFan (by have := four_le_of_dfv h; omega) ρ hρ hf he hs hp

/-- Constant positive profiles use an actual regular strict tangential fan. -/
theorem sideTangentConverse_of_const [NeZero n] (hn : 4 ≤ n) (ρ : ZMod n → ℝ)
    (hρ : ∀ i, 0 < ρ i) {r : ℝ} (hconst : ∀ i, ρ i = r) : RealizesSideTangent ρ := by
  obtain ⟨U, Y, hf⟩ := exists_strictTangentialFan_of_four_le hn
  let U' : ZMod n → ℂ := fun i ↦ U ((cyclicLabelEquiv (0 : ZMod n)).symm i)
  let Y' : ZMod n → ℂ := fun i ↦ Y ((cyclicLabelEquiv (0 : ZMod n)).symm i)
  have hf' : IsCyclicStrictTangentialFan U' Y' := isCyclicStrictTangentialFan_of_finite _ hf
  have hb : ∑ i, (ρ (i - 1) - ρ i) • Y' i = 0 := by
    simp only [hconst, sub_self, zero_smul, Finset.sum_const_zero]
  obtain ⟨P, he, hs, hp⟩ :=
    exists_strictPolygon_of_balanced_scaling (by omega) hf'.cross_support ρ hρ hb
  exact realizesSideTangent_of_scaledFan (by omega) ρ hρ hf' he hs hp

/-- The side-tangent-circle converse for positive cyclic radii: constants and all original
DFV difference profiles, including repeated adjacent radii, have an exact realization. -/
theorem sideTangentConverse [NeZero n] (hn : 4 ≤ n) (ρ : ZMod n → ℝ)
    (h : SideTangentAdmissible ρ) : RealizesSideTangent ρ := by
  obtain ⟨hρ, hconst | hdfv⟩ := h
  · obtain ⟨r, hr⟩ := hconst
    exact sideTangentConverse_of_const hn ρ hρ hr
  · exact sideTangentConverse_of_dfv ρ hρ hdfv

/-- The supporting line through a polygon edge with its chosen outward unit normal. -/
def supportingLine (P N : ZMod n → ℂ) (i : ZMod n) : Set ℂ :=
  {z | ⟪N i, z - P i⟫_ℝ = 0}

/-- The unit-normal signed-distance equation describes actual unique metric tangency. -/
lemma sphere_inter_normalLine {u A C : ℂ} {r : ℝ} (hu : ‖u‖ = 1) (hr : 0 ≤ r)
    (hd : ⟪u, A - C⟫_ℝ = r) :
    Metric.sphere C r ∩ {z | ⟪u, z - A⟫_ℝ = 0} = {C + r • u} := by
  ext z
  simp only [Set.mem_inter_iff, Metric.mem_sphere, dist_eq_norm, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hl⟩
    have hi : ⟪u, z - C⟫_ℝ = r := by
      rw [show z - C = (z - A) + (A - C) by abel, inner_add_right, hl, hd, zero_add]
    have hnorm : ‖(z - C) - r • u‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hu,
        mul_one, real_inner_smul_right, real_inner_comm u (z - C), hi]
      ring
    have hzero := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    linear_combination hzero
  · rintro rfl
    constructor
    · simp [hu, abs_of_nonneg hr]
    · rw [show C + r • u - A = r • u - (A - C) by abel, inner_sub_right,
        real_inner_smul_right, real_inner_self_eq_norm_sq, hu, hd]
      ring

lemma IsSideTangentRealization.normal_edge_orthogonal [NeZero n]
    {ρ : ZMod n → ℝ} {P N C : ZMod n → ℂ} (h : IsSideTangentRealization ρ P N C)
    (i : ZMod n) : ⟪N i, P (i + 1) - P i⟫_ℝ = 0 := by
  obtain ⟨ℓ, _, he⟩ := h.oriented_edge i
  rw [he, real_inner_smul_right]
  have hz : ⟪N i, Complex.I * N i⟫_ℝ = 0 := by simp [Complex.inner, mul_comm]
  rw [hz, mul_zero]

/-- All three selected equations are distances from the actual polygon supporting lines. -/
lemma IsSideTangentRealization.circle_line_distance [NeZero n]
    {ρ : ZMod n → ℝ} {P N C : ZMod n → ℂ} (h : IsSideTangentRealization ρ P N C)
    (i k : ZMod n) (hk : k = i - 1 ∨ k = i ∨ k = i + 1) :
    ⟪N k, P k - C i⟫_ℝ = ρ i := by
  rcases hk with hk | hk | hk
  · rw [hk]
    have hz : ⟪N (i - 1), P i - P (i - 1)⟫_ℝ = 0 := by
      simpa only [sub_add_cancel] using h.normal_edge_orthogonal (i - 1)
    rw [show P (i - 1) - C i = (P i - C i) - (P i - P (i - 1)) by abel,
      inner_sub_right, (h.circles i).1, hz, sub_zero]
  · simpa only [hk] using (h.circles i).2.1
  · simpa only [hk] using (h.circles i).2.2

/-- Each prescribed circle meets each of its three actual supporting lines at exactly one
point. Only its central contact is required to belong to the finite edge segment. -/
theorem IsSideTangentRealization.tangent_sphere [NeZero n]
    {ρ : ZMod n → ℝ} {P N C : ZMod n → ℂ} (h : IsSideTangentRealization ρ P N C)
    (i k : ZMod n) (hk : k = i - 1 ∨ k = i ∨ k = i + 1) :
    Metric.sphere (C i) (ρ i) ∩ supportingLine P N k = {C i + ρ i • N k} :=
  sphere_inter_normalLine (h.unit_normal k) (h.radius_pos i).le (h.circle_line_distance i k hk)

end Gluck.Discrete.SideTangent
