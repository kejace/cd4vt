import Gluck.Discrete.NativeOrderedFirstPair

/-!
# Exact angle coordinates of the orthogonal four-edge core

The identities concern the actual positive half-lengths and principal acute
angles. They provide the coordinate bridge for the incident-endpoint rank
calculation; no derivative-rank assumption is made here.
-/

namespace Gluck.Discrete.NativeOppositePure

open Set N6TypeAThreeCell

theorem coreHalfLengths_pos {u q v : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hq : 1 < q)
    (hv : 0 < v) (hv1 : v < 1) :
    ∀ i, 0 < orderedCoreHalfLengths u q v i := by
  obtain ⟨ha, hb, hc, hd⟩ := r_core_sides_pos (by norm_num : (0 : ℝ) < 1)
    hu (by linarith : 0 < q) hv hu1 (by linarith) hv1 (by linarith)
  intro i
  fin_cases i
  · exact div_pos ha (by norm_num)
  · exact div_pos hb (by norm_num)
  · exact div_pos hc (by norm_num)
  · exact div_pos hd (by norm_num)

/-- The four complementary-square identities retain their actual edge indices. -/
theorem coreHalfLengths_sq {u q v : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hq : 1 < q)
    (hv : 0 < v) (hv1 : v < 1) :
    let L := orderedCoreHalfLengths u q v
    (L 0) ^ 2 + (v * L 2) ^ 2 = 1 ∧
    (L 3) ^ 2 + (u * L 1) ^ 2 = 1 ∧
    (q * L 1) ^ 2 + (v * L 3) ^ 2 = 1 ∧
    (q * L 2) ^ 2 + (u * L 0) ^ 2 = 1 := by
  have hu2 : 0 ≤ 1 - u ^ 2 := by nlinarith
  have hv2 : 0 ≤ 1 - v ^ 2 := by nlinarith
  have hqu : 0 ≤ q ^ 2 - u ^ 2 := by nlinarith
  have hqv : 0 ≤ q ^ 2 - v ^ 2 := by nlinarith
  have hd : 0 < q ^ 2 - u ^ 2 * v ^ 2 := by
    have h := orthogonal_delta_pos_of_strict_alternation
      (by norm_num : (0 : ℝ) < 1) hu (by linarith : 0 < q) hv
      hu1 (by linarith) hv1 (by linarith)
    simpa [orthogonalDelta] using h
  have hdn : q ^ 2 - u ^ 2 * v ^ 2 ≠ 0 := ne_of_gt hd
  have hdn' : q ^ 2 - v ^ 2 * u ^ 2 ≠ 0 := by simpa [mul_comm] using hdn
  dsimp [orderedCoreHalfLengths]
  simp only [r_core_side_a_half_at_one, r_core_side_b_half_at_one,
    r_core_side_c_half_at_one, r_core_side_d_half_at_one,
    mul_pow, div_pow, Real.sq_sqrt hu2, Real.sq_sqrt hv2,
    Real.sq_sqrt hqu, Real.sq_sqrt hqv, Real.sq_sqrt hd.le]
  constructor
  · field_simp [hdn, hdn']
    ring
  constructor
  · field_simp [hdn, hdn']
    ring
  constructor
  · field_simp [hdn, hdn']
    ring
  · field_simp [hdn, hdn']
    ring

private theorem acute_cos_of_complement {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (h : x ^ 2 + y ^ 2 = 1) :
    x ∈ Ioo (0 : ℝ) 1 ∧ Real.cos (Real.arcsin x) = y := by
  have hx1 : x < 1 := by nlinarith [sq_pos_of_pos hy]
  refine ⟨⟨hx, hx1⟩, ?_⟩
  rw [Real.cos_arcsin]
  apply (Real.sqrt_eq_iff_eq_sq (by nlinarith : 0 ≤ 1 - x ^ 2) hy.le).mpr
  linarith

/-- Pure endpoint arguments and their positive cosine branches. -/
theorem coreHalfLengths_angle_data {u q v : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hq : 1 < q)
    (hv : 0 < v) (hv1 : v < 1) :
    let L := orderedCoreHalfLengths u q v
    (L 0 ∈ Ioo (0 : ℝ) 1 ∧ Real.cos (Real.arcsin (L 0)) = v * L 2) ∧
    (L 3 ∈ Ioo (0 : ℝ) 1 ∧ Real.cos (Real.arcsin (L 3)) = u * L 1) ∧
    (q * L 1 ∈ Ioo (0 : ℝ) 1 ∧ Real.cos (Real.arcsin (q * L 1)) = v * L 3) ∧
    (q * L 2 ∈ Ioo (0 : ℝ) 1 ∧ Real.cos (Real.arcsin (q * L 2)) = u * L 0) := by
  have hp := coreHalfLengths_pos hu hu1 hq hv hv1
  obtain ⟨h0, h3, h1, h2⟩ := coreHalfLengths_sq hu hu1 hq hv hv1
  exact ⟨acute_cos_of_complement (hp 0) (mul_pos hv (hp 2)) h0,
    acute_cos_of_complement (hp 3) (mul_pos hu (hp 1)) h3,
    acute_cos_of_complement (mul_pos (by linarith) (hp 1)) (mul_pos hv (hp 3)) h1,
    acute_cos_of_complement (mul_pos (by linarith) (hp 2)) (mul_pos hu (hp 0)) h2⟩

/-- The principal angles are all acute, in native cyclic order. -/
theorem coreHalfLengths_angles_acute {u q v : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hq : 1 < q)
    (hv : 0 < v) (hv1 : v < 1) :
    let L := orderedCoreHalfLengths u q v
    Real.arcsin (L 0) ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧
    Real.arcsin (L 3) ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧
    Real.arcsin (q * L 1) ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧
    Real.arcsin (q * L 2) ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
  obtain ⟨h0, h3, h1, h2⟩ := coreHalfLengths_angle_data hu hu1 hq hv hv1
  exact ⟨⟨Real.arcsin_pos.mpr h0.1.1, Real.arcsin_lt_pi_div_two.mpr h0.1.2⟩,
    ⟨Real.arcsin_pos.mpr h3.1.1, Real.arcsin_lt_pi_div_two.mpr h3.1.2⟩,
    ⟨Real.arcsin_pos.mpr h1.1.1, Real.arcsin_lt_pi_div_two.mpr h1.1.2⟩,
    ⟨Real.arcsin_pos.mpr h2.1.1, Real.arcsin_lt_pi_div_two.mpr h2.1.2⟩⟩

/-- Exact tangent coordinates, without a quotient-sign ambiguity. -/
theorem coreHalfLengths_tan {u q v : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hq : 1 < q)
    (hv : 0 < v) (hv1 : v < 1) :
    let L := orderedCoreHalfLengths u q v
    Real.tan (Real.arcsin (L 0)) = L 0 / (v * L 2) ∧
    Real.tan (Real.arcsin (L 3)) = L 3 / (u * L 1) ∧
    Real.tan (Real.arcsin (q * L 1)) = q * L 1 / (v * L 3) ∧
    Real.tan (Real.arcsin (q * L 2)) = q * L 2 / (u * L 0) := by
  obtain ⟨h0, h3, h1, h2⟩ := coreHalfLengths_angle_data hu hu1 hq hv hv1
  dsimp only
  constructor
  · rw [Real.tan_eq_sin_div_cos, h0.2, Real.sin_arcsin (by linarith [h0.1.1]) h0.1.2.le]
  constructor
  · rw [Real.tan_eq_sin_div_cos, h3.2, Real.sin_arcsin (by linarith [h3.1.1]) h3.1.2.le]
  constructor
  · rw [Real.tan_eq_sin_div_cos, h1.2, Real.sin_arcsin (by linarith [h1.1.1]) h1.1.2.le]
  · rw [Real.tan_eq_sin_div_cos, h2.2, Real.sin_arcsin (by linarith [h2.1.1]) h2.1.2.le]

/-- Both opposite tangent products have the same explicit positive value. -/
theorem coreHalfLengths_tan_products {u q v : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hq : 1 < q)
    (hv : 0 < v) (hv1 : v < 1) :
    let L := orderedCoreHalfLengths u q v
    Real.tan (Real.arcsin (L 0)) * Real.tan (Real.arcsin (q * L 2)) = q / (u * v) ∧
    Real.tan (Real.arcsin (L 3)) * Real.tan (Real.arcsin (q * L 1)) = q / (u * v) := by
  have hp := coreHalfLengths_pos hu hu1 hq hv hv1
  obtain ⟨h0, h3, h1, h2⟩ := coreHalfLengths_tan hu hu1 hq hv hv1
  dsimp only
  rw [h0, h3, h1, h2]
  constructor <;> field_simp [ne_of_gt hu, ne_of_gt hv,
    ne_of_gt (hp 0), ne_of_gt (hp 1), ne_of_gt (hp 2), ne_of_gt (hp 3)]

/-- The opposite tangent product is strictly greater than one. -/
theorem coreHalfLengths_tan_product_gt_one {u q v : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hq : 1 < q)
    (hv : 0 < v) (hv1 : v < 1) :
    let L := orderedCoreHalfLengths u q v
    1 < Real.tan (Real.arcsin (L 0)) * Real.tan (Real.arcsin (q * L 2)) := by
  dsimp only
  rw [(coreHalfLengths_tan_products hu hu1 hq hv hv1).1]
  apply (lt_div_iff₀ (mul_pos hu hv)).mpr
  have huv : u * v < 1 := (mul_lt_mul_of_pos_right hu1 hv).trans (by simpa using hv1)
  linarith

/-- Exact normalized cosine coefficients of the two pure turns. -/
theorem coreHalfLengths_normalized_cos {u q v : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hq : 1 < q)
    (hv : 0 < v) (hv1 : v < 1) :
    let L := orderedCoreHalfLengths u q v
    let α := Real.arcsin (L 0)
    let β := Real.arcsin (L 3)
    let γ := Real.arcsin (q * L 1)
    let δ := Real.arcsin (q * L 2)
    let P := Real.tan α / Real.tan γ
    let Q := 1 / (Real.tan γ * Real.tan δ)
    Real.cos (α + β) = (Q - P ^ 2) / Q * Real.cos α * Real.cos β ∧
    Real.cos (γ + δ) / q = P * (Q - 1) / Q * Real.cos α * Real.cos β := by
  have hp := coreHalfLengths_pos hu hu1 hq hv hv1
  obtain ⟨h0, h3, h1, h2⟩ := coreHalfLengths_angle_data hu hu1 hq hv hv1
  obtain ⟨t0, t3, t1, t2⟩ := coreHalfLengths_tan hu hu1 hq hv hv1
  dsimp only
  rw [t0, t1, t2, Real.cos_add, Real.cos_add, h0.2, h3.2, h1.2, h2.2,
    Real.sin_arcsin (by linarith [h0.1.1]) h0.1.2.le,
    Real.sin_arcsin (by linarith [h3.1.1]) h3.1.2.le,
    Real.sin_arcsin (by linarith [h1.1.1]) h1.1.2.le,
    Real.sin_arcsin (by linarith [h2.1.1]) h2.1.2.le]
  constructor <;> field_simp [ne_of_gt hu, ne_of_gt hv, ne_of_gt (show 0 < q by linarith),
    ne_of_gt (hp 0), ne_of_gt (hp 1), ne_of_gt (hp 2), ne_of_gt (hp 3)]

end Gluck.Discrete.NativeOppositePure
