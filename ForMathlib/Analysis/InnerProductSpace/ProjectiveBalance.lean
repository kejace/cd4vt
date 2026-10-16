module

public import ForMathlib.Analysis.InnerProductSpace.ProjectiveBall

/-!
# Weighted balance under projective ball normalization

A zero of the finite rational field becomes an exact weighted balance of the
transformed vertices. The coefficients themselves are unchanged.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace ProjectiveBall

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

/-- The rational field associated to fixed labelled vertices and real coefficients. -/
noncomputable def field (c : ι → ℝ) (x : ι → E) (a : E) : E :=
  ∑ i, (c i / denominator a (x i)) • x i

/-- The sum of coefficient quotients is determined by the field and coefficient sum. -/
lemma sum_div_denominator (c : ι → ℝ) (x : ι → E) (a : E)
    (hden : ∀ i, denominator a (x i) ≠ 0) :
    ∑ i, c i / denominator a (x i) = (∑ i, c i) + ⟪a, field c x a⟫_ℝ := by
  have hi : ∀ i, c i / denominator a (x i) =
      c i + (c i / denominator a (x i)) * ⟪a, x i⟫_ℝ := by
    intro i
    have hn := hden i
    unfold denominator at hn ⊢
    field_simp
    ring
  simpa only [field, inner_sum, real_inner_smul_right, Finset.sum_add_distrib] using
    Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ ↦ hi i)

/-- A finite sum commutes with the linear part of the projective numerator. -/
lemma sum_smul_numerator (w : ι → ℝ) (x : ι → E) (a : E) (σ : ℝ) :
    ∑ i, w i • numerator a σ (x i) =
      σ • (∑ i, w i • x i) +
        (⟪a, ∑ i, w i • x i⟫_ℝ / (1 + σ) - ∑ i, w i) • a := by
  simp only [numerator, smul_add, smul_smul, Finset.sum_add_distrib,
    inner_sum, real_inner_smul_right]
  simp only [Finset.smul_sum, smul_smul, mul_sub, mul_one, sub_smul, ← mul_div_assoc,
    Finset.sum_sub_distrib, ← Finset.sum_smul, ← Finset.sum_div, mul_comm]

/-- Every zero of the rational field gives the exact labelled projective balance. -/
theorem sum_smul_transform_eq_zero_of_field_eq_zero (c : ι → ℝ) (x : ι → E)
    (a : E) (σ : ℝ) (hden : ∀ i, denominator a (x i) ≠ 0)
    (hsum : ∑ i, c i = 0) (hfield : field c x a = 0) :
    ∑ i, c i • transform a σ (x i) = 0 := by
  have hw : ∑ i, c i / denominator a (x i) = 0 := by
    rw [sum_div_denominator c x a hden, hsum, hfield, inner_zero_right, add_zero]
  have he : ∑ i, c i • transform a σ (x i) =
      ∑ i, (c i / denominator a (x i)) • numerator a σ (x i) := by
    simp only [transform, smul_smul, div_eq_mul_inv]
  rw [he, sum_smul_numerator]
  change σ • field c x a + (⟪a, field c x a⟫_ℝ / (1 + σ) - _) • a = 0
  simp only [hfield, inner_zero_right, zero_div, hw, sub_self, smul_zero, zero_smul, add_zero]

end ProjectiveBall
