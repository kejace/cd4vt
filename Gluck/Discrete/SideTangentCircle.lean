module

public import Gluck.Discrete.SideTangentContact
public import ForMathlib.Analysis.InnerProductSpace.ProjectiveSegments

/-!
# The prescribed inward circle for three consecutive supporting lines

The center is `p - r • x`, where `x` is the corresponding unit-incircle vertex
before positive edge scaling. Strict support of the next nonincident normal
forces uniqueness of both center and radius.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Gluck.Discrete.SideTangent

lemma eq_zero_of_two_inner_eq_zero {u v z : ℂ} (hcross : crossR2 0 u v ≠ 0)
    (hu : ⟪u, z⟫_ℝ = 0) (hv : ⟪v, z⟫_ℝ = 0) : z = 0 := by
  have hre : crossR2 0 u v * z.re = 0 := by
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hu hv
    simp only [crossR2, sub_zero]
    linear_combination v.im * hu - u.im * hv
  have him : crossR2 0 u v * z.im = 0 := by
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im] at hu hv
    simp only [crossR2, sub_zero]
    linear_combination u.re * hv - v.re * hu
  exact Complex.ext ((mul_eq_zero.mp hre).resolve_left hcross)
    ((mul_eq_zero.mp him).resolve_left hcross)

/-- Exact signed distances to the three supporting lines after scaling the central edge. -/
lemma threeLineCircle_equations {u v w x y p q : ℂ} {r : ℝ}
    (hux : ⟪u, x⟫_ℝ = 1) (hvx : ⟪v, x⟫_ℝ = 1) (hwy : ⟪w, y⟫_ℝ = 1)
    (hedge : q - p = r • (y - x)) :
    ⟪u, p - (p - r • x)⟫_ℝ = r ∧ ⟪v, p - (p - r • x)⟫_ℝ = r ∧
      ⟪w, q - (p - r • x)⟫_ℝ = r := by
  have hnext : q - (p - r • x) = r • y := by
    calc
      q - (p - r • x) = (q - p) + r • x := by abel
      _ = r • y := by rw [hedge, smul_sub]; abel
  simp only [sub_sub_cancel, hnext, real_inner_smul_right, hux, hvx, hwy, mul_one, and_self]

/-- Any inward circle at these three lines has exactly the prescribed center and radius. -/
theorem threeLineCircle_unique {u v w x y p q C : ℂ} {r ρ : ℝ}
    (hcross : crossR2 0 u v ≠ 0) (hux : ⟪u, x⟫_ℝ = 1) (hvx : ⟪v, x⟫_ℝ = 1)
    (hwy : ⟪w, y⟫_ℝ = 1) (hwx : ⟪w, x⟫_ℝ < 1)
    (hedge : q - p = r • (y - x))
    (hC₁ : ⟪u, p - C⟫_ℝ = ρ) (hC₂ : ⟪v, p - C⟫_ℝ = ρ)
    (hC₃ : ⟪w, q - C⟫_ℝ = ρ) : C = p - r • x ∧ ρ = r := by
  have hcenter : C = p - ρ • x := by
    have hz : p - C - ρ • x = 0 := eq_zero_of_two_inner_eq_zero hcross
      (by rw [inner_sub_right, hC₁, real_inner_smul_right, hux]; ring)
      (by rw [inner_sub_right, hC₂, real_inner_smul_right, hvx]; ring)
    linear_combination -hz
  have heq : q - C = r • y + (ρ - r) • x := by
    rw [hcenter]
    calc
      q - (p - ρ • x) = (q - p) + ρ • x := by abel
      _ = r • y + (ρ - r) • x := by rw [hedge, smul_sub, sub_smul]; abel
  rw [heq, inner_add_right, real_inner_smul_right, real_inner_smul_right, hwy] at hC₃
  have hr : ρ = r := by nlinarith
  exact ⟨hr ▸ hcenter, hr⟩

/-- Translating and scaling the balanced edge retains its actual interior contact. -/
lemma prescribedContact_mem_openSegment {u x y p q : ℂ} (r : ℝ)
    (hedge : q - p = r • (y - x)) (hu : u ∈ openSegment ℝ x y) :
    p + r • (u - x) ∈ openSegment ℝ p q := by
  obtain ⟨s, t, hs, ht, hst, he⟩ := hu
  refine ⟨s, t, hs, ht, hst, ?_⟩
  have hq : q = p + r • (y - x) := by rw [← hedge]; abel
  rw [hq, ← he]
  match_scalars
  · exact hst
  · ring
  · linear_combination -r * hst

end Gluck.Discrete.SideTangent
