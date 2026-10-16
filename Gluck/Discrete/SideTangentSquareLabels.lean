module

public import Gluck.Discrete.SideTangentPerturbation

/-!
# Labelled collapsed-square configurations

The four corners and four side contacts are a finite limit configuration for
arbitrary polygon size. Coefficients are grouped only for the calculation;
all labels and their original coefficients remain in the perturbed realization.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace Topology

namespace Gluck.Discrete.SideTangent

/-- Four counterclockwise corners, followed by their intervening side contacts. -/
def squareSite : Fin 8 → ℂ :=
  ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]

/-- Grouped coefficients, with the alternating corner signs pulled out. -/
def weightsOfSites (g : Fin 8 → ℝ) : SquareWeights :=
  ⟨g 0, -g 1, g 2, -g 3, g 4, g 5, g 6, g 7⟩

/-- The eight-site finite rational sum is exactly the already verified square field. -/
lemma field_squareSite (g : Fin 8 → ℝ) (a : ℂ) :
    ProjectiveBall.field g squareSite a = (weightsOfSites g).field a := by
  apply Complex.ext <;>
    simp only [ProjectiveBall.field, Fin.sum_univ_succ, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im]
  all_goals simp [squareSite, ProjectiveBall.denominator, Complex.inner,
    SquareWeights.field, upperProjection, weightsOfSites]
  all_goals ring

variable {ι : Type*} [Fintype ι]

/-- Sum the original coefficients at each of the eight limit sites. -/
noncomputable def siteCoefficient (c : ι → ℝ) (tag : ι → Fin 8) (k : Fin 8) : ℝ :=
  ∑ i with tag i = k, c i

/-- Grouping coincident limit sites changes neither the rational field nor its zeros. -/
lemma field_group_sites (c : ι → ℝ) (tag : ι → Fin 8) (a : ℂ) :
    ProjectiveBall.field c (fun i ↦ squareSite (tag i)) a =
      ProjectiveBall.field (siteCoefficient c tag) squareSite a := by
  unfold ProjectiveBall.field siteCoefficient
  rw [← Finset.sum_fiberwise Finset.univ tag]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_div, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [(Finset.mem_filter.mp hi).2]

/-- The inset diamond avoids every pole of every square site. -/
lemma squareSite_denominator_pos {ε : ℝ} (hε : 0 < ε) {a : ℂ}
    (ha : a ∈ Complex.diamond (1 - ε)) (k : Fin 8) :
    0 < ProjectiveBall.denominator a (squareSite k) := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := diamond_denominators hε ha
  fin_cases k <;> simp [squareSite, ProjectiveBall.denominator, Complex.inner]
  all_goals linarith

/-- Every sufficiently close labelled configuration admits exact projective balance
when its four corner coefficients alternate in sign. All side coefficients are arbitrary. -/
theorem eventually_balance_near_square (c : ι → ℝ) (tag : ι → Fin 8)
    (hsum : ∑ i, c i = 0)
    (h₀ : 0 < siteCoefficient c tag 0) (h₁ : siteCoefficient c tag 1 < 0)
    (h₂ : 0 < siteCoefficient c tag 2) (h₃ : siteCoefficient c tag 3 < 0) :
    ∀ᶠ y in 𝓝 (fun i ↦ squareSite (tag i)),
      ∃ a : ℂ, ∃ σ : ℝ, ‖a‖ < 1 ∧ 0 < σ ∧ σ ^ 2 + ‖a‖ ^ 2 = 1 ∧
        (∀ i, 0 < ProjectiveBall.denominator a (y i)) ∧
        ∑ i, c i • ProjectiveBall.transform a σ (y i) = 0 := by
  have hw : (weightsOfSites (siteCoefficient c tag)).Positive :=
    ⟨h₀, neg_pos.mpr h₁, h₂, neg_pos.mpr h₃⟩
  obtain ⟨ε, hε, hε₁, hm⟩ := SquareWeights.exists_margins hw
  apply eventually_exists_projective_balance c (sub_pos.mpr hε₁)
    (by linarith : 1 - ε < 1) hsum
  · exact fun a ha i ↦ squareSite_denominator_pos hε ha (tag i)
  · have he : ProjectiveBall.field c (fun i ↦ squareSite (tag i)) =
        (weightsOfSites (siteCoefficient c tag)).field := by
      funext a
      rw [field_group_sites, field_squareSite]
    rw [he]
    exact SquareWeights.diamondSigns hw hε hm

end Gluck.Discrete.SideTangent
