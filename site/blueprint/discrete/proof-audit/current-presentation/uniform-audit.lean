import Gluck.Regularity.SpaceformUniform

open scoped ContDiff

namespace AppendixUniformAudit

-- Exact old interface, including its separate smoothness implication.
def OriginalUniform (A : (ℝ → ℝ) → ℝ → Prop)
    (R : (ℝ → ℂ) → (ℝ → ℝ) → Prop) : Prop :=
  ∀ (κ : ℝ → ℝ) (c : ℝ), Function.Periodic κ (2 * Real.pi) → Continuous κ →
    A κ c → Gluck.FourVertexAt κ c →
    ∃ γ : ℝ → ℂ, Gluck.IsSimpleClosed γ ∧ R γ κ ∧
      (∀ k : ℕ, ContDiff ℝ (k : ℕ∞ω) κ → ContDiff ℝ ((k + 2 : ℕ) : ℕ∞ω) γ) ∧
      (ContDiff ℝ ∞ κ → ContDiff ℝ ∞ γ)

theorem same_contract (A : ℝ → Prop) (R : (ℝ → ℂ) → (ℝ → ℝ) → Prop) :
    Gluck.UniformRegularStatement A R ↔ OriginalUniform (fun _ c ↦ A c) R := by
  constructor
  · intro h κ c hp hc hA hf
    obtain ⟨γ, hs, hr, hreg⟩ := h κ c hp hc hA hf
    exact ⟨γ, hs, hr, hreg, Gluck.smooth_of_uniform_regularity hreg⟩
  · intro h κ c hp hc hA hf
    obtain ⟨γ, hs, hr, hreg, _⟩ := h κ c hp hc hA hf
    exact ⟨γ, hs, hr, hreg⟩

example : OriginalUniform (fun _ c ↦ 0 < c) Gluck.RealizesCurvature :=
  (same_contract _ _).mp Gluck.dahlberg_converse_uniform
example : OriginalUniform (fun _ c ↦ 0 < c) Gluck.RealizesSphericalCurvature :=
  (same_contract _ _).mp Gluck.spherical_dahlberg_converse_uniform
example : OriginalUniform (fun _ c ↦ 1 < c) Gluck.RealizesHyperbolicCurvature :=
  (same_contract _ _).mp Gluck.hyperbolic_dahlberg_converse_uniform
example (M : Gluck.Regularity.Model) :
    OriginalUniform (fun _ c ↦ match M with | .hyperbolic => 1 < c | _ => 0 < c)
      (Gluck.Regularity.Model.Realizes M) :=
  (same_contract _ _).mp (Gluck.spaceform_dahlberg_converse_uniform M)

#print axioms same_contract
#print axioms Gluck.smooth_of_uniform_regularity
#print axioms Gluck.UniformRegularStatement.exists_smooth
#print axioms Gluck.dahlberg_converse_uniform
#print axioms Gluck.spherical_dahlberg_converse_uniform
#print axioms Gluck.hyperbolic_dahlberg_converse_uniform
#print axioms Gluck.spaceform_dahlberg_converse_uniform

end AppendixUniformAudit
