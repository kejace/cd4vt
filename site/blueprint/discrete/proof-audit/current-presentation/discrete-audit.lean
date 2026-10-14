import Gluck.Discrete.TabachnikovCharacterization
import Gluck.Discrete.GlobalContinuity.EnclosingCircleObstruction
import Gluck.Discrete.NativeIncidentAcuteRank
import Gluck.Discrete.LocalContinuity

#print axioms Gluck.Discrete.tabachnikov_converse
#print axioms Gluck.Discrete.tabachnikov_converse_geometric
#print axioms Gluck.Discrete.IsCoherentConvexPolygon.signedMengerR2_eq_inv_of_radii
#print axioms Gluck.Discrete.IsCoherentConvexPolygon.not_concyclic4_of_radius_ne
#print axioms Gluck.Discrete.tabachnikov_radius_characterization
#print axioms Gluck.Discrete.GlobalContinuity.no_continuous_coherent_hexagon_path
#print axioms Gluck.Discrete.GlobalContinuity.no_continuous_regular_hexagon_path
#print axioms Gluck.Discrete.NativeIncidentProjective.projectiveH_eq_zero
#print axioms Gluck.Discrete.NativeIncidentProjective.not_projective_turn_solution
#print axioms Gluck.Discrete.NativeOppositePure.IncidentProjectiveRankLoss.false
#print axioms Gluck.Discrete.NativeOppositePure.fderiv_nativeLengthController_surjective_of_acute_orthogonal
#print axioms Gluck.Discrete.localContinuousRealization_of_dfv

open Gluck.Discrete Gluck.Forward

-- The compact geometric conclusion recovers every clause of the original public conclusion.
theorem geometric_conclusion_iff_full {n : ℕ} {r : ZMod n → ℝ} :
    (∃ v : ZMod n → ℂ, IsCoherentConvexPolygon v ∧
      ∀ i, vertexCircumradius v i = r i) ↔
    (∃ v : ZMod n → ℂ, IsCoherentConvexPolygon v ∧
      (∀ i, vertexCircumradius v i = r i) ∧
      (∀ i, signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = 1 / r i) ∧
      ((∀ i, r i ≠ r (i + 1)) →
        ∀ i, ¬ Concyclic4 (v (i - 1)) (v i) (v (i + 1)) (v (i + 2)))) := by
  constructor
  · rintro ⟨v, hv, hrad⟩
    exact ⟨v, hv, hrad, hv.signedMengerR2_eq_inv_of_radii hrad,
      fun hne i ↦ hv.not_concyclic4_of_radius_ne hrad i (hne i)⟩
  · rintro ⟨v, hv, hrad, _, _⟩
    exact ⟨v, hv, hrad⟩

-- The printed appendix's direct local interface has the complete instance context.
example {n : ℕ} [NeZero n] {κ₀ : ZMod n → ℝ} {c : ℝ}
    (hκ₀ : ∀ i, 0 < κ₀ i) (hdfv : DFV κ₀ c) :
    Nonempty (LocalDiscreteRealizationFamily κ₀) :=
  localContinuousRealization_of_dfv hκ₀ hdfv

open Gluck.Discrete.GlobalContinuity

-- For this fixed positive profile, dropping orientation changes no realizations.
theorem hexagon_condition_iff_oriented {v : ZMod 6 → ℂ} {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (IsSimplePolygon v ∧ DahlbergRegular v ∧ SignedMengerProfile v = bandProfile s) ↔
    (IsSimplePolygon v ∧ DahlbergRegular v ∧ PositivePolygonOrientation v ∧
      SignedMengerProfile v = bandProfile s) := by
  constructor
  · rintro ⟨hS, hR, hκ⟩
    exact ⟨hS, hR, positivePolygonOrientation_iff_signedMengerProfile_pos.mpr
      (by simpa only [hκ] using bandProfile_pos hs), hκ⟩
  · rintro ⟨hS, hR, _, hκ⟩
    exact ⟨hS, hR, hκ⟩

#print axioms geometric_conclusion_iff_full
#print axioms hexagon_condition_iff_oriented
