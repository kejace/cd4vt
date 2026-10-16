module

public import Gluck.Discrete.TabachnikovConverse
public import Gluck.Forward.Euclidean
public import Gluck.Forward.Discrete.PlateauBridge

/-!
# The exact Menger-radius characterization

For positive nonconstant cyclic radius data, coherent strictly convex
realizability is equivalent to two distinct plateau maxima and minima.
This combines Tabachnikov's converse with Dahlberg's formalized forward theorem;
it concerns vertex circumcircles, not circles tangent to supporting lines.
-/

@[expose] public section

namespace Gluck.Discrete

open Gluck.Forward

variable {n : ℕ}

/-- Coherence supplies Dahlberg's local regularity through the actual circumcircle. -/
lemma CoherentR2.dahlbergRegular {v : ZMod n → ℂ} (h : CoherentR2 v) :
    DahlbergRegular v := by
  intro i
  have hi := (h i).1
  have he := circumcenterR2_equidist hi
  have hp := pairwise_ne_of_crossR2_ne_zero hi
  have hR : 0 < vertexCircumradius v i := by
    apply dist_pos.mpr
    intro hc
    have hd := he.1
    rw [hc, dist_self] at hd
    exact hp.1 (dist_eq_zero.mp hd)
  obtain ⟨s, t, hs, ht, hC⟩ := (h i).2
  refine Or.inr ⟨circumcenterR2 (v i) (v (i - 1)) (v (i + 1)),
    vertexCircumradius v i, ⟨hR, he.1, rfl, he.2⟩, s, t, hs.le, ht.le, ?_⟩
  rw [hC]
  ring

/-- The paper's strict edge support gives positive orientation at every vertex. -/
lemma IsCoherentConvexPolygon.positivePolygonOrientation {v : ZMod n → ℂ}
    (h : IsCoherentConvexPolygon v) : PositivePolygonOrientation v := by
  intro i
  have hp := pairwise_ne_of_crossR2_ne_zero ((h.2.2 i).1)
  have ha : i + 1 ≠ i - 1 := by
    intro he
    exact hp.2.1 (congrArg v he).symm
  have hb : i + 1 ≠ i - 1 + 1 := by
    intro he
    exact hp.2.2 (congrArg v (by simpa only [sub_add_cancel] using he))
  simpa only [sub_add_cancel] using h.2.1 (i - 1) (i + 1) ha hb

/-- In the coherent counterclockwise case, the prescribed radius is the
reciprocal of the positive signed Menger curvature. -/
lemma IsCoherentConvexPolygon.vertexCircumradius_eq_inv {v : ZMod n → ℂ}
    (h : IsCoherentConvexPolygon v) (i : ZMod n) :
    vertexCircumradius v i = 1 / SignedMengerProfile v i := by
  rw [vertexCircumradius, dist_circumcenterR2_eq_inv_abs_signedMenger ((h.2.2 i).1),
    abs_of_pos (signedMengerR2_pos_iff_crossR2_pos.mpr (h.positivePolygonOrientation i))]
  rfl

/-- Prescribing the circumradii of a coherent convex polygon prescribes the reciprocal
signed Menger curvatures of that same polygon. -/
lemma IsCoherentConvexPolygon.signedMengerR2_eq_inv_of_radii
    {v : ZMod n → ℂ} {r : ZMod n → ℝ} (h : IsCoherentConvexPolygon v)
    (hrad : ∀ i, vertexCircumradius v i = r i) (i : ZMod n) :
    signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = 1 / r i := by
  simpa only [one_div_one_div, SignedMengerProfile_apply] using
    congrArg (fun x : ℝ ↦ 1 / x) ((h.vertexCircumradius_eq_inv i).symm.trans (hrad i))

/-- At any adjacent pair with unequal prescribed radii, the same coherent polygon's
four consecutive vertices are not concyclic. Other adjacent radii may be equal. -/
lemma IsCoherentConvexPolygon.not_concyclic4_of_radius_ne
    {v : ZMod n → ℂ} {r : ZMod n → ℝ} (h : IsCoherentConvexPolygon v)
    (hrad : ∀ i, vertexCircumradius v i = r i) (i : ZMod n)
    (hne : r i ≠ r (i + 1)) :
    ¬ Concyclic4 (v (i - 1)) (v i) (v (i + 1)) (v (i + 2)) :=
  fun hcon ↦ hne ((hrad i).symm.trans
    ((vertexCircumradius_eq_of_concyclic i (h.2.2 i).1 (h.2.2 (i + 1)).1 hcon).trans
      (hrad (i + 1))))

/-- **Corollary 1.2.** Positive nonconstant cyclic data are the vertex-circumradius
sequence of a coherent strictly convex polygon exactly when they have two distinct
plateau maxima and two distinct plateau minima. -/
theorem tabachnikov_radius_characterization [NeZero n] (hn : 4 ≤ n) {r : ZMod n → ℝ}
    (hr : ∀ i, 0 < r i) (hnc : ¬ ∃ c, ∀ i, r i = c) :
    (∃ v : ZMod n → ℂ, IsCoherentConvexPolygon v ∧
      ∀ i, vertexCircumradius v i = r i) ↔ IsPlateauTwoMaxTwoMin r := by
  constructor
  · rintro ⟨v, hv, hrad⟩
    have hnoncircle : ¬ Concyclic v := by
      intro hcircle
      obtain ⟨c, hc⟩ := exists_constant_signedMengerProfile_of_concyclic_positiveOrientation
        hv.1 hcircle hv.positivePolygonOrientation
      apply hnc
      refine ⟨1 / c, fun i ↦ ?_⟩
      rw [← hrad i, hv.vertexCircumradius_eq_inv i, hc i]
    have hfv := dahlberg_discrete_four_vertex_E2 hn v hv.1 hv.2.2.dahlbergRegular hnoncircle
    have hpos : ∀ i, 0 < SignedMengerProfile v i := fun i ↦
      signedMengerR2_pos_iff_crossR2_pos.mpr (hv.positivePolygonOrientation i)
    have hinv := dahlbergFourVertex_inv_of_pos hpos hfv
    have heq : ∀ i, r i = (SignedMengerProfile v i)⁻¹ := by
      intro i
      rw [← hrad i, hv.vertexCircumradius_eq_inv i, one_div]
    exact (dahlbergFourVertex_congr heq hinv).hasTwoPlateauMaxRuns_and_min
  · exact tabachnikov_converse_geometric hn hr

end Gluck.Discrete
