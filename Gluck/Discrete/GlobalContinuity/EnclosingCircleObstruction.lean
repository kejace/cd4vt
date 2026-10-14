/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.GlobalContinuity.LevelBands
import Gluck.Forward.Discrete.MinimalDiskBoundaryRadius
import Gluck.Forward.Discrete.Section4AuxiliaryContradiction
import Gluck.Discrete.LocalRegularity
import Gluck.Discrete.TabachnikovFourActive

/-!
# The enclosing-radius obstruction for actual coherent hexagons

The special six-word path admits a shorter proof than the general enclosing-
circle level lemma: contact localization to three consecutive vertices
excludes level 9, and Dahlberg's two containing disks control the last endpoint.
-/

namespace Gluck.Discrete.GlobalContinuity

open Gluck.Forward

noncomputable def enclosingCenter {n : ℕ} [NeZero n] (v : ZMod n → ℂ) : ℂ :=
  (exists_minimalEnclosingDiskR2 v).choose

noncomputable def enclosingRadius {n : ℕ} [NeZero n] (v : ZMod n → ℂ) : ℝ :=
  (exists_minimalEnclosingDiskR2 v).choose_spec.choose

theorem enclosingDisk_minimal {n : ℕ} [NeZero n] (v : ZMod n → ℂ) :
    MinimalEnclosingDiskR2 v (enclosingCenter v) (enclosingRadius v) :=
  (exists_minimalEnclosingDiskR2 v).choose_spec.choose_spec

theorem enclosingRadius_le_add_dist {n : ℕ} [NeZero n]
    (v w : ZMod n → ℂ) : enclosingRadius v ≤ enclosingRadius w + dist v w := by
  have hv := enclosingDisk_minimal v
  have hw := enclosingDisk_minimal w
  apply hv.2.2 (enclosingCenter w) _ (add_nonneg hw.1 dist_nonneg)
  intro i
  apply Metric.mem_closedBall'.mpr
  calc
    dist (enclosingCenter w) (v i) ≤
        dist (enclosingCenter w) (w i) + dist (w i) (v i) := dist_triangle _ _ _
    _ ≤ enclosingRadius w + dist v w := add_le_add
      (Metric.mem_closedBall'.mp (hw.2.1 i))
      (by simpa [dist_comm] using dist_le_pi_dist w v i)

theorem enclosingRadius_lipschitz {n : ℕ} [NeZero n] :
    LipschitzWith 1 (enclosingRadius (n := n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, abs_le]
  have hv := enclosingRadius_le_add_dist v w
  have hw := enclosingRadius_le_add_dist w v
  simp only [NNReal.coe_one, one_mul]
  constructor <;> linarith [dist_comm v w]

/-- If all contacts fit in a vertex's defining triple, its curvature is
at most the reciprocal enclosing radius. No disk-ear descent is needed. -/
theorem curvature_le_level_of_contacts_in_triple
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : IsSimplePolygon v) (horient : PositivePolygonOrientation v)
    (hD : MinimalEnclosingDiskR2 v O R) (i : ZMod n)
    (hsub : ∀ j, OnDiskBoundaryR2 v O R j →
      j = i - 1 ∨ j = i ∨ j = i + 1) :
    SignedMengerProfile v i ≤ 1 / R := by
  have hr := EdgePrevCircleRadiusProfile_pos hsimple i
  have hR := radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hD hsimple
  have hle : R ≤ EdgePrevCircleRadiusProfile v i := by
    apply minimalEnclosingDiskR2_le_of_boundaryContactsInClosedDiskR2 hD hr.le
    intro j hj
    apply Metric.mem_closedBall'.mpr
    rcases hsub j hj with h | h | h
    · rw [h]
      exact (edgePrevCircle_dist_prev_eq_radius_of_positiveOrientation
        hsimple horient i).le
    · rw [h]
      exact (edgePrevCircle_dist_self_eq_radius_of_positiveOrientation
        hsimple horient i).le
    · rw [h]
      exact (edgePrevCircle_dist_next_eq_radius_of_positiveOrientation
        hsimple horient i).le
  rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
    hsimple horient i, ← one_div]
  exact one_div_le_one_div_of_le hR hle

theorem containing_curvature_le_neighbors
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hi : EdgePrevCurvatureDiskContainsAll v i) :
    SignedMengerProfile v i ≤ SignedMengerProfile v (i - 1) ∧
      SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1) := by
  have hh := edgePrevCircleRadiusProfile_neighbors_le_of_containsAll_of_positiveOrientation
    hsimple hregular horient hi
  simp only [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
    hsimple horient]
  constructor
  · exact inv_anti₀ (EdgePrevCircleRadiusProfile_pos hsimple (i - 1)) hh.1
  · exact inv_anti₀ (EdgePrevCircleRadiusProfile_pos hsimple (i + 1)) hh.2

theorem band_enclosing_level_ne_nine {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {v : ZMod 6 → ℂ} (hsimple : IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : PositivePolygonOrientation v)
    (hκ : SignedMengerProfile v = bandProfile s) :
    1 / enclosingRadius v ≠ 9 := by
  intro heq
  have hD := enclosingDisk_minimal v
  have hcontacts : ∀ j, OnDiskBoundaryR2 v (enclosingCenter v) (enclosingRadius v) j →
      j = 0 ∨ j = 1 ∨ j = 2 := by
    intro j hj
    have hh := signedMengerProfile_inv_radius_le_of_minimal_boundary_of_cross_pos
      hsimple hregular hD hj (horient j)
    rw [hκ, heq] at hh
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · norm_num [bandProfile] at hh
    · change (9 : ℝ) ≤ 7 - 3 * s at hh
      linarith [hs.1]
    · norm_num [bandProfile] at hh
  have hh := curvature_le_level_of_contacts_in_triple hsimple horient hD 1
    (by simpa only [show (1 : ZMod 6) - 1 = 0 by decide,
      show (1 : ZMod 6) + 1 = 2 by decide] using hcontacts)
  rw [hκ, heq] at hh
  norm_num [bandProfile] at hh

theorem band_zero_enclosing_level_le_seven
    {v : ZMod 6 → ℂ} (hsimple : IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : PositivePolygonOrientation v)
    (hκ : SignedMengerProfile v = bandProfile 0) :
    1 / enclosingRadius v ≤ 7 := by
  by_contra hnot
  have hgt : 7 < 1 / enclosingRadius v := lt_of_not_ge hnot
  simp only [one_div] at hgt
  have hD := enclosingDisk_minimal v
  have hc (j) (hj : OnDiskBoundaryR2 v (enclosingCenter v) (enclosingRadius v) j) :
      1 / enclosingRadius v ≤ bandProfile 0 j := by
    rw [← hκ]
    exact signedMengerProfile_inv_radius_le_of_minimal_boundary_of_cross_pos
      hsimple hregular hD hj (horient j)
  have hsub : ∀ j, OnDiskBoundaryR2 v (enclosingCenter v) (enclosingRadius v) j →
      j = 0 ∨ j = 1 ∨ j = 2 := by
    intro j hj
    have hh := hc j hj
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    all_goals norm_num [bandProfile] at hh; linarith
  have h11 := curvature_le_level_of_contacts_in_triple hsimple horient hD 1
    (by simpa only [show (1 : ZMod 6) - 1 = 0 by decide,
      show (1 : ZMod 6) + 1 = 2 by decide] using hsub)
  rw [hκ] at h11
  norm_num [bandProfile] at h11
  have hsub' : ∀ j, OnDiskBoundaryR2 v (enclosingCenter v) (enclosingRadius v) j →
      j = 0 ∨ j = 1 := by
    intro j hj
    have hh := hc j hj
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
    all_goals norm_num [bandProfile] at hh; linarith
  have h14 := curvature_le_level_of_contacts_in_triple hsimple horient hD 0 (by
    intro j hj
    rcases hsub' j hj with rfl | rfl <;> simp)
  rw [hκ] at h14
  norm_num [bandProfile] at h14
  have hsingle : ∀ j, OnDiskBoundaryR2 v (enclosingCenter v) (enclosingRadius v) j →
      j = 0 := by
    intro j hj
    have hh := hc j hj
    fin_cases j
    · rfl
    all_goals norm_num [bandProfile] at hh; linarith
  have hRle : enclosingRadius v ≤ 0 := by
    apply minimalEnclosingDiskR2_le_of_boundaryContactsInClosedDiskR2
      (C := v 0) hD le_rfl
    intro j hj
    rw [hsingle j hj]
    exact Metric.mem_closedBall'.mpr (by simp)
  exact (not_le_of_gt
    (radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hD hsimple)) hRle

theorem band_one_enclosing_level_ge_eleven
    {v : ZMod 6 → ℂ} (hsimple : IsSimplePolygon v)
    (hregular : DahlbergRegular v) (horient : PositivePolygonOrientation v)
    (hκ : SignedMengerProfile v = bandProfile 1) :
    11 ≤ 1 / enclosingRadius v := by
  have hnoncircle : ¬ Concyclic v := by
    intro hcircle
    have hconst := exists_constant_signedMengerProfile_of_concyclic_positiveOrientation
      hsimple hcircle horient
    exact bandProfile_nonconstant 1 (by simpa [hκ] using hconst)
  have hsupport : StrictConvexEdgeSupport v :=
    strictConvexEdgeSupport_of_simple_positiveOrientation hsimple horient
  obtain ⟨D⟩ := dahlbergE2Theorem6Lemma5ContainingDisks
    (by norm_num : 4 ≤ 6) hsimple horient hsupport
    (strictConvexCyclicChordGeometry_of_edgeSupport hsupport) hnoncircle
  by_contra hnot
  have hlt : 1 / enclosingRadius v < 11 := lt_of_not_ge hnot
  simp only [one_div] at hlt
  have hi (i : ZMod 6) (hcontains : EdgePrevCurvatureDiskContainsAll v i) : i = 5 := by
    have hn := containing_curvature_le_neighbors hsimple hregular horient hcontains
    have hl := signedMengerProfile_le_inv_minimalRadius_of_curvatureDiskContainsAll
      hsimple (enclosingDisk_minimal v) hcontains (horient i)
    rw [hκ] at hn hl
    fin_cases i
    · change (14 : ℝ) ≤ 3 ∧ 14 ≤ 11 at hn
      norm_num at hn
    · norm_num [bandProfile] at hl
      linarith
    · change (10 + 3 * (1 : ℝ)) ≤ 11 ∧ (10 + 3 * (1 : ℝ)) ≤ 5 at hn
      norm_num at hn
    · change (5 : ℝ) ≤ 10 + 3 * 1 ∧ 5 ≤ 7 - 3 * 1 at hn
      norm_num at hn
    · change (7 - 3 * (1 : ℝ)) ≤ 5 ∧ (7 - 3 * (1 : ℝ)) ≤ 3 at hn
      norm_num at hn
    · rfl
  have heq : D.i = D.j := (hi D.i D.contains_i).trans (hi D.j D.contains_j).symm
  exact D.distinct (congrArg (EdgePrevCurvatureCircleData v) heq)

/-- There is no continuous path of actual regular convex hexagons realizing
the specified nonconstant admissible profile path. -/
theorem no_continuous_coherent_hexagon_path :
    ¬ ∃ p : ℝ → (ZMod 6 → ℂ), ContinuousOn p (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsSimplePolygon (p s) ∧ DahlbergRegular (p s) ∧
        PositivePolygonOrientation (p s) ∧ SignedMengerProfile (p s) = bandProfile s := by
  rintro ⟨p, hp, hphysical⟩
  let c : ℝ → ℝ := fun s => 1 / enclosingRadius (p s)
  have hc : ContinuousOn c (Set.Icc 0 1) := by
    apply continuousOn_const.div (enclosingRadius_lipschitz.continuous.comp_continuousOn hp)
    intro s hs
    exact (radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon
      (enclosingDisk_minimal (p s)) (hphysical s hs).1).ne'
  obtain ⟨hS0,hR0,hO0,hK0⟩ := hphysical 0 (by norm_num)
  obtain ⟨hS1,hR1,hO1,hK1⟩ := hphysical 1 (by norm_num)
  have h0 : c 0 ≤ 7 := band_zero_enclosing_level_le_seven hS0 hR0 hO0 hK0
  have h1 : 11 ≤ c 1 := band_one_enclosing_level_ge_eleven hS1 hR1 hO1 hK1
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
    (show (9 : ℝ) ∈ Set.Icc (c 0) (c 1) from ⟨by linarith, by linarith⟩)
  obtain ⟨hS,hR,hO,hK⟩ := hphysical s hs
  exact band_enclosing_level_ne_nine hs hS hR hO hK heq

/-- The fixed positive band profile already forces positive orientation, so the global
obstruction needs only simplicity, Dahlberg regularity, and the prescribed curvatures. -/
theorem no_continuous_regular_hexagon_path :
    ¬ ∃ p : ℝ → (ZMod 6 → ℂ), ContinuousOn p (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsSimplePolygon (p s) ∧ DahlbergRegular (p s) ∧
        SignedMengerProfile (p s) = bandProfile s :=
  fun ⟨p, hp, h⟩ ↦ no_continuous_coherent_hexagon_path
    ⟨p, hp, fun s hs ↦ ⟨(h s hs).1, (h s hs).2.1,
      positivePolygonOrientation_iff_signedMengerProfile_pos.mpr
        (by simpa only [(h s hs).2.2] using bandProfile_pos hs), (h s hs).2.2⟩⟩

theorem dahlbergRegular_of_locallyRegular
    {n : ℕ} {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v)
    (hlocal : LocallyRegularR2 v) : DahlbergRegular v := by
  intro i
  obtain ⟨hcross, hcone⟩ := hlocal i
  let C := circumcenterR2 (v i) (v (i - 1)) (v (i + 1))
  have heq := circumcenterR2_equidist hcross
  have hCne : C ≠ v i := by
    intro h
    have hp : dist C (v (i - 1)) = dist C (v i) := heq.1
    rw [h, dist_self] at hp
    exact hsimple.1 (i - 1) (by simpa using (dist_eq_zero.mp hp).symm)
  right
  refine ⟨C, dist C (v i), ⟨dist_pos.mpr hCne, heq.1, rfl, heq.2⟩, ?_⟩
  obtain ⟨a,b,ha,hb,he⟩ := hcone
  refine ⟨a,b,ha,hb,?_⟩
  dsimp [C]
  rw [he]
  ring

/-- The counterexample in the original moderate-arc, closure, full-turn and
simplicity language of `RealizesR2`. Only continuity of the vertices is
assumed, making this stronger than an obstruction to C¹ length selection. -/
theorem no_continuous_tabachnikov_hexagon_path :
    ¬ ∃ lengths : ℝ → (ZMod 6 → ℝ),
      ContinuousOn (fun s => polygonR2 (bandProfile s) (lengths s)) (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ModerateArc 0 (bandProfile s) (lengths s) ∧
        closureGap (bandProfile s) (lengths s) = 0 ∧
        turningSum (bandProfile s) (lengths s) = 2 * Real.pi ∧
        IsSimplePolygon (polygonR2 (bandProfile s) (lengths s)) := by
  rintro ⟨lengths, hp, hreal⟩
  apply no_continuous_coherent_hexagon_path
  refine ⟨fun s => polygonR2 (bandProfile s) (lengths s), hp, ?_⟩
  intro s hs
  obtain ⟨hMA,hE,hT,hS⟩ := hreal s hs
  have hK : SignedMengerProfile (polygonR2 (bandProfile s) (lengths s)) = bandProfile s := by
    funext i
    let k := (i - 1).val
    have hk : (k : ZMod 6) = i - 1 := ZMod.natCast_rightInverse _
    have hh := signedMengerR2_development hMA k
    simpa only [SignedMengerProfile, vertexR2_eq_polygon hE hT,
      Nat.cast_add, Nat.cast_one, hk, sub_add_cancel] using hh
  exact ⟨hS, dahlbergRegular_of_locallyRegular hS
      (locallyRegular_development_moderate hMA (bandProfile_pos hs) hE hT),
    positiveOrientation_of_signedMengerProfile_pos hS
      (by rw [hK]; exact bandProfile_pos hs), hK⟩

/-- Every point of the counterexample path has an exact coherent realization.
The obstruction is to continuous selection, not pointwise existence. -/
theorem bandProfile_pointwise_realizable {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    RealizesR2 (bandProfile s) :=
  tabachnikovProblem2_all (by norm_num : 4 ≤ 6) _ (bandProfile_admissible hs)

end Gluck.Discrete.GlobalContinuity
