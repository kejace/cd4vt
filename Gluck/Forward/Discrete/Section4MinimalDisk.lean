/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.CyclicRunAvoidance
import Gluck.Forward.Discrete.Section4Combinatorics
import Gluck.Forward.Discrete.MinimalDiskContacts
import Gluck.Forward.Discrete.MinimalDiskBoundaryHull
import Gluck.Forward.Discrete.Section4ContactOrientation
import Gluck.Forward.Discrete.Dahlberg

/-!
# Minimal-disk contact combinatorics in Dahlberg Section 4

This file separates the connected-contact contradiction in the at-least-three
contact case from the remaining two-contact geometry.
-/

namespace Gluck.Forward

/-- A cyclic interval cannot contain two points separated in both directions
by points outside it.  The indices are written in one natural lift based at
`c`. -/
theorem not_isCyclicInterval_of_alternating_membership
    {n : ℕ} [NeZero n] {S : Finset (ZMod n)} {c : ZMod n}
    {a q b p : ℕ}
    (haq : a < q) (hqb : q < b) (hbp : b < p) (hpa : p < a + n)
    (ha : Gluck.cyclicLift c a ∉ S)
    (hq : Gluck.cyclicLift c q ∈ S)
    (hb : Gluck.cyclicLift c b ∉ S)
    (hp : Gluck.cyclicLift c p ∈ S) :
    ¬ Gluck.IsCyclicInterval S := by
  intro hS
  let d : ZMod n := Gluck.cyclicLift c a
  have hcut : Gluck.IsNatInterval (Gluck.cutFinset d S) :=
    hS.cutFinset_isNatInterval_of_not_mem ha
  rcases hcut with ⟨l, r, hlr, hcut⟩
  let q' : ℕ := q - a
  let b' : ℕ := b - a
  let p' : ℕ := p - a
  have hq'lt : q' < n := by
    dsimp [q']
    omega
  have hb'lt : b' < n := by
    dsimp [b']
    omega
  have hp'lt : p' < n := by
    dsimp [p']
    omega
  have hlift (k : ℕ) (hak : a ≤ k) :
      Gluck.cyclicLift d (k - a) = Gluck.cyclicLift c k := by
    dsimp [d, Gluck.cyclicLift]
    rw [Nat.cast_sub hak]
    ring
  have hqCut : q' ∈ Gluck.cutFinset d S := by
    apply Gluck.mem_cutFinset.mpr
    refine ⟨hq'lt, ?_⟩
    rw [hlift q (by omega)]
    exact hq
  have hpCut : p' ∈ Gluck.cutFinset d S := by
    apply Gluck.mem_cutFinset.mpr
    refine ⟨hp'lt, ?_⟩
    rw [hlift p (by omega)]
    exact hp
  have hbNotCut : b' ∉ Gluck.cutFinset d S := by
    intro hbCut
    have hbS := (Gluck.mem_cutFinset.mp hbCut).2
    apply hb
    rw [← hlift b (by omega)]
    exact hbS
  rw [hcut] at hqCut hpCut hbNotCut
  simp only [Finset.mem_Icc] at hqCut hpCut hbNotCut
  dsimp [q', b', p'] at hqCut hpCut hbNotCut
  omega

/-- Failure of positive orientation gives a nonpositive signed-Menger value. -/
theorem exists_signedMengerProfile_nonpositive_of_not_positiveOrientation
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnot : ¬ PositivePolygonOrientation v) :
    ∃ i : ZMod n, SignedMengerProfile v i ≤ 0 := by
  by_contra hnone
  push Not at hnone
  exact hnot (positiveOrientation_of_signedMengerProfile_pos hsimple hnone)

/-- Exactly two connected contacts are impossible for a locally regular
minimal-disk polygon.  Connectedness makes the contacts adjacent; the
two-contact theorem makes their chord a diameter, while the endpoint's
regular curvature circle has radius strictly smaller than the minimal radius
and contains the same chord. -/
theorem not_isCyclicInterval_circleContactSet_of_minimalEnclosingDisk_of_card_eq_two
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hcard : (circleContactSet v O R).card = 2) :
    ¬ Gluck.IsCyclicInterval (circleContactSet v O R) := by
  intro hinterval
  let E : Finset (ZMod n) := circleContactSet v O R
  rcases hinterval with ⟨c, a, b, hab, hbn, hE⟩
  have hrange : Finset.Icc a b ⊆ Finset.range n := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact Finset.mem_range.mpr (lt_of_le_of_lt hk.2 hbn)
  have hcardMap := Gluck.card_mapCut_of_subset_range c hrange
  have hlen : b = a + 1 := by
    have hcard' : (Gluck.mapCut c (Finset.Icc a b)).card = 2 := by
      rw [← hE]
      exact hcard
    rw [hcardMap, Nat.card_Icc] at hcard'
    omega
  let A : ZMod n := Gluck.cyclicLift c a
  let B : ZMod n := Gluck.cyclicLift c b
  have hAE : A ∈ circleContactSet v O R := by
    rw [hE]
    exact Finset.mem_image.mpr ⟨a, by simp [hab], rfl⟩
  have hBE : B ∈ circleContactSet v O R := by
    rw [hE]
    exact Finset.mem_image.mpr ⟨b, by simp [hab], rfl⟩
  have hBsucc : B = A + 1 := by
    dsimp [A, B, Gluck.cyclicLift]
    rw [hlen]
    push_cast
    ring
  have hboundaryPair : ∀ i : ZMod n,
      OnDiskBoundaryR2 v O R i → i = A ∨ i = B := by
    intro i hi
    have hiE : i ∈ Gluck.mapCut c (Finset.Icc a b) := by
      rw [← hE]
      exact mem_circleContactSet.mpr (Metric.mem_sphere'.mp hi)
    rcases Finset.mem_image.mp hiE with ⟨k, hk, hki⟩
    rw [Finset.mem_Icc, hlen] at hk
    have hka : k = a ∨ k = a + 1 := by omega
    rcases hka with rfl | rfl
    · exact Or.inl hki.symm
    · right
      simpa [B, hlen] using hki.symm
  have hABoundary : OnDiskBoundaryR2 v O R A :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hAE)
  have hBBoundary : OnDiskBoundaryR2 v O R B :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hBE)
  have hAprevNeA : v (A - 1) ≠ v A := by
    simpa [sub_eq_add_neg, add_assoc] using hsimple.1 (A - 1)
  have hAprevNeB : v (A - 1) ≠ v B := by
    rw [hBsucc]
    simpa [sub_eq_add_neg, add_assoc] using
      isSimplePolygon_two_step_ne hsimple (A - 1)
  have hAprevNotBoundary : ¬ OnDiskBoundaryR2 v O R (A - 1) := by
    intro hprev
    rcases hboundaryPair (A - 1) hprev with hprevA | hprevB
    · exact hAprevNeA (congrArg v hprevA)
    · exact hAprevNeB (congrArg v hprevB)
  have hAprevInterior : dist O (v (A - 1)) < R :=
    lt_of_le_of_ne (Metric.mem_closedBall'.mp (hΔ.2.1 (A - 1))) fun hdist =>
      hAprevNotBoundary (Metric.mem_sphere'.mpr hdist)
  have hdiam :=
    isDiameter_of_minimalEnclosingDiskR2_of_boundary_subset_pair
      hΔ hABoundary hBBoundary hboundaryPair
  have hcrossA :
      Gluck.Discrete.crossR2 (v (A - 1)) (v A) (v (A + 1)) ≠ 0 :=
    crossR2_ne_zero_of_minimalEnclosingDisk_boundary
      hsimple hregular hΔ hABoundary
  rcases hregular A with hcol | ⟨C, ρ, hcircle, hcone⟩
  · exact hcrossA hcol.1
  · have hcircle' : CircumcircleR2 (v A) (v (A - 1)) (v (A + 1)) C ρ :=
      ⟨hcircle.1, hcircle.2.2.1, hcircle.2.1, hcircle.2.2.2⟩
    have hρR : ρ ≤ R :=
      circumcircleR2_radius_le_of_inVertexCone_of_boundary
        hcircle' hcone hΔ.1 (Metric.mem_sphere'.mp hABoundary)
          (hΔ.2.1 (A - 1)) (hΔ.2.1 (A + 1))
    have hρne : ρ ≠ R := by
      intro hρeq
      have hcenters : O = C :=
        eq_circumcenter_of_inVertexCone_of_boundary_of_radius_eq
          hcircle' hcone hΔ.1 (Metric.mem_sphere'.mp hABoundary)
            (hΔ.2.1 (A - 1)) (hΔ.2.1 (A + 1)) hρeq
      rw [hcenters, ← hρeq, hcircle.2.1] at hAprevInterior
      exact (lt_irrefl ρ) hAprevInterior
    have hρR' : ρ < R := lt_of_le_of_ne hρR hρne
    have hdistLt : dist (v A) (v B) < 2 * R := by
      calc
        dist (v A) (v B) ≤ dist (v A) C + dist C (v B) :=
          dist_triangle _ _ _
        _ = 2 * ρ := by
          rw [dist_comm (v A), hcircle.2.2.1, hBsucc, hcircle.2.2.2]
          ring
        _ < 2 * R := by linarith
    linarith [hdiam.dist_left_right]

/-- In the at-least-three-contact case of Dahlberg's Section 4 argument, the
contact set of a positive minimal enclosing disk cannot be one cyclic
interval if the four-vertex conclusion fails.

The contact-turn hypothesis isolates the orientation fact used by the two
minimal-disk curvature comparison lemmas. -/
theorem circleContactSet_not_isCyclicInterval_of_minimalEnclosingDisk_of_three_le
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict :
      ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v))
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hcontactCross : ∀ i : ZMod n,
      OnDiskBoundaryR2 v O R i →
        0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hnot : ¬ DahlbergFourVertex (SignedMengerProfile v))
    (hcard : 3 ≤ (circleContactSet v O R).card) :
    ¬ Gluck.IsCyclicInterval (circleContactSet v O R) := by
  intro hinterval
  let κ : ZMod n → ℝ := SignedMengerProfile v
  let E : Finset (ZMod n) := circleContactSet v O R
  have hRpos : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  have hinvPos : 0 < 1 / R := one_div_pos.mpr hRpos
  have hκnc : ¬ ∃ d, ∀ i : ZMod n, κ i = d := by
    simpa [κ] using
      not_constant_signedMengerProfile_of_not_concyclic
        hsimple hregular hnoncircle
  have hnotPos : ¬ PositivePolygonOrientation v := by
    intro hpos
    exact hnonstrict (Or.inl hpos)
  obtain ⟨p, hpNonpos⟩ :=
    exists_signedMengerProfile_nonpositive_of_not_positiveOrientation
      hsimple hnotPos
  have hpNotE : p ∉ E := by
    intro hpE
    have hpBoundary : OnDiskBoundaryR2 v O R p := by
      exact Metric.mem_sphere'.mpr (mem_circleContactSet.mp (by simpa [E] using hpE))
    have hpLower :=
      signedMengerProfile_inv_radius_le_of_minimal_boundary_of_cross_pos
        hsimple hregular hΔ hpBoundary (hcontactCross p hpBoundary)
    linarith
  have hintervalE : Gluck.IsCyclicInterval E := by
    simpa [E] using hinterval
  have hcutInterval : Gluck.IsNatInterval (Gluck.cutFinset p E) :=
    hintervalE.cutFinset_isNatInterval_of_not_mem hpNotE
  rcases hcutInterval with ⟨a, b, hab, hcut⟩
  have hbCut : b ∈ Gluck.cutFinset p E := by
    rw [hcut]
    simp [hab]
  have hbn : b < n := (Gluck.mem_cutFinset.mp hbCut).1
  have haCut : a ∈ Gluck.cutFinset p E := by
    rw [hcut]
    simp [hab]
  have hapos : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro ha0
    have hpE : p ∈ E := by
      have := (Gluck.mem_cutFinset.mp haCut).2
      simpa [ha0, Gluck.cyclicLift] using this
    exact hpNotE hpE
  have hcardCut : 3 ≤ (Gluck.cutFinset p E).card := by
    rw [Gluck.card_cutFinset]
    simpa [E] using hcard
  rw [hcut, Nat.card_Icc] at hcardCut
  have ha2b : a + 2 ≤ b := by omega
  have hmemLift {k : ℕ} (hak : a ≤ k) (hkb : k ≤ b) :
      Gluck.cyclicLift p k ∈ E := by
    have hkCut : k ∈ Gluck.cutFinset p E := by
      rw [hcut]
      exact Finset.mem_Icc.mpr ⟨hak, hkb⟩
    exact (Gluck.mem_cutFinset.mp hkCut).2
  have hnotMemLift {k : ℕ} (hklt : k < n)
      (hkout : k < a ∨ b < k) :
      Gluck.cyclicLift p k ∉ E := by
    intro hkE
    have hkCut : k ∈ Gluck.cutFinset p E :=
      Gluck.mem_cutFinset.mpr ⟨hklt, hkE⟩
    rw [hcut] at hkCut
    simp only [Finset.mem_Icc] at hkCut
    omega
  let A : ZMod n := Gluck.cyclicLift p a
  let Q : ZMod n := Gluck.cyclicLift p (a + 1)
  let B : ZMod n := Gluck.cyclicLift p b
  have hAE : A ∈ E := by
    exact hmemLift le_rfl hab
  have hQE : Q ∈ E := by
    exact hmemLift (by omega) (by omega)
  have hQnextE : Q + 1 ∈ E := by
    have hmem := hmemLift (k := a + 2) (by omega) ha2b
    have heq : Q + 1 = Gluck.cyclicLift p (a + 2) := by
      dsimp [Q, Gluck.cyclicLift]
      push_cast
      ring
    rwa [heq]
  have hBE : B ∈ E := by
    exact hmemLift hab le_rfl
  have hAprevEq : A - 1 = Gluck.cyclicLift p (a - 1) := by
    dsimp [A, Gluck.cyclicLift]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    push_cast
    ring
  have hAprevNotE : A - 1 ∉ E := by
    rw [hAprevEq]
    exact hnotMemLift (by omega) (Or.inl (by omega))
  have hBnextNotE : B + 1 ∉ E := by
    by_cases hbnext : b + 1 < n
    · have heq : B + 1 = Gluck.cyclicLift p (b + 1) := by
        dsimp [B, Gluck.cyclicLift]
        push_cast
        ring
      rw [heq]
      exact hnotMemLift hbnext (Or.inr (by omega))
    · have hbeq : b + 1 = n := by omega
      have heq : B + 1 = p := by
        dsimp [B, Gluck.cyclicLift]
        calc
          p + (b : ZMod n) + 1 = p + ((b + 1 : ℕ) : ZMod n) := by
            push_cast
            ring
          _ = p + (n : ZMod n) := by rw [hbeq]
          _ = p := by rw [ZMod.natCast_self, add_zero]
      rwa [heq]
  have hABoundary : OnDiskBoundaryR2 v O R A :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp (by simpa [E] using hAE))
  have hQBoundary : OnDiskBoundaryR2 v O R Q :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp (by simpa [E] using hQE))
  have hQnextBoundary : OnDiskBoundaryR2 v O R (Q + 1) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp (by simpa [E] using hQnextE))
  have hBBoundary : OnDiskBoundaryR2 v O R B :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp (by simpa [E] using hBE))
  have hAprevInterior : dist O (v (A - 1)) < R :=
    lt_of_le_of_ne (Metric.mem_closedBall'.mp (hΔ.2.1 (A - 1))) fun hdist =>
      hAprevNotE (by
        apply mem_circleContactSet.mpr
        exact hdist)
  have hBnextInterior : dist O (v (B + 1)) < R :=
    lt_of_le_of_ne (Metric.mem_closedBall'.mp (hΔ.2.1 (B + 1))) fun hdist =>
      hBnextNotE (by
        apply mem_circleContactSet.mpr
        exact hdist)
  have hκA : 1 / R < κ A := by
    simpa [κ] using
      signedMengerProfile_inv_radius_lt_of_minimal_boundary_of_cross_pos
        hsimple hregular hΔ hABoundary (Or.inl hAprevInterior)
          (hcontactCross A hABoundary)
  have hQprevEq : Q - 1 = A := by
    dsimp [Q, A, Gluck.cyclicLift]
    push_cast
    ring
  have hκQ : κ Q = 1 / R := by
    dsimp [κ]
    apply signedMengerProfile_eq_inv_radius_of_three_boundaries_of_cross_pos
      hsimple hRpos
    · simpa [hQprevEq] using hABoundary
    · exact hQBoundary
    · exact hQnextBoundary
    · exact hcontactCross Q hQBoundary
  have hκB : 1 / R < κ B := by
    simpa [κ] using
      signedMengerProfile_inv_radius_lt_of_minimal_boundary_of_cross_pos
        hsimple hregular hΔ hBBoundary (Or.inr hBnextInterior)
          (hcontactCross B hBBoundary)
  let μ : ZMod n → ℝ := fun i => κ i - 1 / R
  have hμnc : ¬ ∃ d, ∀ i : ZMod n, μ i = d := by
    rintro ⟨d, hd⟩
    apply hκnc
    refine ⟨d + 1 / R, fun i => ?_⟩
    have hi := hd i
    dsimp [μ] at hi
    linarith
  have hnotμ : ¬ DahlbergFourVertex μ := by
    intro hfv
    apply hnot
    apply (dahlbergFourVertex_posAffine_iff
      (n := n) (κ := κ) (a := 1) (b := -(1 / R)) (by norm_num)).mp
    simpa only [μ, one_mul, sub_eq_add_neg] using hfv
  have hpμ : μ p ≤ 0 := by
    dsimp [μ, κ] at ⊢
    linarith
  obtain ⟨_qmin, _qmax, _hmin, _hmax, _hlt, _htwo, hnonposInterval⟩ :=
    exists_globalMinMax_twoArcMonotone_and_nonpositiveConnected
      hμnc hnotμ ⟨p, hpμ⟩
  let S : Finset (ZMod n) := NonpositiveVertices μ
  have hAS : A ∉ S := by
    rw [show A ∉ S ↔ ¬ μ A ≤ 0 by simp [S]]
    dsimp [μ]
    linarith
  have hQS : Q ∈ S := by
    apply mem_nonpositiveVertices.mpr
    dsimp [μ]
    linarith
  have hBS : B ∉ S := by
    rw [show B ∉ S ↔ ¬ μ B ≤ 0 by simp [S]]
    dsimp [μ]
    linarith
  have hpS : Gluck.cyclicLift p n ∈ S := by
    have hpS' : p ∈ S := mem_nonpositiveVertices.mpr hpμ
    simpa [Gluck.cyclicLift] using hpS'
  exact (not_isCyclicInterval_of_alternating_membership
    (S := S) (c := p) (a := a) (q := a + 1) (b := b) (p := n)
    (by omega) (by omega) hbn (by omega)
    (by simpa [A] using hAS)
    (by simpa [Q] using hQS)
    (by simpa [B] using hBS) hpS)
    (by simpa [S] using hnonposInterval)

/-- Dahlberg's minimal-disk contact set is disconnected in the non-strict,
nonconcyclic branch whenever the signed-Menger four-vertex conclusion is
assumed to fail.  The two-contact case is the Euclidean diameter obstruction;
the at-least-three-contact case is the connected-sublevel obstruction. -/
theorem circleContactSet_not_isCyclicInterval_of_minimalEnclosingDisk_of_not_dahlberg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict :
      ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v))
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hcontactCross : ∀ i : ZMod n,
      OnDiskBoundaryR2 v O R i →
        0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hnot : ¬ DahlbergFourVertex (SignedMengerProfile v)) :
    ¬ Gluck.IsCyclicInterval (circleContactSet v O R) := by
  have hRpos : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  obtain ⟨p, hp⟩ := exists_onDiskBoundaryR2_of_minimalEnclosingDiskR2 hΔ
  have hcardTwo : 2 ≤ (circleContactSet v O R).card :=
    two_le_card_circleContactSet_of_minimalEnclosingDiskR2 hΔ hRpos hp
  by_cases hcardThree : 3 ≤ (circleContactSet v O R).card
  · exact
      circleContactSet_not_isCyclicInterval_of_minimalEnclosingDisk_of_three_le
        hsimple hregular hnoncircle hnonstrict hΔ hcontactCross hnot hcardThree
  · have hcardEq : (circleContactSet v O R).card = 2 := by omega
    exact
      not_isCyclicInterval_circleContactSet_of_minimalEnclosingDisk_of_card_eq_two
        hsimple hregular hΔ hcardEq

end Gluck.Forward
