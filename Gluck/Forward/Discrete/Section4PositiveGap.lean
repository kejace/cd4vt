/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4MinimalDisk

/-!
# The positive complementary gap in Dahlberg Section 4

This file formalizes the interval-selection step after the contact set of a
minimal enclosing disk has been shown to be disconnected.  It selects a
maximal complementary run disjoint from the nonpositive-curvature interval
and proves the strict lower bound by applying the same connected-sublevel
argument at the threshold given by the reciprocal minimal radius.
-/

namespace Gluck

/-- The complement of a proper nonempty cyclic interval is a cyclic
interval. -/
theorem isCyclicInterval_univ_sdiff_of_isCyclicInterval_of_ne_univ
    {n : ℕ} [NeZero n] {S : Finset (ZMod n)}
    (hS : IsCyclicInterval S) (hproper : S ≠ Finset.univ) :
    IsCyclicInterval (Finset.univ \ S) := by
  classical
  rcases hS with ⟨c, a, b, hab, hbn, rfl⟩
  let d : ZMod n := cyclicLift c a
  let L : ℕ := b - a
  have hrange : Finset.Icc a b ⊆ Finset.range n := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact Finset.mem_range.mpr (lt_of_le_of_lt hk.2 hbn)
  have hcard := card_mapCut_of_subset_range c hrange
  have hLlt : L + 1 < n := by
    have hssub : mapCut c (Finset.Icc a b) ⊂
        (Finset.univ : Finset (ZMod n)) :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, hproper⟩
    have hcardlt := Finset.card_lt_card hssub
    have hunivcard : (Finset.univ : Finset (ZMod n)).card = n := by simp
    rw [hunivcard] at hcardlt
    rw [hcard, Nat.card_Icc] at hcardlt
    dsimp [L]
    omega
  have hcut : cutFinset d (Finset.univ \ mapCut c (Finset.Icc a b)) =
      Finset.Icc (L + 1) (n - 1) := by
    ext k
    rw [mem_cutFinset]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_Icc]
    by_cases hklt : k < n
    · have hmem : cyclicLift d k ∈ mapCut c (Finset.Icc a b) ↔
          k ≤ L := by
        constructor
        · intro hk
          rcases Finset.mem_image.mp hk with ⟨j, hj, hjEq⟩
          have haj : a ≤ j := (Finset.mem_Icc.mp hj).1
          have hjb : j ≤ b := (Finset.mem_Icc.mp hj).2
          let t : ℕ := j - a
          have hat : a + t = j := Nat.add_sub_of_le haj
          have htlt : t < n := by
            dsimp [t]
            omega
          have hlift : cyclicLift d t = cyclicLift c j := by
            dsimp [d, cyclicLift]
            rw [← hat, Nat.cast_add]
            ring
          have hkt : k = t :=
            cyclicLift_injOn_range d (Finset.mem_range.mpr hklt)
              (Finset.mem_range.mpr htlt) (hjEq.symm.trans hlift.symm)
          dsimp [L, t] at ⊢
          omega
        · intro hkL
          apply Finset.mem_image.mpr
          refine ⟨a + k, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
          · dsimp [L] at hkL
            omega
          · dsimp [d, cyclicLift]
            push_cast
            ring
      rw [hmem]
      omega
    · omega
  apply isCyclicInterval_of_isNatInterval_cutFinset d
  rw [hcut]
  exact ⟨L + 1, n - 1, by omega, rfl⟩

end Gluck

namespace Gluck.Forward

/-- A disconnected set has a maximal complementary run disjoint from any
connected subset of its complement.  The two cyclic neighbors of the run
belong to the original set. -/
theorem exists_maximal_complementary_run_disjoint_cyclicInterval
    {n : ℕ} [NeZero n] {E F : Finset (ZMod n)}
    (hEne : E.Nonempty) (hEproper : E ≠ Finset.univ)
    (hEnot : ¬ Gluck.IsCyclicInterval E)
    (hFinterval : Gluck.IsCyclicInterval F)
    (hFsub : F ⊆ Finset.univ \ E) :
    ∃ (c : ZMod n) (J : Finset (ZMod n)) (a b : ℕ),
      c ∈ E ∧
      Gluck.IsMaximalCyclicRunAt c (Finset.univ \ E) J ∧
      0 < a ∧ a ≤ b ∧ b < n ∧ b - a + 1 < n ∧
      J = Gluck.mapCut c (Finset.Icc a b) ∧
      Disjoint F J ∧
      Gluck.cyclicLift c (a - 1) ∈ E ∧
      Gluck.cyclicLift c (b + 1) ∈ E := by
  classical
  let T : Finset (ZMod n) := Finset.univ \ E
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := Gluck.exists_not_mem_of_ne_univ hEproper
    exact ⟨z, by simp [T, hz]⟩
  have hTproper : T ≠ Finset.univ := by
    rcases hEne with ⟨e, heE⟩
    intro hTuniv
    have heT : e ∈ T := by rw [hTuniv]; simp
    exact (by simpa [T] using heT : e ∉ E) heE
  have hTnot : ¬ Gluck.IsCyclicInterval T := by
    intro hTinterval
    have hEinterval : Gluck.IsCyclicInterval (Finset.univ \ T) :=
      Gluck.isCyclicInterval_univ_sdiff_of_isCyclicInterval_of_ne_univ
        hTinterval hTproper
    apply hEnot
    convert hEinterval using 1
    ext z
    simp [T]
  obtain ⟨c, R, Q, hc, hR, hQ, hRQ, _hRQdisjoint⟩ :=
    Gluck.exists_cut_with_two_disjoint_runs_of_not_interval
      hTne hTproper hTnot
  have hFsubT : F ⊆ T := by simpa [T] using hFsub
  rcases hR.disjoint_cyclicInterval_or_disjoint_cyclicInterval
      hc hQ hRQ hFinterval hFsubT with hFR | hFQ
  · obtain ⟨a, b, ha, hab, hbn, hlen, hReq, hleft, hright⟩ :=
      Gluck.maximalCyclicRunAt_has_gap_endpoints_of_cut_not_mem hc hR
    refine ⟨c, R, a, b, ?_, hR, ha, hab, hbn, hlen, hReq, hFR, ?_, ?_⟩
    · simpa [T] using hc
    · simpa [T] using hleft
    · simpa [T] using hright
  · obtain ⟨a, b, ha, hab, hbn, hlen, hQeq, hleft, hright⟩ :=
      Gluck.maximalCyclicRunAt_has_gap_endpoints_of_cut_not_mem hc hQ
    refine ⟨c, Q, a, b, ?_, hQ, ha, hab, hbn, hlen, hQeq, hFQ, ?_, ?_⟩
    · simpa [T] using hc
    · simpa [T] using hleft
    · simpa [T] using hright

/-- A connected cyclic set which contains a point outside a maximal run
cannot enter the run's closed one-vertex enlargement without crossing one of
its two excluded endpoints. -/
theorem cyclicInterval_disjoint_closedHat_of_disjoint_run
    {n : ℕ} [NeZero n]
    {F S J : Finset (ZMod n)} {c : ZMod n} {a b : ℕ}
    (ha : 0 < a) (_hab : a ≤ b) (hbn : b < n)
    (hJeq : J = Gluck.mapCut c (Finset.Icc a b))
    (hFne : F.Nonempty) (hcF : c ∉ F)
    (hFS : F ⊆ S) (hFJ : Disjoint F J)
    (hleft : Gluck.cyclicLift c (a - 1) ∉ S)
    (hright : Gluck.cyclicLift c (b + 1) ∉ S)
    (hSinterval : Gluck.IsCyclicInterval S) :
    ∀ k : ℕ, a - 1 ≤ k → k ≤ b + 1 →
      Gluck.cyclicLift c k ∉ S := by
  classical
  rcases hFne with ⟨q, hqF⟩
  have hqS : q ∈ S := hFS hqF
  have hqJ : q ∉ J := by
    exact Finset.disjoint_left.mp hFJ hqF
  let t : ℕ := (q - c).val
  have htlt : t < n := ZMod.val_lt (q - c)
  have htlift : Gluck.cyclicLift c t = q := by
    dsimp [Gluck.cyclicLift, t]
    rw [ZMod.natCast_zmod_val (q - c)]
    abel
  have htpos : 0 < t := by
    apply Nat.pos_of_ne_zero
    intro ht0
    apply hcF
    have hcq : c = q := by
      simpa [Gluck.cyclicLift, ht0] using htlift
    simpa [hcq] using hqF
  have htOutside : t < a - 1 ∨ b + 1 < t := by
    by_contra hout
    push Not at hout
    rcases hout with ⟨hleftle, htrightle⟩
    by_cases htleft : t = a - 1
    · apply hleft
      rw [← htleft, htlift]
      exact hqS
    by_cases htrightEq : t = b + 1
    · apply hright
      rw [← htrightEq, htlift]
      exact hqS
    apply hqJ
    rw [hJeq]
    apply Finset.mem_image.mpr
    refine ⟨t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, htlift⟩
  intro k hkleft hkright
  by_cases hkLeftEq : k = a - 1
  · simpa [hkLeftEq] using hleft
  by_cases hkRightEq : k = b + 1
  · simpa [hkRightEq] using hright
  have hak : a ≤ k := by omega
  have hkb : k ≤ b := by omega
  intro hkS
  rcases htOutside with htBefore | htAfter
  · have hrightBefore : b + 1 < t + n := by omega
    have htWrap : t + n < (a - 1) + n := by omega
    have htliftWrap : Gluck.cyclicLift c (t + n) = q := by
      calc
        Gluck.cyclicLift c (t + n) = Gluck.cyclicLift c t := by
          dsimp [Gluck.cyclicLift]
          rw [Nat.cast_add, ZMod.natCast_self]
          ring
        _ = q := htlift
    exact
      (not_isCyclicInterval_of_alternating_membership
        (S := S) (c := c) (a := a - 1) (q := k)
        (b := b + 1) (p := t + n)
        (by omega) (by omega) hrightBefore htWrap
        hleft hkS hright (by simpa [htliftWrap] using hqS)) hSinterval
  · have htWrap : t < (a - 1) + n := by omega
    exact
      (not_isCyclicInterval_of_alternating_membership
        (S := S) (c := c) (a := a - 1) (q := k)
        (b := b + 1) (p := t)
        (by omega) (by omega) htAfter htWrap
        hleft hkS hright (by simpa [htlift] using hqS)) hSinterval

/-- Once the minimal-disk contact set is disconnected, Dahlberg's selected
complementary run and its closed one-vertex enlargement have curvature
strictly greater than the reciprocal minimal radius. -/
theorem exists_section4_positive_gap_of_disconnected_contacts
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hcontactCross : ∀ i : ZMod n,
      OnDiskBoundaryR2 v O R i →
        0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hnot : ¬ DahlbergFourVertex (SignedMengerProfile v))
    (hnonpos : ∃ i : ZMod n, SignedMengerProfile v i ≤ 0)
    (hEdisconnected :
      ¬ Gluck.IsCyclicInterval (circleContactSet v O R)) :
    ∃ (c : ZMod n) (J : Finset (ZMod n)) (a b : ℕ),
      c ∈ circleContactSet v O R ∧
      Gluck.IsMaximalCyclicRunAt c
        (Finset.univ \ circleContactSet v O R) J ∧
      0 < a ∧ a ≤ b ∧ b < n ∧ b - a + 1 < n ∧
      J = Gluck.mapCut c (Finset.Icc a b) ∧
      Disjoint (NonpositiveVertices (SignedMengerProfile v)) J ∧
      Gluck.cyclicLift c (a - 1) ∈ circleContactSet v O R ∧
      Gluck.cyclicLift c (b + 1) ∈ circleContactSet v O R ∧
      ∀ k : ℕ, a - 1 ≤ k → k ≤ b + 1 →
        1 / R < SignedMengerProfile v (Gluck.cyclicLift c k) := by
  classical
  let κ : ZMod n → ℝ := SignedMengerProfile v
  let E : Finset (ZMod n) := circleContactSet v O R
  let F : Finset (ZMod n) := NonpositiveVertices κ
  have hRpos : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  have hinvPos : 0 < 1 / R := one_div_pos.mpr hRpos
  obtain ⟨q, hqNonpos⟩ := hnonpos
  have hqF : q ∈ F := by
    apply mem_nonpositiveVertices.mpr
    simpa [κ] using hqNonpos
  have hEne : E.Nonempty := by
    obtain ⟨e, he⟩ := exists_onDiskBoundaryR2_of_minimalEnclosingDiskR2 hΔ
    exact ⟨e, by simpa [E] using mem_circleContactSet.mpr (Metric.mem_sphere'.mp he)⟩
  have hFsub : F ⊆ Finset.univ \ E := by
    intro i hiF
    have hiNonpos : κ i ≤ 0 := mem_nonpositiveVertices.mp hiF
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hiE
    have hiBoundary : OnDiskBoundaryR2 v O R i :=
      Metric.mem_sphere'.mpr (mem_circleContactSet.mp (by simpa [E] using hiE))
    have hiLower :=
      signedMengerProfile_inv_radius_le_of_minimal_boundary_of_cross_pos
        hsimple hregular hΔ hiBoundary (hcontactCross i hiBoundary)
    dsimp [κ] at hiNonpos
    linarith
  have hEproper : E ≠ Finset.univ := by
    intro hEuniv
    have hqE : q ∈ E := by rw [hEuniv]; simp
    have hqNotE : q ∉ E := by simpa using hFsub hqF
    exact hqNotE hqE
  have hκnc : ¬ ∃ d, ∀ i : ZMod n, κ i = d := by
    simpa [κ] using
      not_constant_signedMengerProfile_of_not_concyclic
        hsimple hregular hnoncircle
  obtain ⟨_qmin, _qmax, _hmin, _hmax, _hlt, _htwo, hFinterval⟩ :=
    exists_globalMinMax_twoArcMonotone_and_nonpositiveConnected
      hκnc (by simpa [κ] using hnot) ⟨q, by simpa [κ] using hqNonpos⟩
  obtain ⟨c, J, a, b, hcE, hJmax, ha, hab, hbn, hlen,
      hJeq, hFJ, hleftE, hrightE⟩ :=
    exists_maximal_complementary_run_disjoint_cyclicInterval
      hEne hEproper (by simpa [E] using hEdisconnected)
      (by simpa [F] using hFinterval) hFsub
  let μ : ZMod n → ℝ := fun i => κ i - 1 / R
  let S : Finset (ZMod n) := NonpositiveVertices μ
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
  have hqμ : μ q ≤ 0 := by
    dsimp [μ, κ]
    linarith
  obtain ⟨_rmin, _rmax, _hrmin, _hrmax, _hrlt, _hrtwo, hSinterval⟩ :=
    exists_globalMinMax_twoArcMonotone_and_nonpositiveConnected
      hμnc hnotμ ⟨q, hqμ⟩
  have hFS : F ⊆ S := by
    intro i hiF
    apply mem_nonpositiveVertices.mpr
    have hi := mem_nonpositiveVertices.mp hiF
    dsimp [μ]
    linarith
  have hcF : c ∉ F := by
    intro hcFin
    have hcNotE : c ∉ E := by simpa using hFsub hcFin
    exact hcNotE hcE
  have haJ : Gluck.cyclicLift c a ∈ J := by
    rw [hJeq]
    exact Finset.mem_image.mpr ⟨a, by simp [hab], rfl⟩
  have hbJ : Gluck.cyclicLift c b ∈ J := by
    rw [hJeq]
    exact Finset.mem_image.mpr ⟨b, by simp [hab], rfl⟩
  have haNotE : Gluck.cyclicLift c a ∉ E := by
    have haT := hJmax.properties.2.2 haJ
    simpa using haT
  have hbNotE : Gluck.cyclicLift c b ∉ E := by
    have hbT := hJmax.properties.2.2 hbJ
    simpa using hbT
  have hleftBoundary : OnDiskBoundaryR2 v O R
      (Gluck.cyclicLift c (a - 1)) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp (by simpa [E] using hleftE))
  have hrightBoundary : OnDiskBoundaryR2 v O R
      (Gluck.cyclicLift c (b + 1)) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp (by simpa [E] using hrightE))
  have hleftNext : Gluck.cyclicLift c (a - 1) + 1 =
      Gluck.cyclicLift c a := by
    dsimp [Gluck.cyclicLift]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    push_cast
    ring
  have hrightPrev : Gluck.cyclicLift c (b + 1) - 1 =
      Gluck.cyclicLift c b := by
    dsimp [Gluck.cyclicLift]
    push_cast
    ring
  have hleftNextInterior :
      dist O (v (Gluck.cyclicLift c (a - 1) + 1)) < R := by
    apply lt_of_le_of_ne (Metric.mem_closedBall'.mp (hΔ.2.1 _))
    intro heq
    apply haNotE
    rw [← hleftNext]
    apply mem_circleContactSet.mpr
    exact heq
  have hrightPrevInterior :
      dist O (v (Gluck.cyclicLift c (b + 1) - 1)) < R := by
    apply lt_of_le_of_ne (Metric.mem_closedBall'.mp (hΔ.2.1 _))
    intro heq
    apply hbNotE
    rw [← hrightPrev]
    apply mem_circleContactSet.mpr
    exact heq
  have hκleft : 1 / R < κ (Gluck.cyclicLift c (a - 1)) := by
    dsimp [κ]
    exact signedMengerProfile_inv_radius_lt_of_minimal_boundary_of_cross_pos
      hsimple hregular hΔ hleftBoundary (Or.inr hleftNextInterior)
        (hcontactCross _ hleftBoundary)
  have hκright : 1 / R < κ (Gluck.cyclicLift c (b + 1)) := by
    dsimp [κ]
    exact signedMengerProfile_inv_radius_lt_of_minimal_boundary_of_cross_pos
      hsimple hregular hΔ hrightBoundary (Or.inl hrightPrevInterior)
        (hcontactCross _ hrightBoundary)
  have hleftNotS : Gluck.cyclicLift c (a - 1) ∉ S := by
    intro hiS
    have hi := mem_nonpositiveVertices.mp hiS
    dsimp [μ] at hi
    linarith
  have hrightNotS : Gluck.cyclicLift c (b + 1) ∉ S := by
    intro hiS
    have hi := mem_nonpositiveVertices.mp hiS
    dsimp [μ] at hi
    linarith
  have hhat := cyclicInterval_disjoint_closedHat_of_disjoint_run
    ha hab hbn hJeq ⟨q, hqF⟩ hcF hFS hFJ hleftNotS hrightNotS
      (by simpa [S] using hSinterval)
  refine ⟨c, J, a, b, ?_, ?_, ha, hab, hbn, hlen, hJeq, ?_, ?_, ?_, ?_⟩
  · simpa [E] using hcE
  · simpa [E] using hJmax
  · simpa [F, κ] using hFJ
  · simpa [E] using hleftE
  · simpa [E] using hrightE
  · intro k hkleft hkright
    have hkNotS := hhat k hkleft hkright
    have hkμ : ¬ μ (Gluck.cyclicLift c k) ≤ 0 := by
      intro hkμ
      apply hkNotS
      apply mem_nonpositiveVertices.mpr
      simpa [S] using hkμ
    dsimp [μ, κ] at hkμ ⊢
    linarith

/-- In the non-strict branch and under failure of the four-vertex conclusion,
the Section 4 maximal complementary run has curvature strictly above the
reciprocal minimal radius on its closed one-vertex enlargement. -/
theorem exists_section4_positive_gap
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
    ∃ (c : ZMod n) (J : Finset (ZMod n)) (a b : ℕ),
      c ∈ circleContactSet v O R ∧
      Gluck.IsMaximalCyclicRunAt c
        (Finset.univ \ circleContactSet v O R) J ∧
      0 < a ∧ a ≤ b ∧ b < n ∧ b - a + 1 < n ∧
      J = Gluck.mapCut c (Finset.Icc a b) ∧
      Disjoint (NonpositiveVertices (SignedMengerProfile v)) J ∧
      Gluck.cyclicLift c (a - 1) ∈ circleContactSet v O R ∧
      Gluck.cyclicLift c (b + 1) ∈ circleContactSet v O R ∧
      ∀ k : ℕ, a - 1 ≤ k → k ≤ b + 1 →
        1 / R < SignedMengerProfile v (Gluck.cyclicLift c k) := by
  have hnotPos : ¬ PositivePolygonOrientation v := by
    intro hpos
    exact hnonstrict (Or.inl hpos)
  have hnonpos :=
    exists_signedMengerProfile_nonpositive_of_not_positiveOrientation
      hsimple hnotPos
  have hEdisconnected :=
    circleContactSet_not_isCyclicInterval_of_minimalEnclosingDisk_of_not_dahlberg
      hsimple hregular hnoncircle hnonstrict hΔ hcontactCross hnot
  exact exists_section4_positive_gap_of_disconnected_contacts
    hsimple hregular hnoncircle hΔ hcontactCross hnot hnonpos hEdisconnected

end Gluck.Forward
