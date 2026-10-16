/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.RotationalCollar

/-!
# Realizability is open at a regular configuration

At a point of the regular collar interior the joint map
`(closureMapR3, Prod.fst)` is a submersion, so
`projImage_mem_nhds_of_jointSubmersion` makes the PROFILE image of the
regular collar interior a neighbourhood of the profile — realizability is
open there, not merely nonempty.  Combined with the rotational witnesses of
`RotationalCollar.lean` and the openness of the strict four-vertex window,
this produces at every composite `n ≥ 6` a full-dimensional open family of
profiles that are simultaneously `DiscreteFourVertexPos` and `RealizesR2`,
including profiles fixed by no nontrivial rotation.

* `isOpen_positiveProfile`, `DFV.eventually`,
  `DiscreteFourVertexPos.eventually_of_window` — the two open conditions.
* `profileImage_mem_nhds_of_collarRegular` — the load-bearing step: over the
  chamber `univ` the profile image of the regular collar interior is a
  neighbourhood of each of its profiles.
* `realizesR2_eventually_of_collarRegular`,
  `realizesR2_eventually_of_collarRegularInterior_nonempty`,
  `realizesR2_eventually_of_periodic`,
  `interior_realizesR2_nonempty_of_notPrime` — the realizability readouts.
* `blockSpikeProfile_dfv`, `exists_nhds_dfv_realizesR2`,
  `exists_nhds_dfv_realizesR2_of_notPrime`,
  `exists_dfv_realizesR2_no_period` — the four-vertex family.

**Honest scope.**  This is a LOCAL result: it does not cover the DFV
chamber and cannot be iterated to a covering (that is exactly cruxes A′ and
B′, both open).  The analytic step is a standard inverse-function-theorem
argument; the substance is the rank input, which FAILS on the
constant-curvature stratum (`not_momentRank_of_const_curvature`), so no
neighbourhood of a regular `n`-gon is available by this route.  Prime `n`,
`m = 2`, and `n = 4` gain nothing here; nothing here settles Tabachnikov's
Problem 2.

-/

@[expose] public section

namespace Gluck.Discrete

open Filter Set
open scoped Topology

variable {n : ℕ}

/-! ## Two open conditions -/

/-- **`lem:collaropen_pos_open`.**  Strict positivity of a profile is an open
condition: the set is the finite intersection over `i : ZMod n` of the
preimages of `(0, ∞)` under the continuous coordinate evaluations. -/
theorem isOpen_positiveProfile [NeZero n] :
    IsOpen {κ : ZMod n → ℝ | ∀ i, 0 < κ i} := by
  have heq : {κ : ZMod n → ℝ | ∀ i, 0 < κ i}
      = ⋂ i : ZMod n, {κ : ZMod n → ℝ | 0 < κ i} := by
    ext κ
    simp [Set.mem_iInter]
  rw [heq]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_apply i)

/-- **`lem:collaropen_dfv_open`.**  A four-vertex window persists on a
neighbourhood: keep the same four lifted indices; each of the four strict
inequalities is between a constant and a continuous coordinate evaluation,
hence holds on a neighbourhood. -/
theorem DFV.eventually {κ : ZMod n → ℝ} {c : ℝ} (h : DFV κ c) :
    ∀ᶠ κ' in 𝓝 κ, DFV κ' c := by
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, hκ1, hκ2, hκ3, hκ4⟩ := h
  have hgt : ∀ i : ZMod n, c < κ i → ∀ᶠ κ' in 𝓝 κ, c < κ' i := fun i hi =>
    (isOpen_lt continuous_const (continuous_apply i)).eventually_mem hi
  have hlt : ∀ i : ZMod n, κ i < c → ∀ᶠ κ' in 𝓝 κ, κ' i < c := fun i hi =>
    (isOpen_lt (continuous_apply i) continuous_const).eventually_mem hi
  filter_upwards [hgt _ hκ1, hlt _ hκ2, hgt _ hκ3, hlt _ hκ4]
    with κ' h1 h2 h3 h4
  exact ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, h1, h2, h3, h4⟩

/-- **`lem:collaropen_dfvpos_open`.**  Positivity plus a four-vertex window
at a positive level makes the positive four-vertex hypothesis hold on a
neighbourhood, through the right-hand disjunct at the same level. -/
theorem DiscreteFourVertexPos.eventually_of_window [NeZero n]
    {κ : ZMod n → ℝ} {c : ℝ} (hpos : ∀ i, 0 < κ i) (hc : 0 < c)
    (h : DFV κ c) :
    ∀ᶠ κ' in 𝓝 κ, DiscreteFourVertexPos κ' := by
  filter_upwards [isOpen_positiveProfile.eventually_mem hpos, h.eventually]
    with κ' h1 h2
  exact ⟨h1, Or.inr ⟨c, hc, h2⟩⟩

/-! ## The submersion opens the profile image -/

/-- **`thm:collaropen_profile_nhds`.**  At a point of the regular collar
interior over the chamber `univ`, the profile image of the regular collar
interior is a neighbourhood of the profile: the moment rank gives joint
surjectivity of `(closureMapR3, Prod.fst)` through the fibre split, and
`projImage_mem_nhds_of_jointSubmersion` opens the image.  This is the
`hlocal` block of `realizesR2_of_collar_regular` with the chamber `univ`, so
the `𝓝[S]` side condition disappears. -/
theorem profileImage_mem_nhds_of_collarRegular [NeZero n]
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)}
    (hp : p ∈ collarRegularInterior (Set.univ : Set (ZMod n → ℝ))) :
    Prod.fst '' collarRegularInterior (Set.univ : Set (ZMod n → ℝ))
      ∈ 𝓝 p.1 := by
  obtain ⟨hpI, hpR⟩ := hp
  obtain ⟨G', hG⟩ := closureMapR3_hasStrictFDerivAt hpI.2.1
  have hfd : fderiv ℝ closureMapR3 p = G' := hG.hasFDerivAt.fderiv
  have hsurj : (G'.prod
      (ContinuousLinearMap.fst ℝ (ZMod n → ℝ) (ZMod n → ℝ))).range = ⊤ := by
    rw [← hfd]
    exact (range_prod_fst_eq_top_iff _).mpr
      ((lengthRank_iff_momentRank hpI).mpr hpR)
  have h0 : Prod.fst ''
      ({y : (ZMod n → ℝ) × (ZMod n → ℝ) | closureMapR3 y = 0} ∩
        {q : (ZMod n → ℝ) × (ZMod n → ℝ) |
          ModerateArc 0 q.1 q.2 ∧ MomentRank q.1 q.2})
      ∈ 𝓝 p.1 :=
    projImage_mem_nhds_of_jointSubmersion hpI.2.2 hG hasStrictFDerivAt_fst
      hsurj (isOpen_momentRank.mem_nhds ⟨hpI.2.1, hpR⟩) Set.Subset.rfl
  refine Filter.mem_of_superset h0 ?_
  rintro κ' ⟨y, ⟨hy0, hyMA, hyMR⟩, rfl⟩
  exact ⟨y, ⟨⟨Set.mem_univ _, hyMA, hy0⟩, hyMR⟩, rfl⟩

/-- **`thm:collaropen_eventually`.**  Realizability holds on a neighbourhood
of the profile of any positive-profile point of the regular collar interior
over `univ`: intersect the profile-image neighbourhood with the open
positivity set and apply the Positive-Convexity Collapse. -/
theorem realizesR2_eventually_of_collarRegular [NeZero n] (hn : 3 ≤ n)
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)}
    (hp : p ∈ collarRegularInterior (Set.univ : Set (ZMod n → ℝ)))
    (hpos : ∀ i, 0 < p.1 i) :
    ∀ᶠ κ in 𝓝 p.1, RealizesR2 κ := by
  have himg : ∀ᶠ κ in 𝓝 p.1,
      κ ∈ Prod.fst '' collarRegularInterior (Set.univ : Set (ZMod n → ℝ)) :=
    profileImage_mem_nhds_of_collarRegular hp
  filter_upwards [himg, isOpen_positiveProfile.eventually_mem hpos]
    with κ hκ hκpos
  obtain ⟨q, hq, rfl⟩ := hκ
  exact realizesR2_of_mem_collarInterior hn hq.1 hκpos

/-- **`cor:collaropen_from_nonempty`.**  The reusable bridge: a strictly
positive profile whose regular collar interior over the singleton chamber is
nonempty has realizability on a whole neighbourhood.  The chamber enters
`collarRegularInterior` only through the profile-membership condition, so a
member over `{κ}` has first component `κ` and is a member over `univ`. -/
theorem realizesR2_eventually_of_collarRegularInterior_nonempty [NeZero n]
    (hn : 3 ≤ n) {κ : ZMod n → ℝ} (hpos : ∀ i, 0 < κ i)
    (hne : (collarRegularInterior {κ}).Nonempty) :
    ∀ᶠ κ' in 𝓝 κ, RealizesR2 κ' := by
  obtain ⟨p, ⟨hpS, hpMA, hp0⟩, hpR⟩ := hne
  have hp1 : p.1 = κ := Set.mem_singleton_iff.mp hpS
  have hp' : p ∈ collarRegularInterior (Set.univ : Set (ZMod n → ℝ)) :=
    ⟨⟨Set.mem_univ _, hpMA, hp0⟩, hpR⟩
  have h := realizesR2_eventually_of_collarRegular hn hp'
    (by rw [hp1]; exact hpos)
  rwa [hp1] at h

/-! ## Readouts at composite `n` -/

/-- **`thm:collaropen_periodic`.**  Realizability is open around every
strictly positive non-constant `p`-periodic profile at `n = m·p`, `m ≥ 3`,
`p ≥ 2`: the rotational witness makes the regular collar interior over the
singleton chamber nonempty. -/
theorem realizesR2_eventually_of_periodic [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 3 ≤ m) (hp : 2 ≤ p) {κ : ZMod n → ℝ}
    (hpos : ∀ i, 0 < κ i)
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hnc : ¬ ∀ i j : ZMod n, κ i = κ j) :
    ∀ᶠ κ' in 𝓝 κ, RealizesR2 κ' := by
  have h6 : 6 ≤ n := by
    have := Nat.mul_le_mul hm hp
    omega
  exact realizesR2_eventually_of_collarRegularInterior_nonempty (by omega)
    hpos (collarRegularInterior_nonempty_of_periodic hn hm hp hpos hκ hnc)

/-- **`cor:collaropen_interior`.**  At every composite `n ≥ 6` the set of
realizable profiles has nonempty interior — a full-dimensional family, not a
symmetric slice. -/
theorem interior_realizesR2_nonempty_of_notPrime [NeZero n]
    (hn6 : 6 ≤ n) (hnp : ¬ n.Prime) :
    (interior {κ : ZMod n → ℝ | RealizesR2 κ}).Nonempty := by
  obtain ⟨κ, hpos, -, hne⟩ :=
    exists_nonconstant_collarRegularInterior_nonempty_of_notPrime hn6 hnp
  refine ⟨κ, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  exact realizesR2_eventually_of_collarRegularInterior_nonempty (by omega)
    hpos hne

/-! ## A full-dimensional family of four-vertex instances -/

/-- **`lem:collaropen_spike_dfv`.**  The block spike profile has a
four-vertex window at the level `3/2`, with lifted indices `0, 1, p, p+1`:
the profile reads `2, 1, 2, 1` there. -/
theorem blockSpikeProfile_dfv [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 3 ≤ m) (hp : 2 ≤ p) :
    DFV (blockSpikeProfile (n := n) p) (3 / 2 : ℝ) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h3p : 3 * p ≤ n := by
    rw [hn]
    exact Nat.mul_le_mul hm le_rfl
  have hval : ∀ k : ℕ, k < n → ((k : ZMod n)).val = k := fun k hk =>
    ZMod.val_cast_of_lt hk
  have h0 : blockSpikeProfile (n := n) p ((0 : ℕ) : ZMod n) = 2 := by
    unfold blockSpikeProfile
    rw [hval 0 (by omega), Nat.zero_mod]
    norm_num
  have h1 : blockSpikeProfile (n := n) p ((1 : ℕ) : ZMod n) = 1 := by
    unfold blockSpikeProfile
    rw [hval 1 (by omega), Nat.mod_eq_of_lt (by omega : 1 < p)]
    norm_num
  have hpv : blockSpikeProfile (n := n) p ((p : ℕ) : ZMod n) = 2 := by
    unfold blockSpikeProfile
    rw [hval p (by omega), Nat.mod_self]
    norm_num
  have hp1 : blockSpikeProfile (n := n) p (((p + 1 : ℕ)) : ZMod n) = 1 := by
    unfold blockSpikeProfile
    rw [hval (p + 1) (by omega), Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : 1 < p)]
    norm_num
  refine ⟨0, 1, p, p + 1, by omega, by omega, by omega, by omega,
    ?_, ?_, ?_, ?_⟩
  · rw [h0]; norm_num
  · rw [h1]; norm_num
  · rw [hpv]; norm_num
  · rw [hp1]; norm_num

/-- **`thm:collaropen_dfv_family`.**  At every `n = m·p` with `m ≥ 3`,
`p ≥ 2` there is a profile — the block spike — around which a whole
neighbourhood of profiles is simultaneously positive four-vertex and
realizable: a full-dimensional family of verified instances of
Tabachnikov's Problem 2. -/
theorem exists_nhds_dfv_realizesR2 [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 3 ≤ m) (hp : 2 ≤ p) :
    ∃ κ₀ : ZMod n → ℝ,
      ∀ᶠ κ in 𝓝 κ₀, DiscreteFourVertexPos κ ∧ RealizesR2 κ := by
  obtain ⟨hpos, hper, hnc⟩ := blockSpikeProfile_spec hn (by omega) hp
  refine ⟨blockSpikeProfile p, ?_⟩
  have hreal := realizesR2_eventually_of_periodic hn hm hp hpos hper hnc
  have hdfv := DiscreteFourVertexPos.eventually_of_window hpos
    (by norm_num : (0 : ℝ) < 3 / 2) (blockSpikeProfile_dfv hn hm hp)
  exact hdfv.and hreal

/-- Project-local Mathlib supplement (arithmetic readout of
`rem:rotcollar_scope`, re-derived here because the `RotationalCollar.lean`
helper is private): every composite `n ≥ 6` admits a factorization
`n = m·p` with `m ≥ 3` and `p ≥ 2`. -/
private lemma exists_factorization_of_composite {n : ℕ} (hn6 : 6 ≤ n)
    (hnp : ¬ n.Prime) : ∃ m p : ℕ, n = m * p ∧ 3 ≤ m ∧ 2 ≤ p := by
  have hq := Nat.minFac_prime (show n ≠ 1 by omega)
  obtain ⟨d, hd⟩ := Nat.minFac_dvd n
  rcases eq_or_lt_of_le hq.two_le with heq | hlt
  · rw [← heq] at hd
    exact ⟨d, 2, by omega, by omega, le_rfl⟩
  · refine ⟨n.minFac, d, hd, by omega, ?_⟩
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · exfalso
      have hcase : d = 0 ∨ d = 1 := by omega
      rcases hcase with h0 | h1
      · rw [h0, Nat.mul_zero] at hd
        omega
      · rw [h1, Nat.mul_one] at hd
        exact hnp (by rw [hd]; exact hq)
    · exact hd2

/-- **`cor:collaropen_dfv_notPrime`.**  At every composite `n ≥ 6` there is a
profile around which a whole neighbourhood is positive four-vertex and
realizable. -/
theorem exists_nhds_dfv_realizesR2_of_notPrime [NeZero n]
    (hn6 : 6 ≤ n) (hnp : ¬ n.Prime) :
    ∃ κ₀ : ZMod n → ℝ,
      ∀ᶠ κ in 𝓝 κ₀, DiscreteFourVertexPos κ ∧ RealizesR2 κ := by
  obtain ⟨m, p, hn, hm, hp⟩ := exists_factorization_of_composite hn6 hnp
  exact exists_nhds_dfv_realizesR2 hn hm hp

/-- **`thm:collaropen_asymmetric`.**  A realizable positive four-vertex
profile fixed by NO nontrivial rotation: perturb the block spike at the
single index `0` by a small `t ∈ (0, 1)`, staying inside the neighbourhood
of `exists_nhds_dfv_realizesR2`.  For any nonzero shift `c` the value at `c`
is `1` or `2` while the value at `0` is `2 + t`, so the shift moves the
profile. -/
theorem exists_dfv_realizesR2_no_period [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 3 ≤ m) (hp : 2 ≤ p) :
    ∃ κ : ZMod n → ℝ, DiscreteFourVertexPos κ ∧ RealizesR2 κ ∧
      ∀ c : ZMod n, c ≠ 0 → ∃ i : ZMod n, κ (i + c) ≠ κ i := by
  set κ₀ : ZMod n → ℝ := blockSpikeProfile p with hκ₀
  have hN0 : ∀ᶠ κ in 𝓝 κ₀, DiscreteFourVertexPos κ ∧ RealizesR2 κ := by
    obtain ⟨hpos, hper, hnc⟩ := blockSpikeProfile_spec hn (by omega) hp
    have hreal := realizesR2_eventually_of_periodic hn hm hp hpos hper hnc
    have hdfv := DiscreteFourVertexPos.eventually_of_window hpos
      (by norm_num : (0 : ℝ) < 3 / 2) (blockSpikeProfile_dfv hn hm hp)
    exact hdfv.and hreal
  -- walk along the path `t ↦ κ₀ + t • e₀` until it leaves the neighbourhood
  have hpath : Continuous fun t : ℝ =>
      κ₀ + t • (Pi.single (0 : ZMod n) (1 : ℝ)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun t : ℝ => κ₀ + t • (Pi.single (0 : ZMod n) (1 : ℝ))) ⁻¹'
      {κ | DiscreteFourVertexPos κ ∧ RealizesR2 κ} ∈ 𝓝 (0 : ℝ) := by
    refine hpath.continuousAt.preimage_mem_nhds ?_
    have hf0 : κ₀ + (0 : ℝ) • (Pi.single (0 : ZMod n) (1 : ℝ)) = κ₀ := by
      rw [zero_smul, add_zero]
    rw [hf0]
    exact hN0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  set t : ℝ := min (ε / 2) (1 / 2) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set κ : ZMod n → ℝ := κ₀ + t • (Pi.single (0 : ZMod n) (1 : ℝ)) with hκdef
  have hκmem : DiscreteFourVertexPos κ ∧ RealizesR2 κ := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact htε
  refine ⟨κ, hκmem.1, hκmem.2, ?_⟩
  intro c hc
  refine ⟨0, ?_⟩
  rw [zero_add]
  -- value at `c ≠ 0`: the perturbation vanishes, leaving `1` or `2`
  have hvc : κ c = κ₀ c := by
    rw [hκdef]
    simp [Pi.single_eq_of_ne hc]
  have hv0 : κ 0 = 2 + t := by
    rw [hκdef]
    have hb0 : κ₀ 0 = 2 := by
      rw [hκ₀]
      unfold blockSpikeProfile
      rw [ZMod.val_zero, Nat.zero_mod]
      norm_num
    simp [hb0]
  have hcases : κ₀ c = 2 ∨ κ₀ c = 1 := by
    rw [hκ₀]
    unfold blockSpikeProfile
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rw [hvc, hv0]
  rcases hcases with h | h <;> rw [h] <;> linarith

end Gluck.Discrete
