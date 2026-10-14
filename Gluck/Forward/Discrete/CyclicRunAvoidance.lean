import Gluck.Forward.Discrete.CyclicComponents

/-!
# Avoiding connected subsets in finite cyclic component decompositions

This file supplies the final finite selection step used in Dahlberg §4: a
connected cyclic subset contained in a disconnected set can meet at most one
of two distinct maximal runs.
-/

namespace Gluck

/-- An ordinary interval contained in `T` and meeting a maximal run of `T`
is contained in that run. -/
theorem IsMaximalNatRun.interval_subset_of_inter_nonempty
    {T I U : Finset ℕ} (hI : IsMaximalNatRun T I)
    (hU : IsNatInterval U) (hUT : U ⊆ T)
    (hUI : (U ∩ I).Nonempty) :
    U ⊆ I := by
  have hUnion : IsNatInterval (I ∪ U) :=
    isNatInterval_union_of_inter_nonempty hI.1 hU (by
      simpa [Finset.inter_comm] using hUI)
  have hUnionT : I ∪ U ⊆ T := Finset.union_subset hI.2.1 hUT
  have hEq : I ∪ U = I :=
    hI.2.2 (I ∪ U) hUnion Finset.subset_union_left hUnionT
  intro z hzU
  rw [← hEq]
  exact Finset.mem_union_right I hzU

/-- An interval inside `T` cannot meet two distinct maximal runs of `T`. -/
theorem IsMaximalNatRun.disjoint_interval_or_disjoint_interval
    {T I J U : Finset ℕ}
    (hI : IsMaximalNatRun T I) (hJ : IsMaximalNatRun T J)
    (hIJ : I ≠ J) (hU : IsNatInterval U) (hUT : U ⊆ T) :
    Disjoint U I ∨ Disjoint U J := by
  by_contra hnone
  have hnotI : ¬ Disjoint U I := fun h => hnone (Or.inl h)
  have hnotJ : ¬ Disjoint U J := fun h => hnone (Or.inr h)
  rw [Finset.not_disjoint_iff] at hnotI hnotJ
  rcases hnotI with ⟨x, hxU, hxI⟩
  rcases hnotJ with ⟨y, hyU, hyJ⟩
  have hUsubI : U ⊆ I :=
    hI.interval_subset_of_inter_nonempty hU hUT
      ⟨x, Finset.mem_inter.mpr ⟨hxU, hxI⟩⟩
  have hUsubJ : U ⊆ J :=
    hJ.interval_subset_of_inter_nonempty hU hUT
      ⟨y, Finset.mem_inter.mpr ⟨hyU, hyJ⟩⟩
  rcases maximalNatRuns_eq_or_disjoint hI hJ with hEq | hdisj
  · exact hIJ hEq
  · exact (Finset.disjoint_left.mp hdisj) (hUsubI hyU) (hUsubJ hyU)

/-- A cyclic subset whose pullback at the chosen cut is one ordinary interval
cannot meet two distinct maximal runs at that cut. -/
theorem IsMaximalCyclicRunAt.disjoint_interval_or_disjoint_interval
    {n : ℕ} [NeZero n] {c : ZMod n}
    {S R Q F : Finset (ZMod n)}
    (hR : IsMaximalCyclicRunAt c S R)
    (hQ : IsMaximalCyclicRunAt c S Q)
    (hRQ : R ≠ Q)
    (hFinterval : IsNatInterval (cutFinset c F))
    (hFS : F ⊆ S) :
    Disjoint F R ∨ Disjoint F Q := by
  rcases hR with ⟨I, hI, rfl⟩
  rcases hQ with ⟨J, hJ, rfl⟩
  let U : Finset ℕ := cutFinset c F
  have hUr : U ⊆ Finset.range n := cutFinset_subset_range c F
  have hIr : I ⊆ Finset.range n :=
    hI.2.1.trans (cutFinset_subset_range c S)
  have hJr : J ⊆ Finset.range n :=
    hJ.2.1.trans (cutFinset_subset_range c S)
  have hUT : U ⊆ cutFinset c S := by
    intro k hk
    apply mem_cutFinset.mpr
    have hk' := mem_cutFinset.mp hk
    exact ⟨hk'.1, hFS hk'.2⟩
  have hIJ : I ≠ J := by
    intro hEq
    apply hRQ
    rw [hEq]
  rcases hI.disjoint_interval_or_disjoint_interval hJ hIJ
      (by simpa [U] using hFinterval) hUT with hUI | hUJ
  · left
    rw [← mapCut_cutFinset c F]
    exact disjoint_mapCut_of_disjoint_of_subset_range c hUr hIr hUI
  · right
    rw [← mapCut_cutFinset c F]
    exact disjoint_mapCut_of_disjoint_of_subset_range c hUr hJr hUJ

/-- Cutting a cyclic interval at any point outside it produces one ordinary
natural-number interval. -/
theorem IsCyclicInterval.cutFinset_isNatInterval_of_not_mem
    {n : ℕ} [NeZero n] {F : Finset (ZMod n)}
    (hF : IsCyclicInterval F) {c : ZMod n} (hc : c ∉ F) :
    IsNatInterval (cutFinset c F) := by
  rcases hF with ⟨c₀, a, b, hab, hbn, rfl⟩
  let s : ZMod n := cyclicLift c₀ a
  let r : ℕ := (s - c).val
  let L : ℕ := b - a
  have hrlt : r < n := ZMod.val_lt (s - c)
  have hsc : cyclicLift c r = s := by
    dsimp [cyclicLift, r]
    rw [ZMod.natCast_zmod_val (s - c)]
    abel
  have hsca : c + (r : ZMod n) = c₀ + (a : ZMod n) := by
    simpa [s, cyclicLift] using hsc
  have hsMem : s ∈ mapCut c₀ (Finset.Icc a b) := by
    exact Finset.mem_image.mpr ⟨a, by simp [hab], rfl⟩
  have hrpos : 0 < r := by
    apply Nat.pos_of_ne_zero
    intro hr0
    apply hc
    have hsc' : c = s := by
      simpa [cyclicLift, hr0] using hsc
    simpa [hsc'] using hsMem
  have hbound : r + L < n := by
    by_contra hnot
    have hnle : n ≤ r + L := Nat.le_of_not_gt hnot
    let t : ℕ := n - r
    have hrt : r + t = n := by
      dsimp [t]
      exact Nat.add_sub_of_le hrlt.le
    have htL : t ≤ L := by omega
    have hatb : a + t ≤ b := by
      dsimp [L] at htL
      omega
    apply hc
    apply Finset.mem_image.mpr
    refine ⟨a + t, Finset.mem_Icc.mpr ⟨by omega, hatb⟩, ?_⟩
    have hrtCast : (r : ZMod n) + (t : ZMod n) = 0 := by
      rw [← Nat.cast_add, hrt, ZMod.natCast_self]
    dsimp [cyclicLift]
    calc
      c₀ + ((a + t : ℕ) : ZMod n) =
          (c₀ + (a : ZMod n)) + (t : ZMod n) := by push_cast; ring
      _ = (c + (r : ZMod n)) + (t : ZMod n) := by rw [hsca]
      _ = c + ((r : ZMod n) + (t : ZMod n)) := by ring
      _ = c := by rw [hrtCast, add_zero]
  refine ⟨r, r + L, Nat.le_add_right r L, ?_⟩
  ext k
  rw [mem_cutFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hklt, hkF⟩
    rcases Finset.mem_image.mp hkF with ⟨j, hj, hjeq⟩
    rcases Finset.mem_Icc.mp hj with ⟨haj, hjb⟩
    let t : ℕ := j - a
    have hat : a + t = j := by
      dsimp [t]
      omega
    have htL : t ≤ L := by
      dsimp [t, L]
      omega
    have hrtlt : r + t < n := lt_of_le_of_lt (Nat.add_le_add_left htL r) hbound
    have hlift : cyclicLift c (r + t) = cyclicLift c₀ j := by
      dsimp [cyclicLift]
      calc
        c + ((r + t : ℕ) : ZMod n) =
            (c + (r : ZMod n)) + (t : ZMod n) := by push_cast; ring
        _ = (c₀ + (a : ZMod n)) + (t : ZMod n) := by rw [hsca]
        _ = c₀ + ((a + t : ℕ) : ZMod n) := by push_cast; ring
        _ = c₀ + (j : ZMod n) := by rw [hat]
    have hkr : k = r + t :=
      cyclicLift_injOn_range c (Finset.mem_range.mpr hklt)
        (Finset.mem_range.mpr hrtlt) (hjeq.symm.trans hlift.symm)
    omega
  · rintro ⟨hrk, hkrL⟩
    let t : ℕ := k - r
    have hrt : r + t = k := by
      dsimp [t]
      omega
    have htL : t ≤ L := by omega
    have hklt : k < n := lt_of_le_of_lt hkrL hbound
    refine ⟨hklt, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨a + t, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
    · dsimp [L] at htL
      omega
    · dsimp [cyclicLift]
      calc
        c₀ + ((a + t : ℕ) : ZMod n) =
            (c₀ + (a : ZMod n)) + (t : ZMod n) := by push_cast; ring
        _ = (c + (r : ZMod n)) + (t : ZMod n) := by rw [hsca]
        _ = c + ((r + t : ℕ) : ZMod n) := by push_cast; ring
        _ = c + (k : ZMod n) := by rw [hrt]

/-- A cyclic interval contained in `S` avoids one of any two distinct maximal
runs of `S`, provided the component decomposition is cut outside `S`. -/
theorem IsMaximalCyclicRunAt.disjoint_cyclicInterval_or_disjoint_cyclicInterval
    {n : ℕ} [NeZero n] {c : ZMod n}
    {S R Q F : Finset (ZMod n)}
    (hc : c ∉ S)
    (hR : IsMaximalCyclicRunAt c S R)
    (hQ : IsMaximalCyclicRunAt c S Q)
    (hRQ : R ≠ Q)
    (hF : IsCyclicInterval F)
    (hFS : F ⊆ S) :
    Disjoint F R ∨ Disjoint F Q := by
  have hcF : c ∉ F := fun hcF => hc (hFS hcF)
  exact hR.disjoint_interval_or_disjoint_interval hQ hRQ
    (hF.cutFinset_isNatInterval_of_not_mem hcF) hFS

end Gluck
