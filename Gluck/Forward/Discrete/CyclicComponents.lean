import Gluck.Forward.Discrete.Defs

/-!
# Finite cyclic components

An isolated API for the interval bookkeeping in Dahlberg's Lemmas 4--7.
The actual circle is cut at one vertex outside the subset, reducing maximal
cyclic runs to maximal ordinary intervals of natural numbers.
-/

open scoped BigOperators

namespace Gluck

/-- A nonempty ordinary finite interval of natural numbers. -/
def IsNatInterval (I : Finset ℕ) : Prop :=
  ∃ a b : ℕ, a ≤ b ∧ I = Finset.Icc a b

/-- An ordinary interval in `T`, maximal for inclusion. -/
def IsMaximalNatRun (T I : Finset ℕ) : Prop :=
  IsNatInterval I ∧ I ⊆ T ∧
    ∀ J : Finset ℕ, IsNatInterval J → I ⊆ J → J ⊆ T → J = I

theorem isNatInterval_singleton (x : ℕ) :
    IsNatInterval {x} := by
  refine ⟨x, x, le_rfl, ?_⟩
  simp

theorem IsNatInterval.nonempty {I : Finset ℕ} (hI : IsNatInterval I) :
    I.Nonempty := by
  rcases hI with ⟨a, b, hab, rfl⟩
  exact ⟨a, by simp [hab]⟩

theorem IsMaximalNatRun.nonempty {T I : Finset ℕ}
    (hI : IsMaximalNatRun T I) : I.Nonempty :=
  hI.1.nonempty

theorem exists_maximalNatRun_of_mem {T : Finset ℕ} {x : ℕ} (hx : x ∈ T) :
    ∃ I : Finset ℕ, IsMaximalNatRun T I ∧ x ∈ I := by
  classical
  let C : Finset (Finset ℕ) :=
    T.powerset.filter fun I => IsNatInterval I ∧ x ∈ I
  have hC : C.Nonempty := by
    refine ⟨{x}, ?_⟩
    simp [C, hx, isNatInterval_singleton]
  obtain ⟨I, hIC, hmax⟩ := Finset.exists_max_image C Finset.card hC
  have hIpow : I ∈ T.powerset := (Finset.mem_filter.mp hIC).1
  have hIinterval : IsNatInterval I := (Finset.mem_filter.mp hIC).2.1
  have hxI : x ∈ I := (Finset.mem_filter.mp hIC).2.2
  refine ⟨I, ⟨hIinterval, Finset.mem_powerset.mp hIpow, ?_⟩, hxI⟩
  intro J hJinterval hIJ hJT
  have hJC : J ∈ C := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr hJT, hJinterval, hIJ hxI⟩
  exact (Finset.eq_of_subset_of_card_le hIJ (hmax J hJC)).symm

theorem isNatInterval_union_of_inter_nonempty {I J : Finset ℕ}
    (hI : IsNatInterval I) (hJ : IsNatInterval J)
    (hIJ : (I ∩ J).Nonempty) :
    IsNatInterval (I ∪ J) := by
  rcases hI with ⟨a, b, hab, rfl⟩
  rcases hJ with ⟨c, d, hcd, rfl⟩
  rcases hIJ with ⟨x, hx⟩
  have hxI : a ≤ x ∧ x ≤ b := by
    simpa using (Finset.mem_inter.mp hx).1
  have hxJ : c ≤ x ∧ x ≤ d := by
    simpa using (Finset.mem_inter.mp hx).2
  refine ⟨min a c, max b d, by omega, ?_⟩
  ext y
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

theorem maximalNatRuns_eq_or_disjoint {T I J : Finset ℕ}
    (hI : IsMaximalNatRun T I) (hJ : IsMaximalNatRun T J) :
    I = J ∨ Disjoint I J := by
  by_cases hEq : I = J
  · exact Or.inl hEq
  · right
    rw [Finset.disjoint_left]
    intro x hxI hxJ
    have hInter : (I ∩ J).Nonempty :=
      ⟨x, Finset.mem_inter.mpr ⟨hxI, hxJ⟩⟩
    have hUnionInterval : IsNatInterval (I ∪ J) :=
      isNatInterval_union_of_inter_nonempty hI.1 hJ.1 hInter
    have hUnionSub : I ∪ J ⊆ T := Finset.union_subset hI.2.1 hJ.2.1
    have hUnionEqI : I ∪ J = I :=
      hI.2.2 (I ∪ J) hUnionInterval Finset.subset_union_left hUnionSub
    have hJsubI : J ⊆ I := by
      intro y hy
      rw [← hUnionEqI]
      exact Finset.mem_union_right I hy
    have hIEqJ : I = J := hJ.2.2 I hI.1 hJsubI hI.2.1
    exact hEq hIEqJ

theorem exists_two_maximalNatRuns_of_not_interval {T : Finset ℕ}
    (hT : T.Nonempty) (hnot : ¬ IsNatInterval T) :
    ∃ I J : Finset ℕ,
      IsMaximalNatRun T I ∧ IsMaximalNatRun T J ∧ I ≠ J := by
  classical
  rcases hT with ⟨x, hxT⟩
  obtain ⟨I, hI, _hxI⟩ := exists_maximalNatRun_of_mem hxT
  by_contra htwo
  have huniq : ∀ J : Finset ℕ, IsMaximalNatRun T J → J = I := by
    intro J hJ
    by_contra hJI
    exact htwo ⟨I, J, hI, hJ, fun h => hJI h.symm⟩
  have hTsubI : T ⊆ I := by
    intro y hyT
    obtain ⟨J, hJ, hyJ⟩ := exists_maximalNatRun_of_mem hyT
    simpa [huniq J hJ] using hyJ
  have hIT : I = T := Finset.Subset.antisymm hI.2.1 hTsubI
  apply hnot
  simpa [← hIT] using hI.1

theorem IsMaximalNatRun.exists_endpoints_with_gaps
    {T I : Finset ℕ} (hI : IsMaximalNatRun T I) :
    ∃ a b : ℕ, a ≤ b ∧ I = Finset.Icc a b ∧
      (a = 0 ∨ a - 1 ∉ T) ∧ b + 1 ∉ T := by
  rcases hI.1 with ⟨a, b, hab, hIcc⟩
  refine ⟨a, b, hab, hIcc, ?_, ?_⟩
  · by_cases ha0 : a = 0
    · exact Or.inl ha0
    · right
      intro hpredT
      let J : Finset ℕ := Finset.Icc (a - 1) b
      have hJinterval : IsNatInterval J := by
        exact ⟨a - 1, b, by omega, rfl⟩
      have hIJ : I ⊆ J := by
        rw [hIcc]
        intro x hx
        simp only [J, Finset.mem_Icc] at hx ⊢
        omega
      have hJT : J ⊆ T := by
        intro x hx
        simp only [J, Finset.mem_Icc] at hx
        by_cases hxa : x = a - 1
        · simpa [hxa] using hpredT
        · apply hI.2.1
          rw [hIcc]
          simp only [Finset.mem_Icc]
          omega
      have hJI : J = I := hI.2.2 J hJinterval hIJ hJT
      have hpredJ : a - 1 ∈ J := by
        simp only [J, Finset.mem_Icc]
        omega
      have hpredI : a - 1 ∈ I := by simpa [hJI] using hpredJ
      rw [hIcc] at hpredI
      simp only [Finset.mem_Icc] at hpredI
      omega
  · intro hsuccT
    let J : Finset ℕ := Finset.Icc a (b + 1)
    have hJinterval : IsNatInterval J :=
      ⟨a, b + 1, by omega, rfl⟩
    have hIJ : I ⊆ J := by
      rw [hIcc]
      intro x hx
      simp only [J, Finset.mem_Icc] at hx ⊢
      omega
    have hJT : J ⊆ T := by
      intro x hx
      simp only [J, Finset.mem_Icc] at hx
      by_cases hxb : x = b + 1
      · simpa [hxb] using hsuccT
      · apply hI.2.1
        rw [hIcc]
        simp only [Finset.mem_Icc]
        omega
    have hJI : J = I := hI.2.2 J hJinterval hIJ hJT
    have hsuccJ : b + 1 ∈ J := by
      simp only [J, Finset.mem_Icc]
      omega
    have hsuccI : b + 1 ∈ I := by simpa [hJI] using hsuccJ
    rw [hIcc] at hsuccI
    simp only [Finset.mem_Icc] at hsuccI
    omega

/-- The natural lift based at the cut vertex `c`. -/
def cyclicLift {n : ℕ} (c : ZMod n) (k : ℕ) : ZMod n :=
  c + (k : ZMod n)

/-- Pull a cyclic vertex set back to the canonical lift `0, ..., n - 1`
based at `c`. -/
def cutFinset {n : ℕ} (c : ZMod n) (S : Finset (ZMod n)) : Finset ℕ :=
  (Finset.range n).filter fun k => cyclicLift c k ∈ S

/-- Push a finite set of natural lift coordinates back to the cycle. -/
def mapCut {n : ℕ} (c : ZMod n) (I : Finset ℕ) : Finset (ZMod n) :=
  I.image (cyclicLift c)

/-- A nonempty cyclic interval represented by one natural lift `[a,b]`
whose length stays within a single period. -/
def IsCyclicInterval {n : ℕ} (I : Finset (ZMod n)) : Prop :=
  ∃ c : ZMod n, ∃ a b : ℕ,
    a ≤ b ∧ b < n ∧ I = mapCut c (Finset.Icc a b)

theorem cyclicLift_injOn_range {n : ℕ} [NeZero n] (c : ZMod n) :
    Set.InjOn (cyclicLift c) (Finset.range n : Set ℕ) := by
  intro a ha b hb hab
  have hcast : (a : ZMod n) = (b : ZMod n) := by
    exact add_left_cancel hab
  have hmod : a ≡ b [MOD n] :=
    (ZMod.natCast_eq_natCast_iff a b n).mp hcast
  exact hmod.eq_of_lt_of_lt (by simpa using ha) (by simpa using hb)

@[simp] theorem mem_cutFinset {n : ℕ} {c : ZMod n}
    {S : Finset (ZMod n)} {k : ℕ} :
    k ∈ cutFinset c S ↔ k < n ∧ cyclicLift c k ∈ S := by
  simp [cutFinset]

theorem cutFinset_subset_range {n : ℕ} (c : ZMod n)
    (S : Finset (ZMod n)) :
    cutFinset c S ⊆ Finset.range n := by
  intro k hk
  exact Finset.mem_range.mpr (mem_cutFinset.mp hk).1

theorem mapCut_cutFinset {n : ℕ} [NeZero n] (c : ZMod n)
    (S : Finset (ZMod n)) :
    mapCut c (cutFinset c S) = S := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
    exact (mem_cutFinset.mp hk).2
  · intro hz
    let k : ℕ := (z - c).val
    have hklt : k < n := by
      exact ZMod.val_lt (z - c)
    have hklift : cyclicLift c k = z := by
      dsimp [cyclicLift, k]
      rw [ZMod.natCast_zmod_val (z - c)]
      abel
    apply Finset.mem_image.mpr
    exact ⟨k, mem_cutFinset.mpr ⟨hklt, by simpa [hklift] using hz⟩, hklift⟩

theorem isCyclicInterval_mapCut_of_natInterval_of_subset_range
    {n : ℕ} {c : ZMod n} {I : Finset ℕ}
    (hI : IsNatInterval I) (hIr : I ⊆ Finset.range n) :
    IsCyclicInterval (mapCut c I) := by
  rcases hI with ⟨a, b, hab, rfl⟩
  have hb : b < n := Finset.mem_range.mp (hIr (by simp [hab]))
  exact ⟨c, a, b, hab, hb, rfl⟩

/-- If a cyclic set becomes an ordinary interval after a cut, then it was a
cyclic interval. -/
theorem isCyclicInterval_of_isNatInterval_cutFinset
    {n : ℕ} [NeZero n] (c : ZMod n) {S : Finset (ZMod n)}
    (hS : IsNatInterval (cutFinset c S)) :
    IsCyclicInterval S := by
  have hmap : IsCyclicInterval (mapCut c (cutFinset c S)) :=
    isCyclicInterval_mapCut_of_natInterval_of_subset_range hS
      (cutFinset_subset_range c S)
  simpa [mapCut_cutFinset] using hmap

theorem card_mapCut_of_subset_range {n : ℕ} [NeZero n]
    (c : ZMod n) {I : Finset ℕ} (hIr : I ⊆ Finset.range n) :
    (mapCut c I).card = I.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  exact cyclicLift_injOn_range c (hIr ha) (hIr hb) hab

/-- Cutting a cyclic finite set at any basepoint preserves its cardinality. -/
theorem card_cutFinset {n : ℕ} [NeZero n]
    (c : ZMod n) (S : Finset (ZMod n)) :
    (cutFinset c S).card = S.card := by
  have hcard := card_mapCut_of_subset_range c (cutFinset_subset_range c S)
  rw [mapCut_cutFinset] at hcard
  exact hcard.symm

/-- Inclusion of a cyclic set in the image of a cut interval is equivalent
to inclusion of its cut coordinates in that interval. -/
theorem cutFinset_subset_iff
    {n : ℕ} [NeZero n] (c : ZMod n)
    {S : Finset (ZMod n)} {I : Finset ℕ}
    (hI : I ⊆ Finset.range n) :
    cutFinset c S ⊆ I ↔ S ⊆ mapCut c I := by
  constructor
  · intro hcut z hzS
    rw [← mapCut_cutFinset c S] at hzS
    rcases Finset.mem_image.mp hzS with ⟨k, hk, rfl⟩
    exact Finset.mem_image.mpr ⟨k, hcut hk, rfl⟩
  · intro hS k hkcut
    have hklift : cyclicLift c k ∈ S := (mem_cutFinset.mp hkcut).2
    rcases Finset.mem_image.mp (hS hklift) with ⟨j, hjI, hjk⟩
    have hkRange : k ∈ (Finset.range n : Set ℕ) := by
      simpa using (mem_cutFinset.mp hkcut).1
    have hjRange : j ∈ (Finset.range n : Set ℕ) := by
      simpa using Finset.mem_range.mp (hI hjI)
    have hkeqj : k = j :=
      cyclicLift_injOn_range c hkRange hjRange hjk.symm
    simpa [hkeqj] using hjI

theorem disjoint_mapCut_of_disjoint_of_subset_range
    {n : ℕ} [NeZero n] (c : ZMod n) {I J : Finset ℕ}
    (hIr : I ⊆ Finset.range n) (hJr : J ⊆ Finset.range n)
    (hIJ : Disjoint I J) :
    Disjoint (mapCut c I) (mapCut c J) := by
  rw [Finset.disjoint_left] at hIJ ⊢
  intro z hzI hzJ
  rcases Finset.mem_image.mp hzI with ⟨a, haI, haz⟩
  rcases Finset.mem_image.mp hzJ with ⟨b, hbJ, hbz⟩
  have hab : a = b :=
    cyclicLift_injOn_range c (hIr haI) (hJr hbJ) (haz.trans hbz.symm)
  subst b
  exact hIJ haI hbJ

/-- A maximal cyclic run after cutting the cycle at `c`.  If `c ∉ S`, these
are exactly the intrinsic maximal consecutive components of `S`. -/
def IsMaximalCyclicRunAt {n : ℕ} (c : ZMod n)
    (S R : Finset (ZMod n)) : Prop :=
  ∃ I : Finset ℕ,
    IsMaximalNatRun (cutFinset c S) I ∧ R = mapCut c I

theorem IsMaximalCyclicRunAt.properties {n : ℕ} [NeZero n]
    {c : ZMod n} {S R : Finset (ZMod n)}
    (hR : IsMaximalCyclicRunAt c S R) :
    IsCyclicInterval R ∧ R.Nonempty ∧ R ⊆ S := by
  rcases hR with ⟨I, hI, rfl⟩
  have hIr : I ⊆ Finset.range n :=
    hI.2.1.trans (cutFinset_subset_range c S)
  refine ⟨isCyclicInterval_mapCut_of_natInterval_of_subset_range hI.1 hIr,
    ?_, ?_⟩
  · rcases hI.nonempty with ⟨k, hk⟩
    exact ⟨cyclicLift c k, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, hkI, rfl⟩
    exact (mem_cutFinset.mp (hI.2.1 hkI)).2

theorem exists_maximalCyclicRunAt_of_mem {n : ℕ} [NeZero n]
    {c : ZMod n} {S : Finset (ZMod n)} {z : ZMod n} (hz : z ∈ S) :
    ∃ R : Finset (ZMod n), IsMaximalCyclicRunAt c S R ∧ z ∈ R := by
  let k : ℕ := (z - c).val
  have hklt : k < n := ZMod.val_lt (z - c)
  have hklift : cyclicLift c k = z := by
    dsimp [cyclicLift, k]
    rw [ZMod.natCast_zmod_val (z - c)]
    abel
  have hkcut : k ∈ cutFinset c S :=
    mem_cutFinset.mpr ⟨hklt, by simpa [hklift] using hz⟩
  obtain ⟨I, hI, hkI⟩ := exists_maximalNatRun_of_mem hkcut
  refine ⟨mapCut c I, ⟨I, hI, rfl⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨k, hkI, hklift⟩

theorem maximalCyclicRunsAt_eq_or_disjoint {n : ℕ} [NeZero n]
    {c : ZMod n} {S R Q : Finset (ZMod n)}
    (hR : IsMaximalCyclicRunAt c S R)
    (hQ : IsMaximalCyclicRunAt c S Q) :
    R = Q ∨ Disjoint R Q := by
  rcases hR with ⟨I, hI, rfl⟩
  rcases hQ with ⟨J, hJ, rfl⟩
  rcases maximalNatRuns_eq_or_disjoint hI hJ with hIJ | hIJ
  · exact Or.inl (congrArg (mapCut c) hIJ)
  · exact Or.inr (disjoint_mapCut_of_disjoint_of_subset_range c
      (hI.2.1.trans (cutFinset_subset_range c S))
      (hJ.2.1.trans (cutFinset_subset_range c S)) hIJ)

theorem cutFinset_nonempty_iff {n : ℕ} [NeZero n]
    (c : ZMod n) (S : Finset (ZMod n)) :
    (cutFinset c S).Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨cyclicLift c k, (mem_cutFinset.mp hk).2⟩
  · rintro ⟨z, hz⟩
    let k : ℕ := (z - c).val
    have hklt : k < n := ZMod.val_lt (z - c)
    have hklift : cyclicLift c k = z := by
      dsimp [cyclicLift, k]
      rw [ZMod.natCast_zmod_val (z - c)]
      abel
    exact ⟨k, mem_cutFinset.mpr ⟨hklt, by simpa [hklift] using hz⟩⟩

theorem mapCut_injective_on_subsets_range {n : ℕ} [NeZero n]
    (c : ZMod n) {I J : Finset ℕ}
    (hIr : I ⊆ Finset.range n) (hJr : J ⊆ Finset.range n)
    (hmap : mapCut c I = mapCut c J) :
    I = J := by
  apply Finset.Subset.antisymm
  · intro a haI
    have haImage : cyclicLift c a ∈ mapCut c J := by
      rw [← hmap]
      exact Finset.mem_image.mpr ⟨a, haI, rfl⟩
    rcases Finset.mem_image.mp haImage with ⟨b, hbJ, hab⟩
    have hab' : a = b :=
      cyclicLift_injOn_range c (hIr haI) (hJr hbJ) hab.symm
    simpa [hab'] using hbJ
  · intro b hbJ
    have hbImage : cyclicLift c b ∈ mapCut c I := by
      rw [hmap]
      exact Finset.mem_image.mpr ⟨b, hbJ, rfl⟩
    rcases Finset.mem_image.mp hbImage with ⟨a, haI, hab⟩
    have hab' : a = b :=
      cyclicLift_injOn_range c (hIr haI) (hJr hbJ) hab
    simpa [← hab'] using haI

theorem exists_two_maximalCyclicRunsAt_of_not_interval
    {n : ℕ} [NeZero n] (c : ZMod n) {S : Finset (ZMod n)}
    (hS : S.Nonempty) (hnot : ¬ IsCyclicInterval S) :
    ∃ R Q : Finset (ZMod n),
      IsMaximalCyclicRunAt c S R ∧
      IsMaximalCyclicRunAt c S Q ∧
      R ≠ Q ∧ Disjoint R Q := by
  let T : Finset ℕ := cutFinset c S
  have hT : T.Nonempty := by
    simpa [T] using (cutFinset_nonempty_iff c S).mpr hS
  have hTrange : T ⊆ Finset.range n := by
    simpa [T] using cutFinset_subset_range c S
  have hTnot : ¬ IsNatInterval T := by
    intro hTinterval
    apply hnot
    have hcyclic : IsCyclicInterval (mapCut c T) :=
      isCyclicInterval_mapCut_of_natInterval_of_subset_range hTinterval hTrange
    simpa [T, mapCut_cutFinset] using hcyclic
  obtain ⟨I, J, hI, hJ, hIJ⟩ :=
    exists_two_maximalNatRuns_of_not_interval hT hTnot
  have hIr : I ⊆ Finset.range n := hI.2.1.trans hTrange
  have hJr : J ⊆ Finset.range n := hJ.2.1.trans hTrange
  have hmapNe : mapCut c I ≠ mapCut c J := by
    intro hmap
    exact hIJ (mapCut_injective_on_subsets_range c hIr hJr hmap)
  have hdisjoint : Disjoint (mapCut c I) (mapCut c J) :=
    disjoint_mapCut_of_disjoint_of_subset_range c hIr hJr
      ((maximalNatRuns_eq_or_disjoint hI hJ).resolve_left hIJ)
  exact ⟨mapCut c I, mapCut c J,
    ⟨I, by simpa [T] using hI, rfl⟩,
    ⟨J, by simpa [T] using hJ, rfl⟩,
    hmapNe, hdisjoint⟩

theorem maximalCyclicRunAt_has_gap_endpoints_of_cut_not_mem
    {n : ℕ} [NeZero n] {c : ZMod n} {S R : Finset (ZMod n)}
    (hc : c ∉ S) (hR : IsMaximalCyclicRunAt c S R) :
    ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ b < n ∧ b - a + 1 < n ∧
      R = mapCut c (Finset.Icc a b) ∧
      cyclicLift c (a - 1) ∉ S ∧ cyclicLift c (b + 1) ∉ S := by
  rcases hR with ⟨I, hI, rfl⟩
  rcases hI.exists_endpoints_with_gaps with
    ⟨a, b, hab, hIcc, hleft, hright⟩
  have haI : a ∈ I := by
    rw [hIcc]
    simp [hab]
  have hbI : b ∈ I := by
    rw [hIcc]
    simp [hab]
  have haCut : a ∈ cutFinset c S := hI.2.1 haI
  have hbCut : b ∈ cutFinset c S := hI.2.1 hbI
  have halt : a < n := (mem_cutFinset.mp haCut).1
  have hblt : b < n := (mem_cutFinset.mp hbCut).1
  have ha0 : a ≠ 0 := by
    intro ha
    apply hc
    have := (mem_cutFinset.mp haCut).2
    simpa [cyclicLift, ha] using this
  have hpredT : a - 1 ∉ cutFinset c S := hleft.resolve_left ha0
  have hpredS : cyclicLift c (a - 1) ∉ S := by
    intro hpredS
    apply hpredT
    exact mem_cutFinset.mpr ⟨by omega, hpredS⟩
  have hsuccS : cyclicLift c (b + 1) ∉ S := by
    intro hsuccS
    have hle : b + 1 ≤ n := by omega
    rcases lt_or_eq_of_le hle with hlt | heq
    · apply hright
      exact mem_cutFinset.mpr ⟨hlt, hsuccS⟩
    · apply hc
      simpa [cyclicLift, heq, ZMod.natCast_self] using hsuccS
  exact ⟨a, b, Nat.pos_of_ne_zero ha0, hab, hblt, by omega,
    by simp [hIcc], hpredS, hsuccS⟩

theorem mem_iff_exists_maximalCyclicRunAt {n : ℕ} [NeZero n]
    (c : ZMod n) (S : Finset (ZMod n)) (z : ZMod n) :
    z ∈ S ↔
      ∃ R : Finset (ZMod n), IsMaximalCyclicRunAt c S R ∧ z ∈ R := by
  constructor
  · exact exists_maximalCyclicRunAt_of_mem
  · rintro ⟨R, hR, hzR⟩
    exact hR.properties.2.2 hzR

theorem strictSubset_card_lt {α : Type*} {A B : Finset α}
    (hAB : A ⊂ B) : A.card < B.card :=
  Finset.card_lt_card hAB

theorem strictSubset_wellFounded {α : Type*} :
    WellFounded (fun A B : Finset α => A ⊂ B) :=
  Finset.lt_wf

/-- Iterating a strict-shrink step reaches a terminal set in at most the
cardinality of the initial set. -/
theorem exists_terminal_iterate_of_strict_shrink
    {α : Type*}
    (step : Finset α → Finset α) (terminal : Finset α → Prop)
    (hstep : ∀ A, ¬ terminal A → step A ⊂ A) (A : Finset α) :
    ∃ k : ℕ, k ≤ A.card ∧ terminal ((step^[k]) A) := by
  classical
  refine Finset.strongInductionOn A ?_
  intro A ih
  by_cases hterminal : terminal A
  · exact ⟨0, Nat.zero_le _, by simpa using hterminal⟩
  · have hshrink : step A ⊂ A := hstep A hterminal
    obtain ⟨k, hkcard, hkterminal⟩ := ih (step A) hshrink
    refine ⟨k + 1, ?_, ?_⟩
    · have hcard : (step A).card < A.card := strictSubset_card_lt hshrink
      omega
    · simpa [Function.iterate_succ_apply] using hkterminal

theorem exists_not_mem_of_ne_univ {α : Type*} [Fintype α]
    {S : Finset α} (hS : S ≠ Finset.univ) :
    ∃ x : α, x ∉ S := by
  classical
  by_contra hnone
  apply hS
  apply Finset.Subset.antisymm (Finset.subset_univ S)
  intro x _hx
  by_contra hxS
  exact hnone ⟨x, hxS⟩

/-- Cutting at a point outside a proper cyclic subset gives a decomposition
into gap-bounded maximal intervals: the runs cover the subset and are
pairwise equal or disjoint. -/
theorem exists_cut_decomposition_of_proper
    {n : ℕ} [NeZero n] {S : Finset (ZMod n)}
    (hproper : S ≠ Finset.univ) :
    ∃ c : ZMod n, c ∉ S ∧
      (∀ z : ZMod n, z ∈ S ↔
        ∃ R : Finset (ZMod n), IsMaximalCyclicRunAt c S R ∧ z ∈ R) ∧
      (∀ R Q : Finset (ZMod n),
        IsMaximalCyclicRunAt c S R → IsMaximalCyclicRunAt c S Q →
        R = Q ∨ Disjoint R Q) ∧
      (∀ R : Finset (ZMod n), IsMaximalCyclicRunAt c S R →
        ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ b < n ∧ b - a + 1 < n ∧
          R = mapCut c (Finset.Icc a b) ∧
          cyclicLift c (a - 1) ∉ S ∧ cyclicLift c (b + 1) ∉ S) := by
  obtain ⟨c, hc⟩ := exists_not_mem_of_ne_univ hproper
  exact ⟨c, hc, mem_iff_exists_maximalCyclicRunAt c S,
    fun _ _ => maximalCyclicRunsAt_eq_or_disjoint,
    fun _ => maximalCyclicRunAt_has_gap_endpoints_of_cut_not_mem hc⟩

theorem exists_cut_with_two_disjoint_runs_of_not_interval
    {n : ℕ} [NeZero n] {S : Finset (ZMod n)}
    (hS : S.Nonempty) (hproper : S ≠ Finset.univ)
    (hnot : ¬ IsCyclicInterval S) :
    ∃ c : ZMod n, ∃ R Q : Finset (ZMod n),
      c ∉ S ∧ IsMaximalCyclicRunAt c S R ∧
      IsMaximalCyclicRunAt c S Q ∧ R ≠ Q ∧ Disjoint R Q := by
  obtain ⟨c, hc⟩ := exists_not_mem_of_ne_univ hproper
  obtain ⟨R, Q, hR, hQ, hRQ, hdisjoint⟩ :=
    exists_two_maximalCyclicRunsAt_of_not_interval c hS hnot
  exact ⟨c, R, Q, hc, hR, hQ, hRQ, hdisjoint⟩

/-- A finite natural set with at least three points which is not an interval
has an internal maximal gap.  Adding the two contact endpoints to that gap
gives an interval strictly smaller than the convex hull of the original set.

This is the strict-descent measure used after cutting Dahlberg's contact-set
iteration at a vertex outside the current envelope. -/
theorem exists_internal_gap_with_strict_hull
    {C : Finset ℕ} (hC : C.Nonempty) (hcard : 3 ≤ C.card)
    (hnot : ¬ IsNatInterval C) :
    ∃ p q : ℕ,
      p ∈ C ∧ q ∈ C ∧ p + 1 < q ∧
      (∀ k : ℕ, p < k → k < q → k ∉ C) ∧
      Finset.Icc p q ⊂
        Finset.Icc (C.min' hC) (C.max' hC) := by
  let H : Finset ℕ := Finset.Icc (C.min' hC) (C.max' hC)
  have hCH : C ⊆ H := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le C k hk, Finset.le_max' C k hk⟩
  have hHneC : H ≠ C := by
    intro hEq
    apply hnot
    exact ⟨C.min' hC, C.max' hC,
      Finset.min'_le C (C.max' hC) (Finset.max'_mem C hC), hEq.symm⟩
  have hT : (H \ C).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun hHC => hHneC (Finset.Subset.antisymm hHC hCH)
  rcases hT with ⟨x, hxT⟩
  obtain ⟨I, hI, _hxI⟩ := exists_maximalNatRun_of_mem hxT
  rcases hI.exists_endpoints_with_gaps with
    ⟨a, b, hab, hIeq, hleft, hright⟩
  have haI : a ∈ I := by
    rw [hIeq]
    simp [hab]
  have hbI : b ∈ I := by
    rw [hIeq]
    simp [hab]
  have haT : a ∈ H \ C := hI.2.1 haI
  have hbT : b ∈ H \ C := hI.2.1 hbI
  have hminlt : C.min' hC < a := by
    have hminle : C.min' hC ≤ a :=
      (Finset.mem_Icc.mp (Finset.mem_sdiff.mp haT).1).1
    exact lt_of_le_of_ne hminle (fun hEq =>
      (Finset.mem_sdiff.mp haT).2 (by simpa [hEq] using Finset.min'_mem C hC))
  have hbltmax : b < C.max' hC := by
    have hble : b ≤ C.max' hC :=
      (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hbT).1).2
    exact lt_of_le_of_ne hble (fun hEq =>
      (Finset.mem_sdiff.mp hbT).2 (by simpa [hEq] using Finset.max'_mem C hC))
  let p := a - 1
  let q := b + 1
  have hpH : p ∈ H := by
    apply Finset.mem_Icc.mpr
    constructor
    · dsimp [p]
      omega
    · dsimp [p]
      omega
  have hqH : q ∈ H := by
    apply Finset.mem_Icc.mpr
    constructor
    · dsimp [q]
      omega
    · dsimp [q]
      omega
  have ha0 : a ≠ 0 := by omega
  have hpNotT : p ∉ H \ C := by
    dsimp [p]
    exact hleft.resolve_left ha0
  have hqNotT : q ∉ H \ C := by
    dsimp [q]
    exact hright
  have hpC : p ∈ C := by
    by_contra hp
    exact hpNotT (Finset.mem_sdiff.mpr ⟨hpH, hp⟩)
  have hqC : q ∈ C := by
    by_contra hq
    exact hqNotT (Finset.mem_sdiff.mpr ⟨hqH, hq⟩)
  have hpq : p + 1 < q := by
    dsimp [p, q]
    omega
  have hgap : ∀ k : ℕ, p < k → k < q → k ∉ C := by
    intro k hpk hkq hkC
    have hkI : k ∈ I := by
      rw [hIeq]
      simp only [Finset.mem_Icc]
      dsimp [p, q] at hpk hkq
      omega
    exact (Finset.mem_sdiff.mp (hI.2.1 hkI)).2 hkC
  have hpqSub : Finset.Icc p q ⊆ H :=
    Finset.Icc_subset_Icc (Finset.mem_Icc.mp hpH).1 (Finset.mem_Icc.mp hqH).2
  have hpqNe : Finset.Icc p q ≠ H := by
    intro hEq
    have hCpair : C ⊆ {p, q} := by
      intro k hkC
      have hkH : k ∈ H := hCH hkC
      have hkpq : k ∈ Finset.Icc p q := by
        rw [hEq]
        exact hkH
      rw [Finset.mem_Icc] at hkpq
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases eq_or_lt_of_le hkpq.1 with rfl | hpk
      · exact Or.inl rfl
      rcases lt_or_eq_of_le hkpq.2 with hkq | rfl
      · exact False.elim (hgap k hpk hkq hkC)
      · exact Or.inr rfl
    have hcardle := Finset.card_le_card hCpair
    have hpne : p ≠ q := Nat.ne_of_lt (lt_of_lt_of_le (Nat.lt_succ_self p) hpq.le)
    simp [hpne] at hcardle
    omega
  exact ⟨p, q, hpC, hqC, hpq, hgap,
    Finset.ssubset_iff_subset_ne.mpr ⟨hpqSub, hpqNe⟩⟩

/-- A cyclic interval with at least three elements contains three consecutive
cyclic indices.  This is the terminal combinatorial step in Dahlberg's
Lemmas 5 and 7: three connected circle contacts identify a curvature circle. -/
theorem IsCyclicInterval.exists_three_consecutive
    {n : ℕ} [NeZero n] {S : Finset (ZMod n)}
    (hS : IsCyclicInterval S) (hcard : 3 ≤ S.card) :
    ∃ i : ZMod n, i - 1 ∈ S ∧ i ∈ S ∧ i + 1 ∈ S := by
  rcases hS with ⟨c, a, b, hab, hbn, rfl⟩
  have hrange : Finset.Icc a b ⊆ Finset.range n := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact Finset.mem_range.mpr (lt_of_le_of_lt hk.2 hbn)
  have hcardMap := card_mapCut_of_subset_range c hrange
  have hlen : 3 ≤ b + 1 - a := by
    rw [hcardMap, Nat.card_Icc] at hcard
    exact hcard
  let i : ZMod n := cyclicLift c (a + 1)
  refine ⟨i, ?_, ?_, ?_⟩
  · have ha : a ∈ Finset.Icc a b := by
      simp [hab]
    have hmem : cyclicLift c a ∈ mapCut c (Finset.Icc a b) :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hi : i - 1 = cyclicLift c a := by
      dsimp [i, cyclicLift]
      push_cast
      ring
    rw [hi]
    exact hmem
  · have ha1 : a + 1 ∈ Finset.Icc a b := by
      simp only [Finset.mem_Icc]
      omega
    exact Finset.mem_image.mpr ⟨a + 1, ha1, rfl⟩
  · have ha2 : a + 2 ∈ Finset.Icc a b := by
      simp only [Finset.mem_Icc]
      omega
    have hmem : cyclicLift c (a + 2) ∈ mapCut c (Finset.Icc a b) :=
      Finset.mem_image.mpr ⟨a + 2, ha2, rfl⟩
    have hi : i + 1 = cyclicLift c (a + 2) := by
      dsimp [i, cyclicLift]
      push_cast
      ring
    rw [hi]
    exact hmem

/-- A proper cyclic interval with at least three elements has a cut based at
an interior contact for which the complementary gap lies strictly between
two other contacts.  The middle point `k` is a noncontact, while the cut
base itself stays outside the closed gap `[p,q]` because `0 < p`.

This is the cut-coordinate form of the single complementary interval used
to obtain the second disk in Dahlberg's Lemmas 5 and 7. -/
theorem IsCyclicInterval.exists_cutGap_in_complement
    {n : ℕ} [NeZero n] {S : Finset (ZMod n)}
    (hS : IsCyclicInterval S) (hcard : 3 ≤ S.card)
    (hproper : S ≠ Finset.univ) :
    ∃ (c : ZMod n) (p k q : ℕ),
      c ∈ S ∧ 0 < p ∧ p < k ∧ k < q ∧ q < n ∧
      cyclicLift c p ∈ S ∧ cyclicLift c q ∈ S ∧
      cyclicLift c k ∉ S := by
  classical
  have hSss : S ⊂ (Finset.univ : Finset (ZMod n)) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hproper⟩
  have hcardlt : S.card < n := by
    have := Finset.card_lt_card hSss
    simpa using this
  have hn : 4 ≤ n := by omega
  obtain ⟨c, hprev, hself, hnext⟩ := hS.exists_three_consecutive hcard
  obtain ⟨z, hz⟩ := exists_not_mem_of_ne_univ hproper
  let k : ℕ := (z - c).val
  have hklt : k < n := ZMod.val_lt (z - c)
  have hklift : cyclicLift c k = z := by
    dsimp [cyclicLift, k]
    rw [ZMod.natCast_zmod_val (z - c)]
    abel
  have hk0 : k ≠ 0 := by
    intro hk
    apply hz
    have : z = c := by
      rw [← hklift, hk]
      simp [cyclicLift]
    simpa [this] using hself
  have hk1 : k ≠ 1 := by
    intro hk
    apply hz
    have : z = c + 1 := by
      rw [← hklift, hk]
      simp [cyclicLift]
    simpa [this] using hnext
  have hkpred : k ≠ n - 1 := by
    intro hk
    apply hz
    have hpredLift : cyclicLift c (n - 1) = c - 1 := by
      unfold cyclicLift
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      rw [ZMod.natCast_self]
      simp [sub_eq_add_neg]
    have : z = c - 1 := by
      rw [← hklift, hk, hpredLift]
    simpa [this] using hprev
  refine ⟨c, 1, k, n - 1, hself, by omega, ?_, ?_, by omega, ?_, ?_, ?_⟩
  · omega
  · omega
  · simpa [cyclicLift] using hnext
  · have hpredLift : cyclicLift c (n - 1) = c - 1 := by
      unfold cyclicLift
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      rw [ZMod.natCast_self]
      simp [sub_eq_add_neg]
    simpa [hpredLift] using hprev
  · simpa [hklift] using hz

end Gluck
