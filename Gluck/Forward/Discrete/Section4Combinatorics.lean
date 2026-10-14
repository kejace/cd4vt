import Gluck.Forward.Discrete.CyclicComponents

/-!
# Finite curvature combinatorics for Dahlberg §4

This file contains no geometry.  It isolates the finite cyclic consequences
of failure of the plateau-aware four-vertex conclusion.
-/

namespace Gluck.Forward

/-- Weak increase of a cyclic profile along a natural lift `[a,b]`. -/
def WeaklyIncreasingLift {n : ℕ} (κ : ZMod n → ℝ) (a b : ℕ) : Prop :=
  ∀ k : ℕ, a ≤ k → k < b → κ (k : ZMod n) ≤ κ (k + 1 : ZMod n)

/-- Weak decrease of a cyclic profile along a natural lift `[a,b]`. -/
def WeaklyDecreasingLift {n : ℕ} (κ : ZMod n → ℝ) (a b : ℕ) : Prop :=
  ∀ k : ℕ, a ≤ k → k < b → κ (k + 1 : ZMod n) ≤ κ (k : ZMod n)

/-- The two complementary lifted arcs from a chosen global minimum to a
chosen global maximum are weakly monotone in opposite directions. -/
def TwoArcMonotone {n : ℕ} (κ : ZMod n → ℝ)
    (qmin qmax : ZMod n) : Prop :=
  let d := (qmax - qmin).val
  0 < d ∧ d < n ∧
    WeaklyIncreasingLift (fun z => κ (z + qmin)) 0 d ∧
    WeaklyDecreasingLift (fun z => κ (z + qmin)) d n

/-- The finite vertex set on which the signed curvature is nonpositive. -/
noncomputable def NonpositiveVertices {n : ℕ} [NeZero n]
    (κ : ZMod n → ℝ) : Finset (ZMod n) :=
  Finset.univ.filter fun z => κ z ≤ 0

@[simp] theorem mem_nonpositiveVertices {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ}
    {z : ZMod n} :
    z ∈ NonpositiveVertices κ ↔ κ z ≤ 0 := by
  simp [NonpositiveVertices]

/-- Translation of a finite cyclic vertex set. -/
def translateZModFinset {n : ℕ} (a : ZMod n)
    (S : Finset (ZMod n)) : Finset (ZMod n) :=
  S.image fun z => z + a

theorem isCyclicInterval_translateZModFinset {n : ℕ}
    {S : Finset (ZMod n)} (a : ZMod n)
    (hS : Gluck.IsCyclicInterval S) :
    Gluck.IsCyclicInterval (translateZModFinset a S) := by
  rcases hS with ⟨c, l, r, hlr, hrn, rfl⟩
  refine ⟨c + a, l, r, hlr, hrn, ?_⟩
  simp only [translateZModFinset, Gluck.mapCut, Finset.image_image]
  apply Finset.image_congr
  intro k hk
  dsimp [Gluck.cyclicLift]
  abel

theorem translateZModFinset_nonpositiveVertices_shift
    {n : ℕ} [NeZero n] (κ : ZMod n → ℝ) (a : ZMod n) :
    translateZModFinset a (NonpositiveVertices (fun z => κ (z + a))) =
      NonpositiveVertices κ := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, hzy⟩
    apply mem_nonpositiveVertices.mpr
    have hznonpos := mem_nonpositiveVertices.mp hz
    simpa [hzy] using hznonpos
  · intro hy
    apply Finset.mem_image.mpr
    refine ⟨y - a, ?_, by abel⟩
    apply mem_nonpositiveVertices.mpr
    have hynonpos := mem_nonpositiveVertices.mp hy
    simpa only [sub_add_cancel] using hynonpos

theorem isNatInterval_of_nonempty_of_orderConvex {T : Finset ℕ}
    (hT : T.Nonempty)
    (hconvex : ∀ x ∈ T, ∀ y ∈ T, ∀ z : ℕ,
      x ≤ z → z ≤ y → z ∈ T) :
    Gluck.IsNatInterval T := by
  let a : ℕ := T.min' hT
  let b : ℕ := T.max' hT
  have haT : a ∈ T := Finset.min'_mem T hT
  have hbT : b ∈ T := Finset.max'_mem T hT
  have hab : a ≤ b := Finset.min'_le T b hbT
  refine ⟨a, b, hab, ?_⟩
  apply Finset.Subset.antisymm
  · intro z hzT
    exact Finset.mem_Icc.mpr
      ⟨Finset.min'_le T z hzT, Finset.le_max' T z hzT⟩
  · intro z hz
    rcases Finset.mem_Icc.mp hz with ⟨haz, hzb⟩
    exact hconvex a haT b hbT z haz hzb

theorem value_le_of_adjacent_le {f : ℕ → ℝ} {a b x y : ℕ}
    (hstep : ∀ k : ℕ, a ≤ k → k < b → f k ≤ f (k + 1))
    (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    f x ≤ f y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
  suffices h : ∀ d : ℕ, x + d ≤ b → f x ≤ f (x + d) by
    exact h d hyb
  intro e
  induction e with
  | zero =>
      intro _
      simp
  | succ e ih =>
      intro hbound
      exact (ih (by omega)).trans
        (hstep (x + e) (by omega) (by omega))

theorem value_le_of_adjacent_ge {f : ℕ → ℝ} {a b x y : ℕ}
    (hstep : ∀ k : ℕ, a ≤ k → k < b → f (k + 1) ≤ f k)
    (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    f y ≤ f x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
  suffices h : ∀ d : ℕ, x + d ≤ b → f (x + d) ≤ f x by
    exact h d hyb
  intro e
  induction e with
  | zero =>
      intro _
      simp
  | succ e ih =>
      intro hbound
      exact (hstep (x + e) (by omega) (by omega)).trans
        (ih (by omega))

/-- A single strict descent between a global minimum and a later global
maximum forces four alternating plateau-aware extrema. -/
theorem dahlbergFourVertex_of_descent_between_globalMinMax
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {a b : ℕ}
    (hwrap : b < a + n)
    (hminA : ∀ z : ZMod n, κ (a : ZMod n) ≤ κ z)
    (hmaxB : ∀ z : ZMod n, κ z ≤ κ (b : ZMod n))
    (hdesc : ∃ k : ℕ, a ≤ k ∧ k < b ∧
      κ (k + 1 : ZMod n) < κ (k : ZMod n)) :
    DahlbergFourVertex κ := by
  rcases hdesc with ⟨k, hak, hkb, hdesc⟩
  have hnc : ¬ ∃ c, ∀ z : ZMod n, κ z = c := by
    rintro ⟨c, hc⟩
    rw [hc (k + 1 : ZMod n), hc (k : ZMod n)] at hdesc
    exact (lt_irrefl c) hdesc
  have hncNeg : ¬ ∃ c, ∀ z : ZMod n, -κ z = c :=
    not_constant_neg_iff.mpr hnc
  have hA_lt_k : κ (a : ZMod n) < κ (k : ZMod n) :=
    (hminA (k + 1 : ZMod n)).trans_lt hdesc
  have hkp1_lt_B : κ (k + 1 : ZMod n) < κ (b : ZMod n) :=
    hdesc.trans_le (hmaxB (k : ZMod n))
  have hleftA : ∃ t : ℕ, a ≤ t ∧ t ≤ k + 1 ∧
      -κ (t : ZMod n) < -κ (a : ZMod n) :=
    ⟨k, hak, by omega, neg_lt_neg hA_lt_k⟩
  have hleftB : ∃ t : ℕ, a ≤ t ∧ t ≤ k + 1 ∧
      -κ (t : ZMod n) < -κ ((k + 1 : ℕ) : ZMod n) :=
    ⟨k, hak, by omega, by simpa [Nat.cast_add] using neg_lt_neg hdesc⟩
  obtain ⟨p, hap, hpk, hminNeg⟩ :=
    exists_discreteLocalMin_between_of_strictly_below_endpoints
      (κ := fun z => -κ z) (a := a) (b := k + 1)
      (by omega) hleftA hleftB hncNeg
  have hmaxP : DiscreteLocalMax κ (p : ZMod n) :=
    discreteLocalMax_of_neg_localMin hminNeg
  have hrightA : ∃ t : ℕ, k ≤ t ∧ t ≤ b ∧
      κ (t : ZMod n) < κ (k : ZMod n) :=
    ⟨k + 1, by omega, by omega, by simpa [Nat.cast_add] using hdesc⟩
  have hrightB : ∃ t : ℕ, k ≤ t ∧ t ≤ b ∧
      κ (t : ZMod n) < κ (b : ZMod n) :=
    ⟨k + 1, by omega, by omega, by simpa [Nat.cast_add] using hkp1_lt_B⟩
  obtain ⟨m, hkm, hmb, hminM⟩ :=
    exists_discreteLocalMin_between_of_strictly_below_endpoints
      (κ := κ) (a := k) (b := b) hkb hrightA hrightB hnc
  have hminA_local : DiscreteLocalMin κ (a : ZMod n) :=
    discreteLocalMin_of_globalMin_of_not_constant hminA hnc
  have hmaxB_local : DiscreteLocalMax κ (b : ZMod n) :=
    discreteLocalMax_of_globalMax_of_not_constant hmaxB hnc
  have hcast : ((a + n : ℕ) : ZMod n) = (a : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  exact ⟨p, m, b, a + n, by omega, hmb, hwrap, by omega,
    hmaxP, hminM, hmaxB_local, by simpa [hcast] using hminA_local⟩

theorem weaklyIncreasingLift_between_globalMinMax_of_not_dahlberg
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {a b : ℕ}
    (hwrap : b < a + n)
    (hminA : ∀ z : ZMod n, κ (a : ZMod n) ≤ κ z)
    (hmaxB : ∀ z : ZMod n, κ z ≤ κ (b : ZMod n))
    (hnot : ¬ DahlbergFourVertex κ) :
    WeaklyIncreasingLift κ a b := by
  intro k hak hkb
  by_contra hle
  apply hnot
  exact dahlbergFourVertex_of_descent_between_globalMinMax
    hwrap hminA hmaxB ⟨k, hak, hkb, lt_of_not_ge hle⟩

/-- With the global minimum normalized to `0` and the global maximum lifted
to `d ∈ (0,n)`, failure of the four-vertex conclusion forces monotonicity on
both complementary arcs. -/
theorem twoArcMonotone_zero_of_not_dahlberg
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {d : ℕ}
    (hdpos : 0 < d) (hdlt : d < n)
    (hmin0 : ∀ z : ZMod n, κ 0 ≤ κ z)
    (hmaxd : ∀ z : ZMod n, κ z ≤ κ (d : ZMod n))
    (hnot : ¬ DahlbergFourVertex κ) :
    WeaklyIncreasingLift κ 0 d ∧ WeaklyDecreasingLift κ d n := by
  have hinc : WeaklyIncreasingLift κ 0 d :=
    weaklyIncreasingLift_between_globalMinMax_of_not_dahlberg
      (by simpa using hdlt) (by intro z; simpa using hmin0 z) hmaxd hnot
  have hnotNeg : ¬ DahlbergFourVertex (fun z => -κ z) := by
    intro hfv
    exact hnot (dahlbergFourVertex_of_neg hfv)
  have hminNegD : ∀ z : ZMod n, -κ (d : ZMod n) ≤ -κ z := by
    intro z
    exact neg_le_neg (hmaxd z)
  have hmaxNegN : ∀ z : ZMod n, -κ z ≤ -κ (n : ZMod n) := by
    intro z
    have hz := neg_le_neg (hmin0 z)
    simpa [ZMod.natCast_self] using hz
  have hincNeg : WeaklyIncreasingLift (fun z => -κ z) d n :=
    weaklyIncreasingLift_between_globalMinMax_of_not_dahlberg
      (by omega) hminNegD hmaxNegN hnotNeg
  refine ⟨hinc, ?_⟩
  intro k hdk hkn
  exact neg_le_neg_iff.mp (hincNeg k hdk hkn)

/-- A two-arc monotone profile whose global minimum is nonpositive has a
connected nonpositive vertex set.  Connectedness is expressed by the exact
cyclic-interval predicate used by the finite component API. -/
theorem nonpositiveVertices_isCyclicInterval_of_twoArcMonotone_zero
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {d : ℕ}
    (hdlt : d < n) (hmin0 : κ 0 ≤ 0)
    (htwo : WeaklyIncreasingLift κ 0 d ∧ WeaklyDecreasingLift κ d n) :
    Gluck.IsCyclicInterval (NonpositiveVertices κ) := by
  let S : Finset (ZMod n) := NonpositiveVertices κ
  let c : ZMod n := (d : ZMod n)
  let T : Finset ℕ := Gluck.cutFinset c S
  let e : ℕ := n - d
  let f : ℕ → ℝ := fun t => κ (Gluck.cyclicLift c t)
  have hS : S.Nonempty := by
    refine ⟨0, ?_⟩
    simpa [S] using hmin0
  have hT : T.Nonempty := by
    simpa [T] using (Gluck.cutFinset_nonempty_iff c S).mpr hS
  have hTrange : T ⊆ Finset.range n := by
    simpa [T] using Gluck.cutFinset_subset_range c S
  have hdecCut : ∀ t : ℕ, t < e → f (t + 1) ≤ f t := by
    intro t hte
    have hstep := htwo.2 (d + t) (by omega) (by dsimp [e] at hte; omega)
    dsimp [f, c]
    simpa [Gluck.cyclicLift, Nat.cast_add, add_assoc] using hstep
  have hincCut : ∀ t : ℕ, e ≤ t → t < n → f t ≤ f (t + 1) := by
    intro t het htn
    let k : ℕ := t - e
    have hekt : e + k = t := by
      exact Nat.add_sub_of_le het
    have hklt : k < d := by
      dsimp [k, e]
      omega
    have hstep := htwo.1 k (Nat.zero_le k) hklt
    have hidx : Gluck.cyclicLift c t = (k : ZMod n) := by
      dsimp [Gluck.cyclicLift, c]
      rw [← hekt, Nat.cast_add]
      dsimp [e]
      rw [Nat.cast_sub (Nat.le_of_lt hdlt), ZMod.natCast_self]
      abel
    have hidx1 : Gluck.cyclicLift c (t + 1) = (k : ZMod n) + 1 := by
      calc
        Gluck.cyclicLift c (t + 1) = Gluck.cyclicLift c t + 1 := by
          simp [Gluck.cyclicLift, Nat.cast_add, add_assoc]
        _ = (k : ZMod n) + 1 := by rw [hidx]
    dsimp [f]
    rw [hidx, hidx1]
    exact hstep
  have hconvex : ∀ x ∈ T, ∀ y ∈ T, ∀ z : ℕ,
      x ≤ z → z ≤ y → z ∈ T := by
    intro x hxT y hyT z hxz hzy
    have hxlt : x < n := (Gluck.mem_cutFinset.mp (by simpa [T] using hxT)).1
    have hylt : y < n := (Gluck.mem_cutFinset.mp (by simpa [T] using hyT)).1
    have hxnonpos : f x ≤ 0 := by
      have hxS := (Gluck.mem_cutFinset.mp (by simpa [T] using hxT)).2
      exact mem_nonpositiveVertices.mp (by simpa [S, f] using hxS)
    have hynonpos : f y ≤ 0 := by
      have hyS := (Gluck.mem_cutFinset.mp (by simpa [T] using hyT)).2
      exact mem_nonpositiveVertices.mp (by simpa [S, f] using hyS)
    have hzlt : z < n := lt_of_le_of_lt hzy hylt
    have hznonpos : f z ≤ 0 := by
      by_cases hze : z ≤ e
      · exact (value_le_of_adjacent_ge
          (fun t _ ht => hdecCut t ht) (Nat.zero_le x) hxz hze).trans hxnonpos
      · have hez : e ≤ z := le_of_not_ge hze
        exact (value_le_of_adjacent_le hincCut hez hzy hylt.le).trans hynonpos
    apply Gluck.mem_cutFinset.mpr
    refine ⟨hzlt, ?_⟩
    apply mem_nonpositiveVertices.mpr
    simpa [S, f] using hznonpos
  have hTinterval : Gluck.IsNatInterval T :=
    isNatInterval_of_nonempty_of_orderConvex hT hconvex
  have hcyclic : Gluck.IsCyclicInterval (Gluck.mapCut c T) :=
    Gluck.isCyclicInterval_mapCut_of_natInterval_of_subset_range
      hTinterval hTrange
  simpa [T, S, Gluck.mapCut_cutFinset] using hcyclic

theorem nonpositiveVertices_isCyclicInterval_of_twoArcMonotone
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {qmin qmax : ZMod n}
    (hminNonpos : κ qmin ≤ 0)
    (htwo : TwoArcMonotone κ qmin qmax) :
    Gluck.IsCyclicInterval (NonpositiveVertices κ) := by
  let d : ℕ := (qmax - qmin).val
  change 0 < d ∧ d < n ∧
    WeaklyIncreasingLift (fun z => κ (z + qmin)) 0 d ∧
    WeaklyDecreasingLift (fun z => κ (z + qmin)) d n at htwo
  rcases htwo with ⟨_hdpos, hdlt, hinc, hdec⟩
  let μ : ZMod n → ℝ := fun z => κ (z + qmin)
  have hminμ : μ 0 ≤ 0 := by
    simpa [μ] using hminNonpos
  have hintervalμ : Gluck.IsCyclicInterval (NonpositiveVertices μ) :=
    nonpositiveVertices_isCyclicInterval_of_twoArcMonotone_zero
      hdlt hminμ (by simpa [μ] using And.intro hinc hdec)
  have htranslated := isCyclicInterval_translateZModFinset qmin hintervalμ
  rw [translateZModFinset_nonpositiveVertices_shift κ qmin] at htranslated
  exact htranslated

/-- This is the finite combinatorial assertion used twice in Dahlberg §4:
if the profile is nonconstant but does not satisfy the four-vertex conclusion,
global minimum and maximum plateaux can be chosen so that both connecting
arcs are monotone. -/
theorem exists_globalMinMax_twoArcMonotone_of_not_dahlberg
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hnc : ¬ ∃ c, ∀ z : ZMod n, κ z = c)
    (hnot : ¬ DahlbergFourVertex κ) :
    ∃ qmin qmax : ZMod n,
      (∀ z : ZMod n, κ qmin ≤ κ z) ∧
      (∀ z : ZMod n, κ z ≤ κ qmax) ∧
      κ qmin < κ qmax ∧ TwoArcMonotone κ qmin qmax := by
  obtain ⟨qmin, qmax, hmin, hmax, hlt⟩ :=
    exists_globalMinMax_strict_of_not_constant hnc
  let d : ℕ := (qmax - qmin).val
  let μ : ZMod n → ℝ := fun z => κ (z + qmin)
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd0
    have hdiff : qmax - qmin = 0 :=
      (ZMod.val_eq_zero (qmax - qmin)).mp hd0
    have hEq : qmax = qmin := by
      have := congrArg (fun z : ZMod n => z + qmin) hdiff
      simpa using this
    rw [hEq] at hlt
    exact (lt_irrefl _) hlt
  have hdlt : d < n := ZMod.val_lt (qmax - qmin)
  have hdcast : (d : ZMod n) = qmax - qmin := by
    exact ZMod.natCast_zmod_val (qmax - qmin)
  have hminμ : ∀ z : ZMod n, μ 0 ≤ μ z := by
    intro z
    dsimp [μ]
    simpa using hmin (z + qmin)
  have hmaxμ : ∀ z : ZMod n, μ z ≤ μ (d : ZMod n) := by
    intro z
    dsimp [μ]
    have hz := hmax (z + qmin)
    convert hz using 1
    rw [hdcast]
    abel_nf
  have hnotμ : ¬ DahlbergFourVertex μ := by
    intro hfv
    apply hnot
    exact (dahlbergFourVertex_translateIndex_iff (κ := κ) (a := qmin)).mp
      (by simpa [μ] using hfv)
  have htwo := twoArcMonotone_zero_of_not_dahlberg
    hdpos hdlt hminμ hmaxμ hnotμ
  refine ⟨qmin, qmax, hmin, hmax, hlt, ?_⟩
  dsimp [TwoArcMonotone]
  simpa [d, μ] using And.intro hdpos (And.intro hdlt htwo)

/-- Section 4's connected-sign-set consequence: once some curvature value is
nonpositive, the unique global-minimum valley forced by failure of the
four-vertex conclusion makes the entire nonpositive set one cyclic interval. -/
theorem exists_globalMinMax_twoArcMonotone_and_nonpositiveConnected
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hnc : ¬ ∃ c, ∀ z : ZMod n, κ z = c)
    (hnot : ¬ DahlbergFourVertex κ)
    (hnonpos : ∃ z : ZMod n, κ z ≤ 0) :
    ∃ qmin qmax : ZMod n,
      (∀ z : ZMod n, κ qmin ≤ κ z) ∧
      (∀ z : ZMod n, κ z ≤ κ qmax) ∧
      κ qmin < κ qmax ∧
      TwoArcMonotone κ qmin qmax ∧
      Gluck.IsCyclicInterval (NonpositiveVertices κ) := by
  obtain ⟨qmin, qmax, hmin, hmax, hlt, htwo⟩ :=
    exists_globalMinMax_twoArcMonotone_of_not_dahlberg hnc hnot
  rcases hnonpos with ⟨z, hz⟩
  have hminNonpos : κ qmin ≤ 0 := (hmin z).trans hz
  exact ⟨qmin, qmax, hmin, hmax, hlt, htwo,
    nonpositiveVertices_isCyclicInterval_of_twoArcMonotone hminNonpos htwo⟩

end Gluck.Forward
