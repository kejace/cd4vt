import Gluck.Discrete.RegularFourAnchor
import Gluck.Discrete.ConstantRunDFV

/-!
# Removing and restoring one repeated cyclic reading

Deleting a reading equal to its successor preserves the ordered endpoint
pairs of every surviving edge. Consequently a regular four-edge anchor
of the shorter word lifts to the original word, with its full derivative
unchanged. This is a finite operation on actual indices, not a limiting
argument about realizations.
-/

namespace Gluck.Discrete.ConstantRun

/-- The increasing inclusion of all natural indices except `a`. -/
def skip (a j : ℕ) : ℕ := if j < a then j else j + 1

theorem skip_strictMono (a : ℕ) : StrictMono (skip a) := by
  intro i j hij
  simp only [skip]
  split_ifs <;> omega

theorem skip_lt {m a j : ℕ} (hj : j < m) : skip a j < m + 1 := by
  simp only [skip]
  split_ifs <;> omega

/-- The monotone index map identifying the deleted reading with its successor.
At the last reading it may equal `m`, representing the next cyclic zero. -/
def mergeIndex (a j : ℕ) : ℕ := if j ≤ a then j else j - 1

theorem mergeIndex_mono (a : ℕ) : Monotone (mergeIndex a) := by
  intro i j hij
  simp only [mergeIndex]
  split_ifs <;> omega

theorem mergeIndex_le {m a j : ℕ} (hj : j < m + 1) :
    mergeIndex a j ≤ m := by
  simp only [mergeIndex]
  split_ifs <;> omega

/-- The same collapse on arbitrary natural lifts of cyclic indices. -/
def collapse (m a i : ℕ) : ℕ :=
  (i / (m + 1)) * m + mergeIndex a (i % (m + 1))

theorem collapse_mono (m a : ℕ) : Monotone (collapse m a) := by
  intro i j hij
  have hdiv := Nat.div_le_div_right hij (c := m + 1)
  have himod := Nat.mod_lt i (by omega : 0 < m + 1)
  have hjmod := Nat.mod_lt j (by omega : 0 < m + 1)
  have hiadd := Nat.div_add_mod i (m + 1)
  have hjadd := Nat.div_add_mod j (m + 1)
  by_cases heq : i / (m + 1) = j / (m + 1)
  · have hmod : i % (m + 1) ≤ j % (m + 1) := by rw [heq] at hiadd; omega
    simp only [collapse, heq]
    exact Nat.add_le_add_left (mergeIndex_mono a hmod) _
  · have hstep : i / (m + 1) + 1 ≤ j / (m + 1) := by omega
    have hmul := Nat.mul_le_mul_right m hstep
    have himerge := mergeIndex_le (a := a) himod
    simp only [collapse]
    nlinarith

theorem collapse_add_period (m a i : ℕ) :
    collapse m a (i + (m + 1)) = collapse m a i + m := by
  simp [collapse, Nat.add_div_right, Nat.add_mod_right, Nat.add_mul, Nat.add_assoc,
    Nat.add_comm]

/-- Erase the indicated entry; the geometric lifting theorem requires it
to agree with the next entry. -/
def eraseWord {m : ℕ} (κ : ZMod (m + 1) → ℝ) (a : Fin (m + 1)) :
    ZMod m → ℝ := fun i => κ (skip a.val i.val : ZMod (m + 1))

theorem eraseWord_positive {m : ℕ} {κ : ZMod (m + 1) → ℝ}
    (hκ : ∀ i, 0 < κ i) (a : Fin (m + 1)) : ∀ i, 0 < eraseWord κ a i :=
  fun _ => hκ _

theorem eraseWord_mergeIndex {m : ℕ} [NeZero m] {κ : ZMod (m + 1) → ℝ}
    (a : Fin (m + 1))
    (hdup : κ (a.val : ZMod (m + 1)) = κ ((a.val : ZMod (m + 1)) + 1))
    {j : ℕ} (hj : j < m + 1) :
    eraseWord κ a (mergeIndex a.val j : ZMod m) = κ (j : ZMod (m + 1)) := by
  have hm : 0 < m := NeZero.pos m
  have ha : a.val ≤ m := by omega
  by_cases hja : j < a.val
  · have hjm : j < m := by omega
    simp [eraseWord, mergeIndex, Nat.le_of_lt hja, ZMod.val_natCast_of_lt hjm,
      skip, hja]
  · by_cases haj : a.val < j
    · have hjm : j - 1 < m := by omega
      have hskip : skip a.val (j - 1) = j := by simp only [skip]; split_ifs <;> omega
      simp [eraseWord, mergeIndex, Nat.not_le.mpr haj,
        ZMod.val_natCast_of_lt hjm, hskip]
    · have hjeq : j = a.val := by omega
      subst j
      by_cases ham : a.val < m
      · simpa [eraseWord, mergeIndex, ZMod.val_natCast_of_lt ham, skip, Nat.cast_add]
          using hdup.symm
      · have heq : a.val = m := by omega
        have hcast : (m : ZMod (m + 1)) + 1 = 0 := by
          simpa only [Nat.cast_add, Nat.cast_one] using (ZMod.natCast_self (m + 1))
        have hlast : κ (m : ZMod (m + 1)) = κ 0 := by
          simpa only [heq, hcast] using hdup
        simpa [eraseWord, mergeIndex, heq, skip, hm] using hlast.symm

theorem eraseWord_collapse {m : ℕ} [NeZero m] {κ : ZMod (m + 1) → ℝ}
    (a : Fin (m + 1))
    (hdup : κ (a.val : ZMod (m + 1)) = κ ((a.val : ZMod (m + 1)) + 1))
    (i : ℕ) :
    eraseWord κ a (collapse m a.val i : ZMod m) = κ (i : ZMod (m + 1)) := by
  have h := eraseWord_mergeIndex a hdup (Nat.mod_lt i (by omega : 0 < m + 1))
  simpa [collapse, Nat.cast_add, Nat.cast_mul] using h

theorem collapse_skip_succ {m a j : ℕ} (hj : j < m) :
    collapse m a (skip a j + 1) = j + 1 := by
  by_cases hlast : skip a j + 1 < m + 1
  · simp only [collapse, Nat.div_eq_of_lt hlast, Nat.mod_eq_of_lt hlast,
      zero_mul, zero_add]
    simp only [skip, mergeIndex]
    split_ifs <;> omega
  · have hbound := skip_lt (a := a) hj
    have heq : skip a j + 1 = m + 1 := by omega
    have hjlast : j + 1 = m := by simp only [skip] at heq; split_ifs at heq <;> omega
    simp [collapse, heq, mergeIndex, hjlast]

theorem eraseWord_finish {m : ℕ} [NeZero m] {κ : ZMod (m + 1) → ℝ}
    (a : Fin (m + 1))
    (hdup : κ (a.val : ZMod (m + 1)) = κ ((a.val : ZMod (m + 1)) + 1))
    {j : ℕ} (hj : j < m) :
    eraseWord κ a ((j : ZMod m) + 1) = κ ((skip a.val j : ZMod (m + 1)) + 1) := by
  have h := eraseWord_collapse a hdup (skip a.val j + 1)
  simpa only [collapse_skip_succ hj, Nat.cast_add, Nat.cast_one] using h

/-- The same four actual edges after restoring the erased reading. -/
def restoreFrame {m : ℕ} (F : FourActiveSlots.Frame m) (a : Fin (m + 1)) :
    FourActiveSlots.Frame (m + 1) where
  edge := fun j => skip a.val (F.edge j)
  strictMono := (skip_strictMono a.val).comp F.strictMono
  lt_n := fun j => skip_lt (F.lt_n j)

theorem restoreFrame_start {m : ℕ} [NeZero m] (F : FourActiveSlots.Frame m)
    (κ : ZMod (m + 1) → ℝ) (a : Fin (m + 1)) :
    (restoreFrame F a).start κ = F.start (eraseWord κ a) := by
  funext j
  simp [FourActiveSlots.Frame.start, FourActiveSlots.Frame.residue,
    restoreFrame, eraseWord, ZMod.val_natCast_of_lt (F.lt_n j)]

theorem restoreFrame_finish {m : ℕ} [NeZero m] (F : FourActiveSlots.Frame m)
    {κ : ZMod (m + 1) → ℝ} (a : Fin (m + 1))
    (hdup : κ (a.val : ZMod (m + 1)) = κ ((a.val : ZMod (m + 1)) + 1)) :
    (restoreFrame F a).finish κ = F.finish (eraseWord κ a) := by
  funext j
  exact (eraseWord_finish a hdup (F.lt_n j)).symm

/-- Restore one constant-run entry without changing any endpoint function
or the actual rank of the four-length controller. -/
noncomputable def restoreAnchor {m : ℕ} [NeZero m] {κ : ZMod (m + 1) → ℝ}
    (a : Fin (m + 1))
    (hdup : κ (a.val : ZMod (m + 1)) = κ ((a.val : ZMod (m + 1)) + 1))
    (A : RegularFourAnchor (eraseWord κ a)) : RegularFourAnchor κ :=
  A.reembed (restoreFrame A.frame a) (restoreFrame_start A.frame κ a)
    (restoreFrame_finish A.frame a hdup)

theorem realizesR2_of_erased_anchor {m : ℕ} [NeZero m] {κ : ZMod (m + 1) → ℝ}
    (hκ : ∀ i, 0 < κ i) (a : Fin (m + 1))
    (hdup : κ (a.val : ZMod (m + 1)) = κ ((a.val : ZMod (m + 1)) + 1))
    (A : RegularFourAnchor (eraseWord κ a)) : RealizesR2 κ :=
  (restoreAnchor a hdup A).realizesR2 hκ

theorem eraseWord_dfv {m : ℕ} [NeZero m] {κ : ZMod (m + 1) → ℝ} {c : ℝ}
    (a : Fin (m + 1))
    (hdup : κ (a.val : ZMod (m + 1)) = κ ((a.val : ZMod (m + 1)) + 1))
    (hdfv : DFV κ c) : DFV (eraseWord κ a) c :=
  hdfv.of_monotone_periodic_collapse (collapse_mono m a.val)
    (collapse_add_period m a.val) (eraseWord_collapse a hdup)

/-- A producer for all adjacent-unequal DFV words supplies regular anchors
for every DFV word, by finite deletion and exact restoration of constant
runs. This theorem keeps the producer as an explicit remaining premise. -/
theorem nonempty_regularFourAnchor_of_adjacent_unequal_producer
    (hbase : ∀ (m : ℕ) (μ : ZMod m → ℝ) (c : ℝ),
      4 ≤ m → (∀ i, 0 < μ i) → DFV μ c →
      (∀ i, μ i ≠ μ (i + 1)) → Nonempty (RegularFourAnchor μ))
    {n : ℕ} {κ : ZMod n → ℝ} {c : ℝ}
    (hκ : ∀ i, 0 < κ i) (hdfv : DFV κ c) : Nonempty (RegularFourAnchor κ) := by
  classical
  suffices hall : ∀ (k : ℕ) (w : ZMod k → ℝ) (c : ℝ),
      (∀ i, 0 < w i) → DFV w c → Nonempty (RegularFourAnchor w) by
    exact hall n κ c hκ hdfv
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro w c hw hd
    by_cases hne : ∀ i, w i ≠ w (i + 1)
    · exact hbase k w c hd.four_le_period hw hd hne
    · push Not at hne
      obtain ⟨i, hi⟩ := hne
      have hk := hd.four_le_period
      cases k with
      | zero => omega
      | succ m =>
        have hm : 0 < m := by omega
        let : NeZero m := ⟨by omega⟩
        let a : Fin (m + 1) := ⟨i.val, ZMod.val_lt i⟩
        have hdup : w (a.val : ZMod (m + 1)) = w ((a.val : ZMod (m + 1)) + 1) := by
          simpa only [a, ZMod.natCast_zmod_val] using hi
        have hd' := eraseWord_dfv a hdup hd
        obtain ⟨A⟩ := ih m (by omega) (eraseWord w a) c (eraseWord_positive hw a) hd'
        exact ⟨restoreAnchor a hdup A⟩

end Gluck.Discrete.ConstantRun
