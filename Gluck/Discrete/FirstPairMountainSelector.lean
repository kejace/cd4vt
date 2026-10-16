module

public import Gluck.Discrete.CurvatureMountainSelection
public import Gluck.Discrete.NativeFirstPairRealization

/-!
# Selecting a literal first-pair transition on a rising mountain

A nonnegative terminal flag produces its first negative-to-nonnegative
transition on the actual consecutive rising leg. The four retained edges
are exactly `0`, `i-1`, `i`, and `n-1`. The native first-pair theorem opens
all remaining original edges and gives the coherent `RealizesR2` conclusion.
-/

@[expose] public section

namespace Gluck.Discrete

open Set NativeOppositePure FourActiveSlots

/-- A pair whose first reading is at most the normalized low peak has a
strictly negative flag. No extra principal-branch hypothesis is needed. -/
theorem firstPairFlag_lt_zero_of_le_one {p t h l : ℝ}
    (hp : p < 1) (ht : t ≤ 1) : firstPairFlag p t h l < 0 := by
  have hs : 0 ≤ firstPairSigma h l := Real.sqrt_nonneg _
  have hmul : t * firstPairSigma h l ≤ firstPairSigma h l := by
    simpa using mul_le_mul_of_nonneg_right ht hs
  have hangle := Real.arcsin_le_arcsin hmul
  have hpangle := Real.arcsin_lt_pi_div_two.mpr hp
  unfold firstPairFlag
  linarith

/-- The first nonnegative flag on a rising interval is an actual transition.
The incoming reading can be below, equal to, or above p. -/
theorem exists_firstPair_transition_on_rising_interval
    {w : ℕ → ℝ} {p l : ℝ} {a k : ℕ}
    (ha : 0 < a) (hak : a ≤ k) (hp : p < 1)
    (hentry : w (a - 1) ≤ 1) (hhigh : 1 < w a)
    (hrise : StrictMonoOn w (Icc a k))
    (hterminal : 0 ≤ firstPairFlag p (w (k - 1)) (w k) l) :
    ∃ i, a ≤ i ∧ i < k ∧ 1 < w i ∧ w (i - 1) < w i ∧ w i < w (i + 1) ∧
      0 ≤ firstPairFlag p (w i) (w (i + 1)) l ∧
      firstPairFlag p (w (i - 1)) (w i) l < 0 := by
  classical
  let P : ℕ → Prop := fun i => a - 1 ≤ i ∧ i < k ∧
    0 ≤ firstPairFlag p (w i) (w (i + 1)) l
  have hex : ∃ i, P i := by
    refine ⟨k - 1, ?_⟩
    change a - 1 ≤ k - 1 ∧ k - 1 < k ∧ _
    refine ⟨by omega, by omega, ?_⟩
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hterminal
  let i := Nat.find hex
  have hi := Nat.find_spec hex
  change a - 1 ≤ i ∧ i < k ∧ 0 ≤ firstPairFlag p (w i) (w (i + 1)) l at hi
  have hai : a ≤ i := by
    by_contra h
    have hieq : i = a - 1 := by omega
    have hneg := firstPairFlag_lt_zero_of_le_one (h := w a) (l := l) hp hentry
    have hnonneg := hi.2.2
    rw [hieq, Nat.sub_add_cancel (by omega : 1 ≤ a)] at hnonneg
    linarith
  have hprev : firstPairFlag p (w (i - 1)) (w i) l < 0 := by
    by_contra h
    have hPi : P (i - 1) := by
      refine ⟨by omega, by omega, ?_⟩
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using le_of_not_gt h
    have hmin := Nat.find_min' hex hPi
    change i ≤ i - 1 at hmin
    omega
  have hqi : 1 < w i := by
    rcases eq_or_lt_of_le hai with heq | hlt
    · simpa [← heq] using hhigh
    · exact hhigh.trans (hrise ⟨le_rfl, hak⟩ ⟨hai, hi.2.1.le⟩ hlt)
  have hti : w (i - 1) < w i := by
    by_cases hia : i = a
    · simpa only [hia] using lt_of_le_of_lt hentry hhigh
    · apply hrise ⟨by omega, by omega⟩ ⟨hai, hi.2.1.le⟩
      omega
  have hiNext : w i < w (i + 1) :=
    hrise ⟨hai, hi.2.1.le⟩ ⟨by omega, by omega⟩ (by omega)
  exact ⟨i, hai, hi.2.1, hqi, hti, hiNext, hi.2.2, hprev⟩

namespace FourActiveSlots

/-- The four retained edges at an actual consecutive transition. -/
def firstPairFrame {n i : ℕ} (hi : 2 ≤ i) (hin : i + 2 ≤ n) : Frame n where
  edge := ![0, i - 1, i, n - 1]
  strictMono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    fin_cases j <;> simp <;> omega
  lt_n := by
    intro j
    fin_cases j <;> simp <;> omega

theorem firstPairFrame_start {n i : ℕ} (hi : 2 ≤ i) (hin : i + 2 ≤ n)
    (κ : ZMod n → ℝ) (hzero : κ 0 = 1) :
    (firstPairFrame hi hin).start κ =
      ![1, κ ((i - 1 : ℕ) : ZMod n), κ (i : ZMod n), κ ((n - 1 : ℕ) : ZMod n)] := by
  funext j
  fin_cases j <;> simp [Frame.start, Frame.residue, firstPairFrame, hzero]

theorem firstPairFrame_finish {n i : ℕ} (hi : 2 ≤ i) (hin : i + 2 ≤ n)
    (κ : ZMod n → ℝ) (hzero : κ 0 = 1) :
    (firstPairFrame hi hin).finish κ =
      ![κ 1, κ (i : ZMod n), κ ((i + 1 : ℕ) : ZMod n), 1] := by
  have hip : ((i - 1 : ℕ) : ZMod n) + 1 = (i : ZMod n) := by
    rw [Nat.cast_sub (by omega : 1 ≤ i)]
    simp
  have hwrap : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    simp
  funext j
  fin_cases j <;> simp [Frame.finish, Frame.residue, firstPairFrame, hip, hwrap, hzero,
    Nat.cast_add]

end FourActiveSlots

/-- A rising mountain leg with nonnegative terminal flag realizes the
entire original normalized profile, with every hidden reading retained. -/
theorem realizesR2_of_rising_mountain_terminal {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {a k : ℕ}
    (hκ : ∀ j, 0 < κ j) (hzero : κ 0 = 1)
    (hp : κ 1 < 1) (hl : κ ((n - 1 : ℕ) : ZMod n) < 1)
    (ha : 2 ≤ a) (hak : a ≤ k) (hkn : k + 2 ≤ n)
    (hentry : κ ((a - 1 : ℕ) : ZMod n) ≤ 1) (hhigh : 1 < κ (a : ZMod n))
    (hrise : StrictMonoOn (fun j : ℕ => κ (j : ZMod n)) (Icc a k))
    (hterminal : 0 ≤ firstPairFlag (κ 1) (κ ((k - 1 : ℕ) : ZMod n))
      (κ (k : ZMod n)) (κ ((n - 1 : ℕ) : ZMod n))) : RealizesR2 κ := by
  obtain ⟨i, hai, hik, hq, htq, hqh, hflag, hprev⟩ :=
    exists_firstPair_transition_on_rising_interval (by omega) hak hp hentry hhigh hrise hterminal
  have hi : 2 ≤ i := by omega
  have hin : i + 2 ≤ n := by omega
  let F := firstPairFrame hi hin
  exact F.realizesR2_of_firstPair_transition (firstPairFrame_start hi hin κ hzero)
    (firstPairFrame_finish hi hin κ hzero) hκ (hκ 1) hp (hκ _) htq (hκ _) hl
    hq hqh hflag hprev

/-- Apply the fully produced mountain selector directly. Only the selected
peak is normalized and rotated; all other readings are the original data. -/
theorem HighestSecondaryPeak.realizesR2_of_rising_terminal {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {H : ZMod n} (hq : HighestSecondaryPeak κ H 0)
    (hκ : ∀ j, 0 < κ j) (hne : ∀ j, κ j ≠ κ (j + 1))
    (hzero : κ 0 = 1) (hH : 1 < κ H)
    (hterminal : 0 ≤ firstPairFlag (κ 1) (κ ((H.val - 1 : ℕ) : ZMod n))
      (κ H) (κ (-1))) : RealizesR2 κ := by
  obtain ⟨a, b, ha, hak, hkb, hbn, hset, hrise, -⟩ :=
    hq.exists_mountain hne (by simpa only [hzero] using hH)
  simp only [sub_zero, zero_add] at hak hkb hset hrise
  have hkn : H.val + 2 ≤ n := by omega
  have ha_lt : a < n := by omega
  have hwrap : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    simp
  have hp : κ 1 < 1 := by simpa [hzero] using hq.is_peak.2
  have hl : κ ((n - 1 : ℕ) : ZMod n) < 1 := by
    simpa [hwrap, hzero] using hq.is_peak.1
  have hentry : κ ((a - 1 : ℕ) : ZMod n) ≤ 1 := by
    by_contra h
    have hh : κ 0 < κ ((a - 1 : ℕ) : ZMod n) := by simpa only [hzero] using lt_of_not_ge h
    have hbad := ((hset (a - 1) (by omega)).mp hh).1
    omega
  have hhigh : 1 < κ (a : ZMod n) := by
    have hh := (hset a ha_lt).mpr ⟨le_rfl, by omega⟩
    simpa only [hzero] using hh
  apply realizesR2_of_rising_mountain_terminal hκ hzero hp hl ha hak hkn hentry hhigh hrise
  simpa only [ZMod.natCast_zmod_val, hwrap] using hterminal

end Gluck.Discrete
