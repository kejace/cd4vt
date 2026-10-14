import Gluck.Discrete.RegularFourAnchor
import Gluck.Discrete.FirstPairMountainSelector

/-!
# Retaining the first-pair anchor before opening dormant edges

The selected data can be lifted to a word with constant runs before any
edges are opened. No closedness property of `RealizesR2` is used.
-/

namespace Gluck.Discrete

open Set NativeOppositePure FourActiveSlots

theorem FourActiveSlots.Frame.nonempty_regularFourAnchor_of_firstPair_transition
    {n : ℕ} (F : FourActiveSlots.Frame n)
    {κ : ZMod n → ℝ} {p t q h l : ℝ}
    (hstart : F.start κ = ![1, t, q, l])
    (hfinish : F.finish κ = ![p, q, h, 1])
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l)
    (hprev : firstPairFlag p t q l < 0) : Nonempty (RegularFourAnchor κ) := by
  obtain ⟨L, hphysical, hzero, hsurj⟩ :=
    exists_regular_anchor_of_firstPair_transition hp hp1 ht htq hl hl1 hq hqh hflag hprev
  exact ⟨RegularFourAnchor.ofNative F hstart hfinish hphysical hzero hsurj⟩

/-- A rising mountain leg with nonnegative terminal flag realizes the
entire original normalized profile, with every hidden reading retained. -/
theorem nonempty_regularFourAnchor_of_rising_mountain_terminal {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {a k : ℕ}
    (hκ : ∀ j, 0 < κ j) (hzero : κ 0 = 1)
    (hp : κ 1 < 1) (hl : κ ((n - 1 : ℕ) : ZMod n) < 1)
    (ha : 2 ≤ a) (hak : a ≤ k) (hkn : k + 2 ≤ n)
    (hentry : κ ((a - 1 : ℕ) : ZMod n) ≤ 1) (hhigh : 1 < κ (a : ZMod n))
    (hrise : StrictMonoOn (fun j : ℕ => κ (j : ZMod n)) (Icc a k))
    (hterminal : 0 ≤ firstPairFlag (κ 1) (κ ((k - 1 : ℕ) : ZMod n))
      (κ (k : ZMod n)) (κ ((n - 1 : ℕ) : ZMod n))) : Nonempty (RegularFourAnchor κ) := by
  obtain ⟨i, hai, hik, hq, htq, hqh, hflag, hprev⟩ :=
    exists_firstPair_transition_on_rising_interval (by omega) hak hp hentry hhigh hrise hterminal
  have hi : 2 ≤ i := by omega
  have hin : i + 2 ≤ n := by omega
  let F := firstPairFrame hi hin
  exact F.nonempty_regularFourAnchor_of_firstPair_transition (firstPairFrame_start hi hin κ hzero)
    (firstPairFrame_finish hi hin κ hzero) (hκ 1) hp (hκ _) htq (hκ _) hl
    hq hqh hflag hprev

/-- Apply the fully produced mountain selector directly. Only the selected
peak is normalized and rotated; all other readings are the original data. -/
theorem HighestSecondaryPeak.nonempty_regularFourAnchor_of_rising_terminal {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {H : ZMod n} (hq : HighestSecondaryPeak κ H 0)
    (hκ : ∀ j, 0 < κ j) (hne : ∀ j, κ j ≠ κ (j + 1))
    (hzero : κ 0 = 1) (hH : 1 < κ H)
    (hterminal : 0 ≤ firstPairFlag (κ 1) (κ ((H.val - 1 : ℕ) : ZMod n))
      (κ H) (κ (-1))) : Nonempty (RegularFourAnchor κ) := by
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
  apply nonempty_regularFourAnchor_of_rising_mountain_terminal hκ hzero hp hl ha hak hkn hentry hhigh hrise
  simpa only [ZMod.natCast_zmod_val, hwrap] using hterminal

end Gluck.Discrete
