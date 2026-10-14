import Gluck.Discrete.NativeRepeatedMaximum
import Gluck.Discrete.NativeIncidentOrthogonalRank
import Gluck.Discrete.RegularFourAnchor
import Gluck.Discrete.FirstPairMountainSelector

/-!
# An actual regular anchor at two repeated maxima

The selected edges are the four literal edges incident to the two maxima.
All intervening readings remain in the original word. The anchor is kept
as data, so constant runs can subsequently be restored before opening.
-/

namespace Gluck.Discrete

open NativeOppositePure FourActiveSlots

/-- Package the equal-pure producer and its actual half-length rank into
any original-word frame with the required eight endpoint readings. -/
theorem FourActiveSlots.Frame.nonempty_regularFourAnchor_of_repeated_maximum
    {n : ℕ} (F : Frame n) {κ : ZMod n → ℝ} {p t h l : ℝ}
    (hstart : F.start κ = ![1, t, 1, l])
    (hfinish : F.finish κ = ![p, 1, h, 1])
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hh1 : h < 1) (hl : 0 < l) (hl1 : l < 1) :
    Nonempty (RegularFourAnchor κ) := by
  obtain ⟨u, v, _hu, _hv, hphysical, _hres, hzero⟩ :=
    exists_nativeLength_anchor_of_repeated_maximum hp hp1 ht ht1 hh hh1 hl hl1
  have hregular := fderiv_nativeLengthController_surjective_of_equal_pure
    hp hp1 ht ht1 hl hl1 hh hh1 hphysical hzero
  exact ⟨RegularFourAnchor.ofNative F hstart hfinish hphysical hzero hregular⟩

/-- A second normalized maximum is separated from zero by at least one
strictly lower reading in each cyclic direction. -/
theorem repeated_maximum_index_separation {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {H : ZMod n}
    (hne : ∀ i, κ i ≠ κ (i + 1))
    (hzero : κ 0 = 1) (hH : κ H = 1) (hH0 : H ≠ 0) :
    2 ≤ H.val ∧ H.val + 2 ≤ n := by
  have hv : 0 < H.val := Nat.pos_of_ne_zero (fun hz => hH0 ((ZMod.val_eq_zero H).mp hz))
  have hvn := H.val_lt
  have hnot1 : H.val ≠ 1 := by
    intro hv1
    have he : H = 1 := by simpa [hv1] using (ZMod.natCast_zmod_val H).symm
    have hn := hne 0
    simp only [zero_add, hzero, ← he, hH, ne_eq, not_true_eq_false] at hn
  have hnotlast : H.val + 1 ≠ n := by
    intro he
    have hwrap : H + 1 = 0 := by
      rw [← ZMod.natCast_zmod_val H]
      norm_cast
      rw [he, ZMod.natCast_self]
    have hn := hne H
    rw [hwrap, hH, hzero] at hn
    exact hn rfl
  constructor <;> omega

/-- Positive adjacent-unequal words with two occurrences of the normalized
global maximum have an actual regular four-edge anchor. -/
theorem nonempty_regularFourAnchor_of_repeated_normalized_maximum
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {H : ZMod n}
    (hκ : ∀ i, 0 < κ i) (hle : ∀ i, κ i ≤ 1)
    (hne : ∀ i, κ i ≠ κ (i + 1))
    (hzero : κ 0 = 1) (hH : κ H = 1) (hH0 : H ≠ 0) :
    Nonempty (RegularFourAnchor κ) := by
  obtain ⟨hlo, hhi⟩ := repeated_maximum_index_separation hne hzero hH hH0
  let F := firstPairFrame hlo hhi
  have hp1 : κ 1 < 1 := lt_of_le_of_ne (hle 1) (by
    intro he
    exact hne 0 (by simpa [hzero] using he.symm))
  have ht1 : κ (H - 1) < 1 := lt_of_le_of_ne (hle (H - 1)) (by
    intro he
    exact hne (H - 1) (by simpa [hH] using he))
  have hh1 : κ (H + 1) < 1 := lt_of_le_of_ne (hle (H + 1)) (by
    intro he
    exact hne H (by rw [hH, he]))
  have hl1 : κ (-1) < 1 := lt_of_le_of_ne (hle (-1)) (by
    intro he
    exact hne (-1) (by simpa [hzero] using he))
  have hpred : ((H.val - 1 : ℕ) : ZMod n) = H - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ H.val), ZMod.natCast_zmod_val, Nat.cast_one]
  have hlast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    simp
  have hnext : ((H.val + 1 : ℕ) : ZMod n) = H + 1 := by simp
  have hstart : F.start κ = ![1, κ (H - 1), 1, κ (-1)] := by
    simpa [F, hpred, hlast, hH] using firstPairFrame_start hlo hhi κ hzero
  have hfinish : F.finish κ = ![κ 1, 1, κ (H + 1), 1] := by
    simpa [F, hnext, hH] using firstPairFrame_finish hlo hhi κ hzero
  exact F.nonempty_regularFourAnchor_of_repeated_maximum hstart hfinish
    (hκ 1) hp1 (hκ (H - 1)) ht1 (hκ (H + 1)) hh1 (hκ (-1)) hl1

/-- Open the retained repeated-maximum anchor in the original word. -/
theorem realizesR2_of_repeated_normalized_maximum
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {H : ZMod n}
    (hκ : ∀ i, 0 < κ i) (hle : ∀ i, κ i ≤ 1)
    (hne : ∀ i, κ i ≠ κ (i + 1))
    (hzero : κ 0 = 1) (hH : κ H = 1) (hH0 : H ≠ 0) : RealizesR2 κ := by
  obtain ⟨A⟩ := nonempty_regularFourAnchor_of_repeated_normalized_maximum
    hκ hle hne hzero hH hH0
  exact A.realizesR2 hκ

end Gluck.Discrete
