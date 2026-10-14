import Gluck.Discrete.NativeIncidentAcuteRank
import Gluck.Discrete.FirstPairAnchorSelection
import Gluck.Discrete.FirstPairMountainTransport

/-!
# Actual four-edge selection at two negative terminal flags

The selected edges are the literal incident edges of the secondary peak
and the unique global maximum. The native producer supplies physical
closure and actual derivative rank, and its data are retained for later
constant-run restoration.
-/

namespace Gluck.Discrete

open NativeOppositePure FourActiveSlots

theorem FourActiveSlots.Frame.nonempty_regularFourAnchor_of_negative_corners
    {n : ℕ} (F : Frame n) {κ : ZMod n → ℝ} {p t q h l : ℝ}
    (hstart : F.start κ = ![1, t, q, l])
    (hfinish : F.finish κ = ![p, q, h, 1])
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hh : 0 < h) (hhq : h < q) (hq : 1 < q)
    (hflag : firstPairFlag p t q l < 0)
    (hreflected : firstPairFlag l h q p < 0) : Nonempty (RegularFourAnchor κ) := by
  obtain ⟨L, hphysical, hzero, hregular⟩ :=
    exists_nativeLength_regular_of_negative_corners
      hp hp1 hl hl1 ht htq hh hhq hq hflag hreflected
  exact ⟨RegularFourAnchor.ofNative F hstart hfinish hphysical hzero hregular⟩

/-- Select the four actual incident edges from the full DFV mountain data.
All intervening readings remain in the original profile. -/
theorem HighestSecondaryPeak.nonempty_regularFourAnchor_of_negative_terminals
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {H : ZMod n}
    (hq : HighestSecondaryPeak κ H 0)
    (hκ : ∀ i, 0 < κ i) (hne : ∀ i, κ i ≠ κ (i + 1))
    (hzero : κ 0 = 1) (hH : 1 < κ H)
    (hglobal : ∀ i, i ≠ H → κ i < κ H)
    (hforward : firstPairFlag (κ 1) (κ (H - 1)) (κ H) (κ (-1)) < 0)
    (hbackward : firstPairFlag (κ (-1)) (κ (H + 1)) (κ H) (κ 1) < 0) :
    Nonempty (RegularFourAnchor κ) := by
  obtain ⟨a, b, ha, hak, hkb, hbn, _, _, _⟩ :=
    hq.exists_mountain hne (by simpa only [hzero] using hH)
  simp only [sub_zero] at hak hkb
  have hlo : 2 ≤ H.val := by omega
  have hhi : H.val + 2 ≤ n := by omega
  let : Fact (1 < n) := ⟨by omega⟩
  let F := firstPairFrame hlo hhi
  have hp : κ 1 < 1 := by simpa [hzero] using hq.is_peak.2
  have hl : κ (-1) < 1 := by simpa [hzero] using hq.is_peak.1
  have ht : κ (H - 1) < κ H := hglobal _ (by simp)
  have hh : κ (H + 1) < κ H := hglobal _ (by simp)
  have hpred := natPred_val_residue hq.ne_global.symm
  have hlast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    simp
  have hstart : F.start κ = ![1, κ (H - 1), κ H, κ (-1)] := by
    simpa [F, hpred, hlast] using firstPairFrame_start hlo hhi κ hzero
  have hfinish : F.finish κ = ![κ 1, κ H, κ (H + 1), 1] := by
    simpa [F] using firstPairFrame_finish hlo hhi κ hzero
  exact F.nonempty_regularFourAnchor_of_negative_corners hstart hfinish
    (hκ 1) hp (hκ (-1)) hl (hκ (H - 1)) ht (hκ (H + 1)) hh hH hforward hbackward

end Gluck.Discrete
