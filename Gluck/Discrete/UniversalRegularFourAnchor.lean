import Gluck.Discrete.NegativeCornerAnchorSelection
import Gluck.Discrete.RepeatedMaximumAnchor
import Gluck.Discrete.RegularFourAnchorCyclic

/-!
# Regular four-edge anchors for every adjacent-unequal DFV word

Select a global maximum. A repeated maximum gives the equal-pure anchor.
Otherwise select the highest secondary peak and its actual mountain. A
nonnegative terminal flag on either leg gives the first-pair anchor; two
negative flags give the opposite-pure orthogonal anchor. Every branch
retains actual edge indices and actual derivative rank, and positive
scaling and cyclic/reversed transport restore the original profile.
-/

namespace Gluck.Discrete

open NativeOppositePure

/-- Restore the original curvature scale and original cyclic origin while
retaining the regular four-edge witness itself. -/
theorem nonempty_regularFourAnchor_of_normalizedAt
    {n : ℕ} {κ : ZMod n → ℝ} {q : ZMod n}
    (hκ : ∀ i, 0 < κ i)
    (hA : Nonempty (RegularFourAnchor (normalizedAt κ q))) :
    Nonempty (RegularFourAnchor κ) := by
  obtain ⟨A⟩ := hA
  have B := A.scale (hκ q)
  have B' : RegularFourAnchor (fun i => κ (i + q)) := by
    convert B using 1
    funext i
    dsimp only [Gluck.Discrete.normalizedAt]
    field_simp [(hκ q).ne']
  exact ⟨RegularFourAnchor.of_comp_add q hκ B'⟩

theorem HighestSecondaryPeak.nonempty_regularFourAnchor_of_forward_terminal
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {H : ZMod n}
    (hq : HighestSecondaryPeak κ H 0)
    (hκ : ∀ i, 0 < κ i) (hne : ∀ i, κ i ≠ κ (i + 1))
    (hzero : κ 0 = 1) (hH : 1 < κ H)
    (hflag : 0 ≤ firstPairFlag (κ 1) (κ (H - 1)) (κ H) (κ (-1))) :
    Nonempty (RegularFourAnchor κ) := by
  apply hq.nonempty_regularFourAnchor_of_rising_terminal hκ hne hzero hH
  simpa only [natPred_val_residue hq.ne_global.symm] using hflag

/-- A backward first-pair anchor is restored to the original orientation,
including its actual four-edge derivative witness. -/
theorem HighestSecondaryPeak.nonempty_regularFourAnchor_of_backward_terminal
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {H : ZMod n}
    (hq : HighestSecondaryPeak κ H 0)
    (hκ : ∀ i, 0 < κ i) (hne : ∀ i, κ i ≠ κ (i + 1))
    (hzero : κ 0 = 1) (hH : 1 < κ H)
    (hflag : 0 ≤ firstPairFlag (κ (-1)) (κ (H + 1)) (κ H) (κ 1)) :
    Nonempty (RegularFourAnchor κ) := by
  have hq' : HighestSecondaryPeak (fun i => κ (-i)) (-H) 0 := by
    simpa using hq.comp_neg
  apply (RegularFourAnchor.nonempty_comp_neg_iff hκ).mp
  apply hq'.nonempty_regularFourAnchor_of_forward_terminal (fun i => hκ (-i))
    (adjacent_ne_comp_neg hne) (by simpa using hzero) (by simpa using hH)
  simpa [neg_sub, add_comm] using hflag

/-- A selected highest secondary peak gives a regular actual anchor in
every flag branch, with no geometric producer or regularity premise. -/
theorem HighestSecondaryPeak.nonempty_regularFourAnchor
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {H q : ZMod n}
    (hq : HighestSecondaryPeak κ H q)
    (hκ : ∀ i, 0 < κ i) (hne : ∀ i, κ i ≠ κ (i + 1))
    (hglobal : ∀ i, i ≠ H → κ i < κ H) :
    Nonempty (RegularFourAnchor κ) := by
  let μ := Gluck.Discrete.normalizedAt κ q
  have hq' : HighestSecondaryPeak μ (H - q) 0 := hq.normalizedAt (hκ q)
  have hμ : ∀ i, 0 < μ i := normalizedAt_pos hκ q
  have hμne : ∀ i, μ i ≠ μ (i + 1) := normalizedAt_adjacent_ne hne (hκ q)
  have hzero : μ 0 = 1 := by simp [μ, Gluck.Discrete.normalizedAt, (hκ q).ne']
  have hH : 1 < μ (H - q) := by
    simpa [μ, Gluck.Discrete.normalizedAt] using (one_lt_div (hκ q)).mpr (hglobal q hq.ne_global)
  have hglobal' : ∀ i, i ≠ H - q → μ i < μ (H - q) := by
    intro i hi
    have hneq : i + q ≠ H := by
      intro he
      exact hi (eq_sub_iff_add_eq.mpr he)
    simpa [μ, Gluck.Discrete.normalizedAt] using
      div_lt_div_of_pos_right (hglobal (i + q) hneq) (hκ q)
  apply nonempty_regularFourAnchor_of_normalizedAt hκ (q := q)
  change Nonempty (RegularFourAnchor μ)
  by_cases hf : 0 ≤ firstPairFlag (μ 1) (μ ((H - q) - 1)) (μ (H - q)) (μ (-1))
  · exact hq'.nonempty_regularFourAnchor_of_forward_terminal hμ hμne hzero hH hf
  · by_cases hb : 0 ≤ firstPairFlag (μ (-1)) (μ ((H - q) + 1)) (μ (H - q)) (μ 1)
    · exact hq'.nonempty_regularFourAnchor_of_backward_terminal hμ hμne hzero hH hb
    · exact hq'.nonempty_regularFourAnchor_of_negative_terminals hμ hμne hzero hH
        hglobal' (lt_of_not_ge hf) (lt_of_not_ge hb)

/-- Any two occurrences of the global maximum in an adjacent-unequal word
give a regular actual anchor, before restoring any constant runs. -/
theorem nonempty_regularFourAnchor_of_repeated_global_maximum
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {H J : ZMod n}
    (hκ : ∀ i, 0 < κ i) (hne : ∀ i, κ i ≠ κ (i + 1))
    (hmax : ∀ i, κ i ≤ κ H) (hJ : κ J = κ H) (hJH : J ≠ H) :
    Nonempty (RegularFourAnchor κ) := by
  let μ := normalizedAt κ H
  have hμ : ∀ i, 0 < μ i := normalizedAt_pos hκ H
  have hle : ∀ i, μ i ≤ 1 := by
    intro i
    exact (div_le_one (hκ H)).mpr (hmax (i + H))
  have hμne : ∀ i, μ i ≠ μ (i + 1) := normalizedAt_adjacent_ne hne (hκ H)
  have hzero : μ 0 = 1 := by simp [μ, normalizedAt, (hκ H).ne']
  have hJ' : μ (J - H) = 1 := by simp [μ, normalizedAt, hJ, (hκ H).ne']
  apply nonempty_regularFourAnchor_of_normalizedAt hκ (q := H)
  exact nonempty_regularFourAnchor_of_repeated_normalized_maximum hμ hle hμne
    hzero hJ' (sub_ne_zero.mpr hJH)

/-- Unconditional actual regular-anchor production for every positive
adjacent-unequal strict-DFV profile of every size at least four. -/
theorem nonempty_regularFourAnchor_of_adjacent_unequal_dfv
    {n : ℕ} {κ : ZMod n → ℝ} {c : ℝ}
    (hn : 4 ≤ n) (hκ : ∀ i, 0 < κ i) (hdfv : DFV κ c)
    (hne : ∀ i, κ i ≠ κ (i + 1)) : Nonempty (RegularFourAnchor κ) := by
  classical
  let : NeZero n := ⟨by omega⟩
  obtain ⟨H, _, hmax⟩ := Finset.univ.exists_max_image κ
    (by simp : (Finset.univ : Finset (ZMod n)).Nonempty)
  have hmax' : ∀ i, κ i ≤ κ H := fun i => hmax i (Finset.mem_univ i)
  by_cases hrepeat : ∃ J, J ≠ H ∧ κ J = κ H
  · obtain ⟨J, hJH, hJ⟩ := hrepeat
    exact nonempty_regularFourAnchor_of_repeated_global_maximum hκ hne hmax' hJ hJH
  · have hglobal : ∀ i, i ≠ H → κ i < κ H := by
      intro i hi
      apply lt_of_le_of_ne (hmax' i)
      intro he
      exact hrepeat ⟨i, hi, he⟩
    obtain ⟨q, hq⟩ := exists_highestSecondaryPeak hdfv hne H
    exact hq.nonempty_regularFourAnchor hκ hne hglobal

end Gluck.Discrete
