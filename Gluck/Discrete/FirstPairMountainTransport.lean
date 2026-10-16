module

public import Gluck.Discrete.FirstPairMountainSelector
public import Gluck.Discrete.CyclicReindex
public import Gluck.Discrete.RealizesR2Scale

/-!
# Both mountain legs and transport to the original profile

Reflection, cyclic shift, and positive normalization preserve the selected
secondary peak. A nonnegative terminal flag on either side realizes the
original profile. Hence the remaining unique-maximum branch has two
strictly negative normalized terminal flags, without choosing or assuming
a geometric anchor.
-/

@[expose] public section

namespace Gluck.Discrete

open NativeOppositePure

variable {n : ℕ}

/-- Adjacent inequality is preserved by reversing the cyclic word. -/
theorem adjacent_ne_comp_neg {κ : ZMod n → ℝ}
    (hne : ∀ i, κ i ≠ κ (i + 1)) :
    ∀ i, κ (-i) ≠ κ (-(i + 1)) := by
  intro i
  simpa [neg_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using (hne (-i - 1)).symm

/-- Reversing the word reverses the labels but preserves the selected peak. -/
theorem HighestSecondaryPeak.comp_neg {κ : ZMod n → ℝ} {H q : ZMod n}
    (hq : HighestSecondaryPeak κ H q) :
    HighestSecondaryPeak (fun i => κ (-i)) (-H) (-q) := by
  refine ⟨fun h => hq.ne_global (neg_injective h), ?_, ?_⟩
  · constructor
    · simpa [neg_sub, add_comm] using hq.is_peak.2
    · simpa [neg_add, sub_eq_add_neg, add_comm] using hq.is_peak.1
  · intro i hi hpeak
    have hi' : -i ≠ H := by intro e; apply hi; simpa using congrArg Neg.neg e
    have hpeak' : IsStrictLocalMax κ (-i) := by
      constructor
      · simpa [neg_add, sub_eq_add_neg, add_comm] using hpeak.2
      · simpa [neg_sub, sub_eq_add_neg, add_comm] using hpeak.1
    simpa using hq.maximal (-i) hi' hpeak'

/-- Translation of all cyclic labels preserves the selected peak. -/
theorem HighestSecondaryPeak.comp_add {κ : ZMod n → ℝ} {H q : ZMod n}
    (hq : HighestSecondaryPeak κ H q) (a : ZMod n) :
    HighestSecondaryPeak (fun i => κ (i + a)) (H - a) (q - a) := by
  refine ⟨fun h => hq.ne_global (by simpa using congrArg (fun x => x + a) h), ?_, ?_⟩
  · constructor
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hq.is_peak.1
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hq.is_peak.2
  · intro i hi hpeak
    have hi' : i + a ≠ H := by intro e; apply hi; exact eq_sub_iff_add_eq.mpr e
    have hpeak' : IsStrictLocalMax κ (i + a) := by
      constructor
      · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hpeak.1
      · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hpeak.2
    simpa using hq.maximal (i + a) hi' hpeak'

/-- Positive scalar normalization preserves all strict peak comparisons. -/
theorem HighestSecondaryPeak.div_pos {κ : ZMod n → ℝ} {H q : ZMod n}
    (hq : HighestSecondaryPeak κ H q) {s : ℝ} (hs : 0 < s) :
    HighestSecondaryPeak (fun i => κ i / s) H q := by
  refine ⟨hq.ne_global, ?_, ?_⟩
  · exact ⟨div_lt_div_of_pos_right hq.is_peak.1 hs,
      div_lt_div_of_pos_right hq.is_peak.2 hs⟩
  · intro i hi hpeak
    have hpeak' : IsStrictLocalMax κ i :=
      ⟨(div_lt_div_iff_of_pos_right hs).mp hpeak.1,
        (div_lt_div_iff_of_pos_right hs).mp hpeak.2⟩
    exact div_le_div_of_nonneg_right (hq.maximal i hi hpeak') hs.le

/-- Natural predecessor representatives agree with actual cyclic neighbors
away from the chosen index zero. -/
theorem natPred_val_residue [NeZero n] {j : ZMod n} (hj : j ≠ 0) :
    ((j.val - 1 : ℕ) : ZMod n) = j - 1 := by
  have hv : 1 ≤ j.val := by
    have : j.val ≠ 0 := (ZMod.val_eq_zero j).not.mpr hj
    omega
  rw [Nat.cast_sub hv, ZMod.natCast_zmod_val, Nat.cast_one]

/-- The forward terminal is expressed using the actual predecessor of H. -/
theorem HighestSecondaryPeak.realizesR2_of_forward_terminal [NeZero n]
    {κ : ZMod n → ℝ} {H : ZMod n} (hq : HighestSecondaryPeak κ H 0)
    (hκ : ∀ j, 0 < κ j) (hne : ∀ j, κ j ≠ κ (j + 1))
    (hzero : κ 0 = 1) (hH : 1 < κ H)
    (hterminal : 0 ≤ firstPairFlag (κ 1) (κ (H - 1)) (κ H) (κ (-1))) :
    RealizesR2 κ := by
  apply hq.realizesR2_of_rising_terminal hκ hne hzero hH
  simpa only [natPred_val_residue hq.ne_global.symm] using hterminal

/-- The reflected rising leg realizes the same original cyclic profile. -/
theorem HighestSecondaryPeak.realizesR2_of_backward_terminal [NeZero n]
    (hn : 3 ≤ n) {κ : ZMod n → ℝ} {H : ZMod n}
    (hq : HighestSecondaryPeak κ H 0)
    (hκ : ∀ j, 0 < κ j) (hne : ∀ j, κ j ≠ κ (j + 1))
    (hzero : κ 0 = 1) (hH : 1 < κ H)
    (hterminal : 0 ≤ firstPairFlag (κ (-1)) (κ (H + 1)) (κ H) (κ 1)) :
    RealizesR2 κ := by
  have hq' : HighestSecondaryPeak (fun i => κ (-i)) (-H) 0 := by
    simpa using hq.comp_neg
  apply (realizesR2_comp_neg_iff hn hκ).mp
  apply hq'.realizesR2_of_forward_terminal (fun i => hκ (-i))
    (adjacent_ne_comp_neg hne) (by simpa using hzero) (by simpa using hH)
  simpa [neg_sub, add_comm] using hterminal

/-- Coordinates centered at the selected actual peak and normalized by
its positive curvature. -/
noncomputable def normalizedAt (κ : ZMod n → ℝ) (q : ZMod n) (i : ZMod n) : ℝ :=
  κ (i + q) / κ q

theorem HighestSecondaryPeak.normalizedAt {κ : ZMod n → ℝ} {H q : ZMod n}
    (hq : HighestSecondaryPeak κ H q) (hpos : 0 < κ q) :
    HighestSecondaryPeak (normalizedAt κ q) (H - q) 0 := by
  change HighestSecondaryPeak (fun i => κ (i + q) / κ q) (H - q) 0
  simpa only [sub_self] using (hq.comp_add q).div_pos hpos

theorem normalizedAt_pos {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) (q : ZMod n) :
    ∀ i, 0 < normalizedAt κ q i := fun i => div_pos (hκ (i + q)) (hκ q)

theorem normalizedAt_adjacent_ne {κ : ZMod n → ℝ}
    (hne : ∀ i, κ i ≠ κ (i + 1)) {q : ZMod n} (hpos : 0 < κ q) :
    ∀ i, normalizedAt κ q i ≠ normalizedAt κ q (i + 1) := by
  intro i hh
  have heq := (div_left_inj' hpos.ne').mp hh
  apply hne (i + q)
  simpa [add_assoc, add_comm, add_left_comm] using heq

/-- Restore both the original scale and the original cyclic origin. -/
theorem realizesR2_of_normalizedAt [NeZero n] (hn : 3 ≤ n)
    {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) {q : ZMod n}
    (hreal : RealizesR2 (normalizedAt κ q)) : RealizesR2 κ := by
  have hscaled := realizesR2_scale_of_pos hn (hκ q) (normalizedAt_pos hκ q) hreal
  have hshift : RealizesR2 (fun i => κ (i + q)) := by
    convert hscaled using 1
    funext i
    simp [normalizedAt, mul_div_cancel₀, (hκ q).ne']
  exact (realizesR2_comp_add_iff hn hκ q).mp hshift

/-- A forward nonnegative terminal flag at any selected peak realizes the
original, unnormalized cyclic word. -/
theorem HighestSecondaryPeak.realizesR2_of_normalized_forward_terminal [NeZero n]
    (hn : 3 ≤ n) {κ : ZMod n → ℝ} {H q : ZMod n}
    (hq : HighestSecondaryPeak κ H q)
    (hκ : ∀ i, 0 < κ i) (hne : ∀ i, κ i ≠ κ (i + 1)) (hH : κ q < κ H)
    (hterminal : 0 ≤ firstPairFlag (κ (q + 1) / κ q) (κ (H - 1) / κ q)
      (κ H / κ q) (κ (q - 1) / κ q)) : RealizesR2 κ := by
  have hq' := hq.normalizedAt (hκ q)
  apply realizesR2_of_normalizedAt hn hκ (q := q)
  apply hq'.realizesR2_of_forward_terminal (normalizedAt_pos hκ q)
    (normalizedAt_adjacent_ne hne (hκ q))
  · simp [Gluck.Discrete.normalizedAt, (hκ q).ne']
  · simpa [Gluck.Discrete.normalizedAt] using (one_lt_div (hκ q)).mpr hH
  · simpa [Gluck.Discrete.normalizedAt, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      using hterminal

/-- The same unnormalized conclusion from the terminal on the other side. -/
theorem HighestSecondaryPeak.realizesR2_of_normalized_backward_terminal [NeZero n]
    (hn : 3 ≤ n) {κ : ZMod n → ℝ} {H q : ZMod n}
    (hq : HighestSecondaryPeak κ H q)
    (hκ : ∀ i, 0 < κ i) (hne : ∀ i, κ i ≠ κ (i + 1)) (hH : κ q < κ H)
    (hterminal : 0 ≤ firstPairFlag (κ (q - 1) / κ q) (κ (H + 1) / κ q)
      (κ H / κ q) (κ (q + 1) / κ q)) : RealizesR2 κ := by
  have hq' := hq.normalizedAt (hκ q)
  apply realizesR2_of_normalizedAt hn hκ (q := q)
  apply hq'.realizesR2_of_backward_terminal hn (normalizedAt_pos hκ q)
    (normalizedAt_adjacent_ne hne (hκ q))
  · simp [Gluck.Discrete.normalizedAt, (hκ q).ne']
  · simpa [Gluck.Discrete.normalizedAt] using (one_lt_div (hκ q)).mpr hH
  · simpa [Gluck.Discrete.normalizedAt, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      using hterminal

/-- The original DFV unique-maximum case is either realized already, or
has a produced highest secondary peak with two strictly negative terminal
flags. No root, retained frame, or geometric regularity is assumed. -/
theorem exists_secondaryPeak_realizes_or_negativeTerminals [NeZero n]
    (hn : 3 ≤ n) {κ : ZMod n → ℝ} {c : ℝ}
    (hκ : ∀ i, 0 < κ i) (hdfv : DFV κ c) (hne : ∀ i, κ i ≠ κ (i + 1))
    (H : ZMod n) (hglobal : ∀ i, i ≠ H → κ i < κ H) :
    ∃ q, HighestSecondaryPeak κ H q ∧
      (RealizesR2 κ ∨
        firstPairFlag (κ (q + 1) / κ q) (κ (H - 1) / κ q)
          (κ H / κ q) (κ (q - 1) / κ q) < 0 ∧
        firstPairFlag (κ (q - 1) / κ q) (κ (H + 1) / κ q)
          (κ H / κ q) (κ (q + 1) / κ q) < 0) := by
  obtain ⟨q, hq⟩ := exists_highestSecondaryPeak hdfv hne H
  refine ⟨q, hq, ?_⟩
  have hH := hglobal q hq.ne_global
  by_cases hf : 0 ≤ firstPairFlag (κ (q + 1) / κ q) (κ (H - 1) / κ q)
      (κ H / κ q) (κ (q - 1) / κ q)
  · exact Or.inl (hq.realizesR2_of_normalized_forward_terminal hn hκ hne hH hf)
  · by_cases hb : 0 ≤ firstPairFlag (κ (q - 1) / κ q) (κ (H + 1) / κ q)
        (κ H / κ q) (κ (q + 1) / κ q)
    · exact Or.inl (hq.realizesR2_of_normalized_backward_terminal hn hκ hne hH hb)
    · exact Or.inr ⟨lt_of_not_ge hf, lt_of_not_ge hb⟩

end Gluck.Discrete
