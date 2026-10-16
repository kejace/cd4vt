/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.N6MonotoneResidue
public import Mathlib.Order.Interval.Set.Monotone

/-!+# Selecting the highest secondary curvature peak

The selection uses the original strict DFV witness. Above the selected
peak, all readings form one ordinary interval after rotating to that
peak, strictly increasing to the unique global maximum and strictly
decreasing afterward. All paths use actual consecutive cyclic indices.
This formalizes the order-theoretic one-mountain reduction; it does not
construct a geometric realization or assume a bound on the word length.
-/

@[expose] public section

namespace Gluck.Discrete

open Set

variable {n : ℕ} [NeZero n]

/-- A highest strict local maximum other than the marked global maximum. -/
structure HighestSecondaryPeak (κ : ZMod n → ℝ) (H q : ZMod n) : Prop where
  ne_global : q ≠ H
  is_peak : IsStrictLocalMax κ q
  maximal : ∀ i, i ≠ H → IsStrictLocalMax κ i → κ i ≤ κ q

/-- The secondary peak is selected from the actual finite cyclic word,
without requiring all nonadjacent readings to be distinct. -/
theorem exists_highestSecondaryPeak {κ : ZMod n → ℝ} {c : ℝ}
    (hdfv : DFV κ c) (hne : ∀ i, κ i ≠ κ (i + 1)) (H : ZMod n) :
    ∃ q, HighestSecondaryPeak κ H q := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := hdfv.exists_two_strictLocalMax hne
  let s := Finset.univ.filter (fun i : ZMod n => i ≠ H ∧ IsStrictLocalMax κ i)
  have hs : s.Nonempty := by
    by_cases hiH : i = H
    · exact ⟨j, by simp [s, hj, show j ≠ H by intro e; exact hij (hiH.trans e.symm)]⟩
    · exact ⟨i, by simp [s, hiH, hi]⟩
  obtain ⟨q, hq, hmax⟩ := s.exists_max_image κ hs
  have hqm : q ≠ H ∧ IsStrictLocalMax κ q := by simpa [s] using hq
  exact ⟨q, hqm.1, hqm.2, fun i hiH hi => hmax i (by simp [s, hiH, hi])⟩

omit [NeZero n] in
/-- No high reading except the global maximum can be a local maximum. -/
theorem HighestSecondaryPeak.not_isStrictLocalMax {κ : ZMod n → ℝ}
    {H q i : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hi : i ≠ H) (hhigh : κ q < κ i) : ¬ IsStrictLocalMax κ i := by
  intro hpeak
  exact (not_le_of_gt hhigh) (hq.maximal i hi hpeak)

omit [NeZero n] in
/-- Once a high path is increasing, its next actual edge remains increasing
until the global maximum is reached. -/
theorem HighestSecondaryPeak.forward_step {κ : ZMod n → ℝ}
    {H q i : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ j, κ j ≠ κ (j + 1)) (hi : i ≠ H)
    (hhigh : κ q < κ i) (hrise : κ (i - 1) < κ i) :
    κ i < κ (i + 1) := by
  by_contra h
  have hfall : κ (i + 1) < κ i := lt_of_le_of_ne (le_of_not_gt h) (hne i).symm
  exact hq.not_isStrictLocalMax hi hhigh ⟨hrise, hfall⟩

omit [NeZero n] in
/-- The same propagation in the opposite cyclic direction. -/
theorem HighestSecondaryPeak.backward_step {κ : ZMod n → ℝ}
    {H q i : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ j, κ j ≠ κ (j + 1)) (hi : i ≠ H)
    (hhigh : κ q < κ i) (hrise : κ (i + 1) < κ i) :
    κ i < κ (i - 1) := by
  by_contra h
  have hprev : κ (i - 1) ≠ κ i := by simpa using hne (i - 1)
  have hfall : κ (i - 1) < κ i := lt_of_le_of_ne (le_of_not_gt h) hprev
  exact hq.not_isStrictLocalMax hi hhigh ⟨hfall, hrise⟩

/-- An offset before the first representative of `H-i` has not reached H. -/
theorem cyclic_offset_ne_of_lt_distance {i H : ZMod n} {m : ℕ}
    (hm : m < (H - i).val) : i + (m : ZMod n) ≠ H := by
  intro h
  have hcast : (m : ZMod n) = H - i := by
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt (lt_trans hm (ZMod.val_lt _))] at hv
  omega

/-- The forward and backward paths terminate at the literal marked index. -/
theorem cyclic_distance_endpoints (i H : ZMod n) :
    i + ((H - i).val : ZMod n) = H ∧ i - ((i - H).val : ZMod n) = H := by
  simp only [ZMod.natCast_zmod_val]
  constructor <;> ring

/-- A local propagation rule produces a complete monotone path to the
marked maximum, with fewer than n actual cyclic edges. -/
theorem strictMonoOn_cyclicPath_of_rising {κ : ZMod n → ℝ}
    {level : ℝ} {i H : ZMod n}
    (hstep : ∀ j, j ≠ H → level < κ j → κ (j - 1) < κ j → κ j < κ (j + 1))
    (hhigh : level < κ i) (hrise : κ (i - 1) < κ i) :
    (∀ m ≤ (H - i).val, level < κ (i + (m : ZMod n))) ∧
      StrictMonoOn (fun m : ℕ => κ (i + (m : ZMod n))) (Iic (H - i).val) := by
  have hchain : ∀ m, m ≤ (H - i).val →
      level < κ (i + (m : ZMod n)) ∧
      κ (i + (m : ZMod n) - 1) < κ (i + (m : ZMod n)) := by
    intro m
    induction m with
    | zero => intro _; simpa using And.intro hhigh hrise
    | succ m ih =>
      intro hm
      have hm' : m < (H - i).val := by omega
      obtain ⟨hhighm, hrisem⟩ := ih (by omega)
      have hnext := hstep (i + (m : ZMod n))
        (cyclic_offset_ne_of_lt_distance hm') hhighm hrisem
      constructor
      · simpa [Nat.cast_add, add_assoc] using lt_trans hhighm hnext
      · simpa [Nat.cast_add, ← add_assoc] using hnext
  refine ⟨fun m hm => (hchain m hm).1, ?_⟩
  apply strictMonoOn_Iic_of_lt_succ
  intro m hm
  have hnext := hstep (i + (m : ZMod n))
    (cyclic_offset_ne_of_lt_distance hm) (hchain m hm.le).1 (hchain m hm.le).2
  simpa [Nat.cast_add, add_assoc] using hnext

/-- Every initially rising high leg runs strictly upward all the way to H. -/
theorem HighestSecondaryPeak.forward_ascent {κ : ZMod n → ℝ}
    {H q i : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ j, κ j ≠ κ (j + 1))
    (hhigh : κ q < κ i) (hrise : κ (i - 1) < κ i) :
    (∀ m ≤ (H - i).val, κ q < κ (i + (m : ZMod n))) ∧
      StrictMonoOn (fun m : ℕ => κ (i + (m : ZMod n))) (Iic (H - i).val) :=
  strictMonoOn_cyclicPath_of_rising (fun _ => hq.forward_step hne) hhigh hrise

/-- The reflected, literally consecutive high path has the same property. -/
theorem HighestSecondaryPeak.backward_ascent {κ : ZMod n → ℝ}
    {H q i : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ j, κ j ≠ κ (j + 1))
    (hhigh : κ q < κ i) (hrise : κ (i + 1) < κ i) :
    (∀ m ≤ (i - H).val, κ q < κ (i - (m : ZMod n))) ∧
      StrictMonoOn (fun m : ℕ => κ (i - (m : ZMod n))) (Iic (i - H).val) := by
  have hstep : ∀ j : ZMod n, j ≠ -H → κ q < κ (-j) →
      κ (-(j - 1)) < κ (-j) → κ (-j) < κ (-(j + 1)) := by
    intro j hj hh hr
    have hj' : -j ≠ H := by intro e; apply hj; simpa using congrArg Neg.neg e
    have hr' : κ (-j + 1) < κ (-j) := by simpa [neg_sub, sub_eq_add_neg, add_comm] using hr
    simpa [neg_add, sub_eq_add_neg, add_comm] using hq.backward_step hne hj' hh hr'
  have hp := strictMonoOn_cyclicPath_of_rising (κ := fun j : ZMod n => κ (-j))
    (i := -i) (H := -H) hstep (by simpa using hhigh)
      (by simpa [neg_sub, sub_eq_add_neg, add_comm] using hrise)
  simpa [neg_add, neg_sub, sub_eq_add_neg, add_comm] using hp

/-- A first outgoing rise also determines the entire high leg; no condition
on the other neighbor of its initial vertex is needed. -/
theorem strictMonoOn_cyclicPath_of_first_step {κ : ZMod n → ℝ}
    {level : ℝ} {i H : ZMod n}
    (hstep : ∀ j, j ≠ H → level < κ j → κ (j - 1) < κ j → κ j < κ (j + 1))
    (hhigh : level < κ i) (hrise : κ i < κ (i + 1)) :
    (∀ m ≤ (H - i).val, level < κ (i + (m : ZMod n))) ∧
      StrictMonoOn (fun m : ℕ => κ (i + (m : ZMod n))) (Iic (H - i).val) := by
  have hchain : ∀ m, m ≤ (H - i).val →
      level < κ (i + (m : ZMod n)) ∧
      (m < (H - i).val → κ (i + (m : ZMod n)) < κ (i + (m : ZMod n) + 1)) := by
    intro m
    induction m with
    | zero => intro _; simpa using And.intro hhigh (fun _ => hrise)
    | succ m ih =>
      intro hm
      have hm' : m < (H - i).val := by omega
      obtain ⟨hhighm, hrisem⟩ := ih hm'.le
      have hnext := hrisem hm'
      have hhigh' : level < κ (i + ((m + 1 : ℕ) : ZMod n)) := by
        simpa [Nat.cast_add, add_assoc] using lt_trans hhighm hnext
      refine ⟨hhigh', fun hm'' => ?_⟩
      apply hstep _ (cyclic_offset_ne_of_lt_distance hm'') hhigh'
      simpa [Nat.cast_add, ← add_assoc] using hnext
  refine ⟨fun m hm => (hchain m hm).1, ?_⟩
  apply strictMonoOn_Iic_of_lt_succ
  intro m hm
  simpa [Nat.cast_add, add_assoc] using (hchain m hm.le).2 hm

/-- Forward version with an outgoing first step. -/
theorem HighestSecondaryPeak.forward_ascent_of_first_step {κ : ZMod n → ℝ}
    {H q i : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ j, κ j ≠ κ (j + 1))
    (hhigh : κ q < κ i) (hrise : κ i < κ (i + 1)) :
    (∀ m ≤ (H - i).val, κ q < κ (i + (m : ZMod n))) ∧
      StrictMonoOn (fun m : ℕ => κ (i + (m : ZMod n))) (Iic (H - i).val) :=
  strictMonoOn_cyclicPath_of_first_step (fun _ => hq.forward_step hne) hhigh hrise

/-- Backward version with an outgoing first step. -/
theorem HighestSecondaryPeak.backward_ascent_of_first_step {κ : ZMod n → ℝ}
    {H q i : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ j, κ j ≠ κ (j + 1))
    (hhigh : κ q < κ i) (hrise : κ i < κ (i - 1)) :
    (∀ m ≤ (i - H).val, κ q < κ (i - (m : ZMod n))) ∧
      StrictMonoOn (fun m : ℕ => κ (i - (m : ZMod n))) (Iic (i - H).val) := by
  have hstep : ∀ j : ZMod n, j ≠ -H → κ q < κ (-j) →
      κ (-(j - 1)) < κ (-j) → κ (-j) < κ (-(j + 1)) := by
    intro j hj hh hr
    have hj' : -j ≠ H := by intro e; apply hj; simpa using congrArg Neg.neg e
    have hr' : κ (-j + 1) < κ (-j) := by simpa [neg_sub, sub_eq_add_neg, add_comm] using hr
    simpa [neg_add, sub_eq_add_neg, add_comm] using hq.backward_step hne hj' hh hr'
  have hp := strictMonoOn_cyclicPath_of_first_step (κ := fun j : ZMod n => κ (-j))
    (i := -i) (H := -H) hstep (by simpa using hhigh)
      (by simpa [neg_add, sub_eq_add_neg, add_comm] using hrise)
  simpa [neg_add, neg_sub, sub_eq_add_neg, add_comm] using hp

/-- Every high vertex reaches H monotonically in one of the two actual
cyclic directions. All intermediate readings stay strictly above the
selected secondary peak. Each displayed path has length less than n. -/
theorem HighestSecondaryPeak.high_path_to_global {κ : ZMod n → ℝ}
    {H q i : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ j, κ j ≠ κ (j + 1)) (hhigh : κ q < κ i) :
    ((∀ m ≤ (H - i).val, κ q < κ (i + (m : ZMod n))) ∧
      StrictMonoOn (fun m : ℕ => κ (i + (m : ZMod n))) (Iic (H - i).val)) ∨
    ((∀ m ≤ (i - H).val, κ q < κ (i - (m : ZMod n))) ∧
      StrictMonoOn (fun m : ℕ => κ (i - (m : ZMod n))) (Iic (i - H).val)) := by
  by_cases hi : i = H
  · subst i
    left
    constructor
    · simpa using hhigh
    · intro a ha b hb hab
      simp only [sub_self, ZMod.val_zero, mem_Iic] at ha hb
      omega
  · rcases lt_or_gt_of_ne (hne i) with hrise | hfall
    · exact Or.inl (hq.forward_ascent_of_first_step hne hhigh hrise)
    · have hrise : κ i < κ (i - 1) := hq.backward_step hne hi hhigh hfall
      exact Or.inr (hq.backward_ascent_of_first_step hne hhigh hrise)

/-- A high forward path cannot wrap past the selected low boundary q. Its
offsets in the word rotated to q therefore add as ordinary natural numbers. -/
theorem high_forward_path_offsets {κ : ZMod n → ℝ} {H q i : ZMod n}
    (hpath : ∀ m ≤ (H - i).val, κ q < κ (i + (m : ZMod n))) :
    (i - q).val + (H - i).val < n ∧
      (H - q).val = (i - q).val + (H - i).val := by
  have hi_lt := ZMod.val_lt (i - q)
  have hd_lt := ZMod.val_lt (H - i)
  have hsum : (i - q).val + (H - i).val < n := by
    by_contra h
    have hm : n - (i - q).val ≤ (H - i).val := by omega
    have heq : i + ((n - (i - q).val : ℕ) : ZMod n) = q := by
      rw [Nat.cast_sub hi_lt.le, ZMod.natCast_self, ZMod.natCast_zmod_val]
      ring
    have hh := hpath (n - (i - q).val) hm
    rw [heq] at hh
    exact lt_irrefl _ hh
  refine ⟨hsum, ?_⟩
  have hval := ZMod.val_add_of_lt hsum
  have heq : (i - q) + (H - i) = H - q := by ring
  rwa [heq] at hval

/-- The backward high path likewise cannot cross q. -/
theorem high_backward_path_offsets {κ : ZMod n → ℝ} {H q i : ZMod n}
    (hpath : ∀ m ≤ (i - H).val, κ q < κ (i - (m : ZMod n))) :
    (i - H).val < (i - q).val ∧
      (H - q).val = (i - q).val - (i - H).val := by
  have hlt : (i - H).val < (i - q).val := by
    by_contra h
    have hh := hpath (i - q).val (le_of_not_gt h)
    have heq : i - ((i - q).val : ZMod n) = q := by
      rw [ZMod.natCast_zmod_val]
      ring
    rw [heq] at hh
    exact lt_irrefl _ hh
  refine ⟨hlt, ?_⟩
  have hval := ZMod.val_sub hlt.le
  have heq : (i - q) - (i - H) = H - q := by ring
  rwa [heq] at hval

/-- In coordinates rotated to q, every interval between a high reading
and the global maximum consists entirely of high readings. -/
theorem HighestSecondaryPeak.high_interval_to_global {κ : ZMod n → ℝ}
    {H q i : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ j, κ j ≠ κ (j + 1)) (hhigh : κ q < κ i)
    {j : ℕ} (hjlo : min (i - q).val (H - q).val ≤ j)
    (hjhi : j ≤ max (i - q).val (H - q).val) :
    κ q < κ (q + (j : ZMod n)) := by
  rcases hq.high_path_to_global hne hhigh with ⟨hp, -⟩ | ⟨hp, -⟩
  · obtain ⟨-, hoff⟩ := high_forward_path_offsets hp
    have horder : (i - q).val ≤ (H - q).val := by omega
    rw [min_eq_left horder] at hjlo
    rw [max_eq_right horder] at hjhi
    have hm : j - (i - q).val ≤ (H - i).val := by omega
    have hh := hp (j - (i - q).val) hm
    have heq : i + ((j - (i - q).val : ℕ) : ZMod n) = q + (j : ZMod n) := by
      rw [Nat.cast_sub hjlo, ZMod.natCast_zmod_val]
      ring
    rwa [heq] at hh
  · obtain ⟨hd, hoff⟩ := high_backward_path_offsets hp
    have horder : (H - q).val ≤ (i - q).val := by omega
    rw [min_eq_right horder] at hjlo
    rw [max_eq_left horder] at hjhi
    have hm : (i - q).val - j ≤ (i - H).val := by omega
    have hh := hp ((i - q).val - j) hm
    have heq : i - (((i - q).val - j : ℕ) : ZMod n) = q + (j : ZMod n) := by
      rw [Nat.cast_sub hjhi, ZMod.natCast_zmod_val]
      ring
    rwa [heq] at hh

/-- The high set is an ordinary interval after rotating the marked q to
index zero. This includes all repeated nonadjacent readings. -/
theorem HighestSecondaryPeak.high_interval {κ : ZMod n → ℝ}
    {H q : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ i, κ i ≠ κ (i + 1)) {a b j : ℕ}
    (ha : a < n) (hb : b < n)
    (haHigh : κ q < κ (q + (a : ZMod n)))
    (hbHigh : κ q < κ (q + (b : ZMod n))) (haj : a ≤ j) (hjb : j ≤ b) :
    κ q < κ (q + (j : ZMod n)) := by
  have haoff : (q + (a : ZMod n) - q).val = a := by
    simpa using ZMod.val_natCast_of_lt ha
  have hboff : (q + (b : ZMod n) - q).val = b := by
    simpa using ZMod.val_natCast_of_lt hb
  rcases le_total j (H - q).val with hjH | hHj
  · apply hq.high_interval_to_global hne haHigh
    · rw [haoff]; exact (min_le_left _ _).trans haj
    · exact hjH.trans (le_max_right _ _)
  · apply hq.high_interval_to_global hne hbHigh
    · exact (min_le_right _ _).trans hHj
    · rw [hboff]; exact hjb.trans (le_max_left _ _)

/-- High readings before H increase strictly in ordinary rotated order. -/
theorem HighestSecondaryPeak.rising_lt {κ : ZMod n → ℝ}
    {H q : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ i, κ i ≠ κ (i + 1)) {a b : ℕ}
    (hab : a < b) (hbH : b ≤ (H - q).val)
    (haHigh : κ q < κ (q + (a : ZMod n))) :
    κ (q + (a : ZMod n)) < κ (q + (b : ZMod n)) := by
  have ha : a < n := lt_trans hab (lt_of_le_of_lt hbH (ZMod.val_lt _))
  have haoff : (q + (a : ZMod n) - q).val = a := by
    simpa using ZMod.val_natCast_of_lt ha
  rcases hq.high_path_to_global hne haHigh with ⟨hp, hm⟩ | ⟨hp, -⟩
  · have hoff := (high_forward_path_offsets hp).2
    rw [haoff] at hoff
    have hmd : b - a ≤ (H - (q + (a : ZMod n))).val := by omega
    have hh := hm (show 0 ∈ Iic (H - (q + (a : ZMod n))).val by simp)
      hmd (show 0 < b - a by omega)
    have heq : q + (a : ZMod n) + ((b - a : ℕ) : ZMod n) = q + (b : ZMod n) := by
      rw [Nat.cast_sub hab.le]
      ring
    simpa [heq] using hh
  · have hoff := (high_backward_path_offsets hp).2
    rw [haoff] at hoff
    omega

/-- High readings after H decrease strictly in ordinary rotated order. -/
theorem HighestSecondaryPeak.falling_lt {κ : ZMod n → ℝ}
    {H q : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ i, κ i ≠ κ (i + 1)) {a b : ℕ}
    (hHa : (H - q).val ≤ a) (hab : a < b) (hb : b < n)
    (hbHigh : κ q < κ (q + (b : ZMod n))) :
    κ (q + (b : ZMod n)) < κ (q + (a : ZMod n)) := by
  have hboff : (q + (b : ZMod n) - q).val = b := by
    simpa using ZMod.val_natCast_of_lt hb
  rcases hq.high_path_to_global hne hbHigh with ⟨hp, -⟩ | ⟨hp, hm⟩
  · have hoff := (high_forward_path_offsets hp).2
    rw [hboff] at hoff
    omega
  · obtain ⟨hd, hoff⟩ := high_backward_path_offsets hp
    rw [hboff] at hd hoff
    have hmd : b - a ≤ (q + (b : ZMod n) - H).val := by omega
    have hh := hm (show 0 ∈ Iic (q + (b : ZMod n) - H).val by simp)
      hmd (show 0 < b - a by omega)
    have heq : q + (b : ZMod n) - ((b - a : ℕ) : ZMod n) = q + (a : ZMod n) := by
      rw [Nat.cast_sub hab.le]
      ring
    simpa [heq] using hh

/-- The complete single-mountain shape, using natural offsets of actual
cyclic indices. Either monotone side may have length zero. -/
theorem HighestSecondaryPeak.exists_mountain {κ : ZMod n → ℝ}
    {H q : ZMod n} (hq : HighestSecondaryPeak κ H q)
    (hne : ∀ i, κ i ≠ κ (i + 1)) (hH : κ q < κ H) :
    ∃ a b : ℕ, 2 ≤ a ∧ a ≤ (H - q).val ∧ (H - q).val ≤ b ∧ b + 2 ≤ n ∧
      (∀ j < n, κ q < κ (q + (j : ZMod n)) ↔ a ≤ j ∧ j ≤ b) ∧
      StrictMonoOn (fun j : ℕ => κ (q + (j : ZMod n))) (Icc a (H - q).val) ∧
      StrictAntiOn (fun j : ℕ => κ (q + (j : ZMod n))) (Icc (H - q).val b) := by
  classical
  let s := (Finset.range n).filter (fun j : ℕ => κ q < κ (q + (j : ZMod n)))
  have hmem : ∀ j, j ∈ s ↔ j < n ∧ κ q < κ (q + (j : ZMod n)) := by
    intro j; simp [s]
  have hHmem : (H - q).val ∈ s := by
    rw [hmem]
    refine ⟨ZMod.val_lt _, ?_⟩
    simpa [ZMod.natCast_zmod_val] using hH
  have hs : s.Nonempty := ⟨_, hHmem⟩
  let a := s.min' hs
  let b := s.max' hs
  have ha := (hmem a).mp (s.min'_mem hs)
  have hb := (hmem b).mp (s.max'_mem hs)
  have haH : a ≤ (H - q).val := s.min'_le _ hHmem
  have hHb : (H - q).val ≤ b := s.le_max' _ hHmem
  have ha2 : 2 ≤ a := by
    by_contra h
    have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with ha0 | ha1
    · simpa [ha0] using ha.2
    · have hh : κ q < κ (q + 1) := by simpa [ha1] using ha.2
      exact (not_lt_of_gt hq.is_peak.2) hh
  have hb2 : b + 2 ≤ n := by
    by_contra h
    have hbn : b = n - 1 := by omega
    have hidx : q + (b : ZMod n) = q - 1 := by
      rw [hbn, Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
      simp [sub_eq_add_neg]
    have hh : κ q < κ (q - 1) := by simpa [hidx] using hb.2
    exact (not_lt_of_gt hq.is_peak.1) hh
  have hinterval : ∀ j < n, κ q < κ (q + (j : ZMod n)) ↔ a ≤ j ∧ j ≤ b := by
    intro j hj
    constructor
    · intro hh
      have hjmem := (hmem j).mpr ⟨hj, hh⟩
      exact ⟨s.min'_le _ hjmem, s.le_max' _ hjmem⟩
    · rintro ⟨haj, hjb⟩
      exact hq.high_interval hne ha.1 hb.1 ha.2 hb.2 haj hjb
  refine ⟨a, b, ha2, haH, hHb, hb2, hinterval, ?_, ?_⟩
  · intro i hi j hj hij
    rcases hi with ⟨hia, hiH⟩
    rcases hj with ⟨hja, hjH⟩
    apply hq.rising_lt hne hij hjH
    exact (hinterval i (by omega)).mpr ⟨hia, by omega⟩
  · intro i hi j hj hij
    rcases hi with ⟨hiH, hib⟩
    rcases hj with ⟨hjH, hjb⟩
    apply hq.falling_lt hne hiH hij (by omega)
    exact (hinterval j (by omega)).mpr ⟨by omega, hjb⟩

/-- Selection and path control from the original DFV data and a unique
global maximum. Positivity and any bound on the number of distinct values
are unnecessary for this combinatorial conclusion. -/
theorem exists_secondaryPeak_with_high_paths {κ : ZMod n → ℝ} {c : ℝ}
    (hdfv : DFV κ c) (hne : ∀ i, κ i ≠ κ (i + 1))
    (H : ZMod n) (hglobal : ∀ i, i ≠ H → κ i < κ H) :
    ∃ q, HighestSecondaryPeak κ H q ∧ κ q < κ H ∧
      ∀ i, κ q < κ i →
        ((∀ m ≤ (H - i).val, κ q < κ (i + (m : ZMod n))) ∧
          StrictMonoOn (fun m : ℕ => κ (i + (m : ZMod n))) (Iic (H - i).val)) ∨
        ((∀ m ≤ (i - H).val, κ q < κ (i - (m : ZMod n))) ∧
          StrictMonoOn (fun m : ℕ => κ (i - (m : ZMod n))) (Iic (i - H).val)) := by
  obtain ⟨q, hq⟩ := exists_highestSecondaryPeak hdfv hne H
  exact ⟨q, hq, hglobal q hq.ne_global, fun _ => hq.high_path_to_global hne⟩

/-- All-size one-mountain selection from the original window, adjacency
inequality, and uniqueness of the global maximum. The offsets a and b are
literal vertex indices after rotation; the complementary readings are at
most the selected peak, and both immediate neighbors of that peak are low. -/
theorem exists_secondaryPeak_mountain {κ : ZMod n → ℝ} {c : ℝ}
    (hdfv : DFV κ c) (hne : ∀ i, κ i ≠ κ (i + 1))
    (H : ZMod n) (hglobal : ∀ i, i ≠ H → κ i < κ H) :
    ∃ q : ZMod n, ∃ a b : ℕ, HighestSecondaryPeak κ H q ∧
      2 ≤ a ∧ a ≤ (H - q).val ∧ (H - q).val ≤ b ∧ b + 2 ≤ n ∧
      (∀ j < n, κ q < κ (q + (j : ZMod n)) ↔ a ≤ j ∧ j ≤ b) ∧
      StrictMonoOn (fun j : ℕ => κ (q + (j : ZMod n))) (Icc a (H - q).val) ∧
      StrictAntiOn (fun j : ℕ => κ (q + (j : ZMod n))) (Icc (H - q).val b) := by
  obtain ⟨q, hq⟩ := exists_highestSecondaryPeak hdfv hne H
  obtain ⟨a, b, hab⟩ := hq.exists_mountain hne (hglobal q hq.ne_global)
  exact ⟨q, a, b, hq, hab⟩

end Gluck.Discrete
