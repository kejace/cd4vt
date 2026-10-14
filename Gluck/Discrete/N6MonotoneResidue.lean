/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Converse
import Gluck.Discrete.MonotoneCuts
import Gluck.Discrete.N6CarrierSkeleton

/-!
# The ordinary nonzigzag residue at six vertices

This file connects the repository's actual `DFV` predicate to the finite
six-edge run classification.  If adjacent values are unequal, the plateau
extrema extracted from a DFV window collapse to strict extrema.  A nonzigzag
six-word consequently has exactly two strict local maxima, two strict local
minima, and two strict monotone-through vertices.

Together with `CyclicMonotoneRuns.six_run_length_classification` and the
nine-cell table in `N6CarrierSkeleton`, this isolates the remaining analytic
base case without asserting the still-missing carrier degree.
-/

namespace Gluck.Discrete

noncomputable section

local instance instDecidableStrictLocalMaxResidue {n : ℕ}
    (w : ZMod n → ℝ) (i : ZMod n) : Decidable (IsStrictLocalMax w i) :=
  Classical.propDecidable _

local instance instDecidableStrictLocalMinResidue {n : ℕ}
    (w : ZMod n → ℝ) (i : ZMod n) : Decidable (IsStrictLocalMin w i) :=
  Classical.propDecidable _

local instance instDecidableStrictExtremumResidue {n : ℕ}
    (w : ZMod n → ℝ) (i : ZMod n) : Decidable (IsStrictExtremum w i) :=
  Classical.propDecidable _

/-! ## Plateau collapse under adjacent inequality -/

/-- An adjacent-unequal word has no nontrivial plateau maximum run. -/
lemma PlateauMaxRun.eq_zero_of_ne_succ {n : ℕ} {f : ZMod n → ℝ}
    (hne : ∀ i, f i ≠ f (i + 1)) {a k : ℕ} (h : PlateauMaxRun f a k) :
    k = 0 := by
  by_contra hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hc := h.1 1 hk1
  rw [Nat.cast_add, Nat.cast_one] at hc
  exact hne (a : ZMod n) hc.symm

/-- An adjacent-unequal word has no nontrivial plateau minimum run. -/
lemma PlateauMinRun.eq_zero_of_ne_succ {n : ℕ} {f : ZMod n → ℝ}
    (hne : ∀ i, f i ≠ f (i + 1)) {a k : ℕ} (h : PlateauMinRun f a k) :
    k = 0 := by
  by_contra hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hc := h.1 1 hk1
  rw [Nat.cast_add, Nat.cast_one] at hc
  exact hne (a : ZMod n) hc.symm

/-- A plateau maximum of an adjacent-unequal word is a strict local maximum. -/
lemma PlateauMaxRun.isStrictLocalMax_of_ne_succ {n : ℕ} {f : ZMod n → ℝ}
    (hne : ∀ i, f i ≠ f (i + 1)) {a k : ℕ} (h : PlateauMaxRun f a k) :
    IsStrictLocalMax f (a : ZMod n) := by
  have hk := h.eq_zero_of_ne_succ hne
  subst k
  exact ⟨h.2.1, by simpa [Nat.cast_add] using h.2.2⟩

/-- A plateau minimum of an adjacent-unequal word is a strict local minimum. -/
lemma PlateauMinRun.isStrictLocalMin_of_ne_succ {n : ℕ} {f : ZMod n → ℝ}
    (hne : ∀ i, f i ≠ f (i + 1)) {a k : ℕ} (h : PlateauMinRun f a k) :
    IsStrictLocalMin f (a : ZMod n) := by
  have hk := h.eq_zero_of_ne_succ hne
  subst k
  exact ⟨h.2.1, by simpa [Nat.cast_add] using h.2.2⟩

/-! ## Strict extrema forced by a DFV window -/

/-- An adjacent-unequal DFV word has two distinct strict local maxima. -/
theorem DFV.exists_two_strictLocalMax {n : ℕ} {w : ZMod n → ℝ} {c : ℝ}
    (h : DFV w c) (hne : ∀ i, w i ≠ w (i + 1)) :
    ∃ i j, i ≠ j ∧ IsStrictLocalMax w i ∧ IsStrictLocalMax w j := by
  obtain ⟨a, k, b, l, _hk, _hl, ha, hb, hab⟩ := h.plateau_extrema.1
  have hk0 := ha.eq_zero_of_ne_succ hne
  have hl0 := hb.eq_zero_of_ne_succ hne
  subst k
  subst l
  refine ⟨(a : ZMod n), (b : ZMod n), ?_,
    ha.isStrictLocalMax_of_ne_succ hne, hb.isStrictLocalMax_of_ne_succ hne⟩
  simpa using hab 0 (by omega) 0 (by omega)

/-- An adjacent-unequal DFV word has two distinct strict local minima. -/
theorem DFV.exists_two_strictLocalMin {n : ℕ} {w : ZMod n → ℝ} {c : ℝ}
    (h : DFV w c) (hne : ∀ i, w i ≠ w (i + 1)) :
    ∃ i j, i ≠ j ∧ IsStrictLocalMin w i ∧ IsStrictLocalMin w j := by
  obtain ⟨a, k, b, l, _hk, _hl, ha, hb, hab⟩ := h.plateau_extrema.2
  have hk0 := ha.eq_zero_of_ne_succ hne
  have hl0 := hb.eq_zero_of_ne_succ hne
  subst k
  subst l
  refine ⟨(a : ZMod n), (b : ZMod n), ?_,
    ha.isStrictLocalMin_of_ne_succ hne, hb.isStrictLocalMin_of_ne_succ hne⟩
  simpa using hab 0 (by omega) 0 (by omega)

/-- The strict-local-maximum set of an adjacent-unequal DFV word has at
least two elements. -/
theorem DFV.two_le_card_localMax {n : ℕ} [NeZero n]
    {w : ZMod n → ℝ} {c : ℝ} (h : DFV w c)
    (hne : ∀ i, w i ≠ w (i + 1)) :
    2 ≤ (Finset.univ.filter (IsStrictLocalMax w)).card := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := h.exists_two_strictLocalMax hne
  rw [show 2 ≤ (Finset.univ.filter (IsStrictLocalMax w)).card ↔
    1 < (Finset.univ.filter (IsStrictLocalMax w)).card by omega]
  exact Finset.one_lt_card_iff.mpr ⟨i, j, by simp [hi], by simp [hj], hij⟩

/-- The strict-local-minimum set of an adjacent-unequal DFV word has at
least two elements. -/
theorem DFV.two_le_card_localMin {n : ℕ} [NeZero n]
    {w : ZMod n → ℝ} {c : ℝ} (h : DFV w c)
    (hne : ∀ i, w i ≠ w (i + 1)) :
    2 ≤ (Finset.univ.filter (IsStrictLocalMin w)).card := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := h.exists_two_strictLocalMin hne
  rw [show 2 ≤ (Finset.univ.filter (IsStrictLocalMin w)).card ↔
    1 < (Finset.univ.filter (IsStrictLocalMin w)).card by omega]
  exact Finset.one_lt_card_iff.mpr ⟨i, j, by simp [hi], by simp [hj], hij⟩

/-! ## The exact nonzigzag six-word count -/

/-- A vertex is strict monotone-through when the values on its two incident
edges are ordered in the same direction. -/
def IsStrictMonotoneThrough {n : ℕ} (w : ZMod n → ℝ) (i : ZMod n) : Prop :=
  (w (i - 1) < w i ∧ w i < w (i + 1)) ∨
    (w (i + 1) < w i ∧ w i < w (i - 1))

local instance instDecidableStrictMonotoneThrough {n : ℕ}
    (w : ZMod n → ℝ) (i : ZMod n) : Decidable (IsStrictMonotoneThrough w i) :=
  Classical.propDecidable _

/-- Under adjacent inequality, a vertex is not a strict extremum exactly when
it is strict monotone-through. -/
theorem not_isStrictExtremum_iff_isStrictMonotoneThrough {n : ℕ}
    {w : ZMod n → ℝ} (hne : ∀ i, w i ≠ w (i + 1)) (i : ZMod n) :
    ¬IsStrictExtremum w i ↔ IsStrictMonotoneThrough w i := by
  have hprevNe : w (i - 1) ≠ w i := by
    simpa only [sub_add_cancel] using hne (i - 1)
  have hnextNe := hne i
  constructor
  · intro hnone
    rcases lt_or_gt_of_ne hprevNe with hprev | hprev <;>
      rcases lt_or_gt_of_ne hnextNe with hnext | hnext
    · exact Or.inl ⟨hprev, hnext⟩
    · exact (hnone (Or.inl ⟨hprev, hnext⟩)).elim
    · exact (hnone (Or.inr ⟨hprev, hnext⟩)).elim
    · exact Or.inr ⟨hnext, hprev⟩
  · rintro (hup | hdown) (hmax | hmin)
    · exact (lt_asymm hup.2 hmax.2).elim
    · exact (lt_asymm hup.1 hmin.1).elim
    · exact (lt_asymm hdown.2 hmax.1).elim
    · exact (lt_asymm hdown.1 hmin.2).elim

/-- An adjacent-unequal strict-DFV six-word which is not fully zigzag has
exactly two strict maxima, two strict minima, and two monotone-through
vertices. -/
theorem DFV.n6_exact_extrema_counts {w : ZMod 6 → ℝ} {c : ℝ}
    (hdfv : DFV w c) (hne : ∀ i, w i ≠ w (i + 1))
    (hnzig : ¬StrictZigzag w) :
    (Finset.univ.filter (IsStrictLocalMax w)).card = 2 ∧
      (Finset.univ.filter (IsStrictLocalMin w)).card = 2 ∧
      (Finset.univ.filter (IsStrictMonotoneThrough w)).card = 2 := by
  classical
  let maxima := Finset.univ.filter (IsStrictLocalMax w)
  let minima := Finset.univ.filter (IsStrictLocalMin w)
  let extrema := Finset.univ.filter (IsStrictExtremum w)
  have htwo : 2 ≤ maxima.card := hdfv.two_le_card_localMax hne
  have heven := even_card_extrema w hne
  have hext_le : extrema.card ≤ 6 := by
    have hsub : extrema ⊆ Finset.univ := Finset.filter_subset _ _
    simpa [extrema] using Finset.card_le_card hsub
  have hmax_le : maxima.card ≤ 3 := by
    have hdouble : extrema.card = 2 * maxima.card := by
      simpa only [extrema, maxima] using heven.2
    omega
  have hmax_ne : maxima.card ≠ 3 := by
    intro hthree
    have hext_card : extrema.card = 6 := by
      have hdouble : extrema.card = 2 * maxima.card := by
        simpa only [extrema, maxima] using heven.2
      omega
    have hall : extrema = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      simpa [extrema] using hext_card.ge
    apply hnzig
    rw [strictZigzag_iff_forall_extremum]
    intro i
    have hi : i ∈ extrema := by rw [hall]; simp
    exact (Finset.mem_filter.mp hi).2
  have hmax : maxima.card = 2 := by omega
  have hmin : minima.card = 2 := by
    have hbalance : maxima.card = minima.card := by
      simpa only [maxima, minima] using card_localMax_eq_card_localMin w hne
    omega
  have hext : extrema.card = 4 := by
    have hdouble : extrema.card = 2 * maxima.card := by
      simpa only [extrema, maxima] using heven.2
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod 6))) (IsStrictExtremum w)
  have hsplit' : extrema.card +
      (Finset.univ.filter (fun i ↦ ¬IsStrictExtremum w i)).card = 6 := by
    simpa only [extrema, Finset.card_univ, ZMod.card] using hsplit
  have hthrough :
      Finset.univ.filter (IsStrictMonotoneThrough w) =
        Finset.univ.filter (fun i ↦ ¬IsStrictExtremum w i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (not_isStrictExtremum_iff_isStrictMonotoneThrough hne i).symm
  refine ⟨hmax, hmin, ?_⟩
  rw [hthrough]
  omega

/-! ## The extremal metric criterion -/

namespace CyclicMonotoneRuns

/-- A level strictly separates both lows from both highs of a two-high,
two-low six-edge run decomposition. -/
def N6ExtremaStraddle {w : ZMod 6 → ℝ}
    (R : CyclicMonotoneRuns (n := 6) (m := 2) w) (c : ℝ) : Prop :=
  w (R.low 0) < c ∧ w (R.low 1) < c ∧
    c < w (R.high 0) ∧ c < w (R.high 1)

/-- The metric separation of the two extremal lows and two extremal highs. -/
def N6ExtremaSeparated {w : ZMod 6 → ℝ}
    (R : CyclicMonotoneRuns (n := 6) (m := 2) w) : Prop :=
  max (w (R.low 0)) (w (R.low 1)) <
    min (w (R.high 0)) (w (R.high 1))

/-- The max-low/min-high inequality is exactly the existence of a common
strict separating level. -/
theorem exists_n6ExtremaStraddle_iff {w : ZMod 6 → ℝ}
    (R : CyclicMonotoneRuns (n := 6) (m := 2) w) :
    (∃ c, R.N6ExtremaStraddle c) ↔ R.N6ExtremaSeparated := by
  constructor
  · rintro ⟨c, hl0, hl1, hh0, hh1⟩
    unfold N6ExtremaSeparated
    simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · intro h
    unfold N6ExtremaSeparated at h
    let c := (max (w (R.low 0)) (w (R.low 1)) +
      min (w (R.high 0)) (w (R.high 1))) / 2
    have hcLow : max (w (R.low 0)) (w (R.low 1)) < c := by
      dsimp only [c]
      linarith
    have hcHigh : c < min (w (R.high 0)) (w (R.high 1)) := by
      dsimp only [c]
      linarith
    refine ⟨c, ?_⟩
    unfold N6ExtremaStraddle
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hcLow,
      lt_of_le_of_lt (le_max_right _ _) hcLow,
      lt_of_lt_of_le hcHigh (min_le_left _ _),
      lt_of_lt_of_le hcHigh (min_le_right _ _)⟩

/-- A common extremal separating level gives a four-crossing `DFV` witness.
The witness visits `high 0, low 0, high 1, low 1` along the four positive
runs. -/
theorem dfv_of_n6ExtremaStraddle {w : ZMod 6 → ℝ}
    (R : CyclicMonotoneRuns (n := 6) (m := 2) w) {c : ℝ}
    (h : R.N6ExtremaStraddle c) : DFV w c := by
  let a := (R.high 0).val
  let d0 := R.downLength 0
  let u0 := R.upLength 0
  let d1 := R.downLength 1
  let u1 := R.upLength 1
  have hsum : d0 + u0 + d1 + u1 = 6 := by
    have hs := R.edge_count
    rw [← sum_range_natCast_add
      (fun i : ZMod 2 ↦ R.downLength i + R.upLength i) 0] at hs
    norm_num [Finset.sum_range_succ] at hs ⊢
    dsimp only [d0, u0, d1, u1]
    omega
  have ha : ((a : ℕ) : ZMod 6) = R.high 0 :=
    ZMod.natCast_zmod_val (R.high 0)
  have hi2 : (((a + d0 : ℕ) : ZMod 6)) = R.low 0 := by
    push_cast
    rw [ha]
    exact R.down_end 0
  have hi3 : (((a + d0 + u0 : ℕ) : ZMod 6)) = R.high 1 := by
    push_cast
    rw [ha, R.down_end 0]
    simpa using R.up_end 0
  have hi4 : (((a + d0 + u0 + d1 : ℕ) : ZMod 6)) = R.low 1 := by
    push_cast
    rw [ha, R.down_end 0]
    have hu := R.up_end 0
    norm_num at hu
    rw [hu]
    exact R.down_end 1
  have hd0 : 0 < d0 := R.downLength_pos 0
  have hu0 : 0 < u0 := R.upLength_pos 0
  have hd1 : 0 < d1 := R.downLength_pos 1
  have hu1 : 0 < u1 := R.upLength_pos 1
  unfold DFV
  refine ⟨a, a + d0, a + d0 + u0, a + d0 + u0 + d1,
    by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [d0, u0, d1, u1] at hsum ⊢
    omega
  · rw [ha]
    exact h.2.2.1
  · rw [hi2]
    exact h.1
  · rw [hi3]
    exact h.2.2.2
  · rw [hi4]
    exact h.2.1

/-- The extremal max-low/min-high inequality therefore supplies a DFV level. -/
theorem exists_dfv_of_n6ExtremaSeparated {w : ZMod 6 → ℝ}
    (R : CyclicMonotoneRuns (n := 6) (m := 2) w)
    (h : R.N6ExtremaSeparated) : ∃ c, DFV w c := by
  rw [← R.exists_n6ExtremaStraddle_iff] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, R.dfv_of_n6ExtremaStraddle hc⟩

end CyclicMonotoneRuns

end

end Gluck.Discrete
