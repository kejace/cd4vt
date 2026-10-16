/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.TangentChord

/-!
# Cyclic zigzag words

This file develops the order-theoretic part of the discrete zigzag argument.
It characterizes strictly zigzag cyclic words, extracts their extrema and
monotone runs, and supplies a uniform padding construction.  The general
geometric realization theorem is exposed through the explicit proposition
`ZigzagRealizes`; later files discharge its four-vertex case and develop the
general carrier branches.

-/

@[expose] public section

namespace Gluck.Discrete

noncomputable section

variable {n : ℕ}

/-! ## Strict extrema and zigzag words -/

/-- A strict local maximum of a cyclic real word. -/
def IsStrictLocalMax (w : ZMod n → ℝ) (i : ZMod n) : Prop :=
  w (i - 1) < w i ∧ w (i + 1) < w i

/-- A strict local minimum of a cyclic real word. -/
def IsStrictLocalMin (w : ZMod n → ℝ) (i : ZMod n) : Prop :=
  w i < w (i - 1) ∧ w i < w (i + 1)

/-- A strict local extremum of a cyclic real word. -/
def IsStrictExtremum (w : ZMod n → ℝ) (i : ZMod n) : Prop :=
  IsStrictLocalMax w i ∨ IsStrictLocalMin w i

local instance instDecidableIsStrictLocalMax (w : ZMod n → ℝ) (i : ZMod n) :
    Decidable (IsStrictLocalMax w i) := Classical.propDecidable _

local instance instDecidableIsStrictLocalMin (w : ZMod n → ℝ) (i : ZMod n) :
    Decidable (IsStrictLocalMin w i) := Classical.propDecidable _

local instance instDecidableIsStrictExtremum (w : ZMod n → ℝ) (i : ZMod n) :
    Decidable (IsStrictExtremum w i) := Classical.propDecidable _

/-- Consecutive first differences of a strictly zigzag word have opposite signs. -/
def StrictZigzag (w : ZMod n → ℝ) : Prop :=
  ∀ i, (w (i + 1) - w i) * (w (i + 2) - w (i + 1)) < 0

/-- A cyclic real word is strictly zigzag exactly when every vertex is a
strict local extremum. -/
theorem strictZigzag_iff_forall_extremum (w : ZMod n → ℝ) :
    StrictZigzag w ↔ ∀ i, IsStrictExtremum w i := by
  constructor
  · intro h i
    have hi := h (i - 1)
    have hidx₁ : i - 1 + 1 = i := by ring
    have hidx₂ : i - 1 + 2 = i + 1 := by ring
    rw [hidx₁, hidx₂] at hi
    rcases mul_neg_iff.mp hi with hmax | hmin
    · exact Or.inl ⟨sub_pos.mp hmax.1, sub_neg.mp hmax.2⟩
    · exact Or.inr ⟨sub_neg.mp hmin.1, sub_pos.mp hmin.2⟩
  · intro h i
    rcases h (i + 1) with hmax | hmin
    · apply mul_neg_iff.mpr
      left
      rw [IsStrictLocalMax] at hmax
      have hprev : i + 1 - 1 = i := by ring
      have hnext : i + 1 + 1 = i + 2 := by ring
      rw [hprev, hnext] at hmax
      constructor
      · exact sub_pos.mpr hmax.1
      · exact sub_neg.mpr hmax.2
    · apply mul_neg_iff.mpr
      right
      rw [IsStrictLocalMin] at hmin
      have hprev : i + 1 - 1 = i := by ring
      have hnext : i + 1 + 1 = i + 2 := by ring
      rw [hprev, hnext] at hmin
      constructor
      · exact sub_neg.mpr hmin.1
      · exact sub_pos.mpr hmin.2

/-- A strictly zigzag word has no repeated adjacent value. -/
lemma StrictZigzag.ne_succ {w : ZMod n → ℝ} (h : StrictZigzag w) (i : ZMod n) :
    w i ≠ w (i + 1) := by
  intro heq
  have hi := h i
  rw [heq] at hi
  simp at hi

/-- Pointwise inversion preserves the strictly zigzag class on positive words. -/
theorem strictZigzag_inv_iff {w : ZMod n → ℝ} (hpos : ∀ i, 0 < w i) :
    StrictZigzag w ↔ StrictZigzag (fun i ↦ (w i)⁻¹) := by
  have transfer : ∀ {u : ZMod n → ℝ}, (∀ i, 0 < u i) → StrictZigzag u →
      StrictZigzag (fun i ↦ (u i)⁻¹) := by
    intro u hu hz
    rw [strictZigzag_iff_forall_extremum] at hz ⊢
    intro i
    rcases hz i with hmax | hmin
    · right
      exact ⟨(inv_lt_inv₀ (hu i) (hu (i - 1))).2 hmax.1,
        (inv_lt_inv₀ (hu i) (hu (i + 1))).2 hmax.2⟩
    · left
      exact ⟨(inv_lt_inv₀ (hu (i - 1)) (hu i)).2 hmin.1,
        (inv_lt_inv₀ (hu (i + 1)) (hu i)).2 hmin.2⟩
  constructor
  · exact transfer hpos
  · intro h
    have hinvpos : ∀ i, 0 < (w i)⁻¹ := fun i ↦ inv_pos.mpr (hpos i)
    simpa only [inv_inv] using transfer hinvpos h

/-! ## Counting extrema -/

/-- The indicator of an ascending edge, valued in the integers so its cyclic
difference can be summed. -/
def ascentIndicator (w : ZMod n → ℝ) (i : ZMod n) : ℤ :=
  if w i < w (i + 1) then 1 else 0

/-- The change of the ascent indicator at a vertex is the indicator of a
strict minimum minus the indicator of a strict maximum. -/
private lemma ascentIndicator_sub_prev (w : ZMod n → ℝ)
    (hne : ∀ i, w i ≠ w (i + 1)) (i : ZMod n) :
    ascentIndicator w i - ascentIndicator w (i - 1) =
      (if IsStrictLocalMin w i then 1 else 0) -
        if IsStrictLocalMax w i then 1 else 0 := by
  classical
  have hprevne : w (i - 1) ≠ w i := by
    simpa only [sub_add_cancel] using hne (i - 1)
  by_cases hprev : w (i - 1) < w i
  · by_cases hnext : w i < w (i + 1)
    · have hmin : ¬IsStrictLocalMin w i := fun h ↦ (lt_asymm hprev h.1).elim
      have hmax : ¬IsStrictLocalMax w i := fun h ↦ (lt_asymm hnext h.2).elim
      simp [ascentIndicator, hprev, hnext, hmin, hmax]
    · have hnext' : w (i + 1) < w i :=
        lt_of_le_of_ne (le_of_not_gt hnext) (hne i).symm
      have hmin : ¬IsStrictLocalMin w i := fun h ↦ (lt_asymm hprev h.1).elim
      have hmax : IsStrictLocalMax w i := ⟨hprev, hnext'⟩
      simp [ascentIndicator, hprev, hnext, hmin, hmax]
  · have hprev' : w i < w (i - 1) :=
      lt_of_le_of_ne (le_of_not_gt hprev) hprevne.symm
    by_cases hnext : w i < w (i + 1)
    · have hmin : IsStrictLocalMin w i := ⟨hprev', hnext⟩
      have hmax : ¬IsStrictLocalMax w i := fun h ↦ (lt_asymm hprev' h.1).elim
      simp [ascentIndicator, hprev, hnext, hmin, hmax]
    · have hnext' : w (i + 1) < w i :=
        lt_of_le_of_ne (le_of_not_gt hnext) (hne i).symm
      have hmin : ¬IsStrictLocalMin w i := fun h ↦ (lt_asymm hnext' h.2).elim
      have hmax : ¬IsStrictLocalMax w i := fun h ↦ (lt_asymm hprev' h.1).elim
      simp [ascentIndicator, hprev, hnext, hmin, hmax]

/-- A nondegenerate cyclic word has equally many strict local maxima and
strict local minima. -/
theorem card_localMax_eq_card_localMin [NeZero n] (w : ZMod n → ℝ)
    (hne : ∀ i, w i ≠ w (i + 1)) :
    (Finset.univ.filter (IsStrictLocalMax w)).card =
      (Finset.univ.filter (IsStrictLocalMin w)).card := by
  classical
  have hshift :
      ∑ i : ZMod n, ascentIndicator w (i - 1) =
        ∑ i : ZMod n, ascentIndicator w i := by
    exact Fintype.sum_equiv (Equiv.subRight (1 : ZMod n)) _ _ (fun _ ↦ rfl)
  have htel :
      ∑ i : ZMod n, (ascentIndicator w i - ascentIndicator w (i - 1)) = 0 := by
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  have hcount :
      ∑ i : ZMod n,
          ((if IsStrictLocalMin w i then 1 else 0) -
            if IsStrictLocalMax w i then 1 else 0 : ℤ) = 0 := by
    calc
      _ = ∑ i : ZMod n,
          (ascentIndicator w i - ascentIndicator w (i - 1)) :=
        Finset.sum_congr rfl fun i _ ↦ (ascentIndicator_sub_prev w hne i).symm
      _ = 0 := htel
  have hcast :
      ((Finset.univ.filter (IsStrictLocalMin w)).card : ℤ) -
        ((Finset.univ.filter (IsStrictLocalMax w)).card : ℤ) = 0 := by
    simpa only [Finset.sum_sub_distrib, Finset.sum_boole] using hcount
  exact_mod_cast (sub_eq_zero.mp hcast).symm

/-- The strict extrema of a nondegenerate cyclic word have even cardinality;
their cardinality is twice its number of strict local maxima. -/
theorem even_card_extrema [NeZero n] (w : ZMod n → ℝ)
    (hne : ∀ i, w i ≠ w (i + 1)) :
    Even (Finset.univ.filter (IsStrictExtremum w)).card ∧
      (Finset.univ.filter (IsStrictExtremum w)).card =
        2 * (Finset.univ.filter (IsStrictLocalMax w)).card := by
  classical
  let maxima := Finset.univ.filter (IsStrictLocalMax w)
  let minima := Finset.univ.filter (IsStrictLocalMin w)
  let extrema := Finset.univ.filter (IsStrictExtremum w)
  have hunion : extrema = maxima ∪ minima := by
    ext i
    simp only [extrema, maxima, minima, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, IsStrictExtremum]
  have hdisjoint : Disjoint maxima minima := by
    refine Finset.disjoint_left.mpr fun i himax himin ↦ ?_
    have hmax : IsStrictLocalMax w i := (Finset.mem_filter.mp himax).2
    have hmin : IsStrictLocalMin w i := (Finset.mem_filter.mp himin).2
    exact (lt_asymm hmax.2 hmin.2).elim
  have hcard : extrema.card = maxima.card + minima.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisjoint]
  have hbalance : maxima.card = minima.card := card_localMax_eq_card_localMin w hne
  have hdouble : extrema.card = 2 * maxima.card := by omega
  constructor
  · exact ⟨maxima.card, by simpa only [extrema, maxima, two_mul] using hdouble⟩
  · simpa only [extrema, maxima] using hdouble

/-- A strictly zigzag cyclic word has even length. -/
theorem strictZigzag_even_length [NeZero n] {w : ZMod n → ℝ} (h : StrictZigzag w) :
    Even n := by
  classical
  have hall : Finset.univ.filter (IsStrictExtremum w) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _hi
    exact (strictZigzag_iff_forall_extremum w).mp h i
  have heven := (even_card_extrema w h.ne_succ).1
  simpa only [hall, Finset.card_univ, ZMod.card] using heven

/-! ## Monotone runs -/

/-- An ascending edge remains ascending through a run containing no strict
local maximum.  The second conclusion records the comparison with the start
of the run for immediate use by extremum extraction. -/
theorem ascending_run (w : ZMod n → ℝ) (hne : ∀ i, w i ≠ w (i + 1))
    {j : ZMod n} (hj : w j < w (j + 1)) (d : ℕ)
    (hno : ∀ t < d, ¬IsStrictLocalMax w (j + ((t + 1 : ℕ) : ZMod n))) :
    w (j + (d : ZMod n)) < w (j + ((d + 1 : ℕ) : ZMod n)) ∧
      w j < w (j + ((d + 1 : ℕ) : ZMod n)) := by
  induction d with
  | zero => simpa using And.intro hj hj
  | succ d ih =>
      have hno' : ∀ t < d, ¬IsStrictLocalMax w (j + ((t + 1 : ℕ) : ZMod n)) :=
        fun t ht ↦ hno t (Nat.lt_succ_of_lt ht)
      obtain ⟨hedge, hstart⟩ := ih hno'
      have hprevIndex :
          j + ((d + 1 : ℕ) : ZMod n) - 1 = j + (d : ZMod n) := by
        simp [Nat.cast_add]
        ring
      have hnextIndex :
          j + ((d + 1 : ℕ) : ZMod n) + 1 =
            j + ((d + 2 : ℕ) : ZMod n) := by
        simp [Nat.cast_add]
        ring
      have hnext :
          w (j + ((d + 1 : ℕ) : ZMod n)) <
            w (j + ((d + 2 : ℕ) : ZMod n)) := by
        by_contra hlt
        have hle :
            w (j + ((d + 2 : ℕ) : ZMod n)) ≤
              w (j + ((d + 1 : ℕ) : ZMod n)) := le_of_not_gt hlt
        have hstrict :
            w (j + ((d + 2 : ℕ) : ZMod n)) <
              w (j + ((d + 1 : ℕ) : ZMod n)) := by
          apply lt_of_le_of_ne hle
          have hne' := hne (j + ((d + 1 : ℕ) : ZMod n))
          exact fun heq ↦ hne' (by rw [hnextIndex]; exact heq.symm)
        apply hno d (Nat.lt_succ_self d)
        constructor
        · rw [hprevIndex]
          exact hedge
        · rw [hnextIndex]
          exact hstrict
      constructor
      · simpa only [Nat.cast_succ] using hnext
      · simpa only [Nat.cast_succ] using lt_trans hstart hnext

/-- A descending edge remains descending through a run containing no strict
local minimum. -/
theorem descending_run (w : ZMod n → ℝ) (hne : ∀ i, w i ≠ w (i + 1))
    {j : ZMod n} (hj : w (j + 1) < w j) (d : ℕ)
    (hno : ∀ t < d, ¬IsStrictLocalMin w (j + ((t + 1 : ℕ) : ZMod n))) :
    w (j + ((d + 1 : ℕ) : ZMod n)) < w (j + (d : ZMod n)) ∧
      w (j + ((d + 1 : ℕ) : ZMod n)) < w j := by
  induction d with
  | zero => simpa using And.intro hj hj
  | succ d ih =>
      have hno' : ∀ t < d, ¬IsStrictLocalMin w (j + ((t + 1 : ℕ) : ZMod n)) :=
        fun t ht ↦ hno t (Nat.lt_succ_of_lt ht)
      obtain ⟨hedge, hstart⟩ := ih hno'
      have hprevIndex :
          j + ((d + 1 : ℕ) : ZMod n) - 1 = j + (d : ZMod n) := by
        simp [Nat.cast_add]
        ring
      have hnextIndex :
          j + ((d + 1 : ℕ) : ZMod n) + 1 =
            j + ((d + 2 : ℕ) : ZMod n) := by
        simp [Nat.cast_add]
        ring
      have hnext :
          w (j + ((d + 2 : ℕ) : ZMod n)) <
            w (j + ((d + 1 : ℕ) : ZMod n)) := by
        by_contra hlt
        have hle :
            w (j + ((d + 1 : ℕ) : ZMod n)) ≤
              w (j + ((d + 2 : ℕ) : ZMod n)) := le_of_not_gt hlt
        have hstrict :
            w (j + ((d + 1 : ℕ) : ZMod n)) <
              w (j + ((d + 2 : ℕ) : ZMod n)) := by
          apply lt_of_le_of_ne hle
          have hne' := hne (j + ((d + 1 : ℕ) : ZMod n))
          exact fun heq ↦ hne' (by rw [hnextIndex]; exact heq)
        apply hno d (Nat.lt_succ_self d)
        constructor
        · rw [hprevIndex]
          exact hedge
        · rw [hnextIndex]
          exact hstrict
      constructor
      · simpa only [Nat.cast_succ] using hnext
      · simpa only [Nat.cast_succ] using lt_trans hnext hstart

/-- A strict local minimum lies below the first subsequent local maximum when
the intervening run contains no strict local maximum. -/
theorem min_lt_next_max (w : ZMod n → ℝ) (hne : ∀ i, w i ≠ w (i + 1))
    {j : ZMod n} (hj : IsStrictLocalMin w j) (d : ℕ)
    (hno : ∀ t < d, ¬IsStrictLocalMax w (j + ((t + 1 : ℕ) : ZMod n)))
    (_hmax : IsStrictLocalMax w (j + ((d + 1 : ℕ) : ZMod n))) :
    w j < w (j + ((d + 1 : ℕ) : ZMod n)) := by
  exact (ascending_run w hne hj.2 d hno).2

/-- A strict local minimum lies below the preceding local maximum, expressed
by traversing the descending run forward from that maximum. -/
theorem min_lt_prev_max (w : ZMod n → ℝ) (hne : ∀ i, w i ≠ w (i + 1))
    {i₀ : ZMod n} (hi₀ : IsStrictLocalMax w i₀) (d : ℕ)
    (hno : ∀ t < d, ¬IsStrictLocalMin w (i₀ + ((t + 1 : ℕ) : ZMod n)))
    (_hmin : IsStrictLocalMin w (i₀ + ((d + 1 : ℕ) : ZMod n))) :
    w (i₀ + ((d + 1 : ℕ) : ZMod n)) < w i₀ := by
  exact (descending_run w hne hi₀.2 d hno).2

/-! ## Alternating low sets -/

/-- If membership in a set alternates at every edge and its members lie below
both neighbours, the cyclic word is strictly zigzag. -/
theorem strictZigzag_of_alternatingLow (w : ZMod n → ℝ) (S : Set (ZMod n))
    (halt : ∀ i, i ∈ S ↔ i + 1 ∉ S)
    (hlow : ∀ i ∈ S, w i < w (i + 1) ∧ w i < w (i - 1)) :
    StrictZigzag w := by
  rw [strictZigzag_iff_forall_extremum]
  intro i
  by_cases hi : i ∈ S
  · exact Or.inr ⟨(hlow i hi).2, (hlow i hi).1⟩
  · left
    have hsucc : i + 1 ∈ S := by
      by_contra h
      exact hi ((halt i).2 h)
    have hprev : i - 1 ∈ S := by
      apply (halt (i - 1)).2
      simpa only [sub_add_cancel] using hi
    constructor
    · simpa only [sub_add_cancel] using (hlow (i - 1) hprev).1
    · simpa only [add_sub_cancel_right] using (hlow (i + 1) hsucc).2

/-! ## Uniform padding -/

/-- Uniformly interleave a cyclic word with the constant value `M`. -/
def padUniform {l : ℕ} [NeZero l] (v : ZMod l → ℝ) (M : ℝ) :
    ZMod (2 * l) → ℝ := fun k ↦
  if Even k.val then v ((k.val / 2 : ℕ) : ZMod l) else M

/-- Parity of the canonical representative flips under cyclic successor in
`ZMod (2 * l)`, including at the wraparound edge. -/
private lemma even_val_add_one_iff_not {l : ℕ} [NeZero l] (k : ZMod (2 * l)) :
    Even (k + 1).val ↔ ¬Even k.val := by
  have hl : 0 < l := Nat.pos_of_ne_zero (NeZero.ne l)
  have hmodne : 2 * l ≠ 1 := by omega
  rw [ZMod.val_add, ZMod.val_one'' hmodne,
    Even.mod_even_iff (even_two_mul l), Nat.even_add_one]

/-- The original word occurs at the even positions of its uniform padding. -/
theorem padUniform_apply_even {l : ℕ} [NeZero l] (v : ZMod l → ℝ) (M : ℝ)
    (j : ZMod l) :
    padUniform v M ((2 * j.val : ℕ) : ZMod (2 * l)) = v j := by
  have hjlt : j.val < l := j.val_lt
  have hlt : 2 * j.val < 2 * l := by omega
  have hdiv : 2 * j.val / 2 = j.val := by omega
  rw [padUniform, ZMod.val_natCast_of_lt hlt, if_pos (even_two_mul j.val), hdiv,
    ZMod.natCast_zmod_val]

/-- Uniform padding preserves positivity when both kinds of entries are positive. -/
theorem padUniform_pos {l : ℕ} [NeZero l] {v : ZMod l → ℝ} {M : ℝ}
    (hv : ∀ j, 0 < v j) (hM : 0 < M) (k : ZMod (2 * l)) :
    0 < padUniform v M k := by
  rw [padUniform]
  split_ifs
  · exact hv _
  · exact hM

/-- Uniform padding by a dominating value is strictly zigzag.  Its minima are
exactly the even positions and its maxima exactly the odd positions. -/
theorem strictZigzag_padUniform {l : ℕ} [NeZero l] {v : ZMod l → ℝ} {M : ℝ}
    (hM : ∀ j, v j < M) :
    StrictZigzag (padUniform v M) ∧
      (∀ k, IsStrictLocalMin (padUniform v M) k ↔ Even k.val) ∧
      ∀ k, IsStrictLocalMax (padUniform v M) k ↔ ¬Even k.val := by
  have hsucc_odd (k : ZMod (2 * l)) (hk : Even k.val) : ¬Even (k + 1).val := by
    by_contra h
    exact (even_val_add_one_iff_not k).mp h hk
  have hprev_odd (k : ZMod (2 * l)) (hk : Even k.val) : ¬Even (k - 1).val := by
    have hwrap : Even (k - 1 + 1).val := by simpa only [sub_add_cancel] using hk
    exact (even_val_add_one_iff_not (k - 1)).mp hwrap
  have hsucc_even (k : ZMod (2 * l)) (hk : ¬Even k.val) : Even (k + 1).val :=
    (even_val_add_one_iff_not k).mpr hk
  have hprev_even (k : ZMod (2 * l)) (hk : ¬Even k.val) : Even (k - 1).val := by
    by_contra h
    have := (even_val_add_one_iff_not (k - 1)).mpr h
    exact hk (by simpa only [sub_add_cancel] using this)
  have hmin_of_even (k : ZMod (2 * l)) (hk : Even k.val) :
      IsStrictLocalMin (padUniform v M) k := by
    constructor
    · simp only [padUniform, if_pos hk, if_neg (hprev_odd k hk)]
      exact hM _
    · simp only [padUniform, if_pos hk, if_neg (hsucc_odd k hk)]
      exact hM _
  have hmax_of_odd (k : ZMod (2 * l)) (hk : ¬Even k.val) :
      IsStrictLocalMax (padUniform v M) k := by
    constructor
    · simp only [padUniform, if_neg hk, if_pos (hprev_even k hk)]
      exact hM _
    · simp only [padUniform, if_neg hk, if_pos (hsucc_even k hk)]
      exact hM _
  have hzigzag : StrictZigzag (padUniform v M) := by
    apply strictZigzag_of_alternatingLow (padUniform v M)
      {k : ZMod (2 * l) | Even k.val}
    · intro k
      simpa only [Set.mem_setOf_eq, not_not] using
        (not_congr (even_val_add_one_iff_not k)).symm
    · intro k hk
      exact ⟨(hmin_of_even k hk).2, (hmin_of_even k hk).1⟩
  refine ⟨hzigzag, ?_, ?_⟩
  · intro k
    constructor
    · intro hmin
      by_contra hk
      have hmax := hmax_of_odd k hk
      exact (lt_asymm hmin.2 hmax.2).elim
    · exact hmin_of_even k
  · intro k
    constructor
    · intro hmax hk
      have hmin := hmin_of_even k hk
      exact (lt_asymm hmin.2 hmax.2).elim
    · exact hmax_of_odd k

/-! ## Conditional realization statements -/

/-- The analytic realization statement for positive strictly zigzag profiles.
This foundational file defines the target but does not prove it. -/
def ZigzagRealizes (n : ℕ) [NeZero n] : Prop :=
  ∀ κ : ZMod n → ℝ, (∀ i, 0 < κ i) → StrictZigzag κ → RealizesR2 κ

/-- **CD4VT' (conditional).** Assuming `ZigzagRealizes`, a positive strictly
zigzag profile is realized as signed Menger curvature and every prescribed
vertex is a strict curvature extremum. -/
theorem cd4vt_extremal_subprofile [NeZero n] (_hn : 4 ≤ n) {κ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (hzigzag : StrictZigzag κ) (hreal : ZigzagRealizes n) :
    RealizesMenger κ ∧ (∀ i, IsStrictExtremum κ i) ∧ Even n := by
  have hr2 : RealizesR2 κ := hreal κ hκ hzigzag
  exact ⟨realizesR2_realizesMenger hr2,
    (strictZigzag_iff_forall_extremum κ).mp hzigzag,
    strictZigzag_even_length hzigzag⟩

/-- **CD4VT''(W) (conditional).** Assuming `ZigzagRealizes`, any positive
cyclic word occurs at alternate vertices of the realization of its uniformly
padded profile.  The padding manufactures the extremum pattern; it does not
preserve the roles of extrema of the input word. -/
theorem cd4vt_values_only {l : ℕ} [NeZero l] (_hl : 2 ≤ l) {v : ZMod l → ℝ}
    {M : ℝ} (hv : ∀ j, 0 < v j) (hdom : ∀ j, v j < M)
    (hreal : ZigzagRealizes (2 * l)) :
    RealizesR2 (padUniform v M) ∧
      ∀ j, padUniform v M ((2 * j.val : ℕ) : ZMod (2 * l)) = v j := by
  have hMpos : 0 < M := lt_trans (hv 0) (hdom 0)
  have hpositive : ∀ k, 0 < padUniform v M k := padUniform_pos hv hMpos
  have hzigzag : StrictZigzag (padUniform v M) := (strictZigzag_padUniform hdom).1
  exact ⟨hreal (padUniform v M) hpositive hzigzag, padUniform_apply_even v M⟩

end

end Gluck.Discrete
