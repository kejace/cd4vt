/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Convexity

/-!
# Cyclic reindexing of Euclidean realizations

A realization is independent of the chosen first vertex and cyclic orientation.
This file proves both facts directly for every positive profile. Cyclic shifts
rotate all developed edge vectors by one common phase, while cyclic reversal
conjugates them up to a common phase. Positive turning then supplies simplicity
for each reindexed development.
-/

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

private theorem turningAngle_comp_add_one
    (κ ℓ : ZMod n → ℝ) (i : ZMod n) :
    turningAngle 0 (fun j ↦ κ (j + 1)) (fun j ↦ ℓ (j + 1)) i =
      turningAngle 0 κ ℓ (i + 1) := by
  simp only [turningAngle]
  congr 2
  rw [show i - 1 + 1 = i + 1 - 1 by ring_nf]

private theorem heading_succ
    (κ ℓ : ZMod n → ℝ) (j : ℕ) :
    heading κ ℓ (j + 1) =
      heading κ ℓ j + turningAngle 0 κ ℓ ((j + 1 : ℕ) : ZMod n) := by
  unfold heading
  rw [show j + 1 + 1 = (j + 1) + 1 by omega, Finset.sum_range_succ]

private theorem heading_comp_add_one
    (κ ℓ : ZMod n → ℝ) (j : ℕ) :
    heading (fun i ↦ κ (i + 1)) (fun i ↦ ℓ (i + 1)) j =
      heading κ ℓ (j + 1) - turningAngle 0 κ ℓ 0 := by
  induction j with
  | zero =>
      norm_num [heading, Finset.sum_range_succ,
        turningAngle_comp_add_one]
  | succ j ih =>
      rw [heading_succ, heading_succ, ih,
        turningAngle_comp_add_one]
      push_cast
      ring_nf

private theorem sum_range_add_one_eq_of_eq
    {M : Type*} [AddCommGroup M] (f : ℕ → M) (hperiod : f n = f 0) :
    (∑ j ∈ Finset.range n, f (j + 1)) =
      ∑ j ∈ Finset.range n, f j := by
  apply add_right_cancel (b := f 0)
  calc
    (∑ j ∈ Finset.range n, f (j + 1)) + f 0 =
        ∑ j ∈ Finset.range (n + 1), f j :=
      (Finset.sum_range_succ' f n).symm
    _ = (∑ j ∈ Finset.range n, f j) + f n :=
      Finset.sum_range_succ f n
    _ = (∑ j ∈ Finset.range n, f j) + f 0 := by rw [hperiod]

private theorem closureGap_comp_add_one
    [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hT : turningSum κ ℓ = 2 * Real.pi) :
    closureGap (fun i ↦ κ (i + 1)) (fun i ↦ ℓ (i + 1)) =
      Complex.exp
          (((-turningAngle 0 κ ℓ 0 : ℝ) : ℂ) * Complex.I) *
        closureGap κ ℓ := by
  let edge : ℕ → ℂ := fun j =>
    (ℓ (j : ZMod n) : ℂ) *
      Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)
  have hphase :
      Complex.exp ((heading κ ℓ n : ℂ) * Complex.I) =
        Complex.exp ((heading κ ℓ 0 : ℂ) * Complex.I) := by
    have hhead : heading κ ℓ n =
        heading κ ℓ 0 + 2 * Real.pi := by
      simpa using heading_add_n hT 0
    rw [hhead]
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have htwo :
        Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
      push_cast
      exact Complex.exp_two_pi_mul_I
    rw [htwo, mul_one]
  have hedge : edge n = edge 0 := by
    simp [edge, hphase]
  have hsum :
      (∑ j ∈ Finset.range n, edge (j + 1)) =
        ∑ j ∈ Finset.range n, edge j :=
    sum_range_add_one_eq_of_eq edge hedge
  unfold closureGap vertexR2
  calc
    (∑ j ∈ Finset.range n,
        ((fun i : ZMod n ↦ ℓ (i + 1)) (j : ZMod n) : ℂ) *
          Complex.exp
            ((heading (fun i ↦ κ (i + 1)) (fun i ↦ ℓ (i + 1)) j : ℂ) *
              Complex.I)) =
        ∑ j ∈ Finset.range n,
          Complex.exp
              (((-turningAngle 0 κ ℓ 0 : ℝ) : ℂ) * Complex.I) *
            edge (j + 1) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [heading_comp_add_one]
      simp only [edge]
      push_cast
      rw [sub_mul, Complex.exp_sub]
      rw [div_eq_mul_inv]
      rw [← Complex.exp_neg]
      ring_nf
    _ = Complex.exp
          (((-turningAngle 0 κ ℓ 0 : ℝ) : ℂ) * Complex.I) *
        (∑ j ∈ Finset.range n, edge (j + 1)) := by
      rw [Finset.mul_sum]
    _ = Complex.exp
          (((-turningAngle 0 κ ℓ 0 : ℝ) : ℂ) * Complex.I) *
        (∑ j ∈ Finset.range n, edge j) := by rw [hsum]

/-- Simultaneously shifting curvature and edge lengths by one cyclic label
preserves the total turning sum. -/
theorem turningSum_comp_add_one_eq [NeZero n] (κ ℓ : ZMod n → ℝ) :
    turningSum (fun i ↦ κ (i + 1)) (fun i ↦ ℓ (i + 1)) =
      turningSum κ ℓ := by
  unfold turningSum
  simp_rw [turningAngle_comp_add_one]
  exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
    _ _ (fun _ ↦ rfl)

/-- A one-label cyclic shift changes closure only by a common nonzero phase. -/
theorem closureGap_comp_add_one_eq [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hT : turningSum κ ℓ = 2 * Real.pi) :
    closureGap (fun i ↦ κ (i + 1)) (fun i ↦ ℓ (i + 1)) =
      Complex.exp
          (((-turningAngle 0 κ ℓ 0 : ℝ) : ℂ) * Complex.I) *
        closureGap κ ℓ :=
  closureGap_comp_add_one hT

/-- Shifting a positive Euclidean realization by one vertex preserves
realizability. -/
theorem realizesR2_comp_add_one [NeZero n] (hn : 3 ≤ n)
    {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) (h : RealizesR2 κ) :
    RealizesR2 (fun i ↦ κ (i + 1)) := by
  obtain ⟨ℓ, hMA, hE, hT, _hsimple⟩ := h
  let κ' : ZMod n → ℝ := fun i ↦ κ (i + 1)
  let ℓ' : ZMod n → ℝ := fun i ↦ ℓ (i + 1)
  have hMA' : ModerateArc 0 κ' ℓ' := by
    rw [moderateArc_zero_iff] at hMA ⊢
    intro i
    have hidx : i - 1 + 1 = i + 1 - 1 := by ring_nf
    simpa only [κ', ℓ', hidx] using hMA (i + 1)
  have hturn (i : ZMod n) :
      turningAngle 0 κ' ℓ' i = turningAngle 0 κ ℓ (i + 1) := by
    exact turningAngle_comp_add_one κ ℓ i
  have hT' : turningSum κ' ℓ' = 2 * Real.pi := by
    unfold turningSum
    simp_rw [hturn]
    rw [show (∑ i : ZMod n, turningAngle 0 κ ℓ (i + 1)) =
      turningSum κ ℓ by
        unfold turningSum
        exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
          _ _ (fun _ ↦ rfl)]
    exact hT
  have hE' : closureGap κ' ℓ' = 0 := by
    rw [closureGap_comp_add_one hT, hE, mul_zero]
  refine ⟨ℓ', hMA', hE', hT',
    isSimplePolygon_of_turningPositive hn hMA' ?_ hE' hT'⟩
  exact fun i ↦ hκ (i + 1)

/-- Cyclically shifting a positive Euclidean realization by a natural number
of vertices preserves realizability. -/
theorem realizesR2_comp_add_nat [NeZero n] (hn : 3 ≤ n)
    {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) (h : RealizesR2 κ)
    (a : ℕ) :
    RealizesR2 (fun i ↦ κ (i + (a : ZMod n))) := by
  induction a with
  | zero =>
      simpa using h
  | succ a ih =>
      have hshift := realizesR2_comp_add_one hn
        (κ := fun i ↦ κ (i + (a : ZMod n)))
        (fun i ↦ hκ (i + (a : ZMod n))) ih
      convert hshift using 1
      funext i
      congr 1
      push_cast
      ring_nf

/-- Cyclically reindexing a positive Euclidean realization preserves
realizability. -/
theorem realizesR2_comp_add [NeZero n] (hn : 3 ≤ n)
    {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) (h : RealizesR2 κ)
    (a : ZMod n) :
    RealizesR2 (fun i ↦ κ (i + a)) := by
  simpa [ZMod.natCast_zmod_val] using
    realizesR2_comp_add_nat hn hκ h a.val

/-- For a positive profile of length at least three, realizability is
independent of the chosen first cyclic vertex. -/
theorem realizesR2_comp_add_iff [NeZero n] (hn : 3 ≤ n)
    {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) (a : ZMod n) :
    RealizesR2 (fun i ↦ κ (i + a)) ↔ RealizesR2 κ := by
  constructor
  · intro h
    have hback := realizesR2_comp_add hn
      (κ := fun i ↦ κ (i + a)) (fun i ↦ hκ (i + a)) h (-a)
    convert hback using 1
    funext i
    congr 1
    ring_nf
  · intro h
    exact realizesR2_comp_add hn hκ h a

private theorem turningAngle_comp_neg
    (κ ℓ : ZMod n → ℝ) (i : ZMod n) :
    turningAngle 0 (fun j ↦ κ (-j)) (fun j ↦ ℓ (-j - 1)) i =
      turningAngle 0 κ ℓ (-i) := by
  simp only [turningAngle]
  rw [show -(i - 1) - 1 = -i by ring]
  exact add_comm _ _

private theorem moderateArc_comp_neg {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) :
    ModerateArc 0 (fun i ↦ κ (-i)) (fun i ↦ ℓ (-i - 1)) := by
  rw [moderateArc_zero_iff] at h ⊢
  intro i
  have hidx : -(i - 1) - 1 = -i := by ring
  refine ⟨(h (-i - 1)).1, ?_, ?_⟩
  · simpa only [hidx] using (h (-i)).2.2
  · exact (h (-i)).2.1

private theorem turningSum_comp_neg [NeZero n] (κ ℓ : ZMod n → ℝ) :
    turningSum (fun i ↦ κ (-i)) (fun i ↦ ℓ (-i - 1)) = turningSum κ ℓ := by
  unfold turningSum
  simp_rw [turningAngle_comp_neg]
  exact Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun _ ↦ rfl)

private lemma natCast_sub_one_sub {m : ℕ} [NeZero n] (hm : m ≤ n - 1) :
    ((n - 1 - m : ℕ) : ZMod n) = -1 - (m : ZMod n) := by
  have h1 : ((n - 1 - m : ℕ) : ZMod n) = ((n - 1 : ℕ) : ZMod n) - (m : ℕ) :=
    Nat.cast_sub hm
  have h2 : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have h : ((n - 1 : ℕ) : ZMod n) = (n : ZMod n) - ((1 : ℕ) : ZMod n) :=
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
    rw [h, Nat.cast_one, ZMod.natCast_self, zero_sub]
  rw [h1, h2]

private theorem heading_comp_neg [NeZero n] (κ ℓ : ZMod n → ℝ) {j : ℕ}
    (hj : j < n) :
    heading (fun i ↦ κ (-i)) (fun i ↦ ℓ (-i - 1)) j =
      turningAngle 0 κ ℓ 0 + turningSum κ ℓ - heading κ ℓ (n - 1 - j) := by
  let θ : ZMod n → ℝ := turningAngle 0 κ ℓ
  have htail :
      (∑ m ∈ Finset.range j, θ (-((m + 1 : ℕ) : ZMod n))) =
        ∑ m ∈ Finset.range j, θ ((n - j + m : ℕ) : ZMod n) := by
    rw [← Finset.sum_range_reflect
      (fun m ↦ θ ((n - j + m : ℕ) : ZMod n)) j]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [Finset.mem_range] at hm
    rw [show n - j + (j - 1 - m) = n - 1 - m by omega,
      natCast_sub_one_sub (by omega)]
    congr 1
    push_cast
    ring
  have htotal :
      (∑ m ∈ Finset.range n, θ (m : ZMod n)) = turningSum κ ℓ := by
    change (∑ m ∈ Finset.range n, θ (m : ZMod n)) = ∑ i : ZMod n, θ i
    simpa using sum_range_natCast_add θ 0
  have hsplit :
      (∑ m ∈ Finset.range n, θ (m : ZMod n)) =
        (∑ m ∈ Finset.range (n - j), θ (m : ZMod n)) +
          ∑ m ∈ Finset.range j, θ ((n - j + m : ℕ) : ZMod n) := by
    simpa only [show n - j + j = n by omega] using
      Finset.sum_range_add (fun m ↦ θ (m : ZMod n)) (n - j) j
  unfold heading
  rw [Finset.sum_range_succ']
  simp_rw [turningAngle_comp_neg]
  rw [show -((0 : ℕ) : ZMod n) = 0 by simp, htail,
    show n - 1 - j + 1 = n - j by omega, ← htotal, hsplit]
  ring

private theorem exp_two_pi_sub (a b : ℝ) :
    Complex.exp (((a + 2 * Real.pi - b : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((a : ℂ) * Complex.I) *
        (starRingEnd ℂ) (Complex.exp ((b : ℂ) * Complex.I)) := by
  rw [← Complex.exp_conj]
  have harg :
      (((a + 2 * Real.pi - b : ℝ) : ℂ) * Complex.I) =
        ((a : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I) +
          (starRingEnd ℂ) ((b : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private theorem reversed_edge_eq [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hT : turningSum κ ℓ = 2 * Real.pi) {j : ℕ} (hj : j < n) :
    (ℓ (-((n - 1 - j : ℕ) : ZMod n) - 1) : ℂ) *
        Complex.exp
          ((heading (fun i ↦ κ (-i)) (fun i ↦ ℓ (-i - 1)) (n - 1 - j) : ℂ) *
            Complex.I) =
      Complex.exp ((turningAngle 0 κ ℓ 0 : ℂ) * Complex.I) *
        (starRingEnd ℂ)
          ((ℓ (j : ZMod n) : ℂ) *
            Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)) := by
  have hidx : -((n - 1 - j : ℕ) : ZMod n) - 1 = (j : ZMod n) := by
    rw [natCast_sub_one_sub (by omega)]
    ring
  rw [hidx, heading_comp_neg κ ℓ (by omega), show n - 1 - (n - 1 - j) = j by omega, hT,
    exp_two_pi_sub, map_mul, Complex.conj_ofReal]
  ring

private theorem closureGap_comp_neg [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hT : turningSum κ ℓ = 2 * Real.pi) :
    closureGap (fun i ↦ κ (-i)) (fun i ↦ ℓ (-i - 1)) =
      Complex.exp ((turningAngle 0 κ ℓ 0 : ℂ) * Complex.I) *
        (starRingEnd ℂ) (closureGap κ ℓ) := by
  unfold closureGap vertexR2
  rw [← Finset.sum_range_reflect
    (fun j ↦
      ((fun i : ZMod n ↦ ℓ (-i - 1)) (j : ZMod n) : ℂ) *
        Complex.exp
          ((heading (fun i ↦ κ (-i)) (fun i ↦ ℓ (-i - 1)) j : ℂ) * Complex.I)) n]
  calc
    (∑ j ∈ Finset.range n,
        (ℓ (-((n - 1 - j : ℕ) : ZMod n) - 1) : ℂ) *
          Complex.exp
            ((heading (fun i ↦ κ (-i)) (fun i ↦ ℓ (-i - 1)) (n - 1 - j) : ℂ) *
              Complex.I)) =
        ∑ j ∈ Finset.range n,
          Complex.exp ((turningAngle 0 κ ℓ 0 : ℂ) * Complex.I) *
            (starRingEnd ℂ)
              ((ℓ (j : ZMod n) : ℂ) *
                Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)) := by
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      exact reversed_edge_eq hT (Finset.mem_range.1 hj)
    _ = Complex.exp ((turningAngle 0 κ ℓ 0 : ℂ) * Complex.I) *
        ∑ j ∈ Finset.range n,
          (starRingEnd ℂ)
            ((ℓ (j : ZMod n) : ℂ) *
              Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)) := by
      rw [Finset.mul_sum]
    _ = Complex.exp ((turningAngle 0 κ ℓ 0 : ℂ) * Complex.I) *
        (starRingEnd ℂ)
          (∑ j ∈ Finset.range n,
            (ℓ (j : ZMod n) : ℂ) *
              Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)) := by
      rw [map_sum]

/-- Reversing vertex order and the incident edge order preserves total
turning, including for weak compactified data. -/
theorem turningSum_comp_neg_eq [NeZero n] (κ ℓ : ZMod n → ℝ) :
    turningSum (fun i ↦ κ (-i)) (fun i ↦ ℓ (-i - 1)) =
      turningSum κ ℓ :=
  turningSum_comp_neg κ ℓ

/-- Reversing vertex order conjugates closure up to a common phase. -/
theorem closureGap_comp_neg_eq [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hT : turningSum κ ℓ = 2 * Real.pi) :
    closureGap (fun i ↦ κ (-i)) (fun i ↦ ℓ (-i - 1)) =
      Complex.exp ((turningAngle 0 κ ℓ 0 : ℂ) * Complex.I) *
        (starRingEnd ℂ) (closureGap κ ℓ) :=
  closureGap_comp_neg hT

/-- Reversing the cyclic order of a positive Euclidean realization preserves realizability. -/
theorem realizesR2_comp_neg [NeZero n] (hn : 3 ≤ n) {κ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (h : RealizesR2 κ) :
    RealizesR2 (fun i ↦ κ (-i)) := by
  obtain ⟨ℓ, hMA, hE, hT, _⟩ := h
  let κ' : ZMod n → ℝ := fun i ↦ κ (-i)
  let ℓ' : ZMod n → ℝ := fun i ↦ ℓ (-i - 1)
  have hMA' : ModerateArc 0 κ' ℓ' := moderateArc_comp_neg hMA
  have hT' : turningSum κ' ℓ' = 2 * Real.pi := by
    simpa only [κ', ℓ', turningSum_comp_neg] using hT
  have hE' : closureGap κ' ℓ' = 0 := by
    rw [show closureGap κ' ℓ' =
      closureGap (fun i ↦ κ (-i)) (fun i ↦ ℓ (-i - 1)) by rfl,
      closureGap_comp_neg hT, hE, map_zero, mul_zero]
  exact ⟨ℓ', hMA', hE', hT',
    isSimplePolygon_of_turningPositive hn hMA' (fun i ↦ hκ (-i)) hE' hT'⟩

/-- For a positive profile of length at least three, realizability is invariant under reversal. -/
theorem realizesR2_comp_neg_iff [NeZero n] (hn : 3 ≤ n) {κ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) :
    RealizesR2 (fun i ↦ κ (-i)) ↔ RealizesR2 κ := by
  constructor
  · intro h
    simpa using realizesR2_comp_neg hn (κ := fun i ↦ κ (-i)) (fun i ↦ hκ (-i)) h
  · exact realizesR2_comp_neg hn hκ

/-- A shifted cyclic reversal of a positive Euclidean realization preserves realizability. -/
theorem realizesR2_comp_sub_left [NeZero n] (hn : 3 ≤ n) {κ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (h : RealizesR2 κ) (a : ZMod n) :
    RealizesR2 (fun i ↦ κ (a - i)) := by
  have hshift := realizesR2_comp_add hn hκ h a
  have hreverse := realizesR2_comp_neg hn (κ := fun i ↦ κ (i + a))
    (fun i ↦ hκ (i + a)) hshift
  convert hreverse using 1
  funext i
  congr 1
  ring

/-- Realizability of a positive profile is invariant under every shifted cyclic reversal. -/
theorem realizesR2_comp_sub_left_iff [NeZero n] (hn : 3 ≤ n) {κ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (a : ZMod n) :
    RealizesR2 (fun i ↦ κ (a - i)) ↔ RealizesR2 κ := by
  constructor
  · intro h
    have hback := realizesR2_comp_sub_left hn (κ := fun i ↦ κ (a - i))
      (fun i ↦ hκ (a - i)) h a
    convert hback using 1
    funext i
    congr 1
    ring
  · intro h
    exact realizesR2_comp_sub_left hn hκ h a

end Gluck.Discrete
