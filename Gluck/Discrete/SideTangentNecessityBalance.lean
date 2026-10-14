import Gluck.Discrete.SideTangentSignBlocks
import Gluck.Discrete.SideTangentChordSeparation

/-!
# Affine balance forces four cyclic sign changes

A nonzero signed affine dependence among the cyclic vertices of a strictly
convex polygon has at least four sign changes. The proof retains zero
coefficients and separates the two possible sign blocks by a chord.
-/

open scoped BigOperators

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- Zero mass and zero first moment annihilate every affine chord functional. -/
lemma sum_mul_cross_eq_zero [NeZero n] {c : ZMod n → ℝ} {Y : ZMod n → ℂ}
    (hsum : ∑ i, c i = 0) (hbalance : ∑ i, c i • Y i = 0) (A B : ℂ) :
    ∑ i, c i * crossR2 A B (Y i) = 0 := by
  have hre : ∑ i, c i * (Y i).re = 0 := by
    simpa using congrArg Complex.re hbalance
  have him : ∑ i, c i * (Y i).im = 0 := by
    simpa using congrArg Complex.im hbalance
  calc
    ∑ i, c i * crossR2 A B (Y i) =
        ∑ i, ((B - A).re * (c i * (Y i).im) - (B - A).im * (c i * (Y i).re) -
          ((B - A).re * A.im - (B - A).im * A.re) * c i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [crossR2, Complex.sub_re, Complex.sub_im]
      ring
    _ = 0 := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hre, him, hsum, mul_zero, sub_self]

/-- Different labels of a strictly supported polygon have different vertices. -/
lemma vertex_ne_of_strictSupport [NeZero n] (hn : 3 ≤ n) {Y : ZMod n → ℂ}
    (hY : StrictConvexEdgeSupport Y) {a b : ZMod n} (hab : a ≠ b) : Y a ≠ Y b := by
  by_cases hb : b = a + 1
  · rw [hb]
    exact (isSimplePolygon_of_strictConvexEdgeSupport hn hY).1 a
  · exact (pairwise_ne_of_crossR2_ne_zero (hY a b hab.symm hb).ne').2.2.symm

/-- A chord separates the two weak sign blocks, with a strict chord sign away from its endpoints. -/
lemma sign_block_chord_classification [NeZero n] {c : ZMod n → ℝ} {Y : ZMod n → ℂ}
    (hY : StrictConvexEdgeSupport Y) {a b : ℕ} (hab : a < b) (hba : b < a + n)
    (hneg : ∀ k, a < k → k < b → c (k : ZMod n) ≤ 0)
    (hpos : ∀ k, b < k → k < a + n → 0 ≤ c (k : ZMod n)) (j : ZMod n) :
    j = (a : ZMod n) ∨ j = (b : ZMod n) ∨
      (c j ≤ 0 ∧ crossR2 (Y (a : ZMod n)) (Y (b : ZMod n)) (Y j) < 0) ∨
      (0 ≤ c j ∧ 0 < crossR2 (Y (a : ZMod n)) (Y (b : ZMod n)) (Y j)) := by
  let k := a + (j - (a : ZMod n)).val
  have hka : a ≤ k := Nat.le_add_right _ _
  have hkn : k < a + n := Nat.add_lt_add_left (ZMod.val_lt _) a
  have hkj : (k : ZMod n) = j := by
    simp only [k, Nat.cast_add, ZMod.natCast_zmod_val]
    ring
  by_cases hka' : k = a
  · exact Or.inl (hkj.symm.trans (congrArg (fun x : ℕ ↦ (x : ZMod n)) hka'))
  have hak : a < k := lt_of_le_of_ne hka (Ne.symm hka')
  rcases lt_trichotomy k b with hkb | hkb | hbk
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    refine ⟨by simpa only [hkj] using hneg k hak hkb, ?_⟩
    have hcross := crossR2_lifted_triple_pos hY hak hkb hba
    rw [hkj] at hcross
    rw [crossR2_swap]
    exact neg_neg_of_pos hcross
  · exact Or.inr (Or.inl (hkj.symm.trans (congrArg (fun x : ℕ ↦ (x : ZMod n)) hkb)))
  · apply Or.inr ∘ Or.inr ∘ Or.inr
    exact ⟨by simpa only [hkj] using hpos k hbk hkn,
      by simpa only [hkj] using crossR2_lifted_triple_pos hY hab hbk hkn⟩

/-- A nonzero affine dependence of a strictly convex cyclic polygon has four sign changes. -/
theorem zero_or_dfv_of_strict_affine_balance [NeZero n] (hn : 3 ≤ n)
    {c : ZMod n → ℝ} {Y : ZMod n → ℂ} (hY : StrictConvexEdgeSupport Y)
    (hsum : ∑ i, c i = 0) (hbalance : ∑ i, c i • Y i = 0) :
    (∀ i, c i = 0) ∨ DFV c 0 := by
  classical
  by_cases hzero : ∀ i, c i = 0
  · exact Or.inl hzero
  apply Or.inr
  by_contra hdfv
  have hpos : ∃ i, 0 < c i := by
    by_contra h
    have hnonpos : ∀ i, c i ≤ 0 := fun i ↦ le_of_not_gt (fun hi ↦ h ⟨i, hi⟩)
    exact hzero (fun i ↦ congrFun ((Fintype.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum) i)
  have hneg : ∃ i, c i < 0 := by
    by_contra h
    have hnonneg : ∀ i, 0 ≤ c i := fun i ↦ le_of_not_gt (fun hi ↦ h ⟨i, hi⟩)
    exact hzero (fun i ↦ congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum) i)
  obtain ⟨a, b, hab, hba, ha, hb, hnegative, hpositive⟩ :=
    exists_sign_blocks_of_not_dfv hpos hneg hdfv
  let F : ZMod n → ℝ := fun i ↦ crossR2 (Y (a : ZMod n)) (Y (b : ZMod n)) (Y i)
  have hclass := sign_block_chord_classification hY hab hba hnegative hpositive
  have hprod : ∀ i, 0 ≤ c i * F i := by
    intro i
    rcases hclass i with hi | hi | ⟨hc, hf⟩ | ⟨hc, hf⟩
    · simp [F, hi, crossR2, mul_comm]
    · simp [F, hi, crossR2, mul_comm]
    · exact mul_nonneg_of_nonpos_of_nonpos hc hf.le
    · exact mul_nonneg hc hf.le
  have hprodzero : ∀ i, c i * F i = 0 := fun i ↦ congrFun
    ((Fintype.sum_eq_zero_iff_of_nonneg hprod).mp
      (sum_mul_cross_eq_zero hsum hbalance (Y (a : ZMod n)) (Y (b : ZMod n)))) i
  have hsupp : ∀ i, i ≠ (a : ZMod n) → i ≠ (b : ZMod n) → c i = 0 := by
    intro i hia hib
    rcases hclass i with hi | hi | ⟨_, hf⟩ | ⟨_, hf⟩
    · exact (hia hi).elim
    · exact (hib hi).elim
    · exact (mul_eq_zero.mp (hprodzero i)).resolve_right hf.ne
    · exact (mul_eq_zero.mp (hprodzero i)).resolve_right hf.ne'
  have hcenter : ∑ i, c i • (Y i - Y (b : ZMod n)) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum,
      zero_smul, sub_zero, hbalance]
  have hsingle : ∑ i, c i • (Y i - Y (b : ZMod n)) =
      c (a : ZMod n) • (Y (a : ZMod n) - Y (b : ZMod n)) := by
    apply Finset.sum_eq_single (a : ZMod n)
    · intro i hi hia
      by_cases hib : i = (b : ZMod n)
      · simp only [hib, sub_self, smul_zero]
      · rw [hsupp i hia hib, zero_smul]
    · simp
  rw [hsingle] at hcenter
  have habcast : (a : ZMod n) ≠ (b : ZMod n) := by
    intro heq
    rw [heq] at ha
    linarith
  exact (smul_ne_zero ha.ne (sub_ne_zero.mpr (vertex_ne_of_strictSupport hn hY habcast)))
    hcenter

end Gluck.Discrete.SideTangent
