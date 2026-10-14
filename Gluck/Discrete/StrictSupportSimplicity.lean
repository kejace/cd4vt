/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.PolygonConvexity

/-!
# Polygon simplicity from strict edge support

The two segment-separation proofs are extracted from the private lemmas in
`Gluck/Forward/Discrete/Section4CircleSpliceSimple.lean` on `feat-forward`, commit
`a7ebc8ec01e77beefff2b38a4257e2f0ae09f3d5`. Their hypotheses do not require the
circle-splice construction. No original forward file is changed.
-/

namespace Gluck.Discrete

open Set

/-- A segment lying on an oriented line is disjoint from a segment whose two
endpoints lie strictly on the positive side of that line. -/
theorem segment_inter_eq_empty_of_crossR2_pos
    {A B C D : ℂ}
    (hC : 0 < crossR2 A B C) (hD : 0 < crossR2 A B D) :
    segment ℝ A B ∩ segment ℝ C D = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  rcases hz with ⟨hzAB, hzCD⟩
  rw [segment_eq_image_lineMap] at hzAB hzCD
  rcases hzAB with ⟨t, ht, rfl⟩
  rcases hzCD with ⟨s, hs, heq⟩
  have hzero : crossR2 A B (AffineMap.lineMap A B t) = 0 :=
    crossR2_lineMap_self A B t
  have hcross := congrArg (crossR2 A B) heq
  rw [crossR2_lineMap, hzero] at hcross
  have hweight : 0 ≤ 1 - s := by linarith [hs.2]
  by_cases hs0 : s = 0
  · subst s
    simp only [sub_zero, one_mul, zero_mul, add_zero] at hcross
    linarith
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hleft : 0 ≤ (1 - s) * crossR2 A B C :=
      mul_nonneg hweight hC.le
    have hright : 0 < s * crossR2 A B D := mul_pos hspos hD
    linarith

/-- Two consecutive noncollinear segments meet only at their common
endpoint. -/
theorem consecutive_segments_inter_eq_singleton_of_crossR2_pos
    {A B C : ℂ} (hcross : 0 < crossR2 A B C) :
    segment ℝ A B ∩ segment ℝ B C = {B} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩, ?_⟩
  rintro z ⟨hzAB, hzBC⟩
  rw [segment_eq_image_lineMap] at hzAB hzBC
  rcases hzAB with ⟨t, ht, rfl⟩
  rcases hzBC with ⟨s, hs, heq⟩
  have hzero : crossR2 A B (AffineMap.lineMap A B t) = 0 :=
    crossR2_lineMap_self A B t
  have hB : crossR2 A B B = 0 := by
    unfold crossR2
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hcrossEq := congrArg (crossR2 A B) heq
  rw [crossR2_lineMap, hB, mul_zero, zero_add, hzero] at hcrossEq
  have hs0 : s = 0 := by nlinarith [hs.1]
  simpa [hs0] using heq.symm


/-- Global strict edge support is sufficient for simplicity, without a prior
simplicity hypothesis or a prescribed circumradius law. -/
theorem isSimplePolygon_of_strictConvexEdgeSupport {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) {v : ZMod n → ℂ} (hsupport : StrictConvexEdgeSupport v) :
    IsSimplePolygon v := by
  have : Fact (1 < n) := ⟨by omega⟩
  have h₁ : (1 : ZMod n) ≠ 0 := one_ne_zero
  have h₂ : (2 : ZMod n) ≠ 0 := by
    intro h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 n).mp h)
    omega
  have hturn : ∀ i, 0 < crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    intro i
    apply hsupport
    · intro h
      apply h₂
      linear_combination h
    · intro h
      apply h₁
      linear_combination h
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h := hturn i
    simp [hi, crossR2] at h
  · intro i
    exact consecutive_segments_inter_eq_singleton_of_crossR2_pos (hturn i)
  · intro i j hij hisj hjsi
    apply segment_inter_eq_empty_of_crossR2_pos
    · exact hsupport i j hij.symm hisj.symm
    · exact hsupport i (j + 1) hjsi (by
        intro h
        exact hij (add_right_cancel h).symm)

end Gluck.Discrete
