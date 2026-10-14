/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleEdgeSupport
import Gluck.Forward.Discrete.Section4CircleArc

/-!
# Simplicity of the Section 4 circle splice

The retained edges form a contiguous subchain of the original simple polygon.
Every remaining edge is a sufficiently short chord of the completion circle;
strict support by that chord separates it from every nonadjacent splice edge.
-/

namespace Gluck.Forward

open Gluck.Discrete
open Set

/-- A segment lying on an oriented line is disjoint from a segment whose two
endpoints lie strictly on the positive side of that line. -/
private theorem segment_inter_eq_empty_of_crossR2_pos
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
private theorem consecutive_segments_inter_eq_singleton_of_crossR2_pos
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

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- Every splice edge is either one of the retained original-chain edges or
one of the oriented completion-circle mesh edges. -/
theorem circleSplice_edge_chain_or_meshIndex
    (q : ℕ) (i : ZMod (run.spliceVertexCount q)) :
    (∃ t : ℕ, t < run.chainLength - 1 ∧
      i = (t : ZMod (run.spliceVertexCount q))) ∨
    (∃ j : ℕ, j ≤ q ∧ i = run.circleSpliceMeshIndex q j) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  by_cases hchain : i.val < run.chainLength - 1
  · left
    exact ⟨i.val, hchain, (ZMod.natCast_zmod_val i).symm⟩
  · right
    by_cases hlast : i.val = run.chainLength - 1
    · refine ⟨0, by omega, ?_⟩
      simp only [circleSpliceMeshIndex, if_pos]
      exact (ZMod.natCast_zmod_val i).symm.trans
        (congrArg (fun t : ℕ ↦ (t : ZMod (run.spliceVertexCount q))) hlast)
    · let j : ℕ := i.val - run.chainLength + 1
      have hlenle : run.chainLength ≤ i.val := by omega
      have hjpos : 0 < j := by dsimp [j]; omega
      have hival := ZMod.val_lt i
      have hvaleq : run.chainLength + (i.val - run.chainLength) = i.val :=
        Nat.add_sub_of_le hlenle
      have hdiff : i.val - run.chainLength < q := by
        apply Nat.add_lt_add_iff_left.mp
        rw [hvaleq]
        simpa only [spliceVertexCount] using hival
      have hjq : j ≤ q := by
        dsimp [j]
        omega
      refine ⟨j, hjq, ?_⟩
      have hjzero : j ≠ 0 := by omega
      have hjlast : j ≠ q + 1 := by omega
      rw [circleSpliceMeshIndex, if_neg hjzero, if_neg hjlast]
      calc
        i = (i.val : ZMod (run.spliceVertexCount q)) :=
          (ZMod.natCast_zmod_val i).symm
        _ = (run.chainLength + (j - 1) : ℕ) := by
          congr 1
          dsimp [j]
          omega

private theorem chainStart_add_lt_n {t : ℕ}
    (ht : t < run.chainLength - 1) : run.chainStart + t < n := by
  have ha := run.a_pos
  have hab := run.a_le_b
  have hb := run.b_lt
  simp only [chainStart, chainLength] at ht ⊢
  omega

private theorem chainStart_add_succ_le_n {t : ℕ}
    (ht : t < run.chainLength - 1) : run.chainStart + t + 1 ≤ n := by
  have ha := run.a_pos
  have hab := run.a_le_b
  have hb := run.b_lt
  simp only [chainStart, chainLength] at ht ⊢
  omega

private theorem cyclicLift_chain_succ_simple (t : ℕ) :
    Gluck.cyclicLift run.c (run.chainStart + t) + 1 =
      Gluck.cyclicLift run.c (run.chainStart + t + 1) := by
  simp [Gluck.cyclicLift, Nat.cast_add, add_assoc]

/-- Distinct natural starts of retained edges remain distinct cyclic starts
in the original polygon. -/
private theorem retainedChain_edgeStart_ne
    {q t u : ℕ}
    (ht : t < run.chainLength - 1) (hu : u < run.chainLength - 1)
    (htu : (t : ZMod (run.spliceVertexCount q)) ≠
      (u : ZMod (run.spliceVertexCount q))) :
    Gluck.cyclicLift run.c (run.chainStart + t) ≠
      Gluck.cyclicLift run.c (run.chainStart + u) := by
  intro heq
  have hnat := Gluck.cyclicLift_injOn_range run.c
    (Finset.mem_range.mpr (run.chainStart_add_lt_n ht))
    (Finset.mem_range.mpr (run.chainStart_add_lt_n hu)) heq
  apply htu
  exact congrArg (fun x : ℕ ↦ (x : ZMod (run.spliceVertexCount q)))
    (Nat.add_left_cancel hnat)

/-- Successive retained-edge starts remain successive in the original cyclic
polygon.  The only possible extra wrap would identify the two boundary
contacts, which minimal-disk simplicity excludes. -/
private theorem retainedChain_edgeStart_succ_ne
    (hsimple : IsSimplePolygon v) (hΔ : MinimalEnclosingDiskR2 v O R)
    {q t u : ℕ}
    (ht : t < run.chainLength - 1) (hu : u < run.chainLength - 1)
    (htu : (t : ZMod (run.spliceVertexCount q)) + 1 ≠
      (u : ZMod (run.spliceVertexCount q))) :
    Gluck.cyclicLift run.c (run.chainStart + t) + 1 ≠
      Gluck.cyclicLift run.c (run.chainStart + u) := by
  intro heq
  have hlift : Gluck.cyclicLift run.c (run.chainStart + t + 1) =
      Gluck.cyclicLift run.c (run.chainStart + u) := by
    rw [← run.cyclicLift_chain_succ_simple t]
    exact heq
  by_cases htn : run.chainStart + t + 1 < n
  · have hnat := Gluck.cyclicLift_injOn_range run.c
      (Finset.mem_range.mpr htn)
      (Finset.mem_range.mpr (run.chainStart_add_lt_n hu)) hlift
    apply htu
    have htuNat : t + 1 = u := by omega
    simpa [Nat.cast_add] using
      congrArg (fun x : ℕ ↦ (x : ZMod (run.spliceVertexCount q))) htuNat
  · have htEq : run.chainStart + t + 1 = n := by
      have := run.chainStart_add_succ_le_n ht
      omega
    have huZero : run.chainStart + u = 0 := by
      apply Gluck.cyclicLift_injOn_range run.c
        (Finset.mem_range.mpr (run.chainStart_add_lt_n hu))
        (Finset.mem_range.mpr (Nat.pos_of_ne_zero (NeZero.ne n)))
      calc
        Gluck.cyclicLift run.c (run.chainStart + u) =
            Gluck.cyclicLift run.c (run.chainStart + t + 1) := hlift.symm
        _ = Gluck.cyclicLift run.c 0 := by
          rw [htEq]
          simp [Gluck.cyclicLift]
    apply run.endpointIndices_ne hsimple hΔ
    calc
      Gluck.cyclicLift run.c (run.a - 1) =
          Gluck.cyclicLift run.c (run.chainStart + u) := by
        congr 1
        simp only [chainStart]
        omega
      _ = Gluck.cyclicLift run.c (run.chainStart + t + 1) := hlift.symm
      _ = Gluck.cyclicLift run.c (run.b + 1) := by
        congr 1
        have ha := run.a_pos
        have hab := run.a_le_b
        have hb := run.b_lt
        simp only [chainStart, chainLength] at ht hu huZero htEq ⊢
        omega

/-- A retained splice edge is literally the corresponding cyclic edge of the
original polygon. -/
private theorem circleSplice_retainedEdge_segment
    (q : ℕ) (θB θA : ℝ) {t : ℕ}
    (ht : t < run.chainLength - 1) :
    segment ℝ
        (run.circleSplice q θB θA
          (t : ZMod (run.spliceVertexCount q)))
        (run.circleSplice q θB θA
          ((t : ZMod (run.spliceVertexCount q)) + 1)) =
      segment ℝ
        (v (Gluck.cyclicLift run.c (run.chainStart + t)))
        (v (Gluck.cyclicLift run.c (run.chainStart + t) + 1)) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  have htlen : t < run.chainLength := by omega
  have ht1len : t + 1 < run.chainLength := by omega
  have hsucc :
      (t : ZMod (run.spliceVertexCount q)) + 1 =
        (t + 1 : ℕ) := by
    push_cast
    rfl
  rw [hsucc,
    run.circleSplice_natCast_of_lt_chain q θB θA htlen,
    run.circleSplice_natCast_of_lt_chain q θB θA ht1len]
  simp only [point]
  congr 2
  exact (run.cyclicLift_chain_succ_simple t).symm

/-- A sufficiently fine circle completion of the retained Section 4 chain is
a simple polygon.  Simplicity of retained-retained edge pairs is inherited
from the original polygon; every pair involving a circle edge is separated
by that edge's strict supporting line. -/
theorem circleSplice_isSimplePolygon
    (hsimple : IsSimplePolygon v) (hΔ : MinimalEnclosingDiskR2 v O R)
    {q : ℕ} {θB θA : ℝ}
    (hR : 0 < R) (hq : 1 ≤ q)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hinner : run.chainInnerRadius <
      R * Real.cos (((θA - θB) / (q + 1 : ℕ)) / 2))
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hpositive : PositivePolygonOrientation
      (run.circleSplice q θB θA)) :
    IsSimplePolygon (run.circleSplice q θB θA) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  let w : ZMod (run.spliceVertexCount q) → ℂ :=
    run.circleSplice q θB θA
  change IsSimplePolygon w
  change PositivePolygonOrientation w at hpositive
  have hforward (i : ZMod (run.spliceVertexCount q)) :
      0 < crossR2 (w i) (w (i + 1)) (w (i + 1 + 1)) := by
    simpa only [add_sub_cancel_right] using hpositive (i + 1)
  refine ⟨?_, ?_, ?_⟩
  · intro i heq
    have hcross := hforward i
    rw [heq] at hcross
    simp [crossR2] at hcross
  · intro i
    exact consecutive_segments_inter_eq_singleton_of_crossR2_pos (hforward i)
  · intro i j hij hi1j hj1i
    rcases run.circleSplice_edge_chain_or_meshIndex q i with
        ⟨t, ht, rfl⟩ | ⟨k, hk, rfl⟩
    · rcases run.circleSplice_edge_chain_or_meshIndex q j with
          ⟨u, hu, rfl⟩ | ⟨ℓ, hℓ, rfl⟩
      · change
          segment ℝ
              (run.circleSplice q θB θA
                (t : ZMod (run.spliceVertexCount q)))
              (run.circleSplice q θB θA
                ((t : ZMod (run.spliceVertexCount q)) + 1)) ∩
            segment ℝ
              (run.circleSplice q θB θA
                (u : ZMod (run.spliceVertexCount q)))
              (run.circleSplice q θB θA
                ((u : ZMod (run.spliceVertexCount q)) + 1)) = ∅
        rw [run.circleSplice_retainedEdge_segment q θB θA ht,
          run.circleSplice_retainedEdge_segment q θB θA hu]
        exact hsimple.2.2
          (Gluck.cyclicLift run.c (run.chainStart + t))
          (Gluck.cyclicLift run.c (run.chainStart + u))
          (run.retainedChain_edgeStart_ne ht hu hij)
          (run.retainedChain_edgeStart_succ_ne hsimple hΔ ht hu hi1j)
          (run.retainedChain_edgeStart_succ_ne hsimple hΔ hu ht hj1i)
      · rw [Set.inter_comm]
        apply segment_inter_eq_empty_of_crossR2_pos
        · simpa [w] using
            run.circleSplice_circleEdge_strictSupport_cyclic hR hq hBA hspan
              hinner hB hA hℓ
              (t : ZMod (run.spliceVertexCount q)) hij hj1i.symm
        · have hsuccNe :
              (t : ZMod (run.spliceVertexCount q)) + 1 ≠
                run.circleSpliceMeshIndex q ℓ + 1 := by
            intro heq
            apply hij
            exact add_right_cancel heq
          simpa [w] using
            run.circleSplice_circleEdge_strictSupport_cyclic hR hq hBA hspan
              hinner hB hA hℓ
              ((t : ZMod (run.spliceVertexCount q)) + 1) hi1j hsuccNe
    · apply segment_inter_eq_empty_of_crossR2_pos
      · simpa [w] using
          run.circleSplice_circleEdge_strictSupport_cyclic hR hq hBA hspan
            hinner hB hA hk j hij.symm hi1j.symm
      · have hsuccNe : j + 1 ≠ run.circleSpliceMeshIndex q k + 1 := by
          intro heq
          apply hij
          exact (add_right_cancel heq).symm
        simpa [w] using
          run.circleSplice_circleEdge_strictSupport_cyclic hR hq hBA hspan
            hinner hB hA hk (j + 1) hj1i hsuccNe

end Section4PositiveRunCertificate

end Gluck.Forward
