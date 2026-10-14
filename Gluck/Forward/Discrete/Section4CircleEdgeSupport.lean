/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4ChainInnerRadius
import Gluck.Forward.Discrete.Section4MeshDensity

/-!
# Strict support by the circle edges in Dahlberg's Section 4 splice

Every sufficiently short oriented edge of the completion-circle mesh has all
retained interior-chain vertices strictly on its left.  The cyclic ordering of
the circle parameters puts every other mesh vertex, including the two retained
boundary endpoints, strictly on the same side.  The final theorem packages
both facts as strict edge support for the explicit auxiliary splice.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- Every edge of a sufficiently fine completion-circle mesh strictly
supports every retained vertex in the open chain. -/
theorem circleMeshChord_supports_internalChain
    {q j k : ℕ} {θB θA : ℝ}
    (hR : 0 < R) (hq : 1 ≤ q)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hinner : run.chainInnerRadius <
      R * Real.cos (((θA - θB) / (q + 1 : ℕ)) / 2))
    (_hj : j ≤ q) (hak : run.a ≤ k) (hkb : k ≤ run.b) :
    0 < crossR2
      (circlePoint O R (circleMeshAngle q j θB θA))
      (circlePoint O R (circleMeshAngle q (j + 1) θB θA))
      (run.point k) := by
  apply run.crossR2_circlePoint_pos_of_chainInnerRadius_lt hR hak hkb
  · exact circleMeshAngle_succ_lt hBA
  · have hdiff := circleMeshAngle_succ_sub q j θB θA
    have hden : (2 : ℝ) ≤ (q + 1 : ℕ) := by exact_mod_cast (by omega : 2 ≤ q + 1)
    have hδ : θA - θB < 2 * Real.pi := by linarith
    have hstep : (θA - θB) / (q + 1 : ℕ) < Real.pi := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (q + 1 : ℕ))).mpr
      nlinarith [Real.pi_pos]
    linarith
  · rw [circleMeshAngle_succ_sub]
    exact hinner

/-- Every oriented completion-circle mesh edge strictly supports every other
circle vertex in the same lifted one-turn window. -/
theorem circleMeshChord_supports_otherCirclePoint
    {q j ℓ : ℕ} {θB θA : ℝ}
    (hR : 0 < R) (hBA : θB < θA)
    (hspan : θA < θB + 2 * Real.pi)
    (hj : j ≤ q) (hℓ : ℓ ≤ q + 1)
    (hℓj : ℓ ≠ j) (hℓj1 : ℓ ≠ j + 1) :
    0 < crossR2
      (circlePoint O R (circleMeshAngle q j θB θA))
      (circlePoint O R (circleMeshAngle q (j + 1) θB θA))
      (circlePoint O R (circleMeshAngle q ℓ θB θA)) := by
  rcases lt_or_gt_of_ne hℓj with hℓltj | hjltℓ
  · apply crossR2_circlePoint_pos_of_ordered_after_wrap O hR.ne'
    · exact circleMeshAngle_strictMono hBA hℓltj
    · exact circleMeshAngle_succ_lt hBA
    · have hj1 := circleMeshAngle_mem_Icc (q := q) (j := j + 1)
        hBA.le (by omega)
      have hℓI := circleMeshAngle_mem_Icc (q := q) (j := ℓ) hBA.le hℓ
      have hshift : θB + 2 * Real.pi ≤
          circleMeshAngle q ℓ θB θA + 2 * Real.pi := by
        simpa [add_comm] using add_le_add_left hℓI.1 (2 * Real.pi)
      exact hj1.2.trans_lt (hspan.trans_le hshift)
  · have hj1ltℓ : j + 1 < ℓ := by omega
    apply crossR2_circlePoint_pos_of_ordered O hR.ne'
    · exact circleMeshAngle_succ_lt hBA
    · exact circleMeshAngle_strictMono hBA hj1ltℓ
    · have hjI := circleMeshAngle_mem_Icc (q := q) (j := j)
        hBA.le (by omega)
      have hℓI := circleMeshAngle_mem_Icc (q := q) (j := ℓ) hBA.le hℓ
      have hshift : θB + 2 * Real.pi ≤
          circleMeshAngle q j θB θA + 2 * Real.pi := by
        simpa [add_comm] using add_le_add_left hjI.1 (2 * Real.pi)
      exact hℓI.2.trans_lt (hspan.trans_le hshift)

/-- The auxiliary-splice index occupied by mesh parameter `ℓ`.  Parameter
zero is the retained right endpoint, `q+1` is the retained left endpoint, and
the intervening parameters are the inserted circle vertices. -/
def circleSpliceMeshIndex (q ℓ : ℕ) : ZMod (run.spliceVertexCount q) :=
  if ℓ = 0 then (run.chainLength - 1 : ℕ)
  else if ℓ = q + 1 then 0
  else (run.chainLength + (ℓ - 1) : ℕ)

/-- Successive circle-mesh parameters occupy successive cyclic indices in
the explicit splice, including the final wrap back to index zero. -/
theorem circleSpliceMeshIndex_succ {q j : ℕ} (hq : 1 ≤ q) (hj : j ≤ q) :
    run.circleSpliceMeshIndex q (j + 1) =
      run.circleSpliceMeshIndex q j + 1 := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  by_cases hjzero : j = 0
  · subst j
    have h1last : 1 ≠ q + 1 := by omega
    simp only [circleSpliceMeshIndex, Nat.zero_add, one_ne_zero,
      h1last, if_false, if_pos, Nat.reduceSub, Nat.add_zero]
    have := run.three_le_chainLength
    norm_cast
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
    by_cases hjq : j = q
    · subst q
      have hjlastne : j ≠ j + 1 := by omega
      simp only [circleSpliceMeshIndex, Nat.succ_ne_zero, hjzero,
        hjlastne, if_false, if_pos]
      calc
        (0 : ZMod (run.spliceVertexCount j)) =
            ((run.spliceVertexCount j : ℕ) :
              ZMod (run.spliceVertexCount j)) :=
          (ZMod.natCast_self (run.spliceVertexCount j)).symm
        _ = ((run.chainLength + (j - 1) + 1 : ℕ) :
              ZMod (run.spliceVertexCount j)) := by
          congr 1
          simp only [spliceVertexCount]
          omega
        _ = ((run.chainLength + (j - 1) : ℕ) :
              ZMod (run.spliceVertexCount j)) + 1 := by push_cast; rfl
    · have hjlt : j < q := lt_of_le_of_ne hj hjq
      have hjlast : j ≠ q + 1 := by omega
      have hj1last : j + 1 ≠ q + 1 := by omega
      simp only [circleSpliceMeshIndex, hjzero, Nat.succ_ne_zero,
        hjlast, hj1last, if_false]
      calc
        ((run.chainLength + (j + 1 - 1) : ℕ) :
            ZMod (run.spliceVertexCount q)) =
            ((run.chainLength + (j - 1) + 1 : ℕ) :
              ZMod (run.spliceVertexCount q)) := by
          congr 1
          omega
        _ = ((run.chainLength + (j - 1) : ℕ) :
              ZMod (run.spliceVertexCount q)) + 1 := by push_cast; rfl

/-- Evaluation of the explicit splice at a circle-mesh index. -/
theorem circleSplice_apply_meshIndex
    (q : ℕ) (θB θA : ℝ)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    {ℓ : ℕ} (hℓ : ℓ ≤ q + 1) :
    run.circleSplice q θB θA (run.circleSpliceMeshIndex q ℓ) =
      circlePoint O R (circleMeshAngle q ℓ θB θA) := by
  by_cases hzero : ℓ = 0
  · subst ℓ
    simp only [circleSpliceMeshIndex, if_pos, circleMeshAngle_zero]
    rw [run.circleSplice_natCast_of_lt_chain q θB θA (by
      have := run.three_le_chainLength
      omega)]
    rw [run.chainStart_add_chainLength_sub_one, hB]
  by_cases hlast : ℓ = q + 1
  · subst ℓ
    simp only [circleSpliceMeshIndex, if_pos, circleMeshAngle_last]
    exact (run.circleSplice_zero q θB θA).trans hA
  · have hpos : 0 < ℓ := Nat.pos_of_ne_zero hzero
    have hlt : ℓ < q + 1 := lt_of_le_of_ne hℓ hlast
    have hpred : ℓ - 1 < q := by omega
    rw [circleSpliceMeshIndex, if_neg hzero, if_neg hlast]
    simpa only [Nat.cast_add, show ℓ - 1 + 1 = ℓ by omega] using
      run.circleSplice_natCast_circleMesh q θB θA hpred

/-- Every auxiliary-splice vertex is either a retained vertex strictly inside
the minimal circle or one of the parametrized completion-circle vertices.
The two retained boundary endpoints occur in the second alternative. -/
theorem circleSplice_vertex_internalChain_or_meshIndex
    (q : ℕ) (θB θA : ℝ) (i : ZMod (run.spliceVertexCount q)) :
    (∃ k : ℕ, run.a ≤ k ∧ k ≤ run.b ∧
      run.circleSplice q θB θA i = run.point k) ∨
    (∃ ℓ : ℕ, ℓ ≤ q + 1 ∧ i = run.circleSpliceMeshIndex q ℓ) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  by_cases hchain : i.val < run.chainLength
  · by_cases hzero : i.val = 0
    · right
      refine ⟨q + 1, le_rfl, ?_⟩
      have hi : i = 0 := (ZMod.val_eq_zero i).mp hzero
      simpa [circleSpliceMeshIndex] using hi
    by_cases hlast : i.val = run.chainLength - 1
    · right
      refine ⟨0, by omega, ?_⟩
      simp only [circleSpliceMeshIndex, if_pos]
      calc
        i = (i.val : ZMod (run.spliceVertexCount q)) :=
          (ZMod.natCast_zmod_val i).symm
        _ = (run.chainLength - 1 : ℕ) := by rw [hlast]
    · left
      refine ⟨run.chainStart + i.val, ?_, ?_, ?_⟩
      · have ha := run.a_pos
        simp only [chainStart]
        omega
      · have ha := run.a_pos
        have hab := run.a_le_b
        have hlen := run.three_le_chainLength
        simp only [chainStart, chainLength] at hchain hlast ⊢
        omega
      · calc
          run.circleSplice q θB θA i =
              run.circleSplice q θB θA
                (i.val : ZMod (run.spliceVertexCount q)) := by
            rw [ZMod.natCast_zmod_val]
          _ = run.point (run.chainStart + i.val) :=
            run.circleSplice_natCast_of_lt_chain q θB θA hchain
  · right
    let ℓ : ℕ := i.val - run.chainLength + 1
    have hival := ZMod.val_lt i
    have hlenle : run.chainLength ≤ i.val := Nat.le_of_not_gt hchain
    have hsub : i.val - run.chainLength + run.chainLength = i.val :=
      Nat.sub_add_cancel hlenle
    have hvaleq : run.chainLength + (i.val - run.chainLength) = i.val := by
      rw [Nat.add_comm]
      exact hsub
    have hℓpos : 0 < ℓ := by dsimp [ℓ]; omega
    have hℓq : ℓ ≤ q := by
      dsimp only [spliceVertexCount] at hival
      have hdiff : i.val - run.chainLength < q := by
        apply Nat.add_lt_add_iff_left.mp
        rw [hvaleq]
        exact hival
      dsimp [ℓ]
      omega
    refine ⟨ℓ, by omega, ?_⟩
    have hℓzero : ℓ ≠ 0 := by omega
    have hℓlast : ℓ ≠ q + 1 := by omega
    rw [circleSpliceMeshIndex, if_neg hℓzero, if_neg hℓlast]
    calc
      i = (i.val : ZMod (run.spliceVertexCount q)) :=
        (ZMod.natCast_zmod_val i).symm
      _ = (run.chainLength + (ℓ - 1) : ℕ) := by
        congr 1
        dsimp [ℓ]
        omega

/-- Every oriented fine circle-mesh edge strictly supports every auxiliary
splice vertex other than its two endpoints.  This is the circle-edge part of
`StrictConvexEdgeSupport` for the splice. -/
theorem circleSplice_circleEdge_strictSupport
    {q j : ℕ} {θB θA : ℝ}
    (hR : 0 < R) (hq : 1 ≤ q)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hinner : run.chainInnerRadius <
      R * Real.cos (((θA - θB) / (q + 1 : ℕ)) / 2))
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hj : j ≤ q) (i : ZMod (run.spliceVertexCount q))
    (hi0 : i ≠ run.circleSpliceMeshIndex q j)
    (hi1 : i ≠ run.circleSpliceMeshIndex q (j + 1)) :
    0 < crossR2
      (run.circleSplice q θB θA (run.circleSpliceMeshIndex q j))
      (run.circleSplice q θB θA (run.circleSpliceMeshIndex q (j + 1)))
      (run.circleSplice q θB θA i) := by
  have hj' : j ≤ q + 1 := by omega
  have hj1 : j + 1 ≤ q + 1 := by omega
  rw [run.circleSplice_apply_meshIndex q θB θA hB hA hj',
    run.circleSplice_apply_meshIndex q θB θA hB hA hj1]
  rcases run.circleSplice_vertex_internalChain_or_meshIndex q θB θA i with
      ⟨k, hak, hkb, hi⟩ | ⟨ℓ, hℓ, hi⟩
  · rw [hi]
    exact run.circleMeshChord_supports_internalChain hR hq hBA hspan
      hinner hj hak hkb
  · have hℓj : ℓ ≠ j := by
      intro h
      subst ℓ
      exact hi0 hi
    have hℓj1 : ℓ ≠ j + 1 := by
      intro h
      subst ℓ
      exact hi1 hi
    rw [hi, run.circleSplice_apply_meshIndex q θB θA hB hA hℓ]
    exact circleMeshChord_supports_otherCirclePoint (O := O) hR hBA hspan
      hj hℓ hℓj hℓj1

/-- Cyclic-edge form of `circleSplice_circleEdge_strictSupport`: the second
mesh endpoint is definitionally replaced by the successor of the first splice
index. -/
theorem circleSplice_circleEdge_strictSupport_cyclic
    {q j : ℕ} {θB θA : ℝ}
    (hR : 0 < R) (hq : 1 ≤ q)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hinner : run.chainInnerRadius <
      R * Real.cos (((θA - θB) / (q + 1 : ℕ)) / 2))
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hj : j ≤ q) (i : ZMod (run.spliceVertexCount q))
    (hi0 : i ≠ run.circleSpliceMeshIndex q j)
    (hi1 : i ≠ run.circleSpliceMeshIndex q j + 1) :
    0 < crossR2
      (run.circleSplice q θB θA (run.circleSpliceMeshIndex q j))
      (run.circleSplice q θB θA (run.circleSpliceMeshIndex q j + 1))
      (run.circleSplice q θB θA i) := by
  have hsucc := run.circleSpliceMeshIndex_succ hq hj
  have hi1' : i ≠ run.circleSpliceMeshIndex q (j + 1) := by
    intro hi
    apply hi1
    rw [← hsucc]
    exact hi
  rw [← hsucc]
  exact run.circleSplice_circleEdge_strictSupport hR hq hBA hspan
    hinner hB hA hj i hi0 hi1'

end Section4PositiveRunCertificate

end Gluck.Forward
