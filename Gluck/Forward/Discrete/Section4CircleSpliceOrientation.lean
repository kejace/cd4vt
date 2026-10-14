/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleSplice

/-!
# Positive orientation of the Section 4 circle splice

The retained internal vertices inherit their positive turn from the original
run, and every inserted mesh vertex inherits it from the ordered circle arc.
Thus only the two vertices where the original chain meets the circle mesh are
genuine local geometric obligations.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- Positive turns at the two splice endpoints complete the inherited chain
and circle-mesh turns to a positive orientation of the whole auxiliary
polygon. -/
theorem circleSplice_positiveOrientation_of_endpoint_cross_pos
    (hsimple : IsSimplePolygon v) (hR : 0 < R)
    (q : ℕ) (_hq : 1 ≤ q) (θB θA : ℝ)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hleft : 0 < crossR2
      (run.circleSplice q θB θA
        ((0 : ZMod (run.spliceVertexCount q)) - 1))
      (run.circleSplice q θB θA 0)
      (run.circleSplice q θB θA
        ((0 : ZMod (run.spliceVertexCount q)) + 1)))
    (hright : 0 < crossR2
      (run.circleSplice q θB θA
        (((run.chainLength - 1 : ℕ) :
          ZMod (run.spliceVertexCount q)) - 1))
      (run.circleSplice q θB θA
        ((run.chainLength - 1 : ℕ) :
          ZMod (run.spliceVertexCount q)))
      (run.circleSplice q θB θA
        (((run.chainLength - 1 : ℕ) :
          ZMod (run.spliceVertexCount q)) + 1))) :
    PositivePolygonOrientation (run.circleSplice q θB θA) := by
  let m : ℕ := run.spliceVertexCount q
  letI : NeZero m := ⟨(run.spliceVertexCount_pos q).ne'⟩
  intro i
  let t : ℕ := i.val
  have htlt : t < m := i.val_lt
  have hit : (t : ZMod m) = i := ZMod.natCast_zmod_val i
  by_cases htChain : t < run.chainLength
  · by_cases htZero : t = 0
    · have hi : i = 0 := by
        calc
          i = (t : ZMod m) := hit.symm
          _ = 0 := by rw [htZero]; norm_num
      simpa [m, hi] using hleft
    · by_cases htLast : t = run.chainLength - 1
      · have hi : i =
            ((run.chainLength - 1 : ℕ) : ZMod m) := by
          calc
            i = (t : ZMod m) := hit.symm
            _ = ((run.chainLength - 1 : ℕ) : ZMod m) := by rw [htLast]
        simpa [m, hi] using hright
      · have htPos : 0 < t := Nat.pos_of_ne_zero htZero
        have htNext : t + 1 < run.chainLength := by omega
        rw [← hit,
          run.circleSplice_chain_prev q θB θA htPos (by omega),
          run.circleSplice_natCast_of_lt_chain q θB θA htChain,
          run.circleSplice_chain_next q θB θA htNext]
        have hcenterLeft : run.a - 1 ≤ run.chainStart + t := by
          have ha := run.a_pos
          simp only [chainStart]
          omega
        have hcenterRight : run.chainStart + t ≤ run.b + 1 := by
          have ha := run.a_pos
          have hab := run.a_le_b
          simp only [chainStart, chainLength] at htNext ⊢
          omega
        have hturn := run.cross_pos hsimple hR hcenterLeft hcenterRight
        have hkPos : 0 < run.chainStart + t := by
          have ha := run.a_pos
          simp only [chainStart]
          omega
        have hprevLift :
            Gluck.cyclicLift run.c (run.chainStart + t - 1) =
              Gluck.cyclicLift run.c (run.chainStart + t) - 1 := by
          dsimp [Gluck.cyclicLift]
          rw [Nat.cast_sub hkPos]
          push_cast
          ring
        have hnextLift :
            Gluck.cyclicLift run.c (run.chainStart + t + 1) =
              Gluck.cyclicLift run.c (run.chainStart + t) + 1 := by
          dsimp [Gluck.cyclicLift]
          push_cast
          ring
        simpa only [point, hprevLift, hnextLift] using hturn
  · let j : ℕ := t - run.chainLength
    have htEq : run.chainLength + j = t := by
      dsimp [j]
      omega
    have hjq : j < q := by
      dsimp [m, spliceVertexCount] at htlt
      dsimp [j]
      omega
    have hindex :
        (run.chainLength + j : ZMod m) = i := by
      calc
        (run.chainLength + j : ZMod m) =
            ((run.chainLength + j : ℕ) : ZMod m) := by push_cast; rfl
        _ = (t : ZMod m) := congrArg (fun x : ℕ ↦ (x : ZMod m)) htEq
        _ = i := hit
    have hturn := run.circleSplice_circleMesh_cross_pos q θB θA hR
      hBA hspan hB hA hjq
    simpa [m, hindex] using hturn

end Section4PositiveRunCertificate

end Gluck.Forward
