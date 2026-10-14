/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleSpliceRadius
import Gluck.Forward.Discrete.Section4AuxiliaryRadiusObstruction

/-!
# Assembly of the explicit Section 4 circle splice

This file performs the finite cyclic case split for the explicit splice.
Internal retained vertices inherit the original curvature gap, inserted mesh
vertices have three neighbours on the minimal circle, and only the two splice
endpoints remain as separate local geometric obligations.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- Once simplicity, positive orientation, nonconcyclicity, and the two local
endpoint gaps are established, the explicit odd circle splice is exactly a
`Section4AuxiliaryRadiusGeometry`. -/
noncomputable def auxiliaryRadiusGeometry_of_oddCircleSplice
    (k : ℕ) (θB θA : ℝ) (hR : 0 < R)
    (hlower : Real.pi ≤ θA - θB)
    (hupper : θA - θB < 2 * Real.pi)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hsimple : IsSimplePolygon
      (run.circleSplice (2 * k + 1) θB θA))
    (hpositive : PositivePolygonOrientation
      (run.circleSplice (2 * k + 1) θB θA))
    (hnoncyclic : ¬ Concyclic
      (run.circleSplice (2 * k + 1) θB θA))
    (hleftGap : 1 / R < SignedMengerProfile
      (run.circleSplice (2 * k + 1) θB θA) 0)
    (hrightGap : 1 / R < SignedMengerProfile
      (run.circleSplice (2 * k + 1) θB θA)
        (run.chainLength - 1 :
          ZMod (run.spliceVertexCount (2 * k + 1)))) :
    Section4AuxiliaryRadiusGeometry O R := by
  let q : ℕ := 2 * k + 1
  let m : ℕ := run.spliceVertexCount q
  let w : ZMod m → ℂ := run.circleSplice q θB θA
  have hmpos : 0 < m := by
    exact run.spliceVertexCount_pos q
  let hneM : NeZero m := ⟨hmpos.ne'⟩
  letI : NeZero m := hneM
  refine {
    m := m
    hne := hneM
    w := w
    four_le := ?_
    simple := by simpa [m, w, q] using hsimple
    positive := by simpa [m, w, q] using hpositive
    nonconcyclic := by simpa [m, w, q] using hnoncyclic
    radius_obstruction := ?_
    circle_or_curvature_gap := ?_ }
  · dsimp [m, q, spliceVertexCount]
    have hlen := run.three_le_chainLength
    omega
  · simpa [m, w, q] using
      run.circleSplice_oddMesh_radius_obstruction k θB θA hR
        hlower hupper hB hA
  · intro i
    let t : ℕ := i.val
    have htlt : t < m := i.val_lt
    have hit : (t : ZMod m) = i := ZMod.natCast_zmod_val i
    by_cases htChain : t < run.chainLength
    · by_cases htZero : t = 0
      · right
        have hi : i = 0 := by
          calc
            i = (t : ZMod m) := hit.symm
            _ = 0 := by rw [htZero]; rfl
        simpa [m, w, q, hi] using hleftGap
      · by_cases htLast : t = run.chainLength - 1
        · right
          have hiNat : i =
              ((run.chainLength - 1 : ℕ) : ZMod m) := by
            calc
              i = (t : ZMod m) := hit.symm
              _ = ((run.chainLength - 1 : ℕ) : ZMod m) :=
                congrArg (fun x : ℕ ↦ (x : ZMod m)) htLast
          have hcast :
              ((run.chainLength - 1 : ℕ) : ZMod m) =
                (run.chainLength : ZMod m) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ run.chainLength)]
            norm_num
          rw [hiNat, hcast]
          simpa [m, w, q] using hrightGap
        · right
          have htpos : 0 < t := Nat.pos_of_ne_zero htZero
          have htnext : t + 1 < run.chainLength := by omega
          have hgap :=
            run.signedMengerProfile_circleSplice_internal_chain_gap
              q θB θA htpos htnext
          simpa [m, w, q, hit] using hgap
    · left
      let j : ℕ := t - run.chainLength
      have htEq : run.chainLength + j = t := by
        dsimp [j]
        omega
      have hjq : j < q := by
        dsimp [m, spliceVertexCount] at htlt
        dsimp [j]
        omega
      have hcircle :=
        run.circleSplice_circleMesh_triple_boundary q θB θA hR hB hA hjq
      have hindex :
          (run.chainLength + j : ZMod m) = i := by
        calc
          (run.chainLength + j : ZMod m) =
              ((run.chainLength + j : ℕ) : ZMod m) := by push_cast; rfl
          _ = (t : ZMod m) := congrArg (fun x : ℕ ↦ (x : ZMod m)) htEq
          _ = i := hit
      simpa [m, w, q, hindex] using hcircle

end Section4PositiveRunCertificate

end Gluck.Forward
