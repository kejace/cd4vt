/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4PositiveChain
import Gluck.Discrete.CircleParameterGeometry

/-!
# The explicit finite circle splice in Dahlberg Section 4

The auxiliary polygon keeps the enlarged positive-curvature run and then
returns from its right endpoint to its left endpoint through a finite ordered
mesh on the minimal circle.  This file defines that cyclic vertex map and
records its basic indexing identities.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- Natural-coordinate index of the left endpoint of the enlarged run. -/
def chainStart : ℕ := run.a - 1

/-- Number of original vertices in the enlarged run, including both boundary
endpoints. -/
def chainLength : ℕ := run.b - run.a + 3

theorem three_le_chainLength : 3 ≤ run.chainLength := by
  simp only [chainLength]
  omega

theorem chainStart_add_chainLength_sub_one :
    run.chainStart + (run.chainLength - 1) = run.b + 1 := by
  have ha := run.a_pos
  have hab := run.a_le_b
  simp only [chainStart, chainLength]
  omega

theorem chainStart_add_one : run.chainStart + 1 = run.a := by
  have ha := run.a_pos
  simp only [chainStart]
  omega

/-- Total vertex count after inserting `q` interior circle-mesh vertices. -/
def spliceVertexCount (q : ℕ) : ℕ := run.chainLength + q

theorem spliceVertexCount_pos (q : ℕ) : 0 < run.spliceVertexCount q := by
  exact lt_of_lt_of_le (by omega) (run.three_le_chainLength.trans
    (Nat.le_add_right _ _))

/-- The affine angle mesh from the right endpoint angle `θB` to the lifted
left endpoint angle `θA`.  Mesh indices `0` and `q+1` are the endpoints;
indices `1,…,q` are the inserted vertices. -/
noncomputable def circleMeshAngle (q j : ℕ) (θB θA : ℝ) : ℝ :=
  θB + (j : ℝ) / (q + 1 : ℕ) * (θA - θB)

@[simp] theorem circleMeshAngle_zero (q : ℕ) (θB θA : ℝ) :
    circleMeshAngle q 0 θB θA = θB := by
  simp [circleMeshAngle]

@[simp] theorem circleMeshAngle_last (q : ℕ) (θB θA : ℝ) :
    circleMeshAngle q (q + 1) θB θA = θA := by
  have hq : (q + 1 : ℝ) ≠ 0 := by positivity
  simp only [circleMeshAngle, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem circleMeshAngle_strictMono {q j k : ℕ} {θB θA : ℝ}
    (hBA : θB < θA) (hjk : j < k) :
    circleMeshAngle q j θB θA < circleMeshAngle q k θB θA := by
  have hden : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  have hjkReal : (j : ℝ) < k := by exact_mod_cast hjk
  have hfrac : (j : ℝ) / (q + 1 : ℕ) <
      (k : ℝ) / (q + 1 : ℕ) :=
    div_lt_div_of_pos_right hjkReal hden
  unfold circleMeshAngle
  simpa [add_comm] using
    (add_lt_add_left
      (mul_lt_mul_of_pos_right hfrac (sub_pos.mpr hBA)) θB)

theorem circleMeshAngle_mem_Icc {q j : ℕ} {θB θA : ℝ}
    (hBA : θB ≤ θA) (hj : j ≤ q + 1) :
    circleMeshAngle q j θB θA ∈ Set.Icc θB θA := by
  have hden : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) / (q + 1 : ℕ) := by positivity
  have hj1 : (j : ℝ) / (q + 1 : ℕ) ≤ 1 := by
    apply (div_le_one hden).mpr
    exact_mod_cast hj
  constructor
  · unfold circleMeshAngle
    exact le_add_of_nonneg_right (mul_nonneg hj0 (sub_nonneg.mpr hBA))
  · unfold circleMeshAngle
    nlinarith [mul_le_mul_of_nonneg_right hj1 (sub_nonneg.mpr hBA)]

theorem circleMeshAngle_succ_lt {q j : ℕ} {θB θA : ℝ}
    (hBA : θB < θA) :
    circleMeshAngle q j θB θA < circleMeshAngle q (j + 1) θB θA :=
  circleMeshAngle_strictMono hBA (by omega)

/-- The explicit cyclic auxiliary tuple: first the original enlarged run,
then `q` interior points of the circle mesh. -/
noncomputable def circleSplice (q : ℕ) (θB θA : ℝ) :
    ZMod (run.spliceVertexCount q) → ℂ := fun i =>
  if i.val < run.chainLength then
    run.point (run.chainStart + i.val)
  else
    circlePoint O R
      (circleMeshAngle q (i.val - run.chainLength + 1) θB θA)

theorem circleSplice_natCast_of_lt_chain (q : ℕ) (θB θA : ℝ)
    {t : ℕ} (ht : t < run.chainLength) :
    run.circleSplice q θB θA
        (t : ZMod (run.spliceVertexCount q)) =
      run.point (run.chainStart + t) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  have htm : t < run.spliceVertexCount q :=
    ht.trans_le (Nat.le_add_right _ _)
  simp [circleSplice, ZMod.val_cast_of_lt htm, ht]

theorem circleSplice_natCast_circleMesh (q : ℕ) (θB θA : ℝ)
    {j : ℕ} (hj : j < q) :
    run.circleSplice q θB θA
        (run.chainLength + j : ZMod (run.spliceVertexCount q)) =
      circlePoint O R (circleMeshAngle q (j + 1) θB θA) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hindex : run.chainLength + j < run.spliceVertexCount q := by
    simp only [spliceVertexCount]
    omega
  have hval :
      ((run.chainLength : ZMod (run.spliceVertexCount q)) + j).val =
        run.chainLength + j := by
    rw [← Nat.cast_add]
    exact ZMod.val_cast_of_lt hindex
  simp only [circleSplice, hval]
  rw [if_neg (by omega)]
  congr 2
  omega


@[simp] theorem circleSplice_zero (q : ℕ) (θB θA : ℝ) :
    run.circleSplice q θB θA 0 = run.point run.chainStart := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  simpa using run.circleSplice_natCast_of_lt_chain q θB θA
    (show 0 < run.chainLength from run.spliceVertexCount_pos 0)

theorem circleSplice_last_chain (q : ℕ) (θB θA : ℝ) :
    run.circleSplice q θB θA
        (run.chainLength - 1 : ZMod (run.spliceVertexCount q)) =
      run.point (run.b + 1) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hlen : 0 < run.chainLength := run.spliceVertexCount_pos 0
  have hcast :
      ((run.chainLength - 1 : ℕ) : ZMod (run.spliceVertexCount q)) =
        (run.chainLength : ZMod (run.spliceVertexCount q)) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ run.chainLength)]
    norm_num
  rw [← hcast,
    run.circleSplice_natCast_of_lt_chain q θB θA (by omega),
    run.chainStart_add_chainLength_sub_one]

/-- The three auxiliary vertices around an inserted circle point are three
successive points of the lifted angle mesh.  At the two ends this uses the
retained boundary vertices of the original chain. -/
theorem circleSplice_circleMesh_triple
    (q : ℕ) (θB θA : ℝ)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    {j : ℕ} (hj : j < q) :
    run.circleSplice q θB θA
        ((run.chainLength + j : ZMod (run.spliceVertexCount q)) - 1) =
        circlePoint O R (circleMeshAngle q j θB θA) ∧
      run.circleSplice q θB θA
        (run.chainLength + j : ZMod (run.spliceVertexCount q)) =
        circlePoint O R (circleMeshAngle q (j + 1) θB θA) ∧
      run.circleSplice q θB θA
        ((run.chainLength + j : ZMod (run.spliceVertexCount q)) + 1) =
        circlePoint O R (circleMeshAngle q (j + 2) θB θA) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hself := run.circleSplice_natCast_circleMesh q θB θA hj
  refine ⟨?_, hself, ?_⟩
  · by_cases hj0 : j = 0
    · subst j
      have hlen : 1 ≤ run.chainLength := by
        exact run.three_le_chainLength.trans' (by omega)
      have hprev :
          ((run.chainLength : ZMod (run.spliceVertexCount q)) - 1) =
            ((run.chainLength - 1 : ℕ) :
              ZMod (run.spliceVertexCount q)) := by
        rw [Nat.cast_sub hlen]
        norm_num
      simp only [Nat.cast_zero, add_zero]
      rw [hprev,
        run.circleSplice_natCast_of_lt_chain q θB θA (by omega)]
      rw [run.chainStart_add_chainLength_sub_one, hB,
        circleMeshAngle_zero]
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hprev :
          ((run.chainLength + j : ZMod (run.spliceVertexCount q)) - 1) =
            (run.chainLength + (j - 1) : ℕ) := by
        push_cast
        rw [Nat.cast_sub (by omega : 1 ≤ j)]
        push_cast
        ring
      rw [hprev,
        show run.circleSplice q θB θA
            ((run.chainLength + (j - 1) : ℕ) :
              ZMod (run.spliceVertexCount q)) =
              circlePoint O R
                (circleMeshAngle q ((j - 1) + 1) θB θA) by
          simpa only [Nat.cast_add] using
            run.circleSplice_natCast_circleMesh q θB θA
              (j := j - 1) (by omega)]
      congr 3
      omega
  · by_cases hjlast : j + 1 = q
    · have hnext :
          ((run.chainLength + j : ZMod (run.spliceVertexCount q)) + 1) = 0 := by
        calc
          (run.chainLength + j : ZMod (run.spliceVertexCount q)) + 1 =
              ((run.chainLength + j + 1 : ℕ) :
                ZMod (run.spliceVertexCount q)) := by push_cast; rfl
          _ = (run.spliceVertexCount q : ℕ) := by
            congr 1
            simp only [spliceVertexCount]
            omega
          _ = 0 := ZMod.natCast_self (run.spliceVertexCount q)
      rw [hnext, run.circleSplice_zero, hA]
      rw [show j + 2 = q + 1 by omega, circleMeshAngle_last]
    · have hjnext : j + 1 < q := by omega
      have hnext :
          ((run.chainLength + j : ZMod (run.spliceVertexCount q)) + 1) =
            (run.chainLength + (j + 1) : ℕ) := by
        push_cast
        ring
      rw [hnext,
        show run.circleSplice q θB θA
            ((run.chainLength + (j + 1) : ℕ) :
              ZMod (run.spliceVertexCount q)) =
              circlePoint O R
                (circleMeshAngle q ((j + 1) + 1) θB θA) by
          simpa only [Nat.cast_add] using
            run.circleSplice_natCast_circleMesh q θB θA
              (j := j + 1) hjnext]

/-- The predecessor, the mesh vertex, and the successor are all on the
minimal circle. -/
theorem circleSplice_circleMesh_triple_boundary
    (q : ℕ) (θB θA : ℝ) (hR : 0 < R)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    {j : ℕ} (hj : j < q) :
    OnDiskBoundaryR2 (run.circleSplice q θB θA) O R
        ((run.chainLength + j : ZMod (run.spliceVertexCount q)) - 1) ∧
      OnDiskBoundaryR2 (run.circleSplice q θB θA) O R
        (run.chainLength + j : ZMod (run.spliceVertexCount q)) ∧
      OnDiskBoundaryR2 (run.circleSplice q θB θA) O R
        ((run.chainLength + j : ZMod (run.spliceVertexCount q)) + 1) := by
  obtain ⟨hprev, hself, hnext⟩ :=
    run.circleSplice_circleMesh_triple q θB θA hB hA hj
  refine ⟨?_, ?_, ?_⟩
  · change run.circleSplice q θB θA
      ((run.chainLength + j : ZMod (run.spliceVertexCount q)) - 1) ∈ Metric.sphere O R
    rw [hprev]
    exact Metric.mem_sphere'.mpr (by rw [dist_circlePoint_center, abs_of_pos hR])
  · change run.circleSplice q θB θA
      (run.chainLength + j : ZMod (run.spliceVertexCount q)) ∈ Metric.sphere O R
    rw [hself]
    exact Metric.mem_sphere'.mpr (by rw [dist_circlePoint_center, abs_of_pos hR])
  · change run.circleSplice q θB θA
      ((run.chainLength + j : ZMod (run.spliceVertexCount q)) + 1) ∈ Metric.sphere O R
    rw [hnext]
    exact Metric.mem_sphere'.mpr (by rw [dist_circlePoint_center, abs_of_pos hR])

/-- Every inserted mesh vertex turns strictly left when the lifted completion
arc has positive length strictly below one full turn. -/
theorem circleSplice_circleMesh_cross_pos
    (q : ℕ) (θB θA : ℝ) (hR : 0 < R)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    {j : ℕ} (hj : j < q) :
    0 < crossR2
      (run.circleSplice q θB θA
        ((run.chainLength + j : ZMod (run.spliceVertexCount q)) - 1))
      (run.circleSplice q θB θA
        (run.chainLength + j : ZMod (run.spliceVertexCount q)))
      (run.circleSplice q θB θA
        ((run.chainLength + j : ZMod (run.spliceVertexCount q)) + 1)) := by
  obtain ⟨hprev, hself, hnext⟩ :=
    run.circleSplice_circleMesh_triple q θB θA hB hA hj
  rw [hprev, hself, hnext]
  apply crossR2_circlePoint_pos_of_ordered O hR.ne'
  · exact circleMeshAngle_strictMono hBA (by omega)
  · exact circleMeshAngle_strictMono hBA (by omega)
  · have hj0 := circleMeshAngle_mem_Icc (q := q) (j := j)
      hBA.le (by omega)
    have hj2 := circleMeshAngle_mem_Icc (q := q) (j := j + 2)
      hBA.le (by omega)
    have hshift : θB + 2 * Real.pi ≤
        circleMeshAngle q j θB θA + 2 * Real.pi := by
      linarith [hj0.1]
    exact lt_of_le_of_lt hj2.2
      (hspan.trans_le hshift)

/-- At an internal retained-chain index, the preceding auxiliary vertex is
the preceding original run vertex. -/
theorem circleSplice_chain_prev (q : ℕ) (θB θA : ℝ)
    {t : ℕ} (ht : 0 < t) (htlen : t < run.chainLength) :
    run.circleSplice q θB θA
        ((t : ZMod (run.spliceVertexCount q)) - 1) =
      run.point (run.chainStart + t - 1) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hcast :
      (t : ZMod (run.spliceVertexCount q)) - 1 =
        (t - 1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    norm_num
  rw [hcast, run.circleSplice_natCast_of_lt_chain q θB θA (by omega)]
  congr 1
  omega

/-- At an internal retained-chain index, the following auxiliary vertex is
the following original run vertex. -/
theorem circleSplice_chain_next (q : ℕ) (θB θA : ℝ)
    {t : ℕ} (htnext : t + 1 < run.chainLength) :
    run.circleSplice q θB θA
        ((t : ZMod (run.spliceVertexCount q)) + 1) =
      run.point (run.chainStart + t + 1) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  have hcast :
      (t : ZMod (run.spliceVertexCount q)) + 1 =
        (t + 1 : ℕ) := by
    push_cast
    rfl
  rw [hcast, run.circleSplice_natCast_of_lt_chain q θB θA htnext]
  congr 1

private theorem cyclicLift_chain_prev {t : ℕ} (ht : 0 < t) :
    Gluck.cyclicLift run.c (run.chainStart + t - 1) =
      Gluck.cyclicLift run.c (run.chainStart + t) - 1 := by
  dsimp [Gluck.cyclicLift]
  rw [Nat.cast_sub (by omega : 1 ≤ run.chainStart + t)]
  push_cast
  ring

private theorem cyclicLift_chain_next (t : ℕ) :
    Gluck.cyclicLift run.c (run.chainStart + t + 1) =
      Gluck.cyclicLift run.c (run.chainStart + t) + 1 := by
  dsimp [Gluck.cyclicLift]
  push_cast
  ring

/-- Curvature at every internal retained-chain vertex is definitionally the
original signed Menger curvature at the corresponding cyclic index. -/
theorem signedMengerProfile_circleSplice_internal_chain
    (q : ℕ) (θB θA : ℝ) {t : ℕ}
    (ht : 0 < t) (htnext : t + 1 < run.chainLength) :
    SignedMengerProfile (run.circleSplice q θB θA)
        (t : ZMod (run.spliceVertexCount q)) =
      SignedMengerProfile v
        (Gluck.cyclicLift run.c (run.chainStart + t)) := by
  letI : NeZero (run.spliceVertexCount q) :=
    ⟨(run.spliceVertexCount_pos q).ne'⟩
  rw [SignedMengerProfile_apply, SignedMengerProfile_apply,
    run.circleSplice_chain_prev q θB θA ht (by omega),
    run.circleSplice_natCast_of_lt_chain q θB θA (by omega),
    run.circleSplice_chain_next q θB θA htnext]
  simp only [point]
  rw [cyclicLift_chain_prev run ht, cyclicLift_chain_next run t]

/-- Every internal retained-chain vertex inherits Dahlberg's strict
reciprocal-radius curvature gap. -/
theorem signedMengerProfile_circleSplice_internal_chain_gap
    (q : ℕ) (θB θA : ℝ) {t : ℕ}
    (ht : 0 < t) (htnext : t + 1 < run.chainLength) :
    1 / R < SignedMengerProfile (run.circleSplice q θB θA)
      (t : ZMod (run.spliceVertexCount q)) := by
  rw [run.signedMengerProfile_circleSplice_internal_chain q θB θA ht htnext]
  apply run.curvature_gap
  · have ha := run.a_pos
    simp only [chainStart]
    omega
  · have ha := run.a_pos
    have hab := run.a_le_b
    simp only [chainStart, chainLength] at htnext ⊢
    omega

end Section4PositiveRunCertificate

end Gluck.Forward
