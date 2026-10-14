/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleParameters
import Gluck.Forward.Discrete.MinimalDiskBoundarySemicircle
import Gluck.Forward.Discrete.Section4CircleSplice

/-!
# The complementary minimal-circle arc in Dahlberg Section 4

This file packages the exact real-angle data consumed by the finite circle
splice.  The separate contact-order theorem only has to place every minimal
circle contact in the chosen endpoint interval; minimality then forces that
interval to span at least `π`.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- A simple cyclic polygon has pairwise distinct indexed vertices. -/
theorem isSimplePolygon_vertexMap_injective {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) :
    Function.Injective v := by
  intro i j hij
  by_contra hindex
  by_cases hisucc : i + 1 = j
  · exact hsimple.1 i (by simpa [hisucc] using hij)
  by_cases hjsucc : j + 1 = i
  · exact hsimple.1 j (by simpa [hjsucc] using hij.symm)
  have hdisjoint := hsimple.2.2 i j hindex hisucc hjsucc
  have hmem : v i ∈
      segment ℝ (v i) (v (i + 1)) ∩
        segment ℝ (v j) (v (j + 1)) := by
    refine ⟨left_mem_segment ℝ _ _, ?_⟩
    rw [hij]
    exact left_mem_segment ℝ _ _
  rw [hdisjoint] at hmem
  exact hmem

/-- Endpoint angles for the complementary circle arc, including the
minimality-forced semicircle bound. -/
structure Section4CircleArcCertificate {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R) where
  θB : ℝ
  θA : ℝ
  right_eq : run.point (run.b + 1) = circlePoint O R θB
  left_eq : run.point run.chainStart = circlePoint O R θA
  angles_lt : θB < θA
  span_lt : θA < θB + 2 * Real.pi
  pi_le_span : Real.pi ≤ θA - θB

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- The two contacts bounding a nonempty maximal complementary run are
distinct.  Otherwise the run contains every other cyclic index, leaving only
one minimal-circle contact, impossible for a positive-radius minimal disk. -/
theorem endpointIndices_ne
    (hsimple : IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    Gluck.cyclicLift run.c (run.a - 1) ≠
      Gluck.cyclicLift run.c (run.b + 1) := by
  intro heq
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have ha := run.a_pos
  have hab := run.a_le_b
  have hb := run.b_lt
  have hLlt : run.a - 1 < n := by omega
  have hUle : run.b + 1 ≤ n := by omega
  have hUeq : run.b + 1 = n := by
    by_contra hne
    have hUlt : run.b + 1 < n := by omega
    have hnat := Gluck.cyclicLift_injOn_range run.c
      (Finset.mem_range.mpr hLlt) (Finset.mem_range.mpr hUlt) heq
    omega
  have hliftU : Gluck.cyclicLift run.c (run.b + 1) =
      Gluck.cyclicLift run.c 0 := by
    rw [hUeq]
    simp [Gluck.cyclicLift]
  have hLeq : run.a - 1 = 0 :=
    Gluck.cyclicLift_injOn_range run.c
      (Finset.mem_range.mpr hLlt) (Finset.mem_range.mpr hnpos)
      (heq.trans hliftU)
  have haeq : run.a = 1 := by omega
  have hbeq : run.b = n - 1 := by omega
  let E : Finset (ZMod n) := circleContactSet v O R
  have hEsub : E ⊆ {run.c} := by
    intro i hiE
    simp only [Finset.mem_singleton]
    by_contra hic
    let t : ℕ := (i - run.c).val
    have htlt : t < n := ZMod.val_lt (i - run.c)
    have hlift : Gluck.cyclicLift run.c t = i := by
      dsimp [Gluck.cyclicLift, t]
      rw [ZMod.natCast_zmod_val (i - run.c)]
      abel
    have htpos : 0 < t := by
      apply Nat.pos_of_ne_zero
      intro ht0
      apply hic
      have := hlift
      simpa [ht0, Gluck.cyclicLift] using this.symm
    have htIcc : t ∈ Finset.Icc run.a run.b := by
      rw [Finset.mem_Icc, haeq, hbeq]
      omega
    have hiJ : i ∈ run.J := by
      rw [run.run_eq]
      exact Finset.mem_image.mpr ⟨t, htIcc, hlift⟩
    have hiComplement := run.maximal.properties.2.2 hiJ
    have hiNotE : i ∉ E := by simpa [E] using hiComplement
    exact hiNotE hiE
  have hcE : run.c ∈ E := by simpa [E] using run.contact
  have hEeq : E = {run.c} := by
    apply Finset.Subset.antisymm hEsub
    simpa using hcE
  have hR : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  have hcard : 2 ≤ E.card := by
    apply two_le_card_circleContactSet_of_minimalEnclosingDiskR2 hΔ hR
    exact Metric.mem_sphere'.mpr (mem_circleContactSet.mp run.contact)
  rw [hEeq] at hcard
  simp at hcard

/-- The endpoint points themselves are distinct. -/
theorem endpointPoints_ne
    (hsimple : IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    run.point run.chainStart ≠ run.point (run.b + 1) := by
  intro heq
  apply run.endpointIndices_ne hsimple hΔ
  apply isSimplePolygon_vertexMap_injective hsimple
  simpa only [point, chainStart] using heq

/-- Distinct boundary endpoints admit uniquely ordered lifts in one based
angle window. -/
theorem exists_ordered_endpointAngles
    (hne : run.point run.chainStart ≠ run.point (run.b + 1)) :
    ∃ θB θA : ℝ,
      run.point (run.b + 1) = circlePoint O R θB ∧
      run.point run.chainStart = circlePoint O R θA ∧
      θB < θA ∧ θA < θB + 2 * Real.pi := by
  have hend := run.endpoints_boundary
  have hBdist : dist O (run.point (run.b + 1)) = R := by
    simpa [point, dist_comm] using Metric.mem_sphere'.mp hend.2
  have hAdist : dist O (run.point run.chainStart) = R := by
    simpa [point, chainStart, dist_comm] using Metric.mem_sphere'.mp hend.1
  obtain ⟨θB, _hθB, hB⟩ :=
    exists_circlePoint_eq_of_dist_eq hBdist
  obtain ⟨θA, hθA, hA⟩ :=
    exists_circlePoint_eq_mem_angleWindow hAdist θB
  have hBA : θB < θA := by
    refine lt_of_le_of_ne hθA.1 ?_
    intro heq
    apply hne
    rw [hA, hB, heq]
  exact ⟨θB, θA, hB, hA, hBA, hθA.2⟩

/-- Minimality and simplicity discharge the endpoint-distinctness premise of
`exists_ordered_endpointAngles`. -/
theorem exists_ordered_endpointAngles_of_minimalDisk
    (hsimple : IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    ∃ θB θA : ℝ,
      run.point (run.b + 1) = circlePoint O R θB ∧
      run.point run.chainStart = circlePoint O R θA ∧
      θB < θA ∧ θA < θB + 2 * Real.pi :=
  run.exists_ordered_endpointAngles (run.endpointPoints_ne hsimple hΔ)

/-- If every minimal-circle contact lies on the endpoint arc, the contact-hull
minimality theorem upgrades the ordered endpoint lifts to a full arc
certificate with angular span at least `π`. -/
noncomputable def circleArcCertificate_of_contactCoverage
    (hΔ : MinimalEnclosingDiskR2 v O R) (hR : 0 < R)
    {θB θA : ℝ}
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBA : θB < θA) (hspan : θA < θB + 2 * Real.pi)
    (hcoverage : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      ∃ θ : ℝ, θ ∈ Set.Icc θB θA ∧ v i = circlePoint O R θ) :
    Section4CircleArcCertificate run := by
  refine {
    θB := θB
    θA := θA
    right_eq := hB
    left_eq := hA
    angles_lt := hBA
    span_lt := hspan
    pi_le_span := ?_ }
  exact minimalEnclosingDiskR2_pi_le_parameterSpan_of_boundaryContacts
    hΔ hR hcoverage

end Section4PositiveRunCertificate

end Gluck.Forward
