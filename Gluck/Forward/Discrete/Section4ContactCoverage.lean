/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4ContactOrderCrosscut
import Gluck.Forward.Discrete.Section4CircleParameters
import Gluck.Forward.Discrete.Section4CircleArc

/-!
# Propagating the circle order of minimal-disk contacts

The crosscut theorem rules out alternating boundary endpoints for two
separated pieces of a simple polygon.  This file records the cyclic-index
wrapper and the resulting propagation lemma: after the orientation of one
third boundary point has been anchored, every further boundary point on the
same polygonal arc lies on the corresponding oriented circle arc.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- Cyclic-coordinate form of
`not_circle_alternating_of_separated_polygonSubchains`. -/
private theorem not_circle_alternating_of_separated_cyclic_polygon_subchains_aux
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {c : ZMod n} {i j k l : ℕ}
    {θi θk θj θl : ℝ}
    (hsimple : IsSimplePolygon v)
    (hinside : ∀ z : ZMod n, dist O (v z) ≤ R)
    (hR : 0 < R)
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hln : l < n)
    (hi : v (Gluck.cyclicLift c i) = circlePoint O R θi)
    (hk : v (Gluck.cyclicLift c k) = circlePoint O R θk)
    (hj : v (Gluck.cyclicLift c j) = circlePoint O R θj)
    (hl : v (Gluck.cyclicLift c l) = circlePoint O R θl)
    (hik : θi < θk) (hkj : θk < θj)
    (hjl : θj < θl) (hspan : θl < θi + 2 * Real.pi) : False := by
  let w : ZMod n → ℂ := shiftPolygon v c
  have hsimpleW : IsSimplePolygon w := isSimplePolygon_shift hsimple c
  have hinsideW : ∀ z : ZMod n, dist O (w z) ≤ R := by
    intro z
    exact hinside (c + z)
  apply not_circle_alternating_of_separated_polygonSubchains
    hsimpleW hinsideW hR hij hjk hkl hln
  · simpa [w, shiftPolygon, Gluck.cyclicLift] using hi
  · simpa [w, shiftPolygon, Gluck.cyclicLift] using hk
  · simpa [w, shiftPolygon, Gluck.cyclicLift] using hj
  · simpa [w, shiftPolygon, Gluck.cyclicLift] using hl
  · exact hik
  · exact hkj
  · exact hjl
  · exact hspan

private theorem ordered_anchor_indices_ne_aux
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {c : ZMod n} {m p t : ℕ}
    {θB θC θA θD : ℝ}
    (hR : 0 < R)
    (hDwin : θD ∈ Set.Ico θB (θB + 2 * Real.pi))
    (hB : v (Gluck.cyclicLift c 0) = circlePoint O R θB)
    (hC : v (Gluck.cyclicLift c p) = circlePoint O R θC)
    (hA : v (Gluck.cyclicLift c m) = circlePoint O R θA)
    (hD : v (Gluck.cyclicLift c t) = circlePoint O R θD)
    (hBC : θB < θC) (hCA : θC < θA)
    (hspan : θA < θB + 2 * Real.pi)
    (hAD : θA < θD) :
    t ≠ 0 ∧ t ≠ p ∧ t ≠ m := by
  constructor
  · intro ht
    subst t
    have hEq : θD = θB := by
      apply injOn_circleMap_of_abs_sub_le' hR.ne' (by linarith [Real.two_pi_pos])
        hDwin ⟨le_rfl, by linarith [Real.two_pi_pos]⟩
      change circlePoint O R θD = circlePoint O R θB
      rw [← hD, ← hB]
    linarith
  constructor
  · intro ht
    subst t
    have hEq : θD = θC := by
      apply injOn_circleMap_of_abs_sub_le' hR.ne' (by linarith [Real.two_pi_pos])
        hDwin ⟨hBC.le, by linarith⟩
      change circlePoint O R θD = circlePoint O R θC
      rw [← hD, ← hC]
    linarith
  · intro ht
    subst t
    have hEq : θD = θA := by
      apply injOn_circleMap_of_abs_sub_le' hR.ne' (by linarith [Real.two_pi_pos])
        hDwin ⟨(hBC.trans hCA).le, hspan⟩
      change circlePoint O R θD = circlePoint O R θA
      rw [← hD, ← hA]
    linarith

private theorem false_of_ordered_anchor_lt_aux
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {c : ZMod n} {m p t : ℕ}
    {θB θC θA θD : ℝ}
    (hsimple : IsSimplePolygon v)
    (hinside : ∀ z : ZMod n, dist O (v z) ≤ R)
    (hR : 0 < R)
    (hpm : p < m) (hmn : m < n)
    (hB : v (Gluck.cyclicLift c 0) = circlePoint O R θB)
    (hC : v (Gluck.cyclicLift c p) = circlePoint O R θC)
    (hA : v (Gluck.cyclicLift c m) = circlePoint O R θA)
    (hD : v (Gluck.cyclicLift c t) = circlePoint O R θD)
    (hBC : θB < θC) (hCA : θC < θA)
    (ht0 : t ≠ 0) (htp : t < p)
    (hAD : θA < θD) (hDtop : θD < θB + 2 * Real.pi) :
    False := by
  have hmle : m ≤ n := hmn.le
  have hlift (r : ℕ) :
      Gluck.cyclicLift (Gluck.cyclicLift c m) (n - m + r) =
        Gluck.cyclicLift c r := by
    dsimp [Gluck.cyclicLift]
    rw [Nat.cast_add, Nat.cast_sub hmle, ZMod.natCast_self]
    ring
  exact not_circle_alternating_of_separated_cyclic_polygon_subchains_aux
    (c := Gluck.cyclicLift c m)
    (i := 0) (j := n - m) (k := n - m + t) (l := n - m + p)
    hsimple hinside hR (by omega) (by omega) (by omega) (by omega)
    (by simpa only [Gluck.cyclicLift, Nat.cast_zero, add_zero] using hA)
    (by rw [hlift]; exact hD)
    (by
      rw [show n - m = n - m + 0 by omega, hlift]
      simpa only [circlePoint_add_two_pi] using hB)
    (by rw [hlift]; simpa using hC)
    hAD hDtop
    (show θB + 2 * Real.pi < θC + 2 * Real.pi by linarith)
    (show θC + 2 * Real.pi < θA + 2 * Real.pi by linarith)

private theorem false_of_ordered_anchor_gt_aux
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {c : ZMod n} {m p t : ℕ}
    {θB θC θA θD : ℝ}
    (hsimple : IsSimplePolygon v)
    (hinside : ∀ z : ZMod n, dist O (v z) ≤ R)
    (hR : 0 < R)
    (hp : 0 < p) (hpm : p < m) (hmn : m < n)
    (hB : v (Gluck.cyclicLift c 0) = circlePoint O R θB)
    (hC : v (Gluck.cyclicLift c p) = circlePoint O R θC)
    (hA : v (Gluck.cyclicLift c m) = circlePoint O R θA)
    (hD : v (Gluck.cyclicLift c t) = circlePoint O R θD)
    (hBC : θB < θC) (hCA : θC < θA)
    (hpt : p < t) (htm : t < m)
    (hAD : θA < θD) (hDtop : θD < θB + 2 * Real.pi) :
    False := by
  have hple : p ≤ n := (hpm.trans hmn).le
  have hlift (r : ℕ) (hpr : p ≤ r) :
      Gluck.cyclicLift (Gluck.cyclicLift c p) (r - p) =
        Gluck.cyclicLift c r := by
    dsimp [Gluck.cyclicLift]
    rw [Nat.cast_sub hpr]
    ring
  have hliftWrap :
      Gluck.cyclicLift (Gluck.cyclicLift c p) (n - p) =
        Gluck.cyclicLift c 0 := by
    dsimp [Gluck.cyclicLift]
    rw [Nat.cast_sub hple, ZMod.natCast_self]
    ring
  exact not_circle_alternating_of_separated_cyclic_polygon_subchains_aux
    (c := Gluck.cyclicLift c p)
    (i := 0) (j := t - p) (k := m - p) (l := n - p)
    hsimple hinside hR (by omega) (by omega) (by omega) (by omega)
    (by simpa only [Gluck.cyclicLift, Nat.cast_zero, add_zero] using hC)
    (by rw [hlift m hpm.le]; exact hA)
    (by rw [hlift t hpt.le]; exact hD)
    (by rw [hliftWrap]; simpa using hB)
    hCA hAD hDtop (by linarith)

/-- A correctly ordered third point bounds every further contact angle by the
endpoint angle on the same polygonal arc. -/
private theorem circlePoint_angle_le_endpoint_of_ordered_anchor_aux
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {c : ZMod n} {m p t : ℕ}
    {θB θC θA θD : ℝ}
    (hsimple : IsSimplePolygon v)
    (hinside : ∀ z : ZMod n, dist O (v z) ≤ R)
    (hR : 0 < R)
    (hp : 0 < p) (hpm : p < m) (hmn : m < n)
    (htm : t ≤ m)
    (hB : v (Gluck.cyclicLift c 0) = circlePoint O R θB)
    (hC : v (Gluck.cyclicLift c p) = circlePoint O R θC)
    (hA : v (Gluck.cyclicLift c m) = circlePoint O R θA)
    (hD : v (Gluck.cyclicLift c t) = circlePoint O R θD)
    (hBC : θB < θC) (hCA : θC < θA)
    (hspan : θA < θB + 2 * Real.pi)
    (hDwin : θD ∈ Set.Ico θB (θB + 2 * Real.pi)) :
    θD ≤ θA := by
  by_contra hnot
  have hAD : θA < θD := lt_of_not_ge hnot
  have hDtop : θD < θB + 2 * Real.pi := hDwin.2
  obtain ⟨ht0, htp, htmNe⟩ := ordered_anchor_indices_ne_aux
    hR hDwin hB hC hA hD hBC hCA hspan hAD
  rcases lt_or_gt_of_ne htp with htp' | hpt
  · exact false_of_ordered_anchor_lt_aux hsimple hinside hR hpm hmn
      hB hC hA hD hBC hCA ht0 htp' hAD hDtop
  · exact false_of_ordered_anchor_gt_aux hsimple hinside hR hp hpm hmn
      hB hC hA hD hBC hCA hpt (lt_of_le_of_ne htm htmNe) hAD hDtop

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- Number of cyclic index steps from the right endpoint of the retained run
to its left endpoint through the complementary polygonal arc. -/
def complementContactArcLength : ℕ :=
  n - (run.b + 1) + run.chainStart

/-- The complementary-arc length is strictly below one index period. -/
theorem complementContactArcLength_lt :
    run.complementContactArcLength < n := by
  have hb := run.b_lt
  have ha := run.a_pos
  have hab := run.a_le_b
  have hU : run.b + 1 ≤ n := by omega
  have hLU : run.chainStart < run.b + 1 := by
    simp only [chainStart]
    omega
  simp only [complementContactArcLength]
  omega

/-- Advancing by `complementContactArcLength` from the right endpoint reaches
the left endpoint. -/
theorem cyclicLift_right_add_complementContactArcLength :
    Gluck.cyclicLift (Gluck.cyclicLift run.c (run.b + 1))
        run.complementContactArcLength =
      Gluck.cyclicLift run.c run.chainStart := by
  have hb := run.b_lt
  have hU : run.b + 1 ≤ n := by omega
  dsimp [complementContactArcLength, Gluck.cyclicLift]
  push_cast [Nat.cast_sub hU]
  rw [ZMod.natCast_self]
  ring

/-- Every minimal-circle contact occurs on the complementary polygonal arc
from the right endpoint to the left endpoint. -/
private theorem exists_complementContactArcCoordinate_aux
    {i : ZMod n} (hi : OnDiskBoundaryR2 v O R i) :
    ∃ t : ℕ, t ≤ run.complementContactArcLength ∧
      Gluck.cyclicLift (Gluck.cyclicLift run.c (run.b + 1)) t = i := by
  let B : ZMod n := Gluck.cyclicLift run.c (run.b + 1)
  let t : ℕ := (i - B).val
  have htlt : t < n := ZMod.val_lt (i - B)
  have htEq : Gluck.cyclicLift B t = i := by
    dsimp [t, Gluck.cyclicLift]
    rw [ZMod.natCast_zmod_val (i - B)]
    ring
  refine ⟨t, ?_, by simpa [B] using htEq⟩
  by_contra htm
  have hmt : run.complementContactArcLength < t := lt_of_not_ge htm
  let U : ℕ := run.b + 1
  let k : ℕ := U + t - n
  have hb := run.b_lt
  have ha := run.a_pos
  have hab := run.a_le_b
  have hUle : U ≤ n := by dsimp [U]; omega
  have hbase : n - U ≤ run.complementContactArcLength := by
    simp only [complementContactArcLength, U]
    omega
  have hnUt : n ≤ U + t := by omega
  have hka : run.a ≤ k := by
    dsimp [k, U, complementContactArcLength] at hmt ⊢
    simp only [chainStart] at hmt
    omega
  have hkb : k ≤ run.b := by
    dsimp [k, U]
    omega
  have hkJ : Gluck.cyclicLift run.c k ∈ run.J := by
    rw [run.run_eq]
    exact Finset.mem_image.mpr
      ⟨k, Finset.mem_Icc.mpr ⟨hka, hkb⟩, rfl⟩
  have hkNotContact :
      Gluck.cyclicLift run.c k ∉ circleContactSet v O R := by
    have hkComplement := run.maximal.properties.2.2 hkJ
    simpa using hkComplement
  apply hkNotContact
  apply mem_circleContactSet.mpr
  have hkEq : Gluck.cyclicLift run.c k = Gluck.cyclicLift B t := by
    dsimp [k, U, B, Gluck.cyclicLift]
    rw [Nat.cast_sub hnUt, Nat.cast_add, ZMod.natCast_self]
    ring
  rw [hkEq, htEq]
  exact Metric.mem_sphere'.mp hi

/-- With at least three minimal-circle contacts, one contact occurs strictly
between the two run endpoints on the complementary polygonal arc. -/
theorem exists_strict_complementContactArcCoordinate
    (hcard : 3 ≤ (circleContactSet v O R).card) :
    ∃ (i : ZMod n) (t : ℕ),
      OnDiskBoundaryR2 v O R i ∧
      0 < t ∧ t < run.complementContactArcLength ∧
      Gluck.cyclicLift (Gluck.cyclicLift run.c (run.b + 1)) t = i := by
  classical
  let A : ZMod n := Gluck.cyclicLift run.c run.chainStart
  let B : ZMod n := Gluck.cyclicLift run.c (run.b + 1)
  have hex : ∃ i ∈ circleContactSet v O R, i ≠ A ∧ i ≠ B := by
    by_contra hnone
    push Not at hnone
    have hsub : circleContactSet v O R ⊆ {A, B} := by
      intro i hi
      by_cases hiA : i = A
      · simp [hiA]
      · have hiB := hnone i hi hiA
        simp [hiB]
    have hle : (circleContactSet v O R).card ≤ 2 := by
      calc
        (circleContactSet v O R).card ≤ ({A, B} : Finset (ZMod n)).card :=
          Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨i, hiE, hiA, hiB⟩ := hex
  have hi : OnDiskBoundaryR2 v O R i :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hiE)
  obtain ⟨t, htm, htEq⟩ := run.exists_complementContactArcCoordinate_aux hi
  have ht0 : 0 < t := by
    apply Nat.pos_of_ne_zero
    intro ht
    subst t
    apply hiB
    simpa [B, Gluck.cyclicLift] using htEq.symm
  have htm' : t < run.complementContactArcLength := by
    apply lt_of_le_of_ne htm
    intro ht
    have hArc := run.cyclicLift_right_add_complementContactArcLength
    apply hiA
    dsimp [A, B] at hArc ⊢
    rw [← htEq, ht]
    exact hArc
  exact ⟨i, t, hi, ht0, htm', htEq⟩

/-- A correctly oriented third contact supplies the full contact coverage
required by `circleArcCertificate_of_contactCoverage`. -/
noncomputable def circleArcCertificateOfOrderedComplementContact
    (hsimple : IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hR : 0 < R)
    {p : ℕ} {θB θC θA : ℝ}
    (hp : 0 < p) (hpm : p < run.complementContactArcLength)
    (hB : run.point (run.b + 1) = circlePoint O R θB)
    (hC : v (Gluck.cyclicLift
      (Gluck.cyclicLift run.c (run.b + 1)) p) = circlePoint O R θC)
    (hA : run.point run.chainStart = circlePoint O R θA)
    (hBC : θB < θC) (hCA : θC < θA)
    (hspan : θA < θB + 2 * Real.pi) :
    Section4CircleArcCertificate run := by
  apply run.circleArcCertificate_of_contactCoverage hΔ hR hB hA
    (hBC.trans hCA) hspan
  intro i hi
  obtain ⟨t, htm, htEq⟩ := run.exists_complementContactArcCoordinate_aux hi
  have hidist : dist O (v i) = R := by
    simpa [dist_comm] using Metric.mem_sphere'.mp hi
  obtain ⟨θD, hθDwin, hiD⟩ :=
    exists_circlePoint_eq_mem_angleWindow hidist θB
  have hB' : v (Gluck.cyclicLift
      (Gluck.cyclicLift run.c (run.b + 1)) 0) = circlePoint O R θB := by
    simpa [point, Gluck.cyclicLift] using hB
  have hA' : v (Gluck.cyclicLift
      (Gluck.cyclicLift run.c (run.b + 1))
        run.complementContactArcLength) = circlePoint O R θA := by
    rw [run.cyclicLift_right_add_complementContactArcLength]
    simpa [point] using hA
  have hD' : v (Gluck.cyclicLift
      (Gluck.cyclicLift run.c (run.b + 1)) t) = circlePoint O R θD := by
    rw [htEq]
    exact hiD
  have hθDA : θD ≤ θA :=
    circlePoint_angle_le_endpoint_of_ordered_anchor_aux
      hsimple (fun z ↦ Metric.mem_closedBall'.mp (hΔ.2.1 z)) hR hp hpm
      run.complementContactArcLength_lt htm
      hB' hC hA' hD' hBC hCA hspan hθDwin
  exact ⟨θD, ⟨hθDwin.1, hθDA⟩, hiD⟩

end Section4PositiveRunCertificate

end Gluck.Forward
