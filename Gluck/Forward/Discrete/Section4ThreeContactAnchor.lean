/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4ContactCoverage
import Gluck.Forward.Discrete.Section4EndpointInteriorCurvature
import Gluck.Forward.Discrete.Section4LocalDetour
import Gluck.Forward.Discrete.Section4VertexEdgeClearance

/-!
# The three-contact orientation anchor

A small counterclockwise detour at a positively oriented contact fixes the
cyclic order of three circle contacts.
-/

namespace Gluck.Forward

open Gluck.Discrete Metric Set
open scoped unitInterval

private theorem exists_circleContact_incoming_sector_step_aux
    {O B P : ℂ} {R θ η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hB : B = circlePoint O R θ)
    (hP : dist O P < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧ δ < Real.pi ∧
      0 < crossR2 P B (circlePoint O R (θ + δ)) := by
  obtain ⟨ε, hε, hgap⟩ :=
    exists_step_bound_signedMengerR2_circlePoint_successor
      (O := O) (P := P) (R := R) (θ := θ) hR hP
  let δ : ℝ := min ε (min η Real.pi) / 2
  have hmin : 0 < min ε (min η Real.pi) :=
    lt_min hε (lt_min hη Real.pi_pos)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδε : δ < ε := by
    dsimp [δ]
    have := min_le_left ε (min η Real.pi)
    linarith
  have hδη : δ < η := by
    dsimp [δ]
    have h₁ := min_le_right ε (min η Real.pi)
    have h₂ := min_le_left η Real.pi
    linarith
  have hδπ : δ < Real.pi := by
    dsimp [δ]
    have h₁ := min_le_right ε (min η Real.pi)
    have h₂ := min_le_right η Real.pi
    linarith
  have hκgap := hgap δ hδ hδε
  have hκpos : 0 < signedMengerR2 P
      (circlePoint O R θ) (circlePoint O R (θ + δ)) :=
    (one_div_pos.mpr hR).trans hκgap
  have hPB : P ≠ circlePoint O R θ := by
    intro heq
    have : dist O P = R := by
      rw [heq, dist_circlePoint_center, abs_of_pos hR]
    linarith
  refine ⟨δ, hδ, hδη, hδπ, ?_⟩
  rw [hB]
  exact crossR2_pos_of_signedMengerR2_pos hPB hκpos

private theorem exists_openSegment_mem_ball_aux
    {B Q : ℂ} (hBQ : B ≠ Q) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ X : ℂ, X ∈ openSegment ℝ B Q ∧ X ∈ ball B ρ := by
  have hd : 0 < dist B Q := dist_pos.mpr hBQ
  let t : ℝ := min (1 / 2 : ℝ) (ρ / (2 * dist B Q))
  have hratio : 0 < ρ / (2 * dist B Q) :=
    div_pos hρ (mul_pos (by norm_num) hd)
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) hratio
  have htlt : t < 1 := by
    have htle : t ≤ (1 / 2 : ℝ) := min_le_left _ _
    linarith
  let X : ℂ := AffineMap.lineMap B Q t
  refine ⟨X, ?_, ?_⟩
  · dsimp [X]
    exact lineMap_mem_openSegment ℝ B Q ⟨ht, htlt⟩
  · rw [Metric.mem_ball]
    dsimp [X]
    rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_pos ht]
    have htle : t ≤ ρ / (2 * dist B Q) := min_le_right _ _
    have hmul : t * dist B Q ≤ (ρ / (2 * dist B Q)) * dist B Q :=
      mul_le_mul_of_nonneg_right htle (dist_nonneg)
    have hcancel : (ρ / (2 * dist B Q)) * dist B Q = ρ / 2 := by
      field_simp
    rw [hcancel] at hmul
    linarith

private theorem exists_circleContact_incoming_sector_step_mem_ball_aux
    {O B P : ℂ} {R θ η ρ : ℝ}
    (hR : 0 < R) (hη : 0 < η) (hρ : 0 < ρ)
    (hB : B = circlePoint O R θ)
    (hP : dist O P < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧ δ < Real.pi ∧
      0 < crossR2 P B (circlePoint O R (θ + δ)) ∧
      circlePoint O R (θ + δ) ∈ ball B ρ := by
  have hρR : 0 < ρ / R := div_pos hρ hR
  obtain ⟨δ, hδ, hδη, hδπ, hcross⟩ :=
    exists_circleContact_incoming_sector_step_aux hR (lt_min hη hρR) hB hP
  have hδη' : δ < η := hδη.trans_le (min_le_left _ _)
  have hδρR : δ < ρ / R := hδη.trans_le (min_le_right _ _)
  have hδ2π : δ < 2 * Real.pi := by linarith [Real.pi_pos]
  have hsin : Real.sin (δ / 2) ≤ δ / 2 :=
    Real.sin_le (by linarith : 0 ≤ δ / 2)
  have hdist : dist B (circlePoint O R (θ + δ)) < ρ := by
    rw [hB, dist_circlePoint_add_eq_two_mul_sin_half hR hδ hδ2π]
    have hRδ : R * δ < ρ := (lt_div_iff₀' hR).mp hδρR
    nlinarith
  exact ⟨δ, hδ, hδη', hδπ, hcross,
    by simpa [Metric.mem_ball, dist_comm] using hdist⟩

private theorem circlePoint_angle_gt_windowBase_of_ne_aux
    {O P B : ℂ} {R β θ : ℝ}
    (hθ : θ ∈ Set.Ico β (β + 2 * Real.pi))
    (hP : P = circlePoint O R θ)
    (hB : B = circlePoint O R β) (hPB : P ≠ B) :
    β < θ := by
  apply lt_of_le_of_ne hθ.1
  intro hEq
  apply hPB
  rw [hP, hB, hEq]

private theorem circlePoint_angle_lt_endpoint_of_disjoint_detourPaths_aux
    {O : ℂ} {R θB θA θC ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (hεA : θB + ε < θA)
    (hCwin : θC ∈ Set.Ico θB (θB + 2 * Real.pi))
    (γ : Path (circlePoint O R (θB + ε)) (circlePoint O R θC))
    (δ : Path (circlePoint O R θA)
      (circlePoint O R (θB + 2 * Real.pi)))
    (hγinside : ∀ s : I, dist O (γ s) ≤ R)
    (hδinside : ∀ t : I, dist O (δ t) ≤ R)
    (hdisjoint : Disjoint (Set.range γ) (Set.range δ)) :
    θC < θA := by
  by_contra hnot
  have hACle : θA ≤ θC := le_of_not_gt hnot
  have hAC : θA < θC := by
    apply lt_of_le_of_ne hACle
    intro hEq
    have hcommon : circlePoint O R θC ∈ Set.range γ := by
      refine ⟨1, ?_⟩
      simp
    have hcommon' : circlePoint O R θC ∈ Set.range δ := by
      refine ⟨0, ?_⟩
      simp [hEq]
    exact Set.disjoint_left.mp hdisjoint hcommon hcommon'
  obtain ⟨s, t, hst⟩ := paths_intersect_of_circle_alternating
    hR hεA hAC hCwin.2 (by linarith)
    γ δ hγinside hδinside
  apply Set.disjoint_left.mp hdisjoint
  · exact ⟨s, rfl⟩
  · exact ⟨t, hst.symm⟩

private theorem crossR2_pos_of_mem_openSegment_from_second_aux
    {P B Q X : ℂ} (hQ : 0 < crossR2 P B Q)
    (hX : X ∈ openSegment ℝ B Q) :
    0 < crossR2 P B X := by
  rw [openSegment_eq_image_lineMap] at hX
  obtain ⟨t, ht, rfl⟩ := hX
  rw [crossR2_lineMap]
  have hBzero : crossR2 P B B = 0 := by
    unfold crossR2
    ring
  rw [hBzero, mul_zero, zero_add]
  exact mul_pos ht.1 hQ

private structure PositiveContactDetourData
    {n : ℕ} [NeZero n] (v : ZMod n → ℂ) (O : ℂ)
    (R θB θA : ℝ) (m : ℕ) where
  ε : ℝ
  step : ℝ
  X : ℂ
  step_pos : 0 < step
  step_before : θB + step < θA
  D_mem_ball : circlePoint O R (θB + step) ∈ ball (v 0) ε
  X_mem_openSegment : X ∈ openSegment ℝ (v 0) (v 1)
  X_mem_ball : X ∈ ball (v 0) ε
  D_side : 0 < crossR2 (v (-1)) (v 0) (circlePoint O R (θB + step))
  X_side : 0 < crossR2 (v (-1)) (v 0) X
  X_inside : dist O X ≤ R
  clear : ∀ k : ℕ, m ≤ k → k + 1 < n →
    Disjoint (ball (v 0) ε)
      (segment ℝ (v (k : ZMod n)) (v ((k + 1 : ℕ) : ZMod n)))

private theorem exists_positiveContactDetourData_aux
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ}
    {R θB θA : ℝ} {m : ℕ}
    (hsimple : IsSimplePolygon v)
    (hinside : ∀ z : ZMod n, dist O (v z) ≤ R)
    (hR : 0 < R) (hmOne : 1 < m) (hmn : m < n)
    (hIncoming : dist O (v (-1)) < R)
    (hB : v 0 = circlePoint O R θB)
    (hcontact : 0 < crossR2 (v (-1)) (v 0) (v 1))
    (hBA : θB < θA) :
    Nonempty (PositiveContactDetourData v O R θB θA m) := by
  obtain ⟨ε, hε, hclear⟩ :=
    exists_ball_disjoint_later_polygonEdges hsimple hmOne hmn
  obtain ⟨δ, hδ, hδA, _, hDside, hDball⟩ :=
    exists_circleContact_incoming_sector_step_mem_ball_aux
      hR (sub_pos.mpr hBA) hε hB hIncoming
  have hBQ : v 0 ≠ v 1 := by simpa using hsimple.1 0
  obtain ⟨X, hXopen, hXball⟩ := exists_openSegment_mem_ball_aux hBQ hε
  have hXside := crossR2_pos_of_mem_openSegment_from_second_aux hcontact hXopen
  have hBclosed : v 0 ∈ closedBall O R := by
    simpa [Metric.mem_closedBall, dist_comm] using hinside 0
  have hQclosed : v 1 ∈ closedBall O R := by
    simpa [Metric.mem_closedBall, dist_comm] using hinside 1
  have hXclosed : X ∈ closedBall O R :=
    (convex_closedBall O R).segment_subset hBclosed hQclosed
      (openSegment_subset_segment ℝ _ _ hXopen)
  have hXinside : dist O X ≤ R := by
    simpa [Metric.mem_closedBall, dist_comm] using hXclosed
  exact ⟨⟨ε, δ, X, hδ, by linarith, hDball, hXopen, hXball, hDside, hXside,
    hXinside, hclear⟩⟩

private structure ContactAnchorPaths (O : ℂ) (R θB θC θA : ℝ) where
  step : ℝ
  step_pos : 0 < step
  step_before : θB + step < θA
  detour : Path (circlePoint O R (θB + step)) (circlePoint O R θC)
  returnPath : Path (circlePoint O R θA) (circlePoint O R (θB + 2 * Real.pi))
  detour_inside : ∀ s : I, dist O (detour s) ≤ R
  return_inside : ∀ t : I, dist O (returnPath t) ≤ R
  disjoint : Disjoint (Set.range detour) (Set.range returnPath)

private theorem exists_contactAnchorPaths_aux
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ}
    {R θB θC θA : ℝ} {p m : ℕ}
    (hsimple : IsSimplePolygon v)
    (hinside : ∀ z : ZMod n, dist O (v z) ≤ R)
    (hR : 0 < R) (hp : 0 < p) (hpm : p < m) (hmn : m < n)
    (hB : v 0 = circlePoint O R θB)
    (hC : v (p : ZMod n) = circlePoint O R θC)
    (hA : v (m : ZMod n) = circlePoint O R θA)
    (data : PositiveContactDetourData v O R θB θA m) :
    Nonempty (ContactAnchorPaths O R θB θC θA) := by
  let g : ℕ → ℂ := contactDetourVertices v (circlePoint O R (θB + data.step)) data.X
  let q : ℕ → ℂ := contactReturnVertices v m
  have hg0 : g 0 = circlePoint O R (θB + data.step) := by
    simp [g, contactDetourVertices]
  have hgp : g (p + 1) = circlePoint O R θC := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    simpa [g, contactDetourVertices, Nat.add_assoc] using hC
  have hq0 : q 0 = circlePoint O R θA := by
    simpa [q, contactReturnVertices] using hA
  have hqN : q (n - m) = circlePoint O R (θB + 2 * Real.pi) := by
    calc
      q (n - m) = v (n : ZMod n) := by
        simp [q, contactReturnVertices, Nat.add_sub_of_le hmn.le]
      _ = v 0 := by rw [ZMod.natCast_self]
      _ = circlePoint O R θB := hB
      _ = circlePoint O R (θB + 2 * Real.pi) :=
        (circlePoint_add_two_pi O R θB).symm
  let γ₀ := polygonalChainPath g (p + 1)
  let δ₀ := polygonalChainPath q (n - m)
  let γ := γ₀.cast hg0.symm hgp.symm
  let δ := δ₀.cast hq0.symm hqN.symm
  refine ⟨⟨data.step, data.step_pos, data.step_before, γ, δ, ?_, ?_, ?_⟩⟩
  · intro s
    change dist O (γ₀ s) ≤ R
    apply polygonalChainPath_inside_closedDisk
    intro k _
    rcases k with _ | _ | k
    · simp [g, contactDetourVertices, dist_circlePoint_center, abs_of_pos hR]
    · simpa [g, contactDetourVertices] using data.X_inside
    · exact hinside _
  · intro t
    change dist O (δ₀ t) ≤ R
    apply polygonalChainPath_inside_closedDisk
    exact fun _ _ ↦ hinside _
  · have hraw := disjoint_contactDetour_return_path_ranges
      hsimple hp hpm hmn data.X_mem_openSegment data.D_mem_ball data.X_mem_ball
        data.clear data.D_side data.X_side
    simpa only [γ, δ, γ₀, δ₀, g, q, Path.cast_coe] using hraw

private theorem circlePoint_angle_lower_of_contact_aux
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ}
    {R θB θC : ℝ} {p m : ℕ}
    (hsimple : IsSimplePolygon v) (hp : 0 < p) (hpm : p < m) (hmn : m < n)
    (hB : v 0 = circlePoint O R θB)
    (hC : v (p : ZMod n) = circlePoint O R θC)
    (hCwin : θC ∈ Set.Ico θB (θB + 2 * Real.pi)) :
    θB < θC := by
  have hpCast : (p : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hp (hpm.trans hmn)
  apply circlePoint_angle_gt_windowBase_of_ne_aux hCwin hC hB
  intro hEq
  exact hpCast (isSimplePolygon_vertexMap_injective hsimple hEq)

/-- A positive base contact orders an intermediate contact between the endpoint angle lifts. -/
theorem circlePoint_angle_between_of_positive_contact_anchor
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {p m : ℕ} {θB θC θA : ℝ}
    (hsimple : IsSimplePolygon v)
    (hinside : ∀ z : ZMod n, dist O (v z) ≤ R)
    (hR : 0 < R)
    (hp : 0 < p) (hpm : p < m) (hmn : m < n)
    (hIncoming : dist O (v (-1)) < R)
    (hB : v 0 = circlePoint O R θB)
    (hC : v (p : ZMod n) = circlePoint O R θC)
    (hA : v (m : ZMod n) = circlePoint O R θA)
    (hcontact : 0 < crossR2 (v (-1)) (v 0) (v 1))
    (hBA : θB < θA)
    (hCwin : θC ∈ Set.Ico θB (θB + 2 * Real.pi)) :
    θB < θC ∧ θC < θA := by
  have hBC := circlePoint_angle_lower_of_contact_aux hsimple hp hpm hmn hB hC hCwin
  refine ⟨hBC, ?_⟩
  obtain ⟨data⟩ := exists_positiveContactDetourData_aux hsimple hinside hR (by omega) hmn
    hIncoming hB hcontact hBA
  obtain ⟨paths⟩ :=
    exists_contactAnchorPaths_aux hsimple hinside hR hp hpm hmn hB hC hA data
  exact circlePoint_angle_lt_endpoint_of_disjoint_detourPaths_aux hR paths.step_pos
    paths.step_before hCwin paths.detour paths.returnPath paths.detour_inside paths.return_inside
      paths.disjoint

end Gluck.Forward
