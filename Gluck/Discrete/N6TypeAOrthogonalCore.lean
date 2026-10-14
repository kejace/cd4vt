/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.N4Moderate
import Gluck.Discrete.OrthogonalResidualController

/-!
# The normalized orthogonal core for the Type-A R cell

This file exposes the side lengths and retained edge vectors of the
orthogonal quadrilateral with effective curvature profile `(k,u,q,v)`.
The construction in `N4Orthogonal` previously introduced these quantities
only as local proof terms.  Naming them makes the Type-A dormant-opening
family available to continuity and residual-coordinate arguments.
-/

namespace Gluck.Discrete.N6TypeAThreeCell

private lemma unitPhase_def' (x : ℝ) :
    unitPhase x = Complex.exp ((x : ℂ) * Complex.I) := rfl

@[simp] private lemma unitPhase_zero' : unitPhase 0 = 1 := by
  simp [unitPhase]

/-- Explicit four-edge closure expansion in the public unit-phase notation. -/
lemma closure_gap_four_unit_phase (κ ℓ : ZMod 4 → ℝ) :
    closureGap κ ℓ =
      (ℓ 0 : ℂ) * unitPhase (turningAngle 0 κ ℓ 0) +
      (ℓ 1 : ℂ) * (unitPhase (turningAngle 0 κ ℓ 0) *
        unitPhase (turningAngle 0 κ ℓ 1)) +
      (ℓ 2 : ℂ) * (unitPhase (turningAngle 0 κ ℓ 0) *
        unitPhase (turningAngle 0 κ ℓ 1) * unitPhase (turningAngle 0 κ ℓ 2)) +
      (ℓ 3 : ℂ) * (unitPhase (turningAngle 0 κ ℓ 0) *
        unitPhase (turningAngle 0 κ ℓ 1) * unitPhase (turningAngle 0 κ ℓ 2) *
          unitPhase (turningAngle 0 κ ℓ 3)) := by
  simp only [closureGap, vertexR2, ← unitPhase_def']
  norm_num [Finset.sum_range_succ, heading, unitPhase_add]

/-- Explicit six-edge closure expansion in the public unit-phase notation. -/
lemma closure_gap_six_unit_phase (κ ℓ : ZMod 6 → ℝ) :
    closureGap κ ℓ =
      (ℓ 0 : ℂ) * unitPhase (turningAngle 0 κ ℓ 0) +
      (ℓ 1 : ℂ) * (unitPhase (turningAngle 0 κ ℓ 0) *
        unitPhase (turningAngle 0 κ ℓ 1)) +
      (ℓ 2 : ℂ) * (unitPhase (turningAngle 0 κ ℓ 0) *
        unitPhase (turningAngle 0 κ ℓ 1) * unitPhase (turningAngle 0 κ ℓ 2)) +
      (ℓ 3 : ℂ) * (unitPhase (turningAngle 0 κ ℓ 0) *
        unitPhase (turningAngle 0 κ ℓ 1) * unitPhase (turningAngle 0 κ ℓ 2) *
          unitPhase (turningAngle 0 κ ℓ 3)) +
      (ℓ 4 : ℂ) * (unitPhase (turningAngle 0 κ ℓ 0) *
        unitPhase (turningAngle 0 κ ℓ 1) * unitPhase (turningAngle 0 κ ℓ 2) *
          unitPhase (turningAngle 0 κ ℓ 3) * unitPhase (turningAngle 0 κ ℓ 4)) +
      (ℓ 5 : ℂ) * (unitPhase (turningAngle 0 κ ℓ 0) *
        unitPhase (turningAngle 0 κ ℓ 1) * unitPhase (turningAngle 0 κ ℓ 2) *
          unitPhase (turningAngle 0 κ ℓ 3) * unitPhase (turningAngle 0 κ ℓ 4) *
            unitPhase (turningAngle 0 κ ℓ 5)) := by
  simp only [closureGap, vertexR2, ← unitPhase_def']
  norm_num [Finset.sum_range_succ, heading, unitPhase_add]

/-- The normalized canonical Type-A profile `(1,p,t,q,h,l)`. -/
def rActualProfile (p t q h l : ℝ) : ZMod 6 → ℝ := fun i ↦
  ![1, p, t, q, h, l] ⟨i.val, i.val_lt⟩

/-- The first side of the normalized orthogonal core `(k,u,q,v)`. -/
noncomputable def rCoreSideA (k u q v : ℝ) : ℝ :=
  2 * √(q ^ 2 - v ^ 2) / √(orthogonalDelta k u q v)

/-- The second side of the normalized orthogonal core `(k,u,q,v)`. -/
noncomputable def rCoreSideB (k u q v : ℝ) : ℝ :=
  2 * √(k ^ 2 - v ^ 2) / √(orthogonalDelta k u q v)

/-- The third side of the normalized orthogonal core `(k,u,q,v)`. -/
noncomputable def rCoreSideC (k u q v : ℝ) : ℝ :=
  2 * √(k ^ 2 - u ^ 2) / √(orthogonalDelta k u q v)

/-- The fourth side of the normalized orthogonal core `(k,u,q,v)`. -/
noncomputable def rCoreSideD (k u q v : ℝ) : ℝ :=
  2 * √(q ^ 2 - u ^ 2) / √(orthogonalDelta k u q v)

/-- Embed the four orthogonal sides into support `0235`; ambient edges one
and four are dormant. -/
noncomputable def rCoreCompactLengths (k u q v : ℝ) : ZMod 6 → ℝ := fun i ↦
  ![rCoreSideA k u q v, 0, rCoreSideB k u q v,
    rCoreSideC k u q v, 0, rCoreSideD k u q v] ⟨i.val, i.val_lt⟩

/-- One edge vector in the Euclidean development of the effective
orthogonal core. -/
noncomputable def rCoreDevelopedEdge (k u q v : ℝ) (i : ZMod 4) : ℂ :=
  let coreK := fourProfile k u q v
  let coreL := fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
    (rCoreSideC k u q v) (rCoreSideD k u q v)
  ![(coreL 0 : ℂ) * unitPhase (turningAngle 0 coreK coreL 0),
    (coreL 1 : ℂ) * (unitPhase (turningAngle 0 coreK coreL 0) *
      unitPhase (turningAngle 0 coreK coreL 1)),
    (coreL 2 : ℂ) * (unitPhase (turningAngle 0 coreK coreL 0) *
      unitPhase (turningAngle 0 coreK coreL 1) *
        unitPhase (turningAngle 0 coreK coreL 2)),
    (coreL 3 : ℂ) * (unitPhase (turningAngle 0 coreK coreL 0) *
      unitPhase (turningAngle 0 coreK coreL 1) *
        unitPhase (turningAngle 0 coreK coreL 2) *
          unitPhase (turningAngle 0 coreK coreL 3))] ⟨i.val, i.val_lt⟩

@[simp] lemma r_actual_profile_zero (p t q h l : ℝ) :
    rActualProfile p t q h l 0 = 1 := rfl

@[simp] lemma r_actual_profile_one (p t q h l : ℝ) :
    rActualProfile p t q h l 1 = p := rfl

@[simp] lemma r_actual_profile_two (p t q h l : ℝ) :
    rActualProfile p t q h l 2 = t := rfl

@[simp] lemma r_actual_profile_three (p t q h l : ℝ) :
    rActualProfile p t q h l 3 = q := rfl

@[simp] lemma r_actual_profile_four (p t q h l : ℝ) :
    rActualProfile p t q h l 4 = h := rfl

@[simp] lemma r_actual_profile_five (p t q h l : ℝ) :
    rActualProfile p t q h l 5 = l := rfl

@[simp] lemma r_core_compact_lengths_zero (k u q v : ℝ) :
    rCoreCompactLengths k u q v 0 = rCoreSideA k u q v := rfl

@[simp] lemma r_core_compact_lengths_one (k u q v : ℝ) :
    rCoreCompactLengths k u q v 1 = 0 := rfl

@[simp] lemma r_core_compact_lengths_two (k u q v : ℝ) :
    rCoreCompactLengths k u q v 2 = rCoreSideB k u q v := rfl

@[simp] lemma r_core_compact_lengths_three (k u q v : ℝ) :
    rCoreCompactLengths k u q v 3 = rCoreSideC k u q v := rfl

@[simp] lemma r_core_compact_lengths_four (k u q v : ℝ) :
    rCoreCompactLengths k u q v 4 = 0 := rfl

@[simp] lemma r_core_compact_lengths_five (k u q v : ℝ) :
    rCoreCompactLengths k u q v 5 = rCoreSideD k u q v := rfl

@[simp] lemma r_core_developed_edge_zero (k u q v : ℝ) :
    rCoreDevelopedEdge k u q v 0 =
      (rCoreSideA k u q v : ℂ) *
        unitPhase (turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 0) := rfl

@[simp] lemma r_core_developed_edge_one (k u q v : ℝ) :
    rCoreDevelopedEdge k u q v 1 =
      (rCoreSideB k u q v : ℂ) *
        (unitPhase (turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 0) *
        unitPhase (turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 1)) := rfl

@[simp] lemma r_core_developed_edge_two (k u q v : ℝ) :
    rCoreDevelopedEdge k u q v 2 =
      (rCoreSideC k u q v : ℂ) *
        (unitPhase (turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 0) *
        unitPhase (turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 1) *
        unitPhase (turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 2)) := rfl

@[simp] lemma r_core_developed_edge_three (k u q v : ℝ) :
    rCoreDevelopedEdge k u q v 3 =
      (rCoreSideD k u q v : ℂ) *
        (unitPhase (turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 0) *
        unitPhase (turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 1) *
        unitPhase (turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 2) *
        unitPhase (turningAngle 0 (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) 3)) := rfl

/-- The positive-real-axis half-diagonal of the normalized core. -/
noncomputable def rCoreHalfDiagonalA (k u q v : ℝ) : ℝ :=
  k * rCoreSideA k u q v * rCoreSideD k u q v / 2

/-- The positive-imaginary-axis half-diagonal of the normalized core. -/
noncomputable def rCoreHalfDiagonalB (k u q v : ℝ) : ℝ :=
  u * rCoreSideA k u q v * rCoreSideB k u q v / 2

/-- The negative-real-axis half-diagonal of the normalized core. -/
noncomputable def rCoreHalfDiagonalC (k u q v : ℝ) : ℝ :=
  q * rCoreSideB k u q v * rCoreSideC k u q v / 2

/-- The negative-imaginary-axis half-diagonal of the normalized core. -/
noncomputable def rCoreHalfDiagonalD (k u q v : ℝ) : ℝ :=
  v * rCoreSideC k u q v * rCoreSideD k u q v / 2

/-- The first retained edge in the standard orthogonal frame. -/
noncomputable def rCoreFirstEdge (k u q v : ℝ) : ℂ :=
  orthogonalQuadFirstEdge (rCoreHalfDiagonalA k u q v)
    (rCoreHalfDiagonalB k u q v)

/-- The last retained edge in the standard orthogonal frame. -/
noncomputable def rCoreLastEdge (k u q v : ℝ) : ℂ :=
  orthogonalQuadLastEdge (rCoreHalfDiagonalA k u q v)
    (rCoreHalfDiagonalD k u q v)

private lemma continuousOn_two_mul_sqrt_div_sqrt
    {X : Type*} [TopologicalSpace X] {s : Set X} {f g : X → ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hgpos : ∀ x ∈ s, 0 < g x) :
    ContinuousOn (fun x ↦ 2 * √(f x) / √(g x)) s := by
  exact (continuousOn_const.mul
      (Real.continuous_sqrt.comp_continuousOn hf)).div
    (Real.continuous_sqrt.comp_continuousOn hg)
    (fun x hx ↦ (Real.sqrt_pos.2 (hgpos x hx)).ne')

theorem continuousOn_rCoreSideA
    {X : Type*} [TopologicalSpace X] {s : Set X} {k u q v : X → ℝ}
    (hk : ContinuousOn k s) (hu : ContinuousOn u s)
    (hq : ContinuousOn q s) (hv : ContinuousOn v s)
    (hDelta : ∀ x ∈ s, 0 < orthogonalDelta (k x) (u x) (q x) (v x)) :
    ContinuousOn (fun x ↦ rCoreSideA (k x) (u x) (q x) (v x)) s := by
  apply continuousOn_two_mul_sqrt_div_sqrt
  · exact (hq.pow 2).sub (hv.pow 2)
  · unfold orthogonalDelta
    exact ((hk.pow 2).mul (hq.pow 2)).sub ((hu.pow 2).mul (hv.pow 2))
  · exact hDelta

theorem continuousOn_rCoreSideB
    {X : Type*} [TopologicalSpace X] {s : Set X} {k u q v : X → ℝ}
    (hk : ContinuousOn k s) (hu : ContinuousOn u s)
    (hq : ContinuousOn q s) (hv : ContinuousOn v s)
    (hDelta : ∀ x ∈ s, 0 < orthogonalDelta (k x) (u x) (q x) (v x)) :
    ContinuousOn (fun x ↦ rCoreSideB (k x) (u x) (q x) (v x)) s := by
  apply continuousOn_two_mul_sqrt_div_sqrt
  · exact (hk.pow 2).sub (hv.pow 2)
  · unfold orthogonalDelta
    exact ((hk.pow 2).mul (hq.pow 2)).sub ((hu.pow 2).mul (hv.pow 2))
  · exact hDelta

theorem continuousOn_rCoreSideC
    {X : Type*} [TopologicalSpace X] {s : Set X} {k u q v : X → ℝ}
    (hk : ContinuousOn k s) (hu : ContinuousOn u s)
    (hq : ContinuousOn q s) (hv : ContinuousOn v s)
    (hDelta : ∀ x ∈ s, 0 < orthogonalDelta (k x) (u x) (q x) (v x)) :
    ContinuousOn (fun x ↦ rCoreSideC (k x) (u x) (q x) (v x)) s := by
  apply continuousOn_two_mul_sqrt_div_sqrt
  · exact (hk.pow 2).sub (hu.pow 2)
  · unfold orthogonalDelta
    exact ((hk.pow 2).mul (hq.pow 2)).sub ((hu.pow 2).mul (hv.pow 2))
  · exact hDelta

theorem continuousOn_rCoreSideD
    {X : Type*} [TopologicalSpace X] {s : Set X} {k u q v : X → ℝ}
    (hk : ContinuousOn k s) (hu : ContinuousOn u s)
    (hq : ContinuousOn q s) (hv : ContinuousOn v s)
    (hDelta : ∀ x ∈ s, 0 < orthogonalDelta (k x) (u x) (q x) (v x)) :
    ContinuousOn (fun x ↦ rCoreSideD (k x) (u x) (q x) (v x)) s := by
  apply continuousOn_two_mul_sqrt_div_sqrt
  · exact (hq.pow 2).sub (hu.pow 2)
  · unfold orthogonalDelta
    exact ((hk.pow 2).mul (hq.pow 2)).sub ((hu.pow 2).mul (hv.pow 2))
  · exact hDelta

/-- The retained edge pair varies continuously on every positive-delta
parameter set. -/
theorem continuousOn_rCoreFirstLastEdges
    {X : Type*} [TopologicalSpace X] {s : Set X} {k u q v : X → ℝ}
    (hk : ContinuousOn k s) (hu : ContinuousOn u s)
    (hq : ContinuousOn q s) (hv : ContinuousOn v s)
    (hDelta : ∀ x ∈ s, 0 < orthogonalDelta (k x) (u x) (q x) (v x)) :
    ContinuousOn (fun x ↦ rCoreFirstEdge (k x) (u x) (q x) (v x)) s ∧
      ContinuousOn (fun x ↦ rCoreLastEdge (k x) (u x) (q x) (v x)) s := by
  have hA := continuousOn_rCoreSideA hk hu hq hv hDelta
  have hB := continuousOn_rCoreSideB hk hu hq hv hDelta
  have hC := continuousOn_rCoreSideC hk hu hq hv hDelta
  have hD := continuousOn_rCoreSideD hk hu hq hv hDelta
  have ha : ContinuousOn
      (fun x ↦ rCoreHalfDiagonalA (k x) (u x) (q x) (v x)) s := by
    exact ((hk.mul hA).mul hD).div_const 2
  have hb : ContinuousOn
      (fun x ↦ rCoreHalfDiagonalB (k x) (u x) (q x) (v x)) s := by
    exact ((hu.mul hA).mul hB).div_const 2
  have hd : ContinuousOn
      (fun x ↦ rCoreHalfDiagonalD (k x) (u x) (q x) (v x)) s := by
    exact ((hv.mul hC).mul hD).div_const 2
  constructor
  · exact ((Complex.continuous_ofReal.comp_continuousOn hb).mul
      continuousOn_const).sub
        (Complex.continuous_ofReal.comp_continuousOn ha)
  · exact (Complex.continuous_ofReal.comp_continuousOn ha).add
      ((Complex.continuous_ofReal.comp_continuousOn hd).mul continuousOn_const)

lemma orthogonal_delta_pos_of_strict_alternation
    {k u q v : ℝ} (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (_huq : u < q) (_hvk : v < k) (hvq : v < q) :
    0 < orthogonalDelta k u q v := by
  have huv : u * v < k * q := by
    calc
      u * v < k * v := mul_lt_mul_of_pos_right huk hv
      _ < k * q := mul_lt_mul_of_pos_left hvq hk
  have hsum : 0 < k * q + u * v :=
    add_pos (mul_pos hk hq) (mul_pos hu hv)
  rw [show orthogonalDelta k u q v =
    (k * q - u * v) * (k * q + u * v) by
      unfold orthogonalDelta
      ring]
  exact mul_pos (sub_pos.mpr huv) hsum

private lemma square_sub_pos {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    0 < x ^ 2 - y ^ 2 := by
  nlinarith [mul_pos (sub_pos.mpr hyx) (add_pos (hy.trans hyx) hy)]

lemma r_core_sides_pos {k u q v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    0 < rCoreSideA k u q v ∧ 0 < rCoreSideB k u q v ∧
      0 < rCoreSideC k u q v ∧ 0 < rCoreSideD k u q v := by
  have hDelta := orthogonal_delta_pos_of_strict_alternation
    hk hu hq hv huk huq hvk hvq
  have hqv := square_sub_pos hv hvq
  have hkv := square_sub_pos hv hvk
  have hku := square_sub_pos hu huk
  have hqu := square_sub_pos hu huq
  simp only [rCoreSideA, rCoreSideB, rCoreSideC, rCoreSideD]
  exact ⟨div_pos (mul_pos two_pos (Real.sqrt_pos.2 hqv)) (Real.sqrt_pos.2 hDelta),
    div_pos (mul_pos two_pos (Real.sqrt_pos.2 hkv)) (Real.sqrt_pos.2 hDelta),
    div_pos (mul_pos two_pos (Real.sqrt_pos.2 hku)) (Real.sqrt_pos.2 hDelta),
    div_pos (mul_pos two_pos (Real.sqrt_pos.2 hqu)) (Real.sqrt_pos.2 hDelta)⟩

lemma r_core_side_a_sq {k u q v : ℝ}
    (hDelta : 0 ≤ orthogonalDelta k u q v) (hqv : 0 ≤ q ^ 2 - v ^ 2) :
    rCoreSideA k u q v ^ 2 = orthogonalA2 k u q v := by
  rw [rCoreSideA, div_pow, mul_pow, Real.sq_sqrt hqv,
    Real.sq_sqrt hDelta]
  unfold orthogonalA2
  ring

lemma r_core_side_b_sq {k u q v : ℝ}
    (hDelta : 0 ≤ orthogonalDelta k u q v) (hkv : 0 ≤ k ^ 2 - v ^ 2) :
    rCoreSideB k u q v ^ 2 = orthogonalB2 k u q v := by
  rw [rCoreSideB, div_pow, mul_pow, Real.sq_sqrt hkv,
    Real.sq_sqrt hDelta]
  unfold orthogonalB2
  ring

lemma r_core_side_c_sq {k u q v : ℝ}
    (hDelta : 0 ≤ orthogonalDelta k u q v) (hku : 0 ≤ k ^ 2 - u ^ 2) :
    rCoreSideC k u q v ^ 2 = orthogonalC2 k u q v := by
  rw [rCoreSideC, div_pow, mul_pow, Real.sq_sqrt hku,
    Real.sq_sqrt hDelta]
  unfold orthogonalC2
  ring

lemma r_core_side_d_sq {k u q v : ℝ}
    (hDelta : 0 ≤ orthogonalDelta k u q v) (hqu : 0 ≤ q ^ 2 - u ^ 2) :
    rCoreSideD k u q v ^ 2 = orthogonalD2 k u q v := by
  rw [rCoreSideD, div_pow, mul_pow, Real.sq_sqrt hqu,
    Real.sq_sqrt hDelta]
  unfold orthogonalD2
  ring

lemma r_core_half_diagonals_pos {k u q v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    0 < rCoreHalfDiagonalA k u q v ∧
      0 < rCoreHalfDiagonalB k u q v ∧
      0 < rCoreHalfDiagonalC k u q v ∧
      0 < rCoreHalfDiagonalD k u q v := by
  obtain ⟨hA, hB, hC, hD⟩ :=
    r_core_sides_pos hk hu hq hv huk huq hvk hvq
  simp only [rCoreHalfDiagonalA, rCoreHalfDiagonalB,
    rCoreHalfDiagonalC, rCoreHalfDiagonalD]
  exact ⟨div_pos (mul_pos (mul_pos hk hA) hD) two_pos,
    div_pos (mul_pos (mul_pos hu hA) hB) two_pos,
    div_pos (mul_pos (mul_pos hq hB) hC) two_pos,
    div_pos (mul_pos (mul_pos hv hC) hD) two_pos⟩

/-- The named core sides are the four distances between consecutive named
orthogonal half-diagonals. -/
theorem r_core_side_half_diagonal_squares {k u q v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    rCoreSideA k u q v ^ 2 =
        rCoreHalfDiagonalA k u q v ^ 2 + rCoreHalfDiagonalB k u q v ^ 2 ∧
      rCoreSideB k u q v ^ 2 =
        rCoreHalfDiagonalB k u q v ^ 2 + rCoreHalfDiagonalC k u q v ^ 2 ∧
      rCoreSideC k u q v ^ 2 =
        rCoreHalfDiagonalC k u q v ^ 2 + rCoreHalfDiagonalD k u q v ^ 2 ∧
      rCoreSideD k u q v ^ 2 =
        rCoreHalfDiagonalD k u q v ^ 2 + rCoreHalfDiagonalA k u q v ^ 2 := by
  obtain ⟨hA, hB, hC, hD⟩ :=
    r_core_sides_pos hk hu hq hv huk huq hvk hvq
  have hDelta := orthogonal_delta_pos_of_strict_alternation
    hk hu hq hv huk huq hvk hvq
  have hqv := square_sub_pos hv hvq
  have hkv := square_sub_pos hv hvk
  have hku := square_sub_pos hu huk
  have hqu := square_sub_pos hu huq
  have hAroot := r_core_side_a_sq hDelta.le hqv.le
  have hBroot := r_core_side_b_sq hDelta.le hkv.le
  have hCroot := r_core_side_c_sq hDelta.le hku.le
  have hDroot := r_core_side_d_sq hDelta.le hqu.le
  have hasq : rCoreHalfDiagonalA k u q v ^ 2 =
      k ^ 2 * rCoreSideA k u q v ^ 2 * rCoreSideD k u q v ^ 2 / 4 := by
    change (k * rCoreSideA k u q v * rCoreSideD k u q v / 2) ^ 2 = _
    ring
  have hbsq : rCoreHalfDiagonalB k u q v ^ 2 =
      u ^ 2 * rCoreSideA k u q v ^ 2 * rCoreSideB k u q v ^ 2 / 4 := by
    change (u * rCoreSideA k u q v * rCoreSideB k u q v / 2) ^ 2 = _
    ring
  have hcsq : rCoreHalfDiagonalC k u q v ^ 2 =
      q ^ 2 * rCoreSideB k u q v ^ 2 * rCoreSideC k u q v ^ 2 / 4 := by
    change (q * rCoreSideB k u q v * rCoreSideC k u q v / 2) ^ 2 = _
    ring
  have hdsq : rCoreHalfDiagonalD k u q v ^ 2 =
      v ^ 2 * rCoreSideC k u q v ^ 2 * rCoreSideD k u q v ^ 2 / 4 := by
    change (v * rCoreSideC k u q v * rCoreSideD k u q v / 2) ^ 2 = _
    ring
  constructor
  · rw [hAroot, hasq, hbsq, hAroot, hBroot, hDroot]
    exact orthogonalA2_identity hDelta.ne'
  · constructor
    · rw [hBroot, hbsq, hcsq, hAroot, hBroot, hCroot]
      exact orthogonalB2_identity hDelta.ne'
    · constructor
      · rw [hCroot, hcsq, hdsq, hBroot, hCroot, hDroot]
        exact orthogonalC2_identity hDelta.ne'
      · rw [hDroot, hdsq, hasq, hAroot, hCroot, hDroot]
        exact orthogonalD2_identity hDelta.ne'

/-- Strict alternation makes the retained edge pair transverse throughout
the normalized orthogonal core family. -/
theorem r_core_first_last_cross_ne_zero {k u q v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    crossR2 0 (rCoreFirstEdge k u q v) (rCoreLastEdge k u q v) ≠ 0 := by
  obtain ⟨ha, hb, _, hd⟩ :=
    r_core_half_diagonals_pos hk hu hq hv huk huq hvk hvq
  exact crossR2_orthogonal_quad_first_last_ne_zero ha hb hd

/-- The named side family is the literal strict moderate-arc realization
supplied by the orthogonal four-point construction. -/
theorem r_core_realization_data {k u q v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    ModerateArc 0 (fourProfile k u q v)
        (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
          (rCoreSideC k u q v) (rCoreSideD k u q v)) ∧
      closureGap (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) = 0 ∧
      turningSum (fourProfile k u q v)
          (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
            (rCoreSideC k u q v) (rCoreSideD k u q v)) = 2 * Real.pi ∧
      IsSimplePolygon (polygonR2 (fourProfile k u q v)
        (fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
          (rCoreSideC k u q v) (rCoreSideD k u q v))) := by
  let A := rCoreSideA k u q v
  let B := rCoreSideB k u q v
  let C := rCoreSideC k u q v
  let D := rCoreSideD k u q v
  let a := rCoreHalfDiagonalA k u q v
  let b := rCoreHalfDiagonalB k u q v
  let c := rCoreHalfDiagonalC k u q v
  let d := rCoreHalfDiagonalD k u q v
  have hDelta := orthogonal_delta_pos_of_strict_alternation
    hk hu hq hv huk huq hvk hvq
  have hqv := square_sub_pos hv hvq
  have hkv := square_sub_pos hv hvk
  have hku := square_sub_pos hu huk
  have hqu := square_sub_pos hu huq
  obtain ⟨hA, hB, hC, hD⟩ : 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D := by
    simpa only [A, B, C, D] using
      r_core_sides_pos hk hu hq hv huk huq hvk hvq
  obtain ⟨ha, hb, hc, hd⟩ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d := by
    simpa only [a, b, c, d] using
      r_core_half_diagonals_pos hk hu hq hv huk huq hvk hvq
  have hAroot : A ^ 2 = orthogonalA2 k u q v := by
    simpa only [A] using r_core_side_a_sq hDelta.le hqv.le
  have hBroot : B ^ 2 = orthogonalB2 k u q v := by
    simpa only [B] using r_core_side_b_sq hDelta.le hkv.le
  have hCroot : C ^ 2 = orthogonalC2 k u q v := by
    simpa only [C] using r_core_side_c_sq hDelta.le hku.le
  have hDroot : D ^ 2 = orthogonalD2 k u q v := by
    simpa only [D] using r_core_side_d_sq hDelta.le hqu.le
  have hasq : a ^ 2 = k ^ 2 * A ^ 2 * D ^ 2 / 4 := by
    change (k * A * D / 2) ^ 2 = k ^ 2 * A ^ 2 * D ^ 2 / 4
    ring
  have hbsq : b ^ 2 = u ^ 2 * A ^ 2 * B ^ 2 / 4 := by
    change (u * A * B / 2) ^ 2 = u ^ 2 * A ^ 2 * B ^ 2 / 4
    ring
  have hcsq : c ^ 2 = q ^ 2 * B ^ 2 * C ^ 2 / 4 := by
    change (q * B * C / 2) ^ 2 = q ^ 2 * B ^ 2 * C ^ 2 / 4
    ring
  have hdsq : d ^ 2 = v ^ 2 * C ^ 2 * D ^ 2 / 4 := by
    change (v * C * D / 2) ^ 2 = v ^ 2 * C ^ 2 * D ^ 2 / 4
    ring
  have hAsq : A ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hAroot, hasq, hbsq, hAroot, hBroot, hDroot]
    exact orthogonalA2_identity hDelta.ne'
  have hBsq : B ^ 2 = b ^ 2 + c ^ 2 := by
    rw [hBroot, hbsq, hcsq, hAroot, hBroot, hCroot]
    exact orthogonalB2_identity hDelta.ne'
  have hCsq : C ^ 2 = c ^ 2 + d ^ 2 := by
    rw [hCroot, hcsq, hdsq, hBroot, hCroot, hDroot]
    exact orthogonalC2_identity hDelta.ne'
  have hDsq : D ^ 2 = d ^ 2 + a ^ 2 := by
    rw [hDroot, hdsq, hasq, hAroot, hCroot, hDroot]
    exact orthogonalD2_identity hDelta.ne'
  have hkEq : 2 * a / (A * D) = k := by
    change 2 * (k * A * D / 2) / (A * D) = k
    field_simp [hA.ne', hD.ne']
  have huEq : 2 * b / (A * B) = u := by
    change 2 * (u * A * B / 2) / (A * B) = u
    field_simp [hA.ne', hB.ne']
  have hqEq : 2 * c / (B * C) = q := by
    change 2 * (q * B * C / 2) / (B * C) = q
    field_simp [hB.ne', hC.ne']
  have hvEq : 2 * d / (C * D) = v := by
    change 2 * (v * C * D / 2) / (C * D) = v
    field_simp [hC.ne', hD.ne']
  exact orthogonal_realization_data ha hb hc hd hA hB hC hD
    hAsq hBsq hCsq hDsq hkEq huEq hqEq hvEq

/-- Once the normalized core has made one full turn, its last developed edge
lies on the positive real axis. -/
theorem r_core_developed_edge_three_eq_side_d {k u q v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    rCoreDevelopedEdge k u q v 3 = rCoreSideD k u q v := by
  let coreK := fourProfile k u q v
  let coreL := fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
    (rCoreSideC k u q v) (rCoreSideD k u q v)
  have hcore : turningSum coreK coreL = 2 * Real.pi := by
    simpa only [coreK, coreL] using
      (r_core_realization_data hk hu hq hv huk huq hvk hvq).2.2.1
  have hsum :
      turningAngle 0 coreK coreL 0 + turningAngle 0 coreK coreL 1 +
          turningAngle 0 coreK coreL 2 + turningAngle 0 coreK coreL 3 =
        2 * Real.pi := by
    rw [← hcore]
    unfold turningSum
    rw [← sum_range_natCast_add (turningAngle 0 coreK coreL) 0]
    norm_num [Finset.sum_range_succ]
  have hphase :
      unitPhase (turningAngle 0 coreK coreL 0) *
            unitPhase (turningAngle 0 coreK coreL 1) *
          unitPhase (turningAngle 0 coreK coreL 2) *
        unitPhase (turningAngle 0 coreK coreL 3) = 1 := by
    rw [← unitPhase_add, ← unitPhase_add, ← unitPhase_add, hsum]
    calc
      unitPhase (2 * Real.pi) = unitPhase (0 + 2 * Real.pi) := by
        simp only [zero_add]
      _ = unitPhase 0 := unitPhase_add_two_pi 0
      _ = 1 := by simp [unitPhase]
  rw [r_core_developed_edge_three]
  change (rCoreSideD k u q v : ℂ) *
    (unitPhase (turningAngle 0 coreK coreL 0) *
          unitPhase (turningAngle 0 coreK coreL 1) *
        unitPhase (turningAngle 0 coreK coreL 2) *
      unitPhase (turningAngle 0 coreK coreL 3)) = _
  rw [hphase, mul_one]

/-- The first and last developed edges, in the actual closure frame, are
transverse throughout the strict orthogonal core family. -/
theorem r_core_developed_first_last_cross_ne_zero {k u q v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    crossR2 0 (rCoreDevelopedEdge k u q v 0)
      (rCoreDevelopedEdge k u q v 3) ≠ 0 := by
  let coreK := fourProfile k u q v
  let coreL := fourProfile (rCoreSideA k u q v) (rCoreSideB k u q v)
    (rCoreSideC k u q v) (rCoreSideD k u q v)
  have hMA : ModerateArc 0 coreK coreL := by
    simpa only [coreK, coreL] using
      (r_core_realization_data hk hu hq hv huk huq hvk hvq).1
  have htheta0 : 0 < turningAngle 0 coreK coreL 0 := by
    apply turningAngle_pos hMA
    change 0 < k
    exact hk
  have hthetaPi : turningAngle 0 coreK coreL 0 < Real.pi :=
    lt_of_abs_lt (abs_turningAngle_lt_pi hMA 0)
  have hsin : 0 < Real.sin (turningAngle 0 coreK coreL 0) :=
    Real.sin_pos_of_pos_of_lt_pi htheta0 hthetaPi
  have hA : 0 < rCoreSideA k u q v :=
    (r_core_sides_pos hk hu hq hv huk huq hvk hvq).1
  have hD : 0 < rCoreSideD k u q v :=
    (r_core_sides_pos hk hu hq hv huk huq hvk hvq).2.2.2
  rw [r_core_developed_edge_three_eq_side_d hk hu hq hv huk huq hvk hvq,
    r_core_developed_edge_zero]
  change crossR2 0
    ((rCoreSideA k u q v : ℂ) * unitPhase (turningAngle 0 coreK coreL 0))
      (rCoreSideD k u q v : ℂ) ≠ 0
  rw [unitPhase_eq_cos_add_sin_mul_I]
  simp only [crossR2, sub_zero, Complex.mul_re, Complex.ofReal_re,
    Complex.add_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, Complex.mul_im,
    Complex.add_im, mul_one]
  simpa only [zero_add, zero_sub] using
    neg_ne_zero.mpr (ne_of_gt (mul_pos (mul_pos hA hsin) hD))

/-- The four named developed edge vectors form a closed core. -/
theorem r_core_developed_edges_close {k u q v : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (huk : u < k) (huq : u < q) (hvk : v < k) (hvq : v < q) :
    rCoreDevelopedEdge k u q v 0 + rCoreDevelopedEdge k u q v 1 +
        rCoreDevelopedEdge k u q v 2 + rCoreDevelopedEdge k u q v 3 = 0 := by
  have hclose :=
    (r_core_realization_data hk hu hq hv huk huq hvk hvq).2.1
  rw [closure_gap_four_unit_phase] at hclose
  simpa only [r_core_developed_edge_zero, r_core_developed_edge_one,
    r_core_developed_edge_two, r_core_developed_edge_three,
    fourProfile_zero, fourProfile_one, fourProfile_two,
    fourProfile_three] using hclose

@[simp] lemma r_core_side_a_half_at_one (u q v : ℝ) :
    rCoreSideA 1 u q v / 2 =
      √(q ^ 2 - v ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) := by
  simp [rCoreSideA, orthogonalDelta]
  ring

@[simp] lemma r_core_side_b_half_at_one (u q v : ℝ) :
    rCoreSideB 1 u q v / 2 =
      √(1 - v ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) := by
  simp [rCoreSideB, orthogonalDelta]
  ring

@[simp] lemma r_core_side_c_half_at_one (u q v : ℝ) :
    rCoreSideC 1 u q v / 2 =
      √(1 - u ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) := by
  simp [rCoreSideC, orthogonalDelta]
  ring

@[simp] lemma r_core_side_d_half_at_one (u q v : ℝ) :
    rCoreSideD 1 u q v / 2 =
      √(q ^ 2 - u ^ 2) / √(q ^ 2 - u ^ 2 * v ^ 2) := by
  simp [rCoreSideD, orthogonalDelta]
  ring

end Gluck.Discrete.N6TypeAThreeCell
