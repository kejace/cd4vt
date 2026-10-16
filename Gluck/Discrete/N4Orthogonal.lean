/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.TangentChord

/-!
# The orthogonal-diagonal realization for four vertices

An alternating positive curvature profile on `ZMod 4` has an explicit convex
quadrilateral realization.  Its diagonals are the coordinate axes.  The
construction is independent of the closing-map machinery used for larger
polygons.
-/

@[expose] public section

namespace Gluck.Discrete

open scoped Real

/-- Four cyclic values, in their natural order on `ZMod 4`. -/
def fourProfile (x₀ x₁ x₂ x₃ : ℝ) : ZMod 4 → ℝ := fun i =>
  ![x₀, x₁, x₂, x₃] ⟨i.val, i.val_lt⟩

/-- The positively oriented quadrilateral with orthogonal coordinate-axis
diagonals and positive diagonal half-lengths `a,b,c,d`. -/
def orthogonalQuad (a b c d : ℝ) : ZMod 4 → ℂ := fun i =>
  ![(a : ℂ), (b : ℂ) * Complex.I, -(c : ℂ), -(d : ℂ) * Complex.I]
    ⟨i.val, i.val_lt⟩

/-- A segment whose endpoints lie on the real and imaginary coordinate axes. -/
def axisSegment (x y : ℝ) : Set ℂ :=
  segment ℝ (x : ℂ) ((y : ℂ) * Complex.I)

private lemma axisSegment_data {x y : ℝ} {z : ℂ} (hz : z ∈ axisSegment x y) :
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ r + s = 1 ∧ z.re = r * x ∧ z.im = s * y := by
  obtain ⟨r, s, hr, hs, hrs, hz⟩ := hz
  refine ⟨r, s, hr, hs, hrs, ?_, ?_⟩
  · rw [← hz]
    simp
  · rw [← hz]
    simp

private lemma axisSegment_inter_same_im {xₚ xₙ y : ℝ} (hxₚ : 0 < xₚ) (hxₙ : xₙ < 0) :
    axisSegment xₚ y ∩ axisSegment xₙ y = {((y : ℝ) : ℂ) * Complex.I} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨right_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩, ?_⟩
  rintro z ⟨hzₚ, hzₙ⟩
  obtain ⟨rₚ, sₚ, hrₚ, hsₚ, hrsₚ, hreₚ, himₚ⟩ := axisSegment_data hzₚ
  obtain ⟨rₙ, sₙ, hrₙ, hsₙ, hrsₙ, hreₙ, himₙ⟩ := axisSegment_data hzₙ
  have hzre : z.re = 0 := by
    apply le_antisymm
    · rw [hreₙ]
      exact mul_nonpos_of_nonneg_of_nonpos hrₙ hxₙ.le
    · rw [hreₚ]
      exact mul_nonneg hrₚ hxₚ.le
  have hrₚ0 : rₚ = 0 := by
    have hmul : rₚ * xₚ = 0 := by rw [← hreₚ, hzre]
    exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hxₚ)
  have hsₚ1 : sₚ = 1 := by linarith
  apply Complex.ext
  · simpa using hzre
  · rw [himₚ, hsₚ1, one_mul]
    simp

private lemma axisSegment_inter_same_re {x yₚ yₙ : ℝ} (hyₚ : 0 < yₚ) (hyₙ : yₙ < 0) :
    axisSegment x yₚ ∩ axisSegment x yₙ = {(x : ℂ)} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩, ?_⟩
  rintro z ⟨hzₚ, hzₙ⟩
  obtain ⟨rₚ, sₚ, hrₚ, hsₚ, hrsₚ, hreₚ, himₚ⟩ := axisSegment_data hzₚ
  obtain ⟨rₙ, sₙ, hrₙ, hsₙ, hrsₙ, hreₙ, himₙ⟩ := axisSegment_data hzₙ
  have hzim : z.im = 0 := by
    apply le_antisymm
    · rw [himₙ]
      exact mul_nonpos_of_nonneg_of_nonpos hsₙ hyₙ.le
    · rw [himₚ]
      exact mul_nonneg hsₚ hyₚ.le
  have hsₚ0 : sₚ = 0 := by
    have hmul : sₚ * yₚ = 0 := by rw [← himₚ, hzim]
    exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hyₚ)
  have hrₚ1 : rₚ = 1 := by linarith
  apply Complex.ext
  · rw [hreₚ, hrₚ1, one_mul]
    simp
  · simpa using hzim

private lemma axisSegment_inter_opposite {xₚ yₚ xₙ yₙ : ℝ}
    (hxₚ : 0 < xₚ) (hxₙ : xₙ < 0) (hy : yₚ ≠ yₙ) :
    axisSegment xₚ yₚ ∩ axisSegment xₙ yₙ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzₚ, hzₙ⟩
  obtain ⟨rₚ, sₚ, hrₚ, hsₚ, hrsₚ, hreₚ, himₚ⟩ := axisSegment_data hzₚ
  obtain ⟨rₙ, sₙ, hrₙ, hsₙ, hrsₙ, hreₙ, himₙ⟩ := axisSegment_data hzₙ
  have hzre : z.re = 0 := by
    apply le_antisymm
    · rw [hreₙ]
      exact mul_nonpos_of_nonneg_of_nonpos hrₙ hxₙ.le
    · rw [hreₚ]
      exact mul_nonneg hrₚ hxₚ.le
  have hrₚ0 : rₚ = 0 := by
    have hmul : rₚ * xₚ = 0 := by rw [← hreₚ, hzre]
    exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hxₚ)
  have hrₙ0 : rₙ = 0 := by
    have hmul : rₙ * xₙ = 0 := by rw [← hreₙ, hzre]
    exact (mul_eq_zero.mp hmul).resolve_right (ne_of_lt hxₙ)
  have hsₚ1 : sₚ = 1 := by linarith
  have hsₙ1 : sₙ = 1 := by linarith
  have heq : yₚ = yₙ := by
    calc
      yₚ = z.im := by rw [himₚ, hsₚ1, one_mul]
      _ = yₙ := by rw [himₙ, hsₙ1, one_mul]
  exact hy heq

@[simp] lemma fourProfile_zero (x₀ x₁ x₂ x₃ : ℝ) :
    fourProfile x₀ x₁ x₂ x₃ 0 = x₀ := by
  rfl

@[simp] lemma fourProfile_one (x₀ x₁ x₂ x₃ : ℝ) :
    fourProfile x₀ x₁ x₂ x₃ 1 = x₁ := by
  rfl

@[simp] lemma fourProfile_two (x₀ x₁ x₂ x₃ : ℝ) :
    fourProfile x₀ x₁ x₂ x₃ 2 = x₂ := by
  rfl

@[simp] lemma fourProfile_three (x₀ x₁ x₂ x₃ : ℝ) :
    fourProfile x₀ x₁ x₂ x₃ 3 = x₃ := by
  rfl

@[simp] lemma orthogonalQuad_zero (a b c d : ℝ) :
    orthogonalQuad a b c d 0 = a := by
  rfl

@[simp] lemma orthogonalQuad_one (a b c d : ℝ) :
    orthogonalQuad a b c d 1 = (b : ℂ) * Complex.I := by
  rfl

@[simp] lemma orthogonalQuad_two (a b c d : ℝ) :
    orthogonalQuad a b c d 2 = -(c : ℂ) := by
  rfl

@[simp] lemma orthogonalQuad_three (a b c d : ℝ) :
    orthogonalQuad a b c d 3 = -(d : ℂ) * Complex.I := by
  rfl

private lemma orthogonalQuad_edge_zero (a b c d : ℝ) :
    segment ℝ (orthogonalQuad a b c d 0) (orthogonalQuad a b c d 1) =
      axisSegment a b := by
  rw [orthogonalQuad_zero, orthogonalQuad_one]
  rfl

private lemma orthogonalQuad_edge_one (a b c d : ℝ) :
    segment ℝ (orthogonalQuad a b c d 1) (orthogonalQuad a b c d 2) =
      axisSegment (-c) b := by
  rw [orthogonalQuad_one, orthogonalQuad_two]
  simp [axisSegment, segment_symm]

private lemma orthogonalQuad_edge_two (a b c d : ℝ) :
    segment ℝ (orthogonalQuad a b c d 2) (orthogonalQuad a b c d 3) =
      axisSegment (-c) (-d) := by
  rw [orthogonalQuad_two, orthogonalQuad_three]
  simp [axisSegment]

private lemma orthogonalQuad_edge_three (a b c d : ℝ) :
    segment ℝ (orthogonalQuad a b c d 3) (orthogonalQuad a b c d 0) =
      axisSegment a (-d) := by
  rw [orthogonalQuad_three, orthogonalQuad_zero]
  simp [axisSegment, segment_symm]

private lemma zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i
  decide

private lemma orthogonalQuad_edge_ne {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (i : ZMod 4) :
    orthogonalQuad a b c d i ≠ orthogonalQuad a b c d (i + 1) := by
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · rw [show (0 : ZMod 4) + 1 = 1 by norm_num, orthogonalQuad_zero, orthogonalQuad_one]
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  · rw [show (1 : ZMod 4) + 1 = 2 by norm_num, orthogonalQuad_one, orthogonalQuad_two]
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  · rw [show (2 : ZMod 4) + 1 = 3 by norm_num, orthogonalQuad_two, orthogonalQuad_three]
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  · rw [show (3 : ZMod 4) + 1 = 0 by decide, orthogonalQuad_three,
      orthogonalQuad_zero]
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith

private lemma orthogonalQuad_consecutive_inter {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (i : ZMod 4) :
    segment ℝ (orthogonalQuad a b c d i) (orthogonalQuad a b c d (i + 1)) ∩
        segment ℝ (orthogonalQuad a b c d (i + 1))
          (orthogonalQuad a b c d (i + 1 + 1)) =
      {orthogonalQuad a b c d (i + 1)} := by
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · change segment ℝ (orthogonalQuad a b c d 0) (orthogonalQuad a b c d 1) ∩
        segment ℝ (orthogonalQuad a b c d 1) (orthogonalQuad a b c d 2) =
      {orthogonalQuad a b c d 1}
    rw [orthogonalQuad_edge_zero, orthogonalQuad_edge_one, orthogonalQuad_one]
    exact axisSegment_inter_same_im ha (by linarith)
  · change segment ℝ (orthogonalQuad a b c d 1) (orthogonalQuad a b c d 2) ∩
        segment ℝ (orthogonalQuad a b c d 2) (orthogonalQuad a b c d 3) =
      {orthogonalQuad a b c d 2}
    rw [orthogonalQuad_edge_one, orthogonalQuad_edge_two, orthogonalQuad_two]
    simpa using axisSegment_inter_same_re (x := -c) hb (by linarith : -d < 0)
  · change segment ℝ (orthogonalQuad a b c d 2) (orthogonalQuad a b c d 3) ∩
        segment ℝ (orthogonalQuad a b c d 3) (orthogonalQuad a b c d 0) =
      {orthogonalQuad a b c d 3}
    rw [orthogonalQuad_edge_two, orthogonalQuad_edge_three, orthogonalQuad_three,
      Set.inter_comm]
    simpa using axisSegment_inter_same_im ha (by linarith : -c < 0) (y := -d)
  · change segment ℝ (orthogonalQuad a b c d 3) (orthogonalQuad a b c d 0) ∩
        segment ℝ (orthogonalQuad a b c d 0) (orthogonalQuad a b c d 1) =
      {orthogonalQuad a b c d 0}
    rw [orthogonalQuad_edge_three, orthogonalQuad_edge_zero, orthogonalQuad_zero,
      Set.inter_comm]
    exact axisSegment_inter_same_re hb (by linarith)

private lemma orthogonalQuad_nonadjacent_disjoint {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (i j : ZMod 4) (hij : i ≠ j) (hij1 : i + 1 ≠ j) (hji1 : j + 1 ≠ i) :
    segment ℝ (orthogonalQuad a b c d i) (orthogonalQuad a b c d (i + 1)) ∩
        segment ℝ (orthogonalQuad a b c d j) (orthogonalQuad a b c d (j + 1)) = ∅ := by
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · rcases zmod4_cases j with rfl | rfl | rfl | rfl
    · exact (hij rfl).elim
    · exact (hij1 (by norm_num)).elim
    · change segment ℝ (orthogonalQuad a b c d 0) (orthogonalQuad a b c d 1) ∩
          segment ℝ (orthogonalQuad a b c d 2) (orthogonalQuad a b c d 3) = ∅
      rw [orthogonalQuad_edge_zero, orthogonalQuad_edge_two]
      exact axisSegment_inter_opposite ha (by linarith) (by linarith)
    · exact (hji1 (by decide)).elim
  · rcases zmod4_cases j with rfl | rfl | rfl | rfl
    · exact (hji1 (by norm_num)).elim
    · exact (hij rfl).elim
    · exact (hij1 (by norm_num)).elim
    · change segment ℝ (orthogonalQuad a b c d 1) (orthogonalQuad a b c d 2) ∩
          segment ℝ (orthogonalQuad a b c d 3) (orthogonalQuad a b c d 0) = ∅
      rw [orthogonalQuad_edge_one, orthogonalQuad_edge_three, Set.inter_comm]
      exact axisSegment_inter_opposite ha (by linarith) (by linarith)
  · rcases zmod4_cases j with rfl | rfl | rfl | rfl
    · change segment ℝ (orthogonalQuad a b c d 2) (orthogonalQuad a b c d 3) ∩
          segment ℝ (orthogonalQuad a b c d 0) (orthogonalQuad a b c d 1) = ∅
      rw [orthogonalQuad_edge_two, orthogonalQuad_edge_zero, Set.inter_comm]
      exact axisSegment_inter_opposite ha (by linarith) (by linarith)
    · exact (hji1 (by norm_num)).elim
    · exact (hij rfl).elim
    · exact (hij1 (by norm_num)).elim
  · rcases zmod4_cases j with rfl | rfl | rfl | rfl
    · exact (hij1 (by decide)).elim
    · change segment ℝ (orthogonalQuad a b c d 3) (orthogonalQuad a b c d 0) ∩
          segment ℝ (orthogonalQuad a b c d 1) (orthogonalQuad a b c d 2) = ∅
      rw [orthogonalQuad_edge_three, orthogonalQuad_edge_one]
      exact axisSegment_inter_opposite ha (by linarith) (by linarith)
    · exact (hji1 (by norm_num)).elim
    · exact (hij rfl).elim

/-- An orthogonal-axis quadrilateral with positive half-diagonals is simple. -/
theorem isSimplePolygon_orthogonalQuad {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    IsSimplePolygon (orthogonalQuad a b c d) :=
  ⟨orthogonalQuad_edge_ne ha hb hc hd,
    orthogonalQuad_consecutive_inter ha hb hc hd,
    orthogonalQuad_nonadjacent_disjoint ha hb hc hd⟩

private lemma dist_real_mul_I {a b A : ℝ} (hA : 0 ≤ A)
    (hAsq : A ^ 2 = a ^ 2 + b ^ 2) :
    dist (a : ℂ) ((b : ℂ) * Complex.I) = A := by
  rw [dist_eq_norm]
  have hs := Complex.sq_norm ((a : ℂ) - (b : ℂ) * Complex.I)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, zero_sub] at hs
  nlinarith [norm_nonneg ((a : ℂ) - (b : ℂ) * Complex.I)]

private lemma signedMenger_orthogonal_zero {a b d A D : ℝ}
    (_ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hA : 0 < A) (hD : 0 < D)
    (hAsq : A ^ 2 = a ^ 2 + b ^ 2) (hDsq : D ^ 2 = d ^ 2 + a ^ 2) :
    signedMengerR2 (-(d : ℂ) * Complex.I) a ((b : ℂ) * Complex.I) =
      2 * a / (A * D) := by
  have hdistA : dist (a : ℂ) ((b : ℂ) * Complex.I) = A :=
    dist_real_mul_I hA.le hAsq
  have hdistD : dist (-(d : ℂ) * Complex.I) a = D := by
    rw [dist_comm]
    have heq : -(d : ℂ) * Complex.I = ((-d : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [heq]
    apply dist_real_mul_I hD.le
    nlinarith
  have hdistBD : dist ((b : ℂ) * Complex.I) (-(d : ℂ) * Complex.I) = b + d := by
    rw [dist_eq_norm]
    have heq : (b : ℂ) * Complex.I - -(d : ℂ) * Complex.I = ((b + d : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (add_pos hb hd)]
    simp
  rw [signedMengerR2]
  simp only [crossR2, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, zero_sub, hdistD, hdistA, hdistBD]
  have hne : b + d ≠ 0 := ne_of_gt (add_pos hb hd)
  field_simp
  ring

private lemma signedMenger_orthogonal_one {a b c A B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hA : 0 < A) (hB : 0 < B)
    (hAsq : A ^ 2 = a ^ 2 + b ^ 2) (hBsq : B ^ 2 = b ^ 2 + c ^ 2) :
    signedMengerR2 a ((b : ℂ) * Complex.I) (-(c : ℂ)) =
      2 * b / (A * B) := by
  have hrot := signedMengerR2_rotate (u := -Complex.I) (by simp)
    (a : ℂ) ((b : ℂ) * Complex.I) (-(c : ℂ))
  have heq :
      signedMengerR2 (-(a : ℂ) * Complex.I) b ((c : ℂ) * Complex.I) =
        signedMengerR2 a ((b : ℂ) * Complex.I) (-(c : ℂ)) := by
    calc
      _ = signedMengerR2 (-Complex.I * (a : ℂ))
          (-Complex.I * ((b : ℂ) * Complex.I)) (-Complex.I * (-(c : ℂ))) := by
            congr 1 <;> apply Complex.ext <;> norm_num
      _ = _ := hrot
  rw [← heq]
  rw [signedMenger_orthogonal_zero hb hc ha hB hA hBsq (by nlinarith)]
  ring

private lemma signedMenger_orthogonal_two {b c d B C : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hB : 0 < B) (hC : 0 < C)
    (hBsq : B ^ 2 = b ^ 2 + c ^ 2) (hCsq : C ^ 2 = c ^ 2 + d ^ 2) :
    signedMengerR2 ((b : ℂ) * Complex.I) (-(c : ℂ))
        (-(d : ℂ) * Complex.I) = 2 * c / (B * C) := by
  have hrot := signedMengerR2_rotate (u := (-1 : ℂ)) (by simp)
    ((b : ℂ) * Complex.I) (-(c : ℂ)) (-(d : ℂ) * Complex.I)
  have heq :
      signedMengerR2 (-(b : ℂ) * Complex.I) c ((d : ℂ) * Complex.I) =
        signedMengerR2 ((b : ℂ) * Complex.I) (-(c : ℂ))
          (-(d : ℂ) * Complex.I) := by
    simpa using hrot
  rw [← heq]
  rw [signedMenger_orthogonal_zero hc hd hb hC hB hCsq (by nlinarith)]
  ring

private lemma signedMenger_orthogonal_three {a c d C D : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (hC : 0 < C) (hD : 0 < D)
    (hCsq : C ^ 2 = c ^ 2 + d ^ 2) (hDsq : D ^ 2 = d ^ 2 + a ^ 2) :
    signedMengerR2 (-(c : ℂ)) (-(d : ℂ) * Complex.I) a =
      2 * d / (C * D) := by
  have hrot := signedMengerR2_rotate (u := Complex.I) (by simp)
    (-(c : ℂ)) (-(d : ℂ) * Complex.I) (a : ℂ)
  have heq :
      signedMengerR2 (-(c : ℂ) * Complex.I) d ((a : ℂ) * Complex.I) =
        signedMengerR2 (-(c : ℂ)) (-(d : ℂ) * Complex.I) a := by
    calc
      _ = signedMengerR2 (Complex.I * (-(c : ℂ)))
          (Complex.I * (-(d : ℂ) * Complex.I)) (Complex.I * (a : ℂ)) := by
            congr 1 <;> apply Complex.ext <;> norm_num
      _ = _ := hrot
  rw [← heq]
  rw [signedMenger_orthogonal_zero hd ha hc hD hC hDsq (by nlinarith)]
  ring

/-- Abstract orthogonal-diagonal realization criterion.  The four displayed
Pythagorean identities identify `A,B,C,D` with the side lengths, and the four
quotients are exactly the signed Menger curvatures. -/
theorem realizesMenger_fourProfile_of_orthogonal
    {k₀ k₁ k₂ k₃ a b c d A B C D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hAsq : A ^ 2 = a ^ 2 + b ^ 2) (hBsq : B ^ 2 = b ^ 2 + c ^ 2)
    (hCsq : C ^ 2 = c ^ 2 + d ^ 2) (hDsq : D ^ 2 = d ^ 2 + a ^ 2)
    (hk₀ : 2 * a / (A * D) = k₀) (hk₁ : 2 * b / (A * B) = k₁)
    (hk₂ : 2 * c / (B * C) = k₂) (hk₃ : 2 * d / (C * D) = k₃) :
    RealizesMenger (fourProfile k₀ k₁ k₂ k₃) := by
  refine ⟨orthogonalQuad a b c d, isSimplePolygon_orthogonalQuad ha hb hc hd, ?_⟩
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · change signedMengerR2 (orthogonalQuad a b c d 3) (orthogonalQuad a b c d 0)
        (orthogonalQuad a b c d 1) = k₀
    rw [orthogonalQuad_three, orthogonalQuad_zero, orthogonalQuad_one,
      signedMenger_orthogonal_zero ha hb hd hA hD hAsq (by nlinarith), hk₀]
  · change signedMengerR2 (orthogonalQuad a b c d 0) (orthogonalQuad a b c d 1)
        (orthogonalQuad a b c d 2) = k₁
    rw [orthogonalQuad_zero, orthogonalQuad_one, orthogonalQuad_two,
      signedMenger_orthogonal_one ha hb hc hA hB hAsq hBsq, hk₁]
  · change signedMengerR2 (orthogonalQuad a b c d 1) (orthogonalQuad a b c d 2)
        (orthogonalQuad a b c d 3) = k₂
    rw [orthogonalQuad_one, orthogonalQuad_two, orthogonalQuad_three,
      signedMenger_orthogonal_two hb hc hd hB hC hBsq hCsq, hk₂]
  · change signedMengerR2 (orthogonalQuad a b c d 2) (orthogonalQuad a b c d 3)
        (orthogonalQuad a b c d 0) = k₃
    rw [orthogonalQuad_two, orthogonalQuad_three, orthogonalQuad_zero,
      signedMenger_orthogonal_three ha hc hd hC hD hCsq hDsq, hk₃]

def orthogonalDelta (k₀ k₁ k₂ k₃ : ℝ) : ℝ :=
  k₀ ^ 2 * k₂ ^ 2 - k₁ ^ 2 * k₃ ^ 2

noncomputable def orthogonalA2 (k₀ k₁ k₂ k₃ : ℝ) : ℝ :=
  4 * (k₂ ^ 2 - k₃ ^ 2) / orthogonalDelta k₀ k₁ k₂ k₃

noncomputable def orthogonalB2 (k₀ k₁ k₂ k₃ : ℝ) : ℝ :=
  4 * (k₀ ^ 2 - k₃ ^ 2) / orthogonalDelta k₀ k₁ k₂ k₃

noncomputable def orthogonalC2 (k₀ k₁ k₂ k₃ : ℝ) : ℝ :=
  4 * (k₀ ^ 2 - k₁ ^ 2) / orthogonalDelta k₀ k₁ k₂ k₃

noncomputable def orthogonalD2 (k₀ k₁ k₂ k₃ : ℝ) : ℝ :=
  4 * (k₂ ^ 2 - k₁ ^ 2) / orthogonalDelta k₀ k₁ k₂ k₃

lemma orthogonalA2_identity {k₀ k₁ k₂ k₃ : ℝ}
    (hΔ : orthogonalDelta k₀ k₁ k₂ k₃ ≠ 0) :
    orthogonalA2 k₀ k₁ k₂ k₃ =
      k₀ ^ 2 * orthogonalA2 k₀ k₁ k₂ k₃ *
          orthogonalD2 k₀ k₁ k₂ k₃ / 4 +
        k₁ ^ 2 * orthogonalA2 k₀ k₁ k₂ k₃ *
          orthogonalB2 k₀ k₁ k₂ k₃ / 4 := by
  unfold orthogonalA2 orthogonalB2 orthogonalD2
  field_simp [hΔ]
  unfold orthogonalDelta
  ring

lemma orthogonalB2_identity {k₀ k₁ k₂ k₃ : ℝ}
    (hΔ : orthogonalDelta k₀ k₁ k₂ k₃ ≠ 0) :
    orthogonalB2 k₀ k₁ k₂ k₃ =
      k₁ ^ 2 * orthogonalA2 k₀ k₁ k₂ k₃ *
          orthogonalB2 k₀ k₁ k₂ k₃ / 4 +
        k₂ ^ 2 * orthogonalB2 k₀ k₁ k₂ k₃ *
          orthogonalC2 k₀ k₁ k₂ k₃ / 4 := by
  unfold orthogonalA2 orthogonalB2 orthogonalC2
  field_simp [hΔ]
  unfold orthogonalDelta
  ring

lemma orthogonalC2_identity {k₀ k₁ k₂ k₃ : ℝ}
    (hΔ : orthogonalDelta k₀ k₁ k₂ k₃ ≠ 0) :
    orthogonalC2 k₀ k₁ k₂ k₃ =
      k₂ ^ 2 * orthogonalB2 k₀ k₁ k₂ k₃ *
          orthogonalC2 k₀ k₁ k₂ k₃ / 4 +
        k₃ ^ 2 * orthogonalC2 k₀ k₁ k₂ k₃ *
          orthogonalD2 k₀ k₁ k₂ k₃ / 4 := by
  unfold orthogonalB2 orthogonalC2 orthogonalD2
  field_simp [hΔ]
  unfold orthogonalDelta
  ring

lemma orthogonalD2_identity {k₀ k₁ k₂ k₃ : ℝ}
    (hΔ : orthogonalDelta k₀ k₁ k₂ k₃ ≠ 0) :
    orthogonalD2 k₀ k₁ k₂ k₃ =
      k₃ ^ 2 * orthogonalC2 k₀ k₁ k₂ k₃ *
          orthogonalD2 k₀ k₁ k₂ k₃ / 4 +
        k₀ ^ 2 * orthogonalA2 k₀ k₁ k₂ k₃ *
          orthogonalD2 k₀ k₁ k₂ k₃ / 4 := by
  unfold orthogonalA2 orthogonalC2 orthogonalD2
  field_simp [hΔ]
  unfold orthogonalDelta
  ring

/-- **The four-vertex orthogonal-diagonal construction.**  If vertices `0,2`
carry the two strictly larger curvatures and vertices `1,3` the two strictly
smaller ones, the prescribed profile is realized by an explicit simple
orthogonal-diagonal quadrilateral. -/
theorem realizesMenger_fourProfile_of_strictAlternation
    {k₀ k₁ k₂ k₃ : ℝ}
    (hk₀ : 0 < k₀) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (h₁₀ : k₁ < k₀) (h₁₂ : k₁ < k₂)
    (h₃₀ : k₃ < k₀) (h₃₂ : k₃ < k₂) :
    RealizesMenger (fourProfile k₀ k₁ k₂ k₃) := by
  have hprod : k₁ * k₃ < k₀ * k₂ := by
    calc
      k₁ * k₃ < k₀ * k₃ := mul_lt_mul_of_pos_right h₁₀ hk₃
      _ < k₀ * k₂ := mul_lt_mul_of_pos_left h₃₂ hk₀
  have hΔ : 0 < orthogonalDelta k₀ k₁ k₂ k₃ := by
    have hfac : orthogonalDelta k₀ k₁ k₂ k₃ =
        (k₀ * k₂ - k₁ * k₃) * (k₀ * k₂ + k₁ * k₃) := by
      unfold orthogonalDelta
      ring
    rw [hfac]
    exact mul_pos (sub_pos.mpr hprod) (add_pos (mul_pos hk₀ hk₂) (mul_pos hk₁ hk₃))
  have hs₂₃ : 0 < k₂ ^ 2 - k₃ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₃₂) (add_pos hk₂ hk₃)]
  have hs₀₃ : 0 < k₀ ^ 2 - k₃ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₃₀) (add_pos hk₀ hk₃)]
  have hs₀₁ : 0 < k₀ ^ 2 - k₁ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₁₀) (add_pos hk₀ hk₁)]
  have hs₂₁ : 0 < k₂ ^ 2 - k₁ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₁₂) (add_pos hk₂ hk₁)]
  have hA2 : 0 < orthogonalA2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalA2
    exact div_pos (mul_pos (by norm_num) hs₂₃) hΔ
  have hB2 : 0 < orthogonalB2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalB2
    exact div_pos (mul_pos (by norm_num) hs₀₃) hΔ
  have hC2 : 0 < orthogonalC2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalC2
    exact div_pos (mul_pos (by norm_num) hs₀₁) hΔ
  have hD2 : 0 < orthogonalD2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalD2
    exact div_pos (mul_pos (by norm_num) hs₂₁) hΔ
  let A := Real.sqrt (orthogonalA2 k₀ k₁ k₂ k₃)
  let B := Real.sqrt (orthogonalB2 k₀ k₁ k₂ k₃)
  let C := Real.sqrt (orthogonalC2 k₀ k₁ k₂ k₃)
  let D := Real.sqrt (orthogonalD2 k₀ k₁ k₂ k₃)
  have hA : 0 < A := by exact Real.sqrt_pos.2 hA2
  have hB : 0 < B := by exact Real.sqrt_pos.2 hB2
  have hC : 0 < C := by exact Real.sqrt_pos.2 hC2
  have hD : 0 < D := by exact Real.sqrt_pos.2 hD2
  have hAroot : A ^ 2 = orthogonalA2 k₀ k₁ k₂ k₃ := by
    exact Real.sq_sqrt hA2.le
  have hBroot : B ^ 2 = orthogonalB2 k₀ k₁ k₂ k₃ := by
    exact Real.sq_sqrt hB2.le
  have hCroot : C ^ 2 = orthogonalC2 k₀ k₁ k₂ k₃ := by
    exact Real.sq_sqrt hC2.le
  have hDroot : D ^ 2 = orthogonalD2 k₀ k₁ k₂ k₃ := by
    exact Real.sq_sqrt hD2.le
  let a := k₀ * A * D / 2
  let b := k₁ * A * B / 2
  let c := k₂ * B * C / 2
  let d := k₃ * C * D / 2
  have ha : 0 < a := by exact div_pos (mul_pos (mul_pos hk₀ hA) hD) (by norm_num)
  have hb : 0 < b := by exact div_pos (mul_pos (mul_pos hk₁ hA) hB) (by norm_num)
  have hc : 0 < c := by exact div_pos (mul_pos (mul_pos hk₂ hB) hC) (by norm_num)
  have hd : 0 < d := by exact div_pos (mul_pos (mul_pos hk₃ hC) hD) (by norm_num)
  have hasq : a ^ 2 = k₀ ^ 2 * orthogonalA2 k₀ k₁ k₂ k₃ *
      orthogonalD2 k₀ k₁ k₂ k₃ / 4 := by
    dsimp [a]
    rw [div_pow, mul_pow, mul_pow, hAroot, hDroot]
    norm_num
  have hbsq : b ^ 2 = k₁ ^ 2 * orthogonalA2 k₀ k₁ k₂ k₃ *
      orthogonalB2 k₀ k₁ k₂ k₃ / 4 := by
    dsimp [b]
    rw [div_pow, mul_pow, mul_pow, hAroot, hBroot]
    norm_num
  have hcsq : c ^ 2 = k₂ ^ 2 * orthogonalB2 k₀ k₁ k₂ k₃ *
      orthogonalC2 k₀ k₁ k₂ k₃ / 4 := by
    dsimp [c]
    rw [div_pow, mul_pow, mul_pow, hBroot, hCroot]
    norm_num
  have hdsq : d ^ 2 = k₃ ^ 2 * orthogonalC2 k₀ k₁ k₂ k₃ *
      orthogonalD2 k₀ k₁ k₂ k₃ / 4 := by
    dsimp [d]
    rw [div_pow, mul_pow, mul_pow, hCroot, hDroot]
    norm_num
  have hAsq : A ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hAroot, hasq, hbsq]
    exact orthogonalA2_identity hΔ.ne'
  have hBsq : B ^ 2 = b ^ 2 + c ^ 2 := by
    rw [hBroot, hbsq, hcsq]
    exact orthogonalB2_identity hΔ.ne'
  have hCsq : C ^ 2 = c ^ 2 + d ^ 2 := by
    rw [hCroot, hcsq, hdsq]
    exact orthogonalC2_identity hΔ.ne'
  have hDsq : D ^ 2 = d ^ 2 + a ^ 2 := by
    rw [hDroot, hdsq, hasq]
    exact orthogonalD2_identity hΔ.ne'
  apply realizesMenger_fourProfile_of_orthogonal ha hb hc hd hA hB hC hD
    hAsq hBsq hCsq hDsq
  · dsimp [a]
    field_simp [hA.ne', hD.ne']
  · dsimp [b]
    field_simp [hA.ne', hB.ne']
  · dsimp [c]
    field_simp [hB.ne', hC.ne']
  · dsimp [d]
    field_simp [hC.ne', hD.ne']

/-- Profile-valued form of the four-vertex construction, for the chamber in
which indices `0,2` lie above a common level and indices `1,3` lie below it. -/
theorem realizesMenger_zmod4_of_alternating_level {k : ZMod 4 → ℝ} {q : ℝ}
    (hk : ∀ i, 0 < k i) (h₀ : q < k 0) (h₁ : k 1 < q)
    (h₂ : q < k 2) (h₃ : k 3 < q) : RealizesMenger k := by
  have hprofile : k = fourProfile (k 0) (k 1) (k 2) (k 3) := by
    funext i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp
  rw [hprofile]
  exact realizesMenger_fourProfile_of_strictAlternation (hk 0) (hk 1) (hk 2) (hk 3)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- Cyclic reindexing preserves signed-Menger realizability. -/
theorem realizesMenger_comp_add {n : ℕ} [NeZero n] {k : ZMod n → ℝ}
    (h : RealizesMenger k) (a : ZMod n) :
    RealizesMenger (fun i => k (i + a)) := by
  obtain ⟨v, hv, hk⟩ := h
  refine ⟨fun i => v (i + a), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      simpa only [add_assoc, add_comm (1 : ZMod n) a] using hv.1 (i + a)
    · intro i
      convert hv.2.1 (i + a) using 1
      all_goals simp only [add_assoc, add_left_comm, add_comm]
    · intro i j hij hi1j hj1i
      have hij' : i + a ≠ j + a := by
        exact fun h => hij (add_right_cancel h)
      have hi1j' : (i + a) + 1 ≠ j + a := by
        intro h
        apply hi1j
        apply add_right_cancel (b := a)
        calc
          (i + 1) + a = (i + a) + 1 := by ring
          _ = j + a := h
      have hj1i' : (j + a) + 1 ≠ i + a := by
        intro h
        apply hj1i
        apply add_right_cancel (b := a)
        calc
          (j + 1) + a = (j + a) + 1 := by ring
          _ = i + a := h
      convert hv.2.2 (i + a) (j + a) hij' hi1j' hj1i' using 1
      all_goals simp only [add_assoc, add_comm]
  · intro i
    simpa only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk (i + a)

end Gluck.Discrete
