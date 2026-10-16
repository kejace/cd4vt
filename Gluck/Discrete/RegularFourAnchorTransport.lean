module

public import Gluck.Discrete.RegularFourAnchor

/-!
# Transport of retained regular four-edge anchors

Positive curvature scaling transports the actual half-length witness and
its surjective original controller derivative. Reindexing identities are
stated off the zero set so that variable closure gauges are not discarded.
-/

@[expose] public section

namespace Gluck.Discrete

open FourActiveSlots

namespace FourActiveSlots.Frame

variable {n : ℕ} (F : Frame n)

/-- Scaling lengths in the original profile leaves all corner angles equal
to those of the scaled curvature profile. -/
theorem turns_scale_input (κ : ZMod n → ℝ) (s : ℝ) (L : Fin 4 → ℝ) :
    F.turns κ (s • L) = F.turns (fun i => s * κ i) L := by
  funext j
  fin_cases j <;>
    simp [turns, startArc, finishArc, start, finish, Pi.smul_apply, smul_eq_mul,
      mul_assoc, mul_left_comm, mul_comm]

/-- Exact input/output scaling, including the unchanged lifted turn. -/
theorem controller_scale_input (κ : ZMod n → ℝ) (s : ℝ) (L : Fin 4 → ℝ) :
    F.controller κ (s • L) =
      ((s : ℂ) * (F.controller (fun i => s * κ i) L).1,
        (F.controller (fun i => s * κ i) L).2) := by
  apply Prod.ext
  · simp only [controller, turns_scale_input, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  · simp only [controller, turns_scale_input]

/-- The scaled controller is a linear output change after a linear input
change. This holds for arbitrary signed four-length vectors. -/
theorem controller_scale (κ : ZMod n → ℝ) {s : ℝ} (hs : s ≠ 0) (L : Fin 4 → ℝ) :
    F.controller (fun i => s * κ i) L =
      (((s : ℂ)⁻¹) * (F.controller κ (s • L)).1, (F.controller κ (s • L)).2) := by
  rw [F.controller_scale_input]
  simp [hs]

/-- Derivative scaling for the actual native controller, with no appeal to
realizability or to an inferred geometric anchor. -/
theorem fderiv_controller_scale {κ : ZMod n → ℝ} {s : ℝ} (hs : s ≠ 0)
    {L : Fin 4 → ℝ} (hd : DifferentiableAt ℝ (F.controller κ) L) (v : Fin 4 → ℝ) :
    fderiv ℝ (F.controller (fun i => s * κ i)) (s⁻¹ • L) v =
      (((s : ℂ)⁻¹) * (fderiv ℝ (F.controller κ) L (s • v)).1,
        (fderiv ℝ (F.controller κ) L (s • v)).2) := by
  let S : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) := s • ContinuousLinearMap.id ℝ (Fin 4 → ℝ)
  have hSL : S (s⁻¹ • L) = L := by simp [S, hs]
  have hd' : HasFDerivAt (F.controller κ) (fderiv ℝ (F.controller κ) L)
      (S (s⁻¹ • L)) := by simpa only [hSL] using hd.hasFDerivAt
  have hf := hd'.comp (s⁻¹ • L) S.hasFDerivAt
  have hprod := (hf.fst.const_mul ((s : ℂ)⁻¹)).prodMk hf.snd
  have hfun : (fun X : Fin 4 → ℝ =>
      (((s : ℂ)⁻¹) * (F.controller κ (S X)).1, (F.controller κ (S X)).2)) =
      F.controller (fun i => s * κ i) := by
    funext X
    simpa [S] using (F.controller_scale κ hs X).symm
  change HasFDerivAt (fun X : Fin 4 → ℝ =>
      (((s : ℂ)⁻¹) * (F.controller κ (S X)).1, (F.controller κ (S X)).2)) _ _ at hprod
  rw [hfun] at hprod
  rw [hprod.fderiv]
  simp [S, ContinuousLinearMap.comp_apply, smul_eq_mul]

end FourActiveSlots.Frame

namespace RegularFourAnchor

variable {n : ℕ} {κ : ZMod n → ℝ}

/-- Surjectivity forces actual differentiability of the native controller. -/
theorem differentiableAt_controller (A : RegularFourAnchor κ) :
    DifferentiableAt ℝ (A.frame.controller κ) A.halfLengths := by
  by_contra h
  have hs := A.regular
  rw [fderiv_zero_of_not_differentiableAt h] at hs
  obtain ⟨v, hv⟩ := hs (0, 1)
  have := congrArg Prod.snd hv
  norm_num at this

/-- Positive similarity transport of the retained four-edge anchor itself.
The four actual edge indices do not change; lengths divide by s. -/
noncomputable def scale (A : RegularFourAnchor κ) {s : ℝ} (hs : 0 < s) :
    RegularFourAnchor (fun i => s * κ i) where
  frame := A.frame
  halfLengths := s⁻¹ • A.halfLengths
  positive j := mul_pos (inv_pos.mpr hs) (A.positive j)
  start_lt := by
    intro j
    have hproduct : A.frame.start (fun i => s * κ i) j * (s⁻¹ • A.halfLengths) j =
        A.frame.start κ j * A.halfLengths j := by
      simp [Frame.start, Pi.smul_apply, smul_eq_mul, hs.ne', mul_assoc, mul_left_comm]
    rw [hproduct]
    exact A.start_lt j
  finish_lt := by
    intro j
    have hproduct : A.frame.finish (fun i => s * κ i) j * (s⁻¹ • A.halfLengths) j =
        A.frame.finish κ j * A.halfLengths j := by
      simp [Frame.finish, Pi.smul_apply, smul_eq_mul, hs.ne', mul_assoc, mul_left_comm]
    rw [hproduct]
    exact A.finish_lt j
  zero := by
    rw [A.frame.controller_scale κ hs.ne']
    simp [hs.ne', A.zero]
  regular := by
    intro y
    obtain ⟨v, hv⟩ := A.regular ((s : ℂ) * y.1, y.2)
    refine ⟨s⁻¹ • v, ?_⟩
    rw [A.frame.fderiv_controller_scale hs.ne' A.differentiableAt_controller]
    simp [hs.ne', hv]

end RegularFourAnchor

namespace FourActiveSlots

/-- One cyclic relabeling of the four retained edges. -/
def rotateFour {α : Type*} (v : Fin 4 → α) : Fin 4 → α := ![v 1, v 2, v 3, v 0]

/-- Reversal of the four retained edge labels. -/
def reverseFour {α : Type*} (v : Fin 4 → α) : Fin 4 → α := ![v 3, v 2, v 1, v 0]

/-- Native closure and lifted turn from four lengths and four corner turns. -/
noncomputable def slotController (L θ : Fin 4 → ℝ) : ℂ × ℝ :=
  ((L 0 : ℂ) + (L 1 : ℂ) * unitPhase (θ 1) +
    (L 2 : ℂ) * unitPhase (θ 1 + θ 2) +
    (L 3 : ℂ) * unitPhase (θ 1 + θ 2 + θ 3),
    θ 0 + θ 1 + θ 2 + θ 3 - 2 * Real.pi)

private theorem unitPhase_neg_cancel (x : ℝ) : unitPhase (-x) * unitPhase x = 1 := by
  rw [← unitPhase_add]
  simp [unitPhase]

private theorem unitPhase_sub_period (x : ℝ) :
    unitPhase (x - 2 * Real.pi) = unitPhase x := by
  simpa using (unitPhase_add_two_pi (x - 2 * Real.pi)).symm

private theorem conjugate_phase (x : ℝ) : starRingEnd ℂ (unitPhase x) = unitPhase (-x) := by
  apply Complex.ext <;> simp [Real.cos_neg, Real.sin_neg]

/-- Exact cyclic relabeling identity. The lifted-turn correction is present
off the zero set and contributes to the derivative at a zero. -/
theorem slotController_rotate (L θ : Fin 4 → ℝ) :
    slotController (rotateFour L) (rotateFour θ) =
      (unitPhase (-(θ 1)) * ((slotController L θ).1 +
          (L 0 : ℂ) * (unitPhase ((slotController L θ).2) - 1)),
        (slotController L θ).2) := by
  apply Prod.ext
  · have hmul : unitPhase (θ 1) * (slotController (rotateFour L) (rotateFour θ)).1 =
        (slotController L θ).1 +
          (L 0 : ℂ) * (unitPhase ((slotController L θ).2) - 1) := by
      simp only [slotController, rotateFour, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Fin.isValue, unitPhase_sub_period, unitPhase_add]
      ring
    have hh := congrArg (fun z : ℂ => unitPhase (-(θ 1)) * z) hmul
    simpa only [← mul_assoc, unitPhase_neg_cancel, one_mul] using hh
  · simp only [slotController, rotateFour, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue]
    ring

/-- Exact reversal identity, including its parameter-dependent phase.
The reversed corner order is `[0,3,2,1]`, while edge order is `[3,2,1,0]`. -/
theorem slotController_reverse (L θ : Fin 4 → ℝ) :
    slotController (reverseFour L) ![θ 0, θ 3, θ 2, θ 1] =
      (unitPhase (θ 1 + θ 2 + θ 3) * starRingEnd ℂ (slotController L θ).1,
        (slotController L θ).2) := by
  apply Prod.ext
  · have h1 : unitPhase (θ 1 + θ 2 + θ 3) * unitPhase (-(θ 1)) =
        unitPhase (θ 3 + θ 2) := by
      rw [← unitPhase_add]; congr 1; ring
    have h2 : unitPhase (θ 1 + θ 2 + θ 3) * unitPhase (-(θ 1 + θ 2)) =
        unitPhase (θ 3) := by
      rw [← unitPhase_add]; congr 1; ring
    have h3 : unitPhase (θ 1 + θ 2 + θ 3) * unitPhase (-(θ 1 + θ 2 + θ 3)) = 1 := by
      rw [← unitPhase_add]; simp [unitPhase]
    simp only [slotController, reverseFour, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, map_add, map_mul, Complex.conj_ofReal, conjugate_phase]
    rw [show θ 3 + θ 2 + θ 1 = θ 1 + θ 2 + θ 3 by ring]
    linear_combination -(L 1 : ℂ) * h1 - (L 2 : ℂ) * h2 - (L 3 : ℂ) * h3
  · simp only [slotController, reverseFour, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue]
    ring

namespace Frame

/-- Rotation of literal endpoint vectors rotates the four original turns. -/
theorem turns_rotate_of_endpoints {m n : ℕ} {μ : ZMod m → ℝ} {κ : ZMod n → ℝ}
    {F : Frame m} {G : Frame n}
    (hstart : G.start κ = rotateFour (F.start μ))
    (hfinish : G.finish κ = rotateFour (F.finish μ)) (L : Fin 4 → ℝ) :
    G.turns κ (rotateFour L) = rotateFour (F.turns μ L) := by
  funext j
  fin_cases j <;> simp [turns, startArc, finishArc, hstart, hfinish, rotateFour]

/-- Reversal swaps the literal endpoint sides before reversing edge order. -/
theorem turns_reverse_of_endpoints {m n : ℕ} {μ : ZMod m → ℝ} {κ : ZMod n → ℝ}
    {F : Frame m} {G : Frame n}
    (hstart : G.start κ = reverseFour (F.finish μ))
    (hfinish : G.finish κ = reverseFour (F.start μ)) (L : Fin 4 → ℝ) :
    G.turns κ (reverseFour L) =
      ![(F.turns μ L) 0, (F.turns μ L) 3, (F.turns μ L) 2, (F.turns μ L) 1] := by
  funext j
  fin_cases j <;> simp [turns, startArc, finishArc, hstart, hfinish, reverseFour, add_comm]

/-- The cyclic controller identity for arbitrary frames with rotated actual
endpoint pairs, before imposing closure or differentiating. -/
theorem controller_rotate_of_endpoints {m n : ℕ} {μ : ZMod m → ℝ} {κ : ZMod n → ℝ}
    {F : Frame m} {G : Frame n}
    (hstart : G.start κ = rotateFour (F.start μ))
    (hfinish : G.finish κ = rotateFour (F.finish μ)) (L : Fin 4 → ℝ) :
    G.controller κ (rotateFour L) =
      (unitPhase (-((F.turns μ L) 1)) * ((F.controller μ L).1 +
          (L 0 : ℂ) * (unitPhase ((F.controller μ L).2) - 1)),
        (F.controller μ L).2) := by
  change slotController (rotateFour L) (G.turns κ (rotateFour L)) = _
  rw [turns_rotate_of_endpoints hstart hfinish]
  exact slotController_rotate L (F.turns μ L)

/-- The reflected controller identity for arbitrary frames with reversed
and swapped actual endpoint pairs. -/
theorem controller_reverse_of_endpoints {m n : ℕ} {μ : ZMod m → ℝ} {κ : ZMod n → ℝ}
    {F : Frame m} {G : Frame n}
    (hstart : G.start κ = reverseFour (F.finish μ))
    (hfinish : G.finish κ = reverseFour (F.start μ)) (L : Fin 4 → ℝ) :
    G.controller κ (reverseFour L) =
      (unitPhase ((F.turns μ L) 1 + (F.turns μ L) 2 + (F.turns μ L) 3) *
          starRingEnd ℂ (F.controller μ L).1, (F.controller μ L).2) := by
  change slotController (reverseFour L) (G.turns κ (reverseFour L)) = _
  rw [turns_reverse_of_endpoints hstart hfinish]
  exact slotController_reverse L (F.turns μ L)

end Frame

end FourActiveSlots

end Gluck.Discrete
