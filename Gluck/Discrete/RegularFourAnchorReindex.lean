import Gluck.Discrete.RegularFourAnchorTransport

/-!
# Regular-anchor transport under cyclic and reflected endpoint order

The controller identities are differentiated off the zero set. In
particular cyclic transport retains its lifted-turn correction.
-/

namespace Gluck.Discrete

open FourActiveSlots

namespace FourActiveSlots

noncomputable def rotateFourCLM : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ)
      (![1, 2, 3, 0] j)

noncomputable def reverseFourCLM : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ)
      (![3, 2, 1, 0] j)

@[simp] theorem rotateFourCLM_apply (v : Fin 4 → ℝ) : rotateFourCLM v = rotateFour v := by
  ext j
  fin_cases j <;> rfl

@[simp] theorem reverseFourCLM_apply (v : Fin 4 → ℝ) : reverseFourCLM v = reverseFour v := by
  ext j
  fin_cases j <;> rfl

private theorem phase_hasFDerivAt {f : (Fin 4 → ℝ) → ℝ}
    {f' : (Fin 4 → ℝ) →L[ℝ] ℝ} {x : Fin 4 → ℝ}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun z => unitPhase (f z))
      ((unitPhase (f x) * Complex.I) • (Complex.ofRealCLM.comp f')) x := by
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp x hf).mul_const Complex.I
  simpa only [unitPhase, Function.comp_def, Complex.ofRealCLM_apply, smul_smul,
    mul_comm] using hc.cexp

namespace Frame

theorem differentiableAt_turns_of_strict {n : ℕ} {κ : ZMod n → ℝ}
    (F : Frame n) {L : Fin 4 → ℝ}
    (hL : ∀ j, 0 < L j)
    (hspos : ∀ j, 0 < F.start κ j) (hfpos : ∀ j, 0 < F.finish κ j)
    (hs : ∀ j, F.start κ j * L j < 1) (hf : ∀ j, F.finish κ j * L j < 1) :
    ∀ j, DifferentiableAt ℝ (fun X => F.turns κ X j) L := by
  have hsa (j) : DifferentiableAt ℝ (fun X => F.startArc κ X j) L := by
    apply (Real.differentiableAt_arcsin.mpr ?_).comp L
      (show DifferentiableAt ℝ (fun X : Fin 4 → ℝ => F.start κ j * X j) L by fun_prop)
    exact ⟨by linarith [mul_pos (hspos j) (hL j)], ne_of_lt (hs j)⟩
  have hfa (j) : DifferentiableAt ℝ (fun X => F.finishArc κ X j) L := by
    apply (Real.differentiableAt_arcsin.mpr ?_).comp L
      (show DifferentiableAt ℝ (fun X : Fin 4 → ℝ => F.finish κ j * X j) L by fun_prop)
    exact ⟨by linarith [mul_pos (hfpos j) (hL j)], ne_of_lt (hf j)⟩
  intro j
  fin_cases j
  · exact (hfa 3).add (hsa 0)
  · exact (hfa 0).add (hsa 1)
  · exact (hfa 1).add (hsa 2)
  · exact (hfa 2).add (hsa 3)

theorem differentiableAt_controller_of_strict {n : ℕ} {κ : ZMod n → ℝ}
    (F : Frame n) {L : Fin 4 → ℝ}
    (hL : ∀ j, 0 < L j)
    (hspos : ∀ j, 0 < F.start κ j) (hfpos : ∀ j, 0 < F.finish κ j)
    (hs : ∀ j, F.start κ j * L j < 1) (hf : ∀ j, F.finish κ j * L j < 1) :
    DifferentiableAt ℝ (F.controller κ) L := by
  have hd := F.differentiableAt_turns_of_strict hL hspos hfpos hs hf
  unfold controller unitPhase
  fun_prop

/-- Actual derivative under one cyclic relabeling. The correction in the
complex coordinate is `i L₀ dτ`, before multiplication by the new gauge. -/
theorem fderiv_controller_rotate_of_endpoints
    {m n : ℕ} {μ : ZMod m → ℝ} {κ : ZMod n → ℝ}
    {F : Frame m} {G : Frame n} {L : Fin 4 → ℝ}
    (hstart : G.start κ = rotateFour (F.start μ))
    (hfinish : G.finish κ = rotateFour (F.finish μ))
    (hd : DifferentiableAt ℝ (F.controller μ) L)
    (ht : DifferentiableAt ℝ (fun X => F.turns μ X 1) L)
    (hdG : DifferentiableAt ℝ (G.controller κ) (rotateFour L))
    (hz : F.controller μ L = 0) (v : Fin 4 → ℝ) :
    fderiv ℝ (G.controller κ) (rotateFour L) (rotateFour v) =
      (unitPhase (-(F.turns μ L 1)) *
        ((fderiv ℝ (F.controller μ) L v).1 +
          (L 0 : ℂ) * Complex.I * ((fderiv ℝ (F.controller μ) L v).2 : ℂ)),
        (fderiv ℝ (F.controller μ) L v).2) := by
  have hp := phase_hasFDerivAt ht.hasFDerivAt.neg
  have hτ := phase_hasFDerivAt hd.hasFDerivAt.snd
  have hL0 := Complex.ofRealCLM.hasFDerivAt.comp L
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 0 L)
  have he := (hp.mul (hd.hasFDerivAt.fst.add (hL0.mul (hτ.sub_const 1)))).prodMk
    hd.hasFDerivAt.snd
  have hfun : (fun X =>
      (unitPhase (-(F.turns μ X 1)) * ((F.controller μ X).1 +
        (X 0 : ℂ) * (unitPhase ((F.controller μ X).2) - 1)),
        (F.controller μ X).2)) = fun X => G.controller κ (rotateFour X) := by
    funext X
    exact (controller_rotate_of_endpoints hstart hfinish X).symm
  change HasFDerivAt (fun X =>
      (unitPhase (-(F.turns μ X 1)) * ((F.controller μ X).1 +
        (X 0 : ℂ) * (unitPhase ((F.controller μ X).2) - 1)),
        (F.controller μ X).2)) _ L at he
  rw [hfun] at he
  have hrot : HasFDerivAt rotateFour rotateFourCLM L := by
    have hrfun : (rotateFourCLM : (Fin 4 → ℝ) → (Fin 4 → ℝ)) = rotateFour :=
      funext rotateFourCLM_apply
    rw [← hrfun]
    exact rotateFourCLM.hasFDerivAt
  have hc := hdG.hasFDerivAt.comp L hrot
  have hdEq := he.unique hc
  have hh := congrArg (fun D : (Fin 4 → ℝ) →L[ℝ] (ℂ × ℝ) => D v) hdEq
  symm at hh
  simpa [ContinuousLinearMap.comp_apply, hz, unitPhase, mul_assoc, mul_add] using hh

/-- Actual reflected derivative. The derivative of the varying phase
vanishes against the original exact closure zero. -/
theorem fderiv_controller_reverse_of_endpoints
    {m n : ℕ} {μ : ZMod m → ℝ} {κ : ZMod n → ℝ}
    {F : Frame m} {G : Frame n} {L : Fin 4 → ℝ}
    (hstart : G.start κ = reverseFour (F.finish μ))
    (hfinish : G.finish κ = reverseFour (F.start μ))
    (hd : DifferentiableAt ℝ (F.controller μ) L)
    (ht : ∀ j, DifferentiableAt ℝ (fun X => F.turns μ X j) L)
    (hdG : DifferentiableAt ℝ (G.controller κ) (reverseFour L))
    (hz : F.controller μ L = 0) (v : Fin 4 → ℝ) :
    fderiv ℝ (G.controller κ) (reverseFour L) (reverseFour v) =
      (unitPhase (F.turns μ L 1 + F.turns μ L 2 + F.turns μ L 3) *
        starRingEnd ℂ ((fderiv ℝ (F.controller μ) L v).1),
        (fderiv ℝ (F.controller μ) L v).2) := by
  have hp := phase_hasFDerivAt (((ht 1).hasFDerivAt.add (ht 2).hasFDerivAt).add
    (ht 3).hasFDerivAt)
  have hconj := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp L hd.hasFDerivAt.fst
  have he := (hp.mul hconj).prodMk hd.hasFDerivAt.snd
  have hfun : (fun X =>
      (unitPhase (F.turns μ X 1 + F.turns μ X 2 + F.turns μ X 3) *
        starRingEnd ℂ (F.controller μ X).1, (F.controller μ X).2)) =
      fun X => G.controller κ (reverseFour X) := by
    funext X
    exact (controller_reverse_of_endpoints hstart hfinish X).symm
  change HasFDerivAt (fun X =>
      (unitPhase (F.turns μ X 1 + F.turns μ X 2 + F.turns μ X 3) *
        starRingEnd ℂ (F.controller μ X).1, (F.controller μ X).2)) _ L at he
  rw [hfun] at he
  have hrev : HasFDerivAt reverseFour reverseFourCLM L := by
    have hrfun : (reverseFourCLM : (Fin 4 → ℝ) → (Fin 4 → ℝ)) = reverseFour :=
      funext reverseFourCLM_apply
    rw [← hrfun]
    exact reverseFourCLM.hasFDerivAt
  have hc := hdG.hasFDerivAt.comp L hrev
  have hdEq := he.unique hc
  have hh := congrArg (fun D : (Fin 4 → ℝ) →L[ℝ] (ℂ × ℝ) => D v) hdEq
  symm at hh
  simpa [ContinuousLinearMap.comp_apply, hz, mul_assoc] using hh

end Frame

end FourActiveSlots

namespace RegularFourAnchor

/-- Retain a regular anchor on any actual frame with cyclically rotated
endpoint pairs. The derivative transport includes the lifted-turn term. -/
noncomputable def rotateReembed {m n : ℕ} {μ : ZMod m → ℝ} {κ : ZMod n → ℝ}
    (A : RegularFourAnchor μ) (hμ : ∀ i, 0 < μ i) (G : Frame n)
    (hstart : G.start κ = rotateFour (A.frame.start μ))
    (hfinish : G.finish κ = rotateFour (A.frame.finish μ)) :
    RegularFourAnchor κ := by
  have hL : ∀ j, 0 < rotateFour A.halfLengths j := by
    intro j
    fin_cases j <;> exact A.positive _
  have hs : ∀ j, G.start κ j * rotateFour A.halfLengths j < 1 := by
    intro j
    rw [hstart]
    fin_cases j <;> exact A.start_lt _
  have hf : ∀ j, G.finish κ j * rotateFour A.halfLengths j < 1 := by
    intro j
    rw [hfinish]
    fin_cases j <;> exact A.finish_lt _
  have hspos : ∀ j, 0 < G.start κ j := by
    intro j
    rw [hstart]
    fin_cases j <;> exact hμ _
  have hfpos : ∀ j, 0 < G.finish κ j := by
    intro j
    rw [hfinish]
    fin_cases j <;> exact hμ _
  have hdG := G.differentiableAt_controller_of_strict hL hspos hfpos hs hf
  have ht := A.frame.differentiableAt_turns_of_strict A.positive
    (fun j => hμ _) (fun j => hμ _) A.start_lt A.finish_lt
  refine ⟨G, rotateFour A.halfLengths, hL, hs, hf, ?_, ?_⟩
  · rw [Frame.controller_rotate_of_endpoints hstart hfinish, A.zero]
    simp [unitPhase]
  · intro y
    let θ := A.frame.turns μ A.halfLengths 1
    obtain ⟨v, hv⟩ := A.regular
      (unitPhase θ * y.1 - (A.halfLengths 0 : ℂ) * Complex.I * (y.2 : ℂ), y.2)
    refine ⟨rotateFour v, ?_⟩
    rw [Frame.fderiv_controller_rotate_of_endpoints hstart hfinish
      A.differentiableAt_controller (ht 1) hdG A.zero, hv]
    have hc : unitPhase (-θ) * unitPhase θ = 1 := by
      rw [← unitPhase_add]
      simp [unitPhase]
    apply Prod.ext
    · change unitPhase (-θ) *
        ((unitPhase θ * y.1 - (A.halfLengths 0 : ℂ) * Complex.I * (y.2 : ℂ)) +
          (A.halfLengths 0 : ℂ) * Complex.I * (y.2 : ℂ)) = y.1
      rw [sub_add_cancel, ← mul_assoc, hc, one_mul]
    · rfl

/-- Retain a regular anchor on any actual frame with reflected and swapped
endpoint pairs, preserving the original native closure derivative. -/
noncomputable def reverseReembed {m n : ℕ} {μ : ZMod m → ℝ} {κ : ZMod n → ℝ}
    (A : RegularFourAnchor μ) (hμ : ∀ i, 0 < μ i) (G : Frame n)
    (hstart : G.start κ = reverseFour (A.frame.finish μ))
    (hfinish : G.finish κ = reverseFour (A.frame.start μ)) :
    RegularFourAnchor κ := by
  have hL : ∀ j, 0 < reverseFour A.halfLengths j := by
    intro j
    fin_cases j <;> exact A.positive _
  have hs : ∀ j, G.start κ j * reverseFour A.halfLengths j < 1 := by
    intro j
    rw [hstart]
    fin_cases j <;> exact A.finish_lt _
  have hf : ∀ j, G.finish κ j * reverseFour A.halfLengths j < 1 := by
    intro j
    rw [hfinish]
    fin_cases j <;> exact A.start_lt _
  have hspos : ∀ j, 0 < G.start κ j := by
    intro j
    rw [hstart]
    fin_cases j <;> exact hμ _
  have hfpos : ∀ j, 0 < G.finish κ j := by
    intro j
    rw [hfinish]
    fin_cases j <;> exact hμ _
  have hdG := G.differentiableAt_controller_of_strict hL hspos hfpos hs hf
  have ht := A.frame.differentiableAt_turns_of_strict A.positive
    (fun j => hμ _) (fun j => hμ _) A.start_lt A.finish_lt
  refine ⟨G, reverseFour A.halfLengths, hL, hs, hf, ?_, ?_⟩
  · rw [Frame.controller_reverse_of_endpoints hstart hfinish, A.zero]
    simp
  · intro y
    let θ := A.frame.turns μ A.halfLengths 1 + A.frame.turns μ A.halfLengths 2 +
      A.frame.turns μ A.halfLengths 3
    obtain ⟨v, hv⟩ := A.regular (starRingEnd ℂ (unitPhase (-θ) * y.1), y.2)
    refine ⟨reverseFour v, ?_⟩
    rw [Frame.fderiv_controller_reverse_of_endpoints hstart hfinish
      A.differentiableAt_controller ht hdG A.zero, hv]
    have hc : unitPhase θ * unitPhase (-θ) = 1 := by
      rw [← unitPhase_add]
      simp [unitPhase]
    apply Prod.ext
    · change unitPhase θ * starRingEnd ℂ (starRingEnd ℂ (unitPhase (-θ) * y.1)) = y.1
      simp only [starRingEnd_apply, star_star]
      rw [← mul_assoc, hc, one_mul]
    · rfl

end RegularFourAnchor

end Gluck.Discrete
