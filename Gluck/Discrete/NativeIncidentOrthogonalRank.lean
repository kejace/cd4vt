module

public import Gluck.Discrete.NativeOrderedFirstPair

/-!
# Native rank with endpoints below their incident pure peaks

The derivative is taken in genuine angle and half-length coordinates.
This module first treats the chamber in which the second pure turn is
at least a right angle, including the equal-pure-curvature case.
-/

@[expose] public section

namespace Gluck.Discrete.NativeOppositePure

open Set

/-- Coordinates `(S, α, T)` with the first half of the second pure turn fixed. -/
noncomputable def incidentSplitController (p t q h l γ : ℝ)
    (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![chord q (x 1) (x 0 - x 1) γ (x 2 - γ),
    seamLow p t q (x 1) (x 0 - x 1) γ (x 2 - γ),
    seamHigh q h l (x 1) (x 0 - x 1) γ (x 2 - γ)]

noncomputable def incidentNativeController (p t q h l γ : ℝ)
    (x : Fin 3 → ℝ) : ℂ × ℝ :=
  (nativeHalfClosure p t q h l (x 1) (x 0 - x 1) γ (x 2 - γ),
    turnDefect p t q h l (x 1) (x 0 - x 1) γ (x 2 - γ))

noncomputable def incidentDifferential (R W A B D : ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![
    R • ContinuousLinearMap.proj 0 - W • ContinuousLinearMap.proj 2,
    ContinuousLinearMap.proj 0 - A • ContinuousLinearMap.proj 1 +
      ContinuousLinearMap.proj 2,
    (1 - B) • ContinuousLinearMap.proj 0 + B • ContinuousLinearMap.proj 1 +
      (1 - D) • ContinuousLinearMap.proj 2]

theorem incidentDifferential_surjective {R W A B D : ℝ}
    (hR : R < 0) (hW : W ≤ 0) (hA : 0 < A) (hA1 : A < 1)
    (hB : 0 < B) (hD1 : D < 1) :
    Function.Surjective (incidentDifferential R W A B D) := by
  let U := A + B - A * B
  let V := A + B - A * D
  have hU : 0 < U := by
    dsimp [U]
    nlinarith [mul_pos hB (sub_pos.mpr hA1)]
  have hV : 0 < V := by
    dsimp [V]
    nlinarith [mul_pos hA (sub_pos.mpr hD1)]
  have hdet : R * V + W * U ≠ 0 :=
    ne_of_lt (add_neg_of_neg_of_nonpos (mul_neg_of_neg_of_pos hR hV)
      (mul_nonpos_of_nonpos_of_nonneg hW hU.le))
  intro y
  let N := A * y 2 + B * y 1
  let S := (V * y 0 + W * N) / (R * V + W * U)
  let T := (R * N - U * y 0) / (R * V + W * U)
  have hm : R * S - W * T = y 0 := by
    dsimp [S, T]
    field_simp
    ring
  have hn : U * S + V * T = N := by
    calc
      _ = (R * V + W * U) * N / (R * V + W * U) := by
        dsimp [S, T]
        ring
      _ = N := mul_div_cancel_left₀ N hdet
  refine ⟨![S, (S + T - y 1) / A, T], ?_⟩
  ext i
  fin_cases i
  · simpa [incidentDifferential] using hm
  · simp [incidentDifferential]
    field_simp
    ring
  · simp [incidentDifferential]
    apply (mul_left_inj' (ne_of_gt hA)).mp
    have hcancel : A * ((S + T - y 1) / A) = S + T - y 1 :=
      mul_div_cancel₀ _ (ne_of_gt hA)
    dsimp [U, V, N] at hn
    nlinarith

theorem hasFDerivAt_incidentSplitController
    {p t q h l γ : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hh : 0 < h) (hhq : h < q) (hq : 0 < q)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) γ (x 2 - γ)) :
    HasFDerivAt (incidentSplitController p t q h l γ)
      (incidentDifferential (Real.cos (x 0)) (Real.cos (x 2) / q)
        (1 - angleSlope p (x 1)) (1 - angleSlope l (x 0 - x 1))
        (1 - angleSlope (h / q) (x 2 - γ))) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 x
  have hpD := (hasDerivAt_angleDefect hp hp1 ha.1.1 ha.1.2).comp_hasFDerivAt x h1
  have hlD := (hasDerivAt_angleDefect hl hl1 ha.2.1.1 ha.2.1.2).comp_hasFDerivAt x
    (h0.sub h1)
  have hhD := (hasDerivAt_angleDefect (div_pos hh hq) ((div_lt_one hq).mpr hhq)
    ha.2.2.2.1.1 ha.2.2.2.1.2).comp_hasFDerivAt x (h2.sub_const γ)
  have hM := ((Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0).sub
    (((Real.hasDerivAt_sin (x 2)).comp_hasFDerivAt x h2).mul_const q⁻¹)
  have hH := ((((h0.add h2).sub_const Real.pi).sub hpD).sub_const
    (angleDefect (t / q) γ))
  have hK := (((h0.add h2).sub_const Real.pi).sub hlD).sub hhD
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert hM using 1
    · ext z
      simp [incidentSplitController, chord, Function.comp_def, div_eq_mul_inv]
    · ext z
      simp [div_eq_mul_inv]
      ring
  · convert hH using 1
    · ext z
      simp [incidentSplitController, seamLow, lowTurn, angleDefect, Function.comp_def]
      ring
    · ext z
      simp
      ring
  · convert hK using 1
    · ext z
      simp [incidentSplitController, seamHigh, highTurn, angleDefect, Function.comp_def]
      ring
    · ext z
      simp
      ring

private theorem cos_first_sum_neg_of_one_le
    {S T q : ℝ} (hS : 0 < S) (hS1 : S < Real.pi)
    (hT1 : T < Real.pi) (hsum : Real.pi < S + T) (hq : 1 ≤ q)
    (hc : Real.sin S = Real.sin T / q) : Real.cos S < 0 := by
  have hS2 : Real.pi / 2 < S := by
    by_contra hn
    have hs := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ Real.pi - T by linarith [Real.pi_pos])
      (le_of_not_gt hn) (show Real.pi - T < S by linarith)
    rw [Real.sin_pi_sub] at hs
    have hp := Real.sin_pos_of_pos_of_lt_pi hS hS1
    have he := (eq_div_iff (by linarith : q ≠ 0)).mp hc
    nlinarith
  exact Real.cos_neg_of_pi_div_two_lt_of_lt hS2 (by linarith [Real.pi_pos])

/-- Actual split rank in the nonacute second-turn chamber. Equal pure
curvatures are allowed; no orthogonality assumption is needed here. -/
theorem fderiv_incidentSplitController_surjective
    {p t q h l γ : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q)
    (hl : 0 < l) (hl1 : l < 1) (hh : 0 < h) (hhq : h < q)
    (hq : 1 ≤ q) (hT : Real.pi / 2 ≤ x 2)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) γ (x 2 - γ))
    (hzero : incidentSplitController p t q h l γ x = 0) :
    Function.Surjective (fderiv ℝ (incidentSplitController p t q h l γ) x) := by
  have hq0 : 0 < q := by linarith
  have hlow : seamLow p t q (x 1) (x 0 - x 1) γ (x 2 - γ) = 0 :=
    congrFun hzero 1
  have hchord : chord q (x 1) (x 0 - x 1) γ (x 2 - γ) = 0 :=
    congrFun hzero 0
  have hsum := angle_sums_gt_pi_of_seamLow_zero hp hp1 ht htq hq0 ha.1 ha.2.2.1 hlow
  have hR : Real.cos (x 0) < 0 := by
    apply cos_first_sum_neg_of_one_le (q := q) (T := x 2)
      (by linarith [ha.1.1, ha.2.1.1]) (by linarith [ha.1.2, ha.2.1.2])
      (by linarith [ha.2.2.1.2, ha.2.2.2.1.2]) (by linarith) hq
    simpa [chord] using sub_eq_zero.mp hchord
  have hW : Real.cos (x 2) / q ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hq0.le
    exact Real.cos_nonpos_of_pi_div_two_le_of_le hT
      (by linarith [ha.2.2.1.2, ha.2.2.2.1.2, Real.pi_pos])
  rw [(hasFDerivAt_incidentSplitController hp hp1 hl hl1 hh hhq hq0 ha).fderiv]
  exact incidentDifferential_surjective hR hW
    (lowDefect_derivative_pos hp hp1 ha.1.1 ha.1.2)
    (by
      have hs := angleSlope_pos hp ha.1.1 ha.1.2
        (endpoint_arg_lt_one hp hp1 ha.1.1 ha.1.2)
      linarith)
    (lowDefect_derivative_pos hl hl1 ha.2.1.1 ha.2.1.2)
    (by
      have hs := angleSlope_pos (div_pos hh hq0) ha.2.2.2.1.1 ha.2.2.2.1.2
        (endpoint_arg_lt_one (div_pos hh hq0) ((div_lt_one hq0).mpr hhq)
          ha.2.2.2.1.1 ha.2.2.2.1.2)
      linarith)

private theorem hasFDerivAt_incidentPhase {f : (Fin 3 → ℝ) → ℝ}
    {f' : (Fin 3 → ℝ) →L[ℝ] ℝ} {x : Fin 3 → ℝ}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun z => unitPhase (f z))
      ((unitPhase (f x) * Complex.I) • (Complex.ofRealCLM.comp f')) x := by
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp x hf).mul_const Complex.I
  simpa only [unitPhase, Function.comp_def, Complex.ofRealCLM_apply, smul_smul,
    mul_comm] using hc.cexp

/-- Differentiation of the exact identity at a simultaneous split zero.
The target transformation is proved bijective in `NativeOppositePureClosure`. -/
theorem hasFDerivAt_incidentNativeController_of_split
    {p t q h l γ : ℝ} {x : Fin 3 → ℝ}
    {f' : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)}
    (hf : HasFDerivAt (incidentSplitController p t q h l γ) f' x)
    (hz : incidentSplitController p t q h l γ x = 0) :
    HasFDerivAt (incidentNativeController p t q h l γ)
      ((closureTargetLinearMap (x 0 - x 1) (Real.sin (x 2) / q)
        (Complex.I * (Real.sin (x 0 - x 1) : ℂ) *
          unitPhase (-(x 0)))).toContinuousLinearMap.comp f')
      x := by
  let f := incidentSplitController p t q h l γ
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 x
  have hM := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt.comp x hf
  have hH := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).hasFDerivAt.comp x hf
  have hK := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt.comp x hf
  have hMC := Complex.ofRealCLM.hasFDerivAt.comp x hM
  have hphase := hasFDerivAt_incidentPhase (h0.sub h1).neg
  have hLow := hasFDerivAt_incidentPhase hH
  have hTurn := hasFDerivAt_incidentPhase (hH.add hK)
  have hsin := (Real.hasDerivAt_sin (x 0 - x 1)).comp_hasFDerivAt x (h0.sub h1)
  have hsinC := Complex.ofRealCLM.hasFDerivAt.comp x hsin
  have hcoeff := hsinC.mul (hasFDerivAt_incidentPhase h0.neg)
  have hr := ((Real.hasDerivAt_sin (x 2)).comp_hasFDerivAt x h2).mul_const q⁻¹
  have hrC := Complex.ofRealCLM.hasFDerivAt.comp x hr
  have hE := (hphase.mul (hMC.add (hrC.mul (hLow.const_sub 1)))).add
    (hcoeff.mul (hTurn.sub_const 1))
  have hprod := hE.prodMk (hH.add hK)
  have hfun : (fun z : Fin 3 → ℝ =>
      (unitPhase (-(z 0 - z 1)) *
          ((f z 0 : ℂ) + ((Real.sin (z 2) * q⁻¹ : ℝ) : ℂ) * (1 - unitPhase (f z 1))) +
        (Real.sin (z 0 - z 1) : ℂ) * unitPhase (-(z 0)) *
          (unitPhase (f z 1 + f z 2) - 1), f z 1 + f z 2)) =
      incidentNativeController p t q h l γ := by
    funext z
    apply Prod.ext
    · simp only [incidentNativeController, nativeHalfClosure_eq]
      have ht := seamLow_add_seamHigh p t q h l (z 1) (z 0 - z 1) γ (z 2 - γ)
      simp only [f, incidentSplitController, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, chord]
      rw [ht]
      simp only [add_sub_cancel]
      simp only [div_eq_mul_inv]
      push_cast
      ring
    · exact seamLow_add_seamHigh p t q h l (z 1) (z 0 - z 1) γ (z 2 - γ)
  change HasFDerivAt (fun z : Fin 3 → ℝ =>
      (unitPhase (-(z 0 - z 1)) *
          ((f z 0 : ℂ) + ((Real.sin (z 2) * q⁻¹ : ℝ) : ℂ) * (1 - unitPhase (f z 1))) +
        (Real.sin (z 0 - z 1) : ℂ) * unitPhase (-(z 0)) *
          (unitPhase (f z 1 + f z 2) - 1), f z 1 + f z 2)) _ x at hprod
  rw [hfun] at hprod
  apply hprod.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · simp [closureTargetLinearMap, Function.comp_def, hz, unitPhase, div_eq_mul_inv]
    ring
  · simp [closureTargetLinearMap]

/-- Rank of the original native angle equations in the nonacute chamber. -/
theorem fderiv_incidentNativeController_surjective
    {p t q h l γ : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q)
    (hl : 0 < l) (hl1 : l < 1) (hh : 0 < h) (hhq : h < q)
    (hq : 1 ≤ q) (hT : Real.pi / 2 ≤ x 2)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) γ (x 2 - γ))
    (hzero : incidentNativeController p t q h l γ x = 0) :
    Function.Surjective (fderiv ℝ (incidentNativeController p t q h l γ) x) := by
  have hq0 : 0 < q := by linarith
  have hz := (native_zero_iff_of_strictAngles (l := l) hp.le ht.le hq0 ha).mp
    ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  have hs : incidentSplitController p t q h l γ x = 0 := by
    ext i
    fin_cases i
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2
  have hf := hasFDerivAt_incidentSplitController (t := t) hp hp1 hl hl1 hh hhq hq0 ha
  have hn := hasFDerivAt_incidentNativeController_of_split hf hs
  have hsin : 0 < Real.sin (x 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [ha.2.2.1.1, ha.2.2.2.1.1])
    (by linarith [ha.2.2.1.2, ha.2.2.2.1.2])
  rw [hn.fderiv]
  have htarget := closureTargetLinearMap_surjective
    (β := x 0 - x 1) (ne_of_gt (div_pos hsin hq0))
    (Complex.I * (Real.sin (x 0 - x 1) : ℂ) * unitPhase (-(x 0)))
  have hsplit := fderiv_incidentSplitController_surjective hp hp1 ht htq hl hl1
    hh hhq hq hT ha hs
  rw [hf.fderiv] at hsplit
  exact htarget.comp hsplit

/-- Direct differentiability of all eight original endpoint arcs. -/
theorem differentiableAt_nativeLengthController_of_physical
    {p t q h l : ℝ} {L : Fin 4 → ℝ}
    (hp : 0 < p) (ht : 0 < t) (hq : 0 < q) (hh : 0 < h) (hl : 0 < l)
    (hphys : NativeLengthPhysical p t q h l L) :
    DifferentiableAt ℝ (nativeLengthController p t q h l) L := by
  rcases hphys with ⟨hpos, h0, hp0, ht1, hq1, hq2, hh2, hl3, h3⟩
  have hd {g : (Fin 4 → ℝ) → ℝ} (hg : DifferentiableAt ℝ g L)
      (hlo : 0 < g L) (hhi : g L < 1) :
      DifferentiableAt ℝ (fun z => Real.arcsin (g z)) L :=
    (Real.differentiableAt_arcsin.mpr ⟨by linarith, ne_of_lt hhi⟩).comp L hg
  have hd0 := hd (g := fun z => z 0) (by fun_prop) (hpos 0) h0
  have hd3 := hd (g := fun z => z 3) (by fun_prop) (hpos 3) h3
  have hdp := hd (g := fun z => p * z 0) (by fun_prop) (mul_pos hp (hpos 0)) hp0
  have hdt := hd (g := fun z => t * z 1) (by fun_prop) (mul_pos ht (hpos 1)) ht1
  have hdq1 := hd (g := fun z => q * z 1) (by fun_prop) (mul_pos hq (hpos 1)) hq1
  have hdq2 := hd (g := fun z => q * z 2) (by fun_prop) (mul_pos hq (hpos 2)) hq2
  have hdh := hd (g := fun z => h * z 2) (by fun_prop) (mul_pos hh (hpos 2)) hh2
  have hdl := hd (g := fun z => l * z 3) (by fun_prop) (mul_pos hl (hpos 3)) hl3
  unfold nativeLengthController lengthTurns unitPhase
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Matrix.head_fin_const]
  fun_prop

noncomputable def incidentHalfLengths (q γ : ℝ) (x : Fin 3 → ℝ) : Fin 4 → ℝ :=
  splitHalfLengths q (x 2) ![x 0, x 1, γ]

/-- Transfer to the four actual active half-lengths in the nonacute chamber. -/
theorem fderiv_nativeLengthController_surjective_of_incident_angles
    {p t q h l γ : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q)
    (hl : 0 < l) (hl1 : l < 1) (hh : 0 < h) (hhq : h < q)
    (hq : 1 ≤ q) (hT : Real.pi / 2 ≤ x 2)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) γ (x 2 - γ))
    (hzero : incidentNativeController p t q h l γ x = 0) :
    Function.Surjective (fderiv ℝ (nativeLengthController p t q h l)
      (incidentHalfLengths q γ x)) := by
  have hq0 : 0 < q := by linarith
  have hphys : NativeLengthPhysical p t q h l (incidentHalfLengths q γ x) :=
    nativeLengthPhysical_splitHalfLengths hp hp1 ht htq hl hl1 hq0 ha
  have hd := differentiableAt_nativeLengthController_of_physical hp ht hq0 hh hl hphys
  have hg : DifferentiableAt ℝ (incidentHalfLengths q γ) x := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [incidentHalfLengths, splitHalfLengths] <;> fun_prop
  have hc0 : ContinuousAt (fun z : Fin 3 → ℝ => z 0) x := (continuous_apply 0).continuousAt
  have hc1 : ContinuousAt (fun z : Fin 3 → ℝ => z 1) x := (continuous_apply 1).continuousAt
  have hc2 : ContinuousAt (fun z : Fin 3 → ℝ => z 2) x := (continuous_apply 2).continuousAt
  have heα := hc1.eventually (Ioo_mem_nhds ha.1.1 ha.1.2)
  have heβ := (hc0.sub hc1).eventually (Ioo_mem_nhds ha.2.1.1 ha.2.1.2)
  have heδ := (hc2.sub_const γ).eventually
    (Ioo_mem_nhds ha.2.2.2.1.1 ha.2.2.2.1.2)
  have he : (nativeLengthController p t q h l ∘ incidentHalfLengths q γ) =ᶠ[nhds x]
      incidentNativeController p t q h l γ := by
    filter_upwards [heα, heβ, heδ] with z hα hβ hδ
    exact nativeLengthController_splitHalfLengths (x := ![z 0, z 1, γ])
      (ne_of_gt hq0) hα hβ ha.2.2.1 hδ
  have hs := fderiv_incidentNativeController_surjective hp hp1 ht htq hl hl1
    hh hhq hq hT ha hzero
  rw [← he.fderiv_eq, fderiv_comp x hd hg] at hs
  intro y
  obtain ⟨v, hv⟩ := hs y
  exact ⟨fderiv ℝ (incidentHalfLengths q γ) x v, hv⟩

/-- A physical native root has rank three whenever its second pure turn
is at least a right angle. This is a chamber theorem, not the full unequal-peak result. -/
theorem fderiv_nativeLengthController_surjective_of_nonacute_incident
    {p t q h l : ℝ} {L : Fin 4 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q)
    (hl : 0 < l) (hl1 : l < 1) (hh : 0 < h) (hhq : h < q)
    (hq : 1 ≤ q) (hphys : NativeLengthPhysical p t q h l L)
    (hzero : nativeLengthController p t q h l L = 0)
    (hT : Real.pi / 2 ≤ Real.arcsin (q * L 1) + Real.arcsin (q * L 2)) :
    Function.Surjective (fderiv ℝ (nativeLengthController p t q h l) L) := by
  let α := Real.arcsin (L 0)
  let β := Real.arcsin (L 3)
  let γ := Real.arcsin (q * L 1)
  let δ := Real.arcsin (q * L 2)
  let x : Fin 3 → ℝ := ![α + β, α, γ + δ]
  have hq0 : 0 < q := by linarith
  have hacute {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
      Real.arcsin z ∈ Ioo 0 (Real.pi / 2) :=
    ⟨Real.arcsin_pos.mpr hz, Real.arcsin_lt_pi_div_two.mpr hz1⟩
  rcases hphys with ⟨hpos, h0, hp0, ht1, hq1, hq2, hh2, hl3, h3⟩
  have ha : StrictAngles q h (x 1) (x 0 - x 1) γ (x 2 - γ) := by
    dsimp [x]
    simp only [add_sub_cancel_left]
    refine ⟨hacute (hpos 0) h0, hacute (hpos 3) h3,
      hacute (mul_pos hq0 (hpos 1)) hq1, hacute (mul_pos hq0 (hpos 2)) hq2, ?_⟩
    dsimp [δ]
    rw [Real.sin_arcsin (by nlinarith [hpos 2]) hq2.le]
    convert hh2 using 1
    field_simp
  have hL : incidentHalfLengths q γ x = L := by
    have hs {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
        Real.sin (Real.arcsin z) = z := Real.sin_arcsin (by linarith) hz1.le
    ext i
    fin_cases i <;> dsimp [incidentHalfLengths, splitHalfLengths, x]
    · exact hs (hpos 0) h0
    · dsimp [γ]
      rw [hs (mul_pos hq0 (hpos 1)) hq1, mul_div_cancel_left₀ _ (ne_of_gt hq0)]
    · rw [add_sub_cancel_left]
      dsimp [δ]
      rw [hs (mul_pos hq0 (hpos 2)) hq2, mul_div_cancel_left₀ _ (ne_of_gt hq0)]
    · rw [add_sub_cancel_left]
      exact hs (hpos 3) h3
  have hz : incidentNativeController p t q h l γ x = 0 := by
    have he := nativeLengthController_splitHalfLengths (p := p) (t := t) (h := h) (l := l)
      (x := ![x 0, x 1, γ])
      (ne_of_gt hq0) ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1
    change nativeLengthController p t q h l (incidentHalfLengths q γ x) =
      incidentNativeController p t q h l γ x at he
    rw [← he, hL, hzero]
  rw [← hL]
  exact fderiv_nativeLengthController_surjective_of_incident_angles
    hp hp1 ht htq hl hl1 hh hhq hq hT ha hz

/-- Equal pure curvatures force both pure turns to be obtuse at any
strict native zero with all mixed endpoints below that curvature. -/
theorem fderiv_nativeLengthController_surjective_of_equal_pure
    {p t h l : ℝ} {L : Fin 4 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (ht1 : t < 1)
    (hl : 0 < l) (hl1 : l < 1) (hh : 0 < h) (hh1 : h < 1)
    (hphys : NativeLengthPhysical p t 1 h l L)
    (hzero : nativeLengthController p t 1 h l L = 0) :
    Function.Surjective (fderiv ℝ (nativeLengthController p t 1 h l) L) := by
  obtain ⟨T, x, ha, hL⟩ := exists_splitHalfLengths_of_physical zero_lt_one hphys
  have hz : nativeSplitController p t 1 h l T x = 0 := by
    rw [← nativeLengthController_splitHalfLengths one_ne_zero
      ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1, hL, hzero]
  have hroots := (native_zero_iff_of_strictAngles (l := l) hp.le ht.le zero_lt_one ha).mp
    ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩
  have hsum := angle_sums_gt_pi_of_seamLow_zero hp hp1 ht ht1 zero_lt_one
    ha.1 ha.2.2.1 hroots.2.1
  have heq : Real.sin (x 0) = Real.sin T := by
    simpa [chord] using sub_eq_zero.mp hroots.1
  have hT : Real.pi / 2 ≤ T := by
    by_contra hn
    have hs := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ Real.pi - x 0 by linarith [ha.1.2, ha.2.1.2, Real.pi_pos])
      (le_of_lt (lt_of_not_ge hn)) (show Real.pi - x 0 < T by linarith)
    rw [Real.sin_pi_sub, heq] at hs
    exact (lt_irrefl _ hs)
  have hi : incidentNativeController p t 1 h l (x 2) ![x 0, x 1, T] = 0 := hz
  have hia : StrictAngles 1 h (![x 0, x 1, T] 1)
      (![x 0, x 1, T] 0 - ![x 0, x 1, T] 1) (x 2)
      (![x 0, x 1, T] 2 - x 2) := ha
  have hr := fderiv_nativeLengthController_surjective_of_incident_angles
    hp hp1 ht ht1 hl hl1 hh hh1 le_rfl hT hia hi
  have hLi : incidentHalfLengths 1 (x 2) ![x 0, x 1, T] = L := hL
  rwa [hLi] at hr


end Gluck.Discrete.NativeOppositePure
