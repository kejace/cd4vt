import Gluck.Discrete.NativeIncidentOrthogonalRank
import Gluck.Discrete.NativeIncidentCoreTrig
import Gluck.Discrete.NativeIncidentProjectiveElimination
import Gluck.Discrete.NativeNegativeCorners

/-!
# The acute second-turn incident rank reduction

This module keeps the actual native equations and exposes both genuine
angle-chart minors needed for the remaining acute orthogonal chamber.
-/

namespace Gluck.Discrete.NativeOppositePure

open Set

theorem splitDifferential_surjective_of_det_ne_zero {R A B C G : ℝ}
    (hR : R ≠ 0) (hD : A * G + B * C ≠ 0) :
    Function.Surjective (splitDifferential R A B C G) := by
  intro y
  let u := y 0 / R
  let v := y 1 - u
  let w := y 2 - (1 - B) * u
  refine ⟨![u, (C * w - G * v) / (A * G + B * C),
    (-A * w - B * v) / (A * G + B * C)], ?_⟩
  rw [splitDifferential_apply]
  have hD' : A * G + C * B ≠ 0 := by simpa only [mul_comm C B] using hD
  have hD'' : G * A + B * C ≠ 0 := by simpa only [mul_comm G A] using hD
  ext i
  fin_cases i <;> simp [u, v, w]
  all_goals field_simp [hR, hD, hD', hD'']
  all_goals nlinarith

theorem incidentDifferential_surjective_of_det_ne_zero {R W A B D : ℝ}
    (hA : A ≠ 0)
    (hdet : R * (A + B - A * D) + W * (A + B - A * B) ≠ 0) :
    Function.Surjective (incidentDifferential R W A B D) := by
  let U := A + B - A * B
  let V := A + B - A * D
  intro y
  let N := A * y 2 + B * y 1
  let S := (V * y 0 + W * N) / (R * V + W * U)
  let T := (R * N - U * y 0) / (R * V + W * U)
  have hdet' : R * V + W * U ≠ 0 := hdet
  have hm : R * S - W * T = y 0 := by
    dsimp [S, T]
    field_simp [hdet']
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
  · change (1 - B) * S + B * ((S + T - y 1) / A) + (1 - D) * T = y 2
    apply (mul_left_inj' hA).mp
    have hcancel : A * ((S + T - y 1) / A) = S + T - y 1 :=
      mul_div_cancel₀ _ hA
    dsimp [U, V, N] at hn
    linear_combination hn + B * hcancel

/-- The fixed-second-turn chart has the same explicit derivative when the
fourth endpoint is below its incident peak; its excess coefficient is negative. -/
theorem hasFDerivAt_splitController_incident
    {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 0 < q) (hh : 0 < h) (hhq : h < q)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2)) :
    HasFDerivAt (splitController p t q h l T)
      (splitDifferential (Real.cos (x 0))
        (1 - angleSlope p (x 1)) (1 - angleSlope l (x 0 - x 1))
        (1 - angleSlope (t / q) (x 2)) (angleSlope (h / q) (T - x 2) - 1)) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 x
  have hpD := (hasDerivAt_angleDefect hp hp1 ha.1.1 ha.1.2).comp_hasFDerivAt x h1
  have htD := (hasDerivAt_angleDefect (div_pos ht hq) ((div_lt_one hq).2 htq)
    ha.2.2.1.1 ha.2.2.1.2).comp_hasFDerivAt x h2
  have hlD := (hasDerivAt_angleDefect hl hl1 ha.2.1.1 ha.2.1.2).comp_hasFDerivAt x (h0.sub h1)
  have hhD := (hasDerivAt_angleDefect (div_pos hh hq) ((div_lt_one hq).2 hhq)
    ha.2.2.2.1.1 ha.2.2.2.1.2).comp_hasFDerivAt x (h2.const_sub T)
  have hM := ((Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0).sub_const (Real.sin T / q)
  have hLow := (((h0.add_const T).sub_const Real.pi).sub hpD).sub htD
  have hHigh := (((h0.add_const T).sub_const Real.pi).sub hlD).sub hhD
  unfold splitDifferential
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert hM using 1 <;> simp [splitController, chord]
  · convert hLow using 1
    · ext y
      simp [splitController, seamLow, lowTurn, angleDefect, Function.comp_def]
      ring
    · simp
  · convert hHigh using 1
    · ext y
      simp [splitController, seamHigh, highTurn, angleDefect, Function.comp_def]
      ring
    · ext v
      simp
      ring

/-- Either genuine split minor can supply rank. This version exposes the
fixed-first-half-of-the-second-turn minor without any sign assumption on its cosine. -/
theorem fderiv_incidentNativeController_surjective_of_minor
    {p t q h l γ : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t)
    (hl : 0 < l) (hl1 : l < 1) (hh : 0 < h) (hhq : h < q) (hq : 0 < q)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) γ (x 2 - γ))
    (hzero : incidentNativeController p t q h l γ x = 0)
    (hminor : Real.cos (x 0) *
        ((1 - angleSlope p (x 1)) + (1 - angleSlope l (x 0 - x 1)) -
          (1 - angleSlope p (x 1)) * (1 - angleSlope (h / q) (x 2 - γ))) +
      (Real.cos (x 2) / q) *
        ((1 - angleSlope p (x 1)) + (1 - angleSlope l (x 0 - x 1)) -
          (1 - angleSlope p (x 1)) * (1 - angleSlope l (x 0 - x 1))) ≠ 0) :
    Function.Surjective (fderiv ℝ (incidentNativeController p t q h l γ) x) := by
  have hz := (native_zero_iff_of_strictAngles (l := l) hp.le ht.le hq ha).mp
    ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  have hs : incidentSplitController p t q h l γ x = 0 := by
    ext i
    fin_cases i
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2
  have hf := hasFDerivAt_incidentSplitController (t := t) hp hp1 hl hl1 hh hhq hq ha
  have hn := hasFDerivAt_incidentNativeController_of_split hf hs
  have hsin : 0 < Real.sin (x 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [ha.2.2.1.1, ha.2.2.2.1.1])
    (by linarith [ha.2.2.1.2, ha.2.2.2.1.2])
  rw [hn.fderiv]
  have htarget := closureTargetLinearMap_surjective
    (β := x 0 - x 1) (ne_of_gt (div_pos hsin hq))
    (Complex.I * (Real.sin (x 0 - x 1) : ℂ) * unitPhase (-(x 0)))
  exact htarget.comp (incidentDifferential_surjective_of_det_ne_zero
    (ne_of_gt (lowDefect_derivative_pos hp hp1 ha.1.1 ha.1.2)) hminor)

/-- A fixed-second-turn minor gives the derivative of the original native
equations, including below-peak actual endpoints. -/
theorem fderiv_nativeSplitController_surjective_of_incident_minor
    {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hh : 0 < h) (hhq : h < q)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2))
    (hzero : nativeSplitController p t q h l T x = 0)
    (hminor : (1 - angleSlope p (x 1)) * (1 - angleSlope (h / q) (T - x 2)) ≠
      (1 - angleSlope l (x 0 - x 1)) * (1 - angleSlope (t / q) (x 2))) :
    Function.Surjective (fderiv ℝ (nativeSplitController p t q h l T) x) := by
  have hq0 : 0 < q := by linarith
  have hz := (native_zero_iff_of_strictAngles (l := l) hp.le ht.le hq0 ha).mp
    ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  have hs : splitController p t q h l T x = 0 := by
    ext i
    fin_cases i
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2
  have hf := hasFDerivAt_splitController_incident hp hp1 hl hl1 ht htq hq0 hh hhq ha
  have hn := hasFDerivAt_nativeSplitController_of_split hf hs
  have hsin : 0 < Real.sin T := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [ha.2.2.1.1, ha.2.2.2.1.1])
    (by linarith [ha.2.2.1.2, ha.2.2.2.1.2])
  have hcos := cos_first_sum_neg_of_root hp hp1 ht htq hq ha hz.2.1 hz.1
  rw [hn.fderiv]
  have htarget := closureTargetLinearMap_surjective
    (β := x 0 - x 1) (ne_of_gt (div_pos hsin hq0))
    (Complex.I * (Real.sin (x 0 - x 1) : ℂ) * unitPhase (-(x 0)))
  apply htarget.comp
  apply splitDifferential_surjective_of_det_ne_zero
  · simpa using ne_of_lt hcos
  · intro he
    apply hminor
    nlinarith

private theorem native_rank_of_parametric_rank
    {p t q h l : ℝ} {f : (Fin 3 → ℝ) → (Fin 4 → ℝ)}
    {g : (Fin 3 → ℝ) → ℂ × ℝ} {x : Fin 3 → ℝ}
    (hd : DifferentiableAt ℝ (nativeLengthController p t q h l) (f x))
    (hf : DifferentiableAt ℝ f x)
    (he : (nativeLengthController p t q h l ∘ f) =ᶠ[nhds x] g)
    (hs : Function.Surjective (fderiv ℝ g x)) :
    Function.Surjective (fderiv ℝ (nativeLengthController p t q h l) (f x)) := by
  rw [← he.fderiv_eq, fderiv_comp x hd hf] at hs
  intro y
  obtain ⟨v, hv⟩ := hs y
  exact ⟨fderiv ℝ f x v, hv⟩

theorem fderiv_nativeLengthController_surjective_of_fixedTurn_minor
    {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hh : 0 < h) (hhq : h < q)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2))
    (hzero : nativeSplitController p t q h l T x = 0)
    (hminor : (1 - angleSlope p (x 1)) * (1 - angleSlope (h / q) (T - x 2)) ≠
      (1 - angleSlope l (x 0 - x 1)) * (1 - angleSlope (t / q) (x 2))) :
    Function.Surjective (fderiv ℝ (nativeLengthController p t q h l)
      (splitHalfLengths q T x)) := by
  have hq0 : 0 < q := by linarith
  have hd := differentiableAt_nativeLengthController_of_physical hp ht hq0 hh hl
    (nativeLengthPhysical_splitHalfLengths hp hp1 ht htq hl hl1 hq0 ha)
  have hf : DifferentiableAt ℝ (splitHalfLengths q T) x := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [splitHalfLengths] <;> fun_prop
  have hc0 : ContinuousAt (fun z : Fin 3 → ℝ => z 0) x := (continuous_apply 0).continuousAt
  have hc1 : ContinuousAt (fun z : Fin 3 → ℝ => z 1) x := (continuous_apply 1).continuousAt
  have hc2 : ContinuousAt (fun z : Fin 3 → ℝ => z 2) x := (continuous_apply 2).continuousAt
  have heα := hc1.eventually (Ioo_mem_nhds ha.1.1 ha.1.2)
  have heβ := (hc0.sub hc1).eventually (Ioo_mem_nhds ha.2.1.1 ha.2.1.2)
  have heγ := hc2.eventually (Ioo_mem_nhds ha.2.2.1.1 ha.2.2.1.2)
  have heδ := (hc2.const_sub T).eventually (Ioo_mem_nhds ha.2.2.2.1.1 ha.2.2.2.1.2)
  apply native_rank_of_parametric_rank (f := splitHalfLengths q T)
    (g := nativeSplitController p t q h l T) (x := x) hd hf
  · filter_upwards [heα, heβ, heγ, heδ] with z hα hβ hγ hδ
    exact nativeLengthController_splitHalfLengths (ne_of_gt hq0) hα hβ hγ hδ
  · exact fderiv_nativeSplitController_surjective_of_incident_minor hp hp1 hl hl1
      ht htq hq hh hhq ha hzero hminor

theorem fderiv_nativeLengthController_surjective_of_fixedHalf_minor
    {p t q h l γ : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q)
    (hl : 0 < l) (hl1 : l < 1) (hh : 0 < h) (hhq : h < q) (hq : 0 < q)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) γ (x 2 - γ))
    (hzero : incidentNativeController p t q h l γ x = 0)
    (hminor : Real.cos (x 0) *
        ((1 - angleSlope p (x 1)) + (1 - angleSlope l (x 0 - x 1)) -
          (1 - angleSlope p (x 1)) * (1 - angleSlope (h / q) (x 2 - γ))) +
      (Real.cos (x 2) / q) *
        ((1 - angleSlope p (x 1)) + (1 - angleSlope l (x 0 - x 1)) -
          (1 - angleSlope p (x 1)) * (1 - angleSlope l (x 0 - x 1))) ≠ 0) :
    Function.Surjective (fderiv ℝ (nativeLengthController p t q h l)
      (incidentHalfLengths q γ x)) := by
  have hd := differentiableAt_nativeLengthController_of_physical hp ht hq hh hl
    (nativeLengthPhysical_splitHalfLengths (x := ![x 0, x 1, γ]) (T := x 2)
      hp hp1 ht htq hl hl1 hq ha)
  have hf : DifferentiableAt ℝ (incidentHalfLengths q γ) x := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [incidentHalfLengths, splitHalfLengths] <;> fun_prop
  have hc0 : ContinuousAt (fun z : Fin 3 → ℝ => z 0) x := (continuous_apply 0).continuousAt
  have hc1 : ContinuousAt (fun z : Fin 3 → ℝ => z 1) x := (continuous_apply 1).continuousAt
  have hc2 : ContinuousAt (fun z : Fin 3 → ℝ => z 2) x := (continuous_apply 2).continuousAt
  have heα := hc1.eventually (Ioo_mem_nhds ha.1.1 ha.1.2)
  have heβ := (hc0.sub hc1).eventually (Ioo_mem_nhds ha.2.1.1 ha.2.1.2)
  have heδ := (hc2.sub_const γ).eventually (Ioo_mem_nhds ha.2.2.2.1.1 ha.2.2.2.1.2)
  apply native_rank_of_parametric_rank (f := incidentHalfLengths q γ)
    (g := incidentNativeController p t q h l γ) (x := x) hd hf
  · filter_upwards [heα, heβ, heδ] with z hα hβ hδ
    exact nativeLengthController_splitHalfLengths (x := ![z 0, z 1, γ])
      (ne_of_gt hq) hα hβ ha.2.2.1 hδ
  · exact fderiv_incidentNativeController_surjective_of_minor
      hp hp1 ht hl hl1 hh hhq hq ha hzero hminor

/-- Actual native rank loss forces both independent incidence minors to
vanish. The conclusion is an exact derivative statement, not a numerical test. -/
theorem incident_minors_vanish_of_not_surjective
    {p t q h l α β γ δ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hh : 0 < h) (hhq : h < q)
    (ha : StrictAngles q h α β γ δ)
    (hzero : (nativeHalfClosure p t q h l α β γ δ,
      turnDefect p t q h l α β γ δ) = 0)
    (hnon : ¬Function.Surjective (fderiv ℝ (nativeLengthController p t q h l)
      ![Real.sin α, Real.sin γ / q, Real.sin δ / q, Real.sin β])) :
    let A := 1 - angleSlope p α
    let B := 1 - angleSlope l β
    let C := 1 - angleSlope (t / q) γ
    let D := 1 - angleSlope (h / q) δ
    A * D = B * C ∧
      Real.cos (α + β) * (A + B - A * D) +
        (Real.cos (γ + δ) / q) * (A + B - A * B) = 0 := by
  dsimp only
  constructor
  · by_contra hne
    apply hnon
    have hax : StrictAngles q h (![α + β, α, γ] 1)
        (![α + β, α, γ] 0 - ![α + β, α, γ] 1)
        (![α + β, α, γ] 2) ((γ + δ) - ![α + β, α, γ] 2) := by
      simpa using ha
    have hzx : nativeSplitController p t q h l (γ + δ) ![α + β, α, γ] = 0 := by
      simpa [nativeSplitController] using hzero
    have hmx : (1 - angleSlope p (![α + β, α, γ] 1)) *
        (1 - angleSlope (h / q) ((γ + δ) - ![α + β, α, γ] 2)) ≠
        (1 - angleSlope l (![α + β, α, γ] 0 - ![α + β, α, γ] 1)) *
        (1 - angleSlope (t / q) (![α + β, α, γ] 2)) := by simpa using hne
    simpa [splitHalfLengths] using
      fderiv_nativeLengthController_surjective_of_fixedTurn_minor
        hp hp1 hl hl1 ht htq hq hh hhq hax hzx hmx
  · by_contra hne
    apply hnon
    have hax : StrictAngles q h (![α + β, α, γ + δ] 1)
        (![α + β, α, γ + δ] 0 - ![α + β, α, γ + δ] 1) γ
        (![α + β, α, γ + δ] 2 - γ) := by simpa using ha
    have hzx : incidentNativeController p t q h l γ ![α + β, α, γ + δ] = 0 := by
      simpa [incidentNativeController] using hzero
    have hs := fderiv_nativeLengthController_surjective_of_fixedHalf_minor
      hp hp1 ht htq hl hl1 hh hhq (by linarith : 0 < q) hax hzx
    apply (show Function.Surjective (fderiv ℝ (nativeLengthController p t q h l)
        (incidentHalfLengths q γ ![α + β, α, γ + δ])) → _ by
      simp [incidentHalfLengths, splitHalfLengths])
    apply hs
    simpa using hne

/-- The actual endpoint tangent is its incidence slope times the pure tangent. -/
theorem tan_angleAtom_eq_slope_mul_tan {a z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.tan (angleAtom a z) = angleSlope a z * Real.tan z := by
  have hc : Real.cos z ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hz.1], hz.2⟩)
  rw [angleAtom, Real.tan_arcsin, angleSlope, Real.tan_eq_sin_div_cos]
  field_simp [hc]

/-- Cross-multiplied tangent addition is valid even if an intermediate
two-angle turn is right. Only the four individual cosines are divided out. -/
theorem tangent_turn_polynomial {x y z w : ℝ}
    (hx : Real.cos x ≠ 0) (hy : Real.cos y ≠ 0)
    (hz : Real.cos z ≠ 0) (hw : Real.cos w ≠ 0)
    (hsum : x + y + z + w = Real.pi) :
    (Real.tan z * Real.tan w - 1) * (Real.tan x + Real.tan y) =
      (Real.tan z + Real.tan w) * (1 - Real.tan x * Real.tan y) := by
  have hs : Real.sin (x + y + z + w) = 0 := by rw [hsum, Real.sin_pi]
  simp only [Real.sin_add, Real.cos_add] at hs
  simp only [Real.tan_eq_sin_div_cos]
  field_simp [hx, hy, hz, hw]
  nlinarith [hs]

/-- Pure polynomial form of the first mixed-turn identity in normalized
projective coordinates. -/
theorem first_projective_turn_polynomial {P Q b r k : ℝ}
    (hQ : Q ≠ 0) (hb : b ≠ 0)
    (hturn : ((P / b) * (1 / b) - 1) *
        ((P * b / Q) * (1 - 2 * r) + (b / Q) * (1 - 2 * k)) =
      (P / b + 1 / b) *
        (1 - ((P * b / Q) * (1 - 2 * r)) * ((b / Q) * (1 - 2 * k)))) :
    Q * (P - b ^ 2) * (P * (1 - 2 * r) + (1 - 2 * k)) -
      (P + 1) * (Q ^ 2 - P * b ^ 2 * (1 - 2 * r) * (1 - 2 * k)) = 0 := by
  field_simp [hQ, hb] at hturn
  nlinarith [hturn]

/-- Pure polynomial form of the reflected mixed-turn identity. -/
theorem second_projective_turn_polynomial {P Q b r k T : ℝ}
    (hQ : Q ≠ 0) (hb : b ≠ 0) (hT : T ≠ 0)
    (hturn : ((P * b / Q) * (b / Q) - 1) *
        ((1 / b) * (1 - 2 * k / T) + (P / b) * (1 - 2 * r / T)) =
      (P * b / Q + b / Q) *
        (1 - ((1 / b) * (1 - 2 * k / T)) * ((P / b) * (1 - 2 * r / T)))) :
    (P * b ^ 2 - Q ^ 2) * T * (T - 2 * k + P * (T - 2 * r)) -
      Q * (P + 1) * (b ^ 2 * T ^ 2 - P * (T - 2 * k) * (T - 2 * r)) = 0 := by
  field_simp [hQ, hb, hT] at hturn
  nlinarith [hturn]

/-- The second native minor becomes the exact affine line-value relation. -/
theorem projective_affine_of_incident_minor
    {P Q K A B C D R W : ℝ} (hK : K ≠ 0) (_hA : A ≠ 0) (hB : B ≠ 0)
    (hR : R = K * (Q - P ^ 2)) (hW : W = K * P * (Q - 1))
    (hcross : A * D = B * C)
    (hminor : R * (A + B - A * D) + W * (A + B - A * B) = 0) :
    -(P + 1) * (P - Q) * (1 + A / B) +
      2 * (P ^ 2 - Q) * (C / 2) - 2 * P * (Q - 1) * (A / 2) = 0 := by
  rw [hR, hW] at hminor
  have hm : (Q - P ^ 2) * (A + B - A * D) +
      P * (Q - 1) * (A + B - A * B) = 0 := by
    apply (mul_left_cancel₀ hK)
    nlinarith [hminor]
  field_simp [hB]
  rw [hcross] at hm
  linear_combination hm

theorem acute_projective_coordinates {α β γ δ : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hβ : β ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hγ : γ ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hδ : δ ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hT : γ + δ < Real.pi / 2)
    (hprod : Real.tan α * Real.tan δ = Real.tan β * Real.tan γ)
    (hprod1 : 1 < Real.tan α * Real.tan δ) :
    let P := Real.tan α / Real.tan γ
    let Q := 1 / (Real.tan γ * Real.tan δ)
    let b := 1 / Real.tan δ
    0 < b ∧ 1 < Q ∧ Q < P ∧
      Real.tan α = P * b / Q ∧ Real.tan β = P / b ∧
      Real.tan γ = b / Q ∧ Real.tan δ = 1 / b := by
  have ha := Real.tan_pos_of_pos_of_lt_pi_div_two hα.1 hα.2
  have hb := Real.tan_pos_of_pos_of_lt_pi_div_two hβ.1 hβ.2
  have hc := Real.tan_pos_of_pos_of_lt_pi_div_two hγ.1 hγ.2
  have hd := Real.tan_pos_of_pos_of_lt_pi_div_two hδ.1 hδ.2
  have hcg : 0 < Real.cos γ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hγ.1], hγ.2⟩
  have hcd : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hδ.1], hδ.2⟩
  have hct : 0 < Real.cos (γ + δ) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hγ.1, hδ.1], hT⟩
  have htprod : Real.tan γ * Real.tan δ < 1 := by
    rw [Real.cos_add] at hct
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
    rw [div_mul_div_comm, div_lt_one (mul_pos hcg hcd)]
    linarith
  dsimp only
  refine ⟨one_div_pos.mpr hd, (one_lt_div (mul_pos hc hd)).mpr htprod, ?_, ?_, ?_, ?_, ?_⟩
  · apply (div_lt_div_iff₀ (mul_pos hc hd) hc).mpr
    nlinarith [mul_lt_mul_of_pos_right hprod1 hc]
  · field_simp
  · apply (mul_right_cancel₀ (ne_of_gt hc))
    field_simp
    nlinarith [hprod]
  · field_simp
  · field_simp

theorem incident_projective_parameters {A B C D : ℝ}
    (hA : A ∈ Ioo (0 : ℝ) 1) (hB : B ∈ Ioo (0 : ℝ) 1)
    (hC : C ∈ Ioo (0 : ℝ) 1) (hD : D ∈ Ioo (0 : ℝ) 1)
    (hcross : A * D = B * C) :
    0 < A / 2 ∧ A / 2 < 1 / 2 ∧ 0 < C / 2 ∧ C / 2 < 1 / 2 ∧
    2 * (A / 2) < A / B ∧ 2 * (C / 2) < A / B ∧
    B = 2 * (A / 2) / (A / B) ∧ D = 2 * (C / 2) / (A / B) := by
  refine ⟨half_pos hA.1, by linarith [hA.2], half_pos hC.1, by linarith [hC.2], ?_, ?_, ?_, ?_⟩
  · apply (lt_div_iff₀ hB.1).mpr
    nlinarith [mul_lt_mul_of_pos_left hB.2 hA.1]
  · apply (lt_div_iff₀ hB.1).mpr
    nlinarith [mul_lt_mul_of_pos_left hD.2 hA.1]
  · field_simp [ne_of_gt hA.1, ne_of_gt hB.1]
  · field_simp [ne_of_gt hA.1, ne_of_gt hB.1]
    nlinarith [hcross]

/-- The exact algebraic packet forced by rank loss in the one-sided chamber. -/
structure IncidentProjectiveRankLoss where
  P : ℝ
  Q : ℝ
  B : ℝ
  r : ℝ
  k : ℝ
  T : ℝ
  one_lt_Q : 1 < Q
  Q_lt_P : Q < P
  B_pos : 0 < B
  r_pos : 0 < r
  r_half : r < 1 / 2
  k_pos : 0 < k
  k_half : k < 1 / 2
  r_T : 2 * r < T
  k_T : 2 * k < T
  affine : -(P + 1) * (P - Q) * (1 + T) +
    2 * (P ^ 2 - Q) * k - 2 * P * (Q - 1) * r = 0
  turnOne : Q * (P - B) * (P * (1 - 2 * r) + (1 - 2 * k)) -
    (P + 1) * (Q ^ 2 - P * B * (1 - 2 * r) * (1 - 2 * k)) = 0
  turnTwo : (P * B - Q ^ 2) * T * (T - 2 * k + P * (T - 2 * r)) -
    Q * (P + 1) * (B * T ^ 2 - P * (T - 2 * k) * (T - 2 * r)) = 0

private theorem defectSlope_mem_Ioo {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : z ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    1 - angleSlope a z ∈ Ioo (0 : ℝ) 1 :=
  ⟨lowDefect_derivative_pos ha ha1 hz.1 hz.2,
    by linarith [angleSlope_pos ha hz.1 hz.2 (endpoint_arg_lt_one ha ha1 hz.1 hz.2)]⟩

private theorem atom_cos_pos {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : z ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.cos (angleAtom a z) := by
  have hpos : 0 < angleAtom a z := Real.arcsin_pos.mpr
    (mul_pos ha (Real.sin_pos_of_pos_of_lt_pi hz.1 (by linarith [hz.2, Real.pi_pos])))
  have hlt : angleAtom a z < Real.pi / 2 :=
    (endpointAtom_lt_angle ha ha1 hz.1 hz.2).trans hz.2
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩

/-- Both native derivative minors, the original two seam equations and
the genuine orthogonal tangent chart produce the archived polynomial packet. -/
theorem incidentProjectiveRankLoss_of_angles
    {p t q h l α β γ δ : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hh : 0 < h) (hhq : h < q)
    (ha : StrictAngles q h α β γ δ)
    (hT : γ + δ < Real.pi / 2)
    (hprod : Real.tan α * Real.tan δ = Real.tan β * Real.tan γ)
    (hprod1 : 1 < Real.tan α * Real.tan δ)
    (hcos : let P := Real.tan α / Real.tan γ
      let Q := 1 / (Real.tan γ * Real.tan δ)
      Real.cos (α + β) = (Q - P ^ 2) / Q * Real.cos α * Real.cos β ∧
        Real.cos (γ + δ) / q = P * (Q - 1) / Q * Real.cos α * Real.cos β)
    (hzero : (nativeHalfClosure p t q h l α β γ δ,
      turnDefect p t q h l α β γ δ) = 0)
    (hnon : ¬Function.Surjective (fderiv ℝ (nativeLengthController p t q h l)
      ![Real.sin α, Real.sin γ / q, Real.sin δ / q, Real.sin β])) :
    Nonempty IncidentProjectiveRankLoss := by
  let P := Real.tan α / Real.tan γ
  let Q := 1 / (Real.tan γ * Real.tan δ)
  let b := 1 / Real.tan δ
  let A := 1 - angleSlope p α
  let B := 1 - angleSlope l β
  let C := 1 - angleSlope (t / q) γ
  let D := 1 - angleSlope (h / q) δ
  let r := A / 2
  let k := C / 2
  let T := A / B
  have hq0 : 0 < q := by linarith
  obtain ⟨hb, hQ, hQP, hαtan, hβtan, hγtan, hδtan⟩ :=
    acute_projective_coordinates ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 hT hprod hprod1
  change 0 < b at hb
  change 1 < Q at hQ
  change Q < P at hQP
  change Real.tan α = P * b / Q at hαtan
  change Real.tan β = P / b at hβtan
  change Real.tan γ = b / Q at hγtan
  change Real.tan δ = 1 / b at hδtan
  have hA := defectSlope_mem_Ioo hp hp1 ha.1
  have hB := defectSlope_mem_Ioo hl hl1 ha.2.1
  have hC := defectSlope_mem_Ioo (div_pos ht hq0) ((div_lt_one hq0).mpr htq) ha.2.2.1
  have hD := defectSlope_mem_Ioo (div_pos hh hq0) ((div_lt_one hq0).mpr hhq) ha.2.2.2.1
  obtain ⟨hcross, hminor⟩ := incident_minors_vanish_of_not_surjective
    hp hp1 hl hl1 ht htq hq hh hhq ha hzero hnon
  change A * D = B * C at hcross
  change Real.cos (α + β) * (A + B - A * D) +
    (Real.cos (γ + δ) / q) * (A + B - A * B) = 0 at hminor
  obtain ⟨hr0, hr1, hk0, hk1, hrT, hkT, hBT, hDT⟩ :=
    incident_projective_parameters hA hB hC hD hcross
  change 0 < r at hr0
  change r < 1 / 2 at hr1
  change 0 < k at hk0
  change k < 1 / 2 at hk1
  change 2 * r < T at hrT
  change 2 * k < T at hkT
  change B = 2 * r / T at hBT
  change D = 2 * k / T at hDT
  have hT0 : 0 < T := by linarith
  have hQ0 : 0 < Q := by linarith
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ha.1.1, Real.pi_pos], ha.1.2⟩
  have hcβ : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ha.2.1.1, Real.pi_pos], ha.2.1.2⟩
  have hcγ : 0 < Real.cos γ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ha.2.2.1.1, Real.pi_pos], ha.2.2.1.2⟩
  have hcδ : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ha.2.2.2.1.1, Real.pi_pos], ha.2.2.2.1.2⟩
  let K := Real.cos α * Real.cos β / Q
  have hK : 0 < K := div_pos (mul_pos hcα hcβ) hQ0
  have hR : Real.cos (α + β) = K * (Q - P ^ 2) := by
    rw [hcos.1]
    change (Q - P ^ 2) / Q * Real.cos α * Real.cos β = K * (Q - P ^ 2)
    dsimp only [K]
    ring
  have hW : Real.cos (γ + δ) / q = K * P * (Q - 1) := by
    rw [hcos.2]
    change P * (Q - 1) / Q * Real.cos α * Real.cos β = K * P * (Q - 1)
    dsimp only [K]
    ring
  have haff := projective_affine_of_incident_minor (ne_of_gt hK)
    (ne_of_gt hA.1) (ne_of_gt hB.1) hR hW hcross hminor
  have tx : Real.tan (angleAtom p α) = (P * b / Q) * (1 - 2 * r) := by
    rw [tan_angleAtom_eq_slope_mul_tan ha.1, hαtan]
    dsimp [r, A]
    ring
  have ty : Real.tan (angleAtom (t / q) γ) = (b / Q) * (1 - 2 * k) := by
    rw [tan_angleAtom_eq_slope_mul_tan ha.2.2.1, hγtan]
    dsimp [k, C]
    ring
  have tz : Real.tan (angleAtom (h / q) δ) = (1 / b) * (1 - 2 * k / T) := by
    rw [tan_angleAtom_eq_slope_mul_tan ha.2.2.2.1, hδtan]
    change 1 - angleSlope (h / q) δ = 2 * k / T at hDT
    nlinarith only [congrArg (fun x : ℝ => (1 / b) * x) hDT]
  have tw : Real.tan (angleAtom l β) = (P / b) * (1 - 2 * r / T) := by
    rw [tan_angleAtom_eq_slope_mul_tan ha.2.1, hβtan]
    change 1 - angleSlope l β = 2 * r / T at hBT
    nlinarith only [congrArg (fun x : ℝ => (P / b) * x) hBT]
  have hz := (native_zero_iff_of_strictAngles (l := l) hp.le ht.le hq0 ha).mp
    ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  have hlow : angleAtom p α + angleAtom (t / q) γ + β + δ = Real.pi := by
    have he := hz.2.1
    unfold seamLow lowTurn at he
    linarith only [he]
  have hhigh : angleAtom (h / q) δ + angleAtom l β + α + γ = Real.pi := by
    have he := hz.2.2
    unfold seamHigh highTurn at he
    linarith only [he]
  have ht1 := tangent_turn_polynomial
    (ne_of_gt (atom_cos_pos hp hp1 ha.1))
    (ne_of_gt (atom_cos_pos (div_pos ht hq0) ((div_lt_one hq0).mpr htq) ha.2.2.1))
    (ne_of_gt hcβ) (ne_of_gt hcδ) hlow
  rw [tx, ty, hβtan, hδtan] at ht1
  have ht2 := tangent_turn_polynomial
    (ne_of_gt (atom_cos_pos (div_pos hh hq0) ((div_lt_one hq0).mpr hhq) ha.2.2.2.1))
    (ne_of_gt (atom_cos_pos hl hl1 ha.2.1))
    (ne_of_gt hcα) (ne_of_gt hcγ) hhigh
  rw [tz, tw, hαtan, hγtan] at ht2
  exact ⟨⟨P, Q, b ^ 2, r, k, T, hQ, hQP, sq_pos_of_pos hb, hr0, hr1, hk0, hk1,
    hrT, hkT, haff,
    first_projective_turn_polynomial (ne_of_gt hQ0) (ne_of_gt hb) ht1,
    second_projective_turn_polynomial (ne_of_gt hQ0) (ne_of_gt hb) (ne_of_gt hT0) ht2⟩⟩

theorem IncidentProjectiveRankLoss.false (z : IncidentProjectiveRankLoss) : False :=
  NativeIncidentProjective.not_projective_turn_solution z.one_lt_Q z.Q_lt_P z.B_pos
    z.r_pos z.k_pos z.k_half z.r_T z.k_T z.turnOne z.turnTwo z.affine

/-- Every strict original orthogonal incident anchor has native rank three
in the acute higher-pure-turn chamber. No supplied minor is assumed. -/
theorem fderiv_nativeLengthController_surjective_of_acute_orthogonal
    {p t q h l u v : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hh : 0 < h) (hhq : h < q)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hphys : NativeLengthPhysical p t q h l (orderedCoreHalfLengths u q v))
    (hzero : nativeLengthController p t q h l (orderedCoreHalfLengths u q v) = 0)
    (hT : Real.arcsin (q * orderedCoreHalfLengths u q v 1) +
      Real.arcsin (q * orderedCoreHalfLengths u q v 2) < Real.pi / 2) :
    Function.Surjective (fderiv ℝ (nativeLengthController p t q h l)
      (orderedCoreHalfLengths u q v)) := by
  let L := orderedCoreHalfLengths u q v
  let α := Real.arcsin (L 0)
  let β := Real.arcsin (L 3)
  let γ := Real.arcsin (q * L 1)
  let δ := Real.arcsin (q * L 2)
  have hq0 : 0 < q := by linarith
  obtain ⟨hα, hβ, hγ, hδ⟩ := coreHalfLengths_angles_acute hu.1 hu.2 hq hv.1 hv.2
  obtain ⟨a0, a3, a1, a2⟩ := coreHalfLengths_angle_data hu.1 hu.2 hq hv.1 hv.2
  have hs0 : Real.sin α = L 0 := Real.sin_arcsin (by linarith [a0.1.1]) a0.1.2.le
  have hs3 : Real.sin β = L 3 := Real.sin_arcsin (by linarith [a3.1.1]) a3.1.2.le
  have hs1 : Real.sin γ = q * L 1 := Real.sin_arcsin (by linarith [a1.1.1]) a1.1.2.le
  have hs2 : Real.sin δ = q * L 2 := Real.sin_arcsin (by linarith [a2.1.1]) a2.1.2.le
  have ha : StrictAngles q h α β γ δ := by
    refine ⟨hα, hβ, hγ, hδ, ?_⟩
    rw [hs2]
    have hh2 := hphys.2.2.2.2.2.2.1
    convert hh2 using 1
    field_simp
    rfl
  have hL : ![Real.sin α, Real.sin γ / q, Real.sin δ / q, Real.sin β] = L := by
    ext i
    fin_cases i <;> simp [hs0, hs3, hs1, hs2, ne_of_gt hq0]
  have hx : StrictAngles q h (![α + β, α, γ] 1)
      (![α + β, α, γ] 0 - ![α + β, α, γ] 1)
      (![α + β, α, γ] 2) ((γ + δ) - ![α + β, α, γ] 2) := by simpa using ha
  have hnative := nativeLengthController_splitHalfLengths
    (p := p) (t := t) (h := h) (l := l) (x := ![α + β, α, γ]) (T := γ + δ)
    (ne_of_gt hq0) hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
  have hz : (nativeHalfClosure p t q h l α β γ δ,
      turnDefect p t q h l α β γ δ) = 0 := by
    have he : nativeLengthController p t q h l
        ![Real.sin α, Real.sin γ / q, Real.sin δ / q, Real.sin β] =
        (nativeHalfClosure p t q h l α β γ δ, turnDefect p t q h l α β γ δ) := by
      simpa [splitHalfLengths, nativeSplitController] using hnative
    rw [← he, hL]
    exact hzero
  obtain ⟨htan1, htan2⟩ := coreHalfLengths_tan_products hu.1 hu.2 hq hv.1 hv.2
  have htaneq : Real.tan α * Real.tan δ = Real.tan β * Real.tan γ := htan1.trans htan2.symm
  have htan_gt : 1 < Real.tan α * Real.tan δ :=
    coreHalfLengths_tan_product_gt_one hu.1 hu.2 hq hv.1 hv.2
  have hcos := coreHalfLengths_normalized_cos hu.1 hu.2 hq hv.1 hv.2
  by_contra hn
  have hn' : ¬Function.Surjective (fderiv ℝ (nativeLengthController p t q h l)
      ![Real.sin α, Real.sin γ / q, Real.sin δ / q, Real.sin β]) := by rwa [hL]
  obtain ⟨z⟩ := incidentProjectiveRankLoss_of_angles hp hp1 hl hl1 ht htq hq hh hhq
    ha hT htaneq htan_gt hcos hz hn'
  exact z.false

/-- The acute and nonacute chambers together prove full native rank at
every strict orthogonal incident anchor with unequal pure curvatures. -/
theorem fderiv_nativeLengthController_surjective_of_incident_orthogonal
    {p t q h l u v : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hh : 0 < h) (hhq : h < q)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hphys : NativeLengthPhysical p t q h l (orderedCoreHalfLengths u q v))
    (hzero : nativeLengthController p t q h l (orderedCoreHalfLengths u q v) = 0) :
    Function.Surjective (fderiv ℝ (nativeLengthController p t q h l)
      (orderedCoreHalfLengths u q v)) := by
  by_cases hT : Real.pi / 2 ≤ Real.arcsin (q * orderedCoreHalfLengths u q v 1) +
      Real.arcsin (q * orderedCoreHalfLengths u q v 2)
  · exact fderiv_nativeLengthController_surjective_of_nonacute_incident hp hp1 ht htq
      hl hl1 hh hhq hq.le hphys hzero hT
  · exact fderiv_nativeLengthController_surjective_of_acute_orthogonal hp hp1 hl hl1
      ht htq hq hh hhq hu hv hphys hzero (lt_of_not_ge hT)

/-- The original two negative flags now produce a regular physical anchor,
including actual four-length derivative surjectivity for dormant opening. -/
theorem exists_nativeLength_regular_of_negative_corners {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hh : 0 < h) (hhq : h < q) (hq : 1 < q)
    (hflag : firstPairFlag p t q l < 0)
    (hreflected : firstPairFlag l h q p < 0) :
    ∃ L : Fin 4 → ℝ, NativeLengthPhysical p t q h l L ∧
      nativeLengthController p t q h l L = 0 ∧
      Function.Surjective (fderiv ℝ (nativeLengthController p t q h l) L) := by
  obtain ⟨u, v, hu, hv, hphys, _, hzero⟩ :=
    exists_nativeLength_anchor_of_negative_corners hp hp1 hl hl1 ht htq hh hhq hq hflag hreflected
  exact ⟨orderedCoreHalfLengths u q v, hphys, hzero,
    fderiv_nativeLengthController_surjective_of_incident_orthogonal hp hp1 hl hl1
      ht htq hq hh hhq hu hv hphys hzero⟩

end Gluck.Discrete.NativeOppositePure
