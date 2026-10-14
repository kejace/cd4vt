import Gluck.Discrete.NativeOppositePureClosure
import Gluck.Discrete.NativeOppositePureRank

/-!
# Rank of the original opposite-pure closure equations

This file differentiates the exact off-zero native closure identity. Thus
the split-controller rank is transferred to the actual complex closure and
lifted real turn, without replacing either equation by a relaxed residual.
-/

namespace Gluck.Discrete.NativeOppositePure

/-- Original half-closure and lifted turn in coordinates `(S, α, γ)` at
fixed second pure turn `T`. -/
noncomputable def nativeSplitController (p t q h l T : ℝ) (x : Fin 3 → ℝ) : ℂ × ℝ :=
  (nativeHalfClosure p t q h l (x 1) (x 0 - x 1) (x 2) (T - x 2),
    turnDefect p t q h l (x 1) (x 0 - x 1) (x 2) (T - x 2))

private theorem hasFDerivAt_phase {f : (Fin 3 → ℝ) → ℝ}
    {f' : (Fin 3 → ℝ) →L[ℝ] ℝ} {x : Fin 3 → ℝ}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun z => unitPhase (f z))
      ((unitPhase (f x) * Complex.I) • (Complex.ofRealCLM.comp f')) x := by
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp x hf).mul_const Complex.I
  simpa only [unitPhase, Function.comp_def, Complex.ofRealCLM_apply, smul_smul,
    mul_comm] using hc.cexp

/-- Differentiation of the exact identity at a simultaneous split zero.
The target transformation is proved bijective in `NativeOppositePureClosure`. -/
theorem hasFDerivAt_nativeSplitController_of_split
    {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    {f' : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)}
    (hf : HasFDerivAt (splitController p t q h l T) f' x)
    (hz : splitController p t q h l T x = 0) :
    HasFDerivAt (nativeSplitController p t q h l T)
      ((closureTargetLinearMap (x 0 - x 1) (Real.sin T / q)
        (Complex.I * (Real.sin (x 0 - x 1) : ℂ) *
          unitPhase (-(x 0)))).toContinuousLinearMap.comp f')
      x := by
  let f := splitController p t q h l T
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 x
  have hM := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt.comp x hf
  have hH := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).hasFDerivAt.comp x hf
  have hK := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt.comp x hf
  have hMC := Complex.ofRealCLM.hasFDerivAt.comp x hM
  have hphase := hasFDerivAt_phase (h0.sub h1).neg
  have hLow := hasFDerivAt_phase hH
  have hTurn := hasFDerivAt_phase (hH.add hK)
  have hsin := (Real.hasDerivAt_sin (x 0 - x 1)).comp_hasFDerivAt x (h0.sub h1)
  have hsinC := Complex.ofRealCLM.hasFDerivAt.comp x hsin
  have hcoeff := hsinC.mul (hasFDerivAt_phase h0.neg)
  have hE := (hphase.mul (hMC.add ((hLow.const_sub 1).const_mul
    ((Real.sin T / q : ℝ) : ℂ)))).add (hcoeff.mul (hTurn.sub_const 1))
  have hprod := hE.prodMk (hH.add hK)
  have hfun : (fun z : Fin 3 → ℝ =>
      (unitPhase (-(z 0 - z 1)) *
          ((f z 0 : ℂ) + ((Real.sin T / q : ℝ) : ℂ) * (1 - unitPhase (f z 1))) +
        (Real.sin (z 0 - z 1) : ℂ) * unitPhase (-(z 0)) *
          (unitPhase (f z 1 + f z 2) - 1), f z 1 + f z 2)) =
      nativeSplitController p t q h l T := by
    funext z
    apply Prod.ext
    · simp only [nativeSplitController, nativeHalfClosure_eq]
      have ht := seamLow_add_seamHigh p t q h l (z 1) (z 0 - z 1) (z 2) (T - z 2)
      simp only [f, splitController, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, chord]
      rw [ht]
      simp only [add_sub_cancel]
      push_cast
      ring
    · exact seamLow_add_seamHigh p t q h l (z 1) (z 0 - z 1) (z 2) (T - z 2)
  change HasFDerivAt (fun z : Fin 3 → ℝ =>
      (unitPhase (-(z 0 - z 1)) *
          ((f z 0 : ℂ) + ((Real.sin T / q : ℝ) : ℂ) * (1 - unitPhase (f z 1))) +
        (Real.sin (z 0 - z 1) : ℂ) * unitPhase (-(z 0)) *
          (unitPhase (f z 1 + f z 2) - 1), f z 1 + f z 2)) _ x at hprod
  rw [hfun] at hprod
  apply hprod.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · simp [closureTargetLinearMap, Function.comp_def, hz, unitPhase]
    ring
  · simp [closureTargetLinearMap]

/-- Every strict opposite-pure zero has surjective derivative for the
original complex half-closure and lifted turn, in the three split variables. -/
theorem fderiv_nativeSplitController_surjective
    {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hqh : q < h)
    (hangles : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2))
    (hlow : seamLow p t q (x 1) (x 0 - x 1) (x 2) (T - x 2) = 0)
    (hchord : chord q (x 1) (x 0 - x 1) (x 2) (T - x 2) = 0)
    (hhigh : seamHigh q h l (x 1) (x 0 - x 1) (x 2) (T - x 2) = 0) :
    Function.Surjective (fderiv ℝ (nativeSplitController p t q h l T) x) := by
  have hq0 : 0 < q := by linarith
  have hf := hasFDerivAt_splitController hp hp1 hl hl1 ht htq hq0 hqh hangles
  have hz : splitController p t q h l T x = 0 := by
    ext i
    fin_cases i <;> simp [splitController, hlow, hchord, hhigh]
  have hn := hasFDerivAt_nativeSplitController_of_split hf hz
  have hsin : 0 < Real.sin T := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hangles.2.2.1.1, hangles.2.2.2.1.1])
    (by linarith [hangles.2.2.1.2, hangles.2.2.2.1.2])
  rw [hn.fderiv]
  have htarget := closureTargetLinearMap_surjective
    (β := x 0 - x 1) (ne_of_gt (div_pos hsin hq0))
    (Complex.I * (Real.sin (x 0 - x 1) : ℂ) * unitPhase (-(x 0)))
  have hsplit := fderiv_splitController_surjective hp hp1 hl hl1 ht htq hq hqh
    hangles hlow hchord
  rw [hf.fderiv] at hsplit
  exact htarget.comp hsplit

/-- The same rank conclusion stated solely with the original native
closure/full-turn zero, rather than with split-equation hypotheses. -/
theorem fderiv_nativeSplitController_surjective_of_native_zero
    {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hqh : q < h)
    (hangles : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2))
    (hzero : nativeSplitController p t q h l T x = 0) :
    Function.Surjective (fderiv ℝ (nativeSplitController p t q h l T) x) := by
  have hz := (native_zero_iff_of_strictAngles (l := l) hp.le ht.le
    (by linarith : 0 < q) hangles).mp
    ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  exact fderiv_nativeSplitController_surjective hp hp1 hl hl1 ht htq hq hqh
    hangles hz.2.1 hz.1 hz.2.2

/-- The actual four positive half-lengths in cyclic edge order. -/
noncomputable def splitHalfLengths (q T : ℝ) (x : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![Real.sin (x 1), Real.sin (x 2) / q,
    Real.sin (T - x 2) / q, Real.sin (x 0 - x 1)]

/-- The four original corner turns, expressed in the actual half-lengths. -/
noncomputable def lengthTurns (p t q h l : ℝ) (L : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![Real.arcsin (L 3) + Real.arcsin (L 0),
    Real.arcsin (p * L 0) + Real.arcsin (t * L 1),
    Real.arcsin (q * L 1) + Real.arcsin (q * L 2),
    Real.arcsin (h * L 2) + Real.arcsin (l * L 3)]

/-- Original four-edge half-closure and full-turn defect, with all eight
actual endpoint arcs retained. The first edge has heading zero. -/
noncomputable def nativeLengthController (p t q h l : ℝ) (L : Fin 4 → ℝ) : ℂ × ℝ :=
  let θ := lengthTurns p t q h l L
  ((L 0 : ℂ) + (L 1 : ℂ) * unitPhase (θ 1) +
    (L 2 : ℂ) * unitPhase (θ 1 + θ 2) +
    (L 3 : ℂ) * unitPhase (θ 1 + θ 2 + θ 3),
    θ 0 + θ 1 + θ 2 + θ 3 - 2 * Real.pi)

theorem nativeLengthController_splitHalfLengths
    {p t q h l T : ℝ} {x : Fin 3 → ℝ} (hq : q ≠ 0)
    (hα : x 1 ∈ Set.Ioo 0 (Real.pi / 2))
    (hβ : x 0 - x 1 ∈ Set.Ioo 0 (Real.pi / 2))
    (hγ : x 2 ∈ Set.Ioo 0 (Real.pi / 2))
    (hδ : T - x 2 ∈ Set.Ioo 0 (Real.pi / 2)) :
    nativeLengthController p t q h l (splitHalfLengths q T x) =
      nativeSplitController p t q h l T x := by
  have hs (z : ℝ) (hz : z ∈ Set.Ioo 0 (Real.pi / 2)) :
      Real.arcsin (Real.sin z) = z :=
    Real.arcsin_sin (by linarith [hz.1, Real.pi_pos]) hz.2.le
  have he (a z : ℝ) : a * (Real.sin z / q) = (a / q) * Real.sin z := by ring
  simp only [nativeLengthController, lengthTurns, splitHalfLengths,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, nativeSplitController,
    nativeHalfClosure, turnDefect,
    lowTurn, highTurn, angleAtom]
  simp only [mul_div_cancel₀ _ hq, he, hs _ hα, hs _ hβ, hs _ hγ, hs _ hδ]
  apply Prod.ext
  · rfl
  · ring

private theorem sin_mem_unit {z : ℝ} (hz : z ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin z ∈ Set.Ioo 0 1 := by
  refine ⟨Real.sin_pos_of_pos_of_lt_pi hz.1 (by linarith [hz.2, Real.pi_pos]), ?_⟩
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ z by linarith [hz.1, Real.pi_pos]) le_rfl hz.2
  simpa using h

/-- The original half-length controller is differentiable at every strict
physical point used by the opposite-pure construction. -/
theorem differentiableAt_nativeLengthController_splitHalfLengths
    {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 0 < q) (hqh : q < h)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2)) :
    DifferentiableAt ℝ (nativeLengthController p t q h l) (splitHalfLengths q T x) := by
  let L := splitHalfLengths q T x
  have hsa := sin_mem_unit ha.1
  have hsb := sin_mem_unit ha.2.1
  have hsg := sin_mem_unit ha.2.2.1
  have hsd := sin_mem_unit ha.2.2.2.1
  have hqh0 : 0 < h / q := div_pos (by linarith) hq
  have hpa : p * Real.sin (x 1) ∈ Set.Ioo 0 1 :=
    ⟨mul_pos hp hsa.1, endpoint_arg_lt_one hp hp1 ha.1.1 ha.1.2⟩
  have htg : (t / q) * Real.sin (x 2) ∈ Set.Ioo 0 1 :=
    ⟨mul_pos (div_pos ht hq) hsg.1,
      endpoint_arg_lt_one (div_pos ht hq) ((div_lt_one hq).2 htq)
        ha.2.2.1.1 ha.2.2.1.2⟩
  have hhd : (h / q) * Real.sin (T - x 2) ∈ Set.Ioo 0 1 :=
    ⟨mul_pos hqh0 hsd.1, ha.2.2.2.2⟩
  have hlb : l * Real.sin (x 0 - x 1) ∈ Set.Ioo 0 1 :=
    ⟨mul_pos hl hsb.1, endpoint_arg_lt_one hl hl1 ha.2.1.1 ha.2.1.2⟩
  have hd {g : (Fin 4 → ℝ) → ℝ} (hg : DifferentiableAt ℝ g L)
      (hw : g L ∈ Set.Ioo 0 1) : DifferentiableAt ℝ (fun z => Real.arcsin (g z)) L :=
    (Real.differentiableAt_arcsin.mpr ⟨by linarith [hw.1], ne_of_lt hw.2⟩).comp L hg
  have h0 := hd (g := fun z => z 0) (by fun_prop) (by simpa [L, splitHalfLengths] using hsa)
  have h3 := hd (g := fun z => z 3) (by fun_prop) (by simpa [L, splitHalfLengths] using hsb)
  have hp0 := hd (g := fun z => p * z 0) (by fun_prop) (by simpa [L, splitHalfLengths] using hpa)
  have ht1 := hd (g := fun z => t * z 1) (by fun_prop)
    (by simpa [L, splitHalfLengths, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using htg)
  have hq1 := hd (g := fun z => q * z 1) (by fun_prop)
    (by simpa [L, splitHalfLengths, mul_div_cancel₀, ne_of_gt hq] using hsg)
  have hq2 := hd (g := fun z => q * z 2) (by fun_prop)
    (by simpa [L, splitHalfLengths, mul_div_cancel₀, ne_of_gt hq] using hsd)
  have hh2 := hd (g := fun z => h * z 2) (by fun_prop)
    (by simpa [L, splitHalfLengths, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hhd)
  have hl3 := hd (g := fun z => l * z 3) (by fun_prop) (by simpa [L, splitHalfLengths] using hlb)
  change DifferentiableAt ℝ (nativeLengthController p t q h l) L
  unfold nativeLengthController lengthTurns unitPhase
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Matrix.head_fin_const]
  fun_prop

/-- Surjectivity in the four actual positive half-length variables. No
orthogonality or independently assumed active-column rank is required. -/
theorem fderiv_nativeLengthController_surjective
    {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hq : 1 < q) (hqh : q < h)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2))
    (hzero : nativeSplitController p t q h l T x = 0) :
    Function.Surjective
      (fderiv ℝ (nativeLengthController p t q h l) (splitHalfLengths q T x)) := by
  have hq0 : 0 < q := by linarith
  have hc0 : ContinuousAt (fun z : Fin 3 → ℝ => z 0) x := (continuous_apply 0).continuousAt
  have hc1 : ContinuousAt (fun z : Fin 3 → ℝ => z 1) x := (continuous_apply 1).continuousAt
  have hc2 : ContinuousAt (fun z : Fin 3 → ℝ => z 2) x := (continuous_apply 2).continuousAt
  have heα := hc1.eventually (Ioo_mem_nhds ha.1.1 ha.1.2)
  have heβ := (hc0.sub hc1).eventually (Ioo_mem_nhds ha.2.1.1 ha.2.1.2)
  have heγ := hc2.eventually (Ioo_mem_nhds ha.2.2.1.1 ha.2.2.1.2)
  have heδ := (hc2.const_sub T).eventually
    (Ioo_mem_nhds ha.2.2.2.1.1 ha.2.2.2.1.2)
  have he : (nativeLengthController p t q h l ∘ splitHalfLengths q T) =ᶠ[nhds x]
      nativeSplitController p t q h l T := by
    filter_upwards [heα, heβ, heγ, heδ] with z hα hβ hγ hδ
    exact nativeLengthController_splitHalfLengths (ne_of_gt hq0) hα hβ hγ hδ
  have hdL := differentiableAt_nativeLengthController_splitHalfLengths
    hp hp1 hl hl1 ht htq hq0 hqh ha
  have hdS : DifferentiableAt ℝ (splitHalfLengths q T) x := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [splitHalfLengths]
    all_goals fun_prop
  have hs := fderiv_nativeSplitController_surjective_of_native_zero
    hp hp1 hl hl1 ht htq hq hqh ha hzero
  rw [← he.fderiv_eq, fderiv_comp x hdL hdS] at hs
  intro y
  obtain ⟨v, hv⟩ := hs y
  exact ⟨fderiv ℝ (splitHalfLengths q T) x v, hv⟩

end Gluck.Discrete.NativeOppositePure
