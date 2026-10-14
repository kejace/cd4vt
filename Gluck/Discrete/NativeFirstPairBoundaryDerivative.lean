/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.NativeFirstPairInterior
import Gluck.Discrete.NativeOppositePureRank
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! # The inward first-pair derivative at the outgoing pure-one wall

This is an original-angle calculation at `α = π/2`, `γ = 0`.
It needs only the strict remaining physical guards, not equality or
strictness of a failure flag. The final high-seam derivative is in fact
strictly larger than one.
-/

namespace Gluck.Discrete.NativeOppositePure

open Set

theorem hasDerivAt_lowTurn_boundary {p t q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun α : ℝ => lowTurn p t q α 0) 0 (Real.pi / 2) := by
  have hs : HasDerivAt (fun α : ℝ => p * Real.sin α) 0 (Real.pi / 2) := by
    simpa using (Real.hasDerivAt_sin (Real.pi / 2)).const_mul p
  have ha : HasDerivAt Real.arcsin (1 / √(1 - p ^ 2)) (p * Real.sin (Real.pi / 2)) := by
    simpa using Real.hasDerivAt_arcsin (by linarith : p ≠ -1) (ne_of_lt hp1)
  have hd := ha.comp (Real.pi / 2) hs
  simpa [lowTurn, angleAtom, Function.comp_def] using hd

theorem hasDerivAt_interiorD_boundary {p t q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun α : ℝ => interiorD p t q α 0)
      (-q * √(1 - p ^ 2)) (Real.pi / 2) := by
  have hφ := (hasDerivAt_lowTurn_boundary (t := t) (q := q) hp hp1).sub
    (hasDerivAt_id (Real.pi / 2))
  have hcos := hφ.cos
  have hd := (hcos.const_mul q).sub_const (Real.cos 0)
  simpa [interiorD, lowTurn, angleAtom, Real.sin_sub_pi_div_two,
    Real.cos_arcsin, Function.comp_def, Pi.sub_apply] using hd

theorem hasDerivAt_interiorN_boundary {p t q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun α : ℝ => interiorN p t q α 0)
      (q * p) (Real.pi / 2) := by
  have hφ := (hasDerivAt_lowTurn_boundary (t := t) (q := q) hp hp1).sub
    (hasDerivAt_id (Real.pi / 2))
  have hsin := hφ.sin
  have hd := (hsin.const_mul q).const_sub (Real.sin 0)
  simpa [interiorN, lowTurn, angleAtom, Real.cos_sub_pi_div_two,
    Real.sin_arcsin (by linarith : -1 ≤ p) hp1.le, Function.comp_def, Pi.sub_apply] using hd

/-- The arctangent cap angle moves strictly in the positive direction
as alpha increases at the construction boundary. -/
theorem exists_pos_derivative_interiorDelta_boundary {p t q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hD : 0 < interiorD p t q (Real.pi / 2) 0)
    (hN : 0 < interiorN p t q (Real.pi / 2) 0) :
    ∃ d > 0, HasDerivAt (fun α : ℝ => interiorDelta p t q α 0) d (Real.pi / 2) := by
  have hrad : 0 < 1 - p ^ 2 := by nlinarith
  have hsqrt : 0 < √(1 - p ^ 2) := Real.sqrt_pos.2 hrad
  let D := interiorD p t q (Real.pi / 2) 0
  let N := interiorN p t q (Real.pi / 2) 0
  let d := (q * p * D - N * (-q * √(1 - p ^ 2))) / D ^ 2
  have hd : 0 < d := by
    dsimp [d, D, N]
    apply div_pos
    · nlinarith [mul_pos (mul_pos hq hp) hD,
        mul_pos hN (mul_pos hq hsqrt)]
    · exact sq_pos_of_pos hD
  have hquot := (hasDerivAt_interiorN_boundary (t := t) (q := q) hp hp1).div
    (hasDerivAt_interiorD_boundary (t := t) (q := q) hp hp1) (ne_of_gt hD)
  have harctan := (Real.hasDerivAt_arctan (N / D)).comp (Real.pi / 2) hquot
  refine ⟨1 / (1 + (N / D) ^ 2) * d, mul_pos (by positivity) hd, ?_⟩
  simpa only [interiorDelta, D, N, d, Function.comp_def, Pi.div_apply] using harctan

theorem exists_derivative_gt_one_interiorHigh_boundary {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hqh : q < h)
    (hl : 0 < l) (hl1 : l < 1)
    (hphysical : InteriorPhysical p t q h (Real.pi / 2) 0) :
    ∃ d > 1, HasDerivAt (fun α : ℝ => interiorHigh p t q h l α 0) d (Real.pi / 2) := by
  obtain ⟨dδ, hdδ, hδD⟩ := exists_pos_derivative_interiorDelta_boundary hp hp1 hq
    hphysical.1 hphysical.2.1
  have hlow := hasDerivAt_lowTurn_boundary (t := t) (q := q) hp hp1
  have hβD : HasDerivAt (fun α : ℝ => interiorBeta p t q α 0) (-dδ) (Real.pi / 2) := by
    convert (hδD.const_sub Real.pi).sub hlow using 1 <;> simp [interiorBeta]
    rfl
  have hδpos := interiorDelta_pos hphysical.1 hphysical.2.1
  have hδlt := interiorDelta_lt_pi_div_two p t q (Real.pi / 2) 0
  have hβ := hphysical.2.2.1
  have hwall := hphysical.2.2.2
  have hlowwall := endpoint_arg_lt_one hl hl1 hβ.1 hβ.2
  have hhighD := (hasDerivAt_angleAtom (div_pos (lt_trans hq hqh) hq)
    hδpos hδlt hwall).comp (Real.pi / 2) hδD
  have hlowD := (hasDerivAt_angleAtom hl hβ.1 hβ.2 hlowwall).comp (Real.pi / 2) hβD
  have hhighSlope := one_lt_angleSlope ((one_lt_div hq).2 hqh) hδpos hδlt hwall
  have hlowSlope := angleSlope_lt_one hl hl1 hβ.1 hβ.2
  refine ⟨1 + (angleSlope (h / q) (interiorDelta p t q (Real.pi / 2) 0) -
      angleSlope l (interiorBeta p t q (Real.pi / 2) 0)) * dδ, ?_, ?_⟩
  · nlinarith [mul_pos (sub_pos.mpr (lt_trans hlowSlope hhighSlope)) hdδ]
  · have hd := (((hasDerivAt_id (Real.pi / 2)).add_const 0).add
      (hhighD.add hlowD)).sub_const Real.pi
    convert hd using 1 <;> simp [interiorHigh, seamHigh, highTurn, Function.comp_def]
    ring

/-- The positive derivative hypothesis used by the compact boundary-IVT
consumer is produced from the original strict physical conditions. -/
theorem exists_pos_derivative_interiorHigh_boundary {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hqh : q < h)
    (hl : 0 < l) (hl1 : l < 1)
    (hphysical : InteriorPhysical p t q h (Real.pi / 2) 0) :
    ∃ d > 0, HasDerivAt (fun α : ℝ => interiorHigh p t q h l α 0) d (Real.pi / 2) := by
  obtain ⟨d, hd, hD⟩ := exists_derivative_gt_one_interiorHigh_boundary
    hp hp1 hq hqh hl hl1 hphysical
  exact ⟨d, lt_trans zero_lt_one hd, hD⟩

end Gluck.Discrete.NativeOppositePure
