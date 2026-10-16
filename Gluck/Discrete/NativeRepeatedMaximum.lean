module

public import Gluck.Discrete.NativeNegativeCorners
public import ForMathlib.Analysis.Complex.PoincareMiranda

/-!
# Native four-slot anchors between equal maximum readings

The two actual pure readings are both one. All four mixed endpoint readings
lie strictly below one. An interior rectangle gives strict residual signs,
and Poincaré–Miranda supplies an original, strictly physical native zero.
-/

@[expose] public section

namespace Gluck.Discrete.NativeOppositePure

open Set N6TypeAThreeCell

private lemma equalPeak_denom_pos {u v : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 < 1 - u ^ 2 * v ^ 2 := by
  have huv0 : 0 < u * v := mul_pos hu.1 hv.1
  have huv1 : u * v < 1 := (mul_lt_mul_of_pos_right hu.2 hv.1).trans (by simpa using hv.2)
  nlinarith [sq_nonneg (u * v - 1)]

private lemma equalPeak_scale_bounds {u v : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 < Real.sqrt (1 - v ^ 2) / Real.sqrt (1 - u ^ 2 * v ^ 2) ∧
    Real.sqrt (1 - v ^ 2) / Real.sqrt (1 - u ^ 2 * v ^ 2) < 1 := by
  have hn : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hd := equalPeak_denom_pos hu hv
  refine ⟨div_pos (Real.sqrt_pos.2 hn) (Real.sqrt_pos.2 hd), ?_⟩
  apply (div_lt_one (Real.sqrt_pos.2 hd)).2
  apply Real.sqrt_lt_sqrt hn.le
  have hu2 : u ^ 2 < 1 := by nlinarith [hu.1, hu.2]
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv.1
  nlinarith [mul_lt_mul_of_pos_right hu2 hv2]

private lemma arcsin_mul_strict {x y a : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) (ha : a ∈ Ioo (0 : ℝ) 1) :
    Real.arcsin (x * a) < Real.arcsin (y * a) := by
  apply Real.arcsin_lt_arcsin
  · nlinarith [mul_pos hx ha.1]
  · exact mul_lt_mul_of_pos_right hxy ha.1
  · exact ((mul_lt_mul_of_pos_right hy ha.1).trans (by simpa using ha.2)).le

lemma equalPeak_first_residual_pos {p t u v : ℝ}
    (hp1 : p < 1) (ht1 : t < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hup : u < p) (hut : u < t) : 0 < rResidualOne p t 1 u v := by
  have ha := equalPeak_scale_bounds hu hv
  have hp := arcsin_mul_strict hu.1 hup hp1 ha
  have ht := arcsin_mul_strict hu.1 hut ht1 ha
  simp only [rResidualOne, one_pow]
  linarith

lemma equalPeak_first_residual_neg {p t u v : ℝ}
    (hp : 0 < p) (ht : 0 < t)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hpu : p < u) (htu : t < u) : rResidualOne p t 1 u v < 0 := by
  have ha := equalPeak_scale_bounds hu hv
  have hp' := arcsin_mul_strict hp hpu hu.2 ha
  have ht' := arcsin_mul_strict ht htu hu.2 ha
  simp only [rResidualOne, one_pow]
  linarith

/-- With two equal pure maxima, every four positive submaximal endpoint
readings have an interior zero of the literal residuals. -/
theorem exists_r_zero_of_repeated_maximum {p t h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hh1 : h < 1) (hl : 0 < l) (hl1 : l < 1) :
    ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, rResidualMap p t 1 h l z = 0 := by
  let a := min (min p t) (min h l) / 2
  let b := (1 + max (max p t) (max h l)) / 2
  have ha0 : 0 < a := half_pos (lt_min (lt_min hp ht) (lt_min hh hl))
  have hap : a < p := by dsimp [a]; linarith [min_le_left p t, min_le_left (min p t) (min h l)]
  have hat : a < t := by dsimp [a]; linarith [min_le_right p t, min_le_left (min p t) (min h l)]
  have hah : a < h := by dsimp [a]; linarith [min_le_left h l, min_le_right (min p t) (min h l)]
  have hal : a < l := by dsimp [a]; linarith [min_le_right h l, min_le_right (min p t) (min h l)]
  have hb1 : b < 1 := by
    have := max_lt (max_lt hp1 ht1) (max_lt hh1 hl1)
    dsimp [b]; linarith
  have hpb : p < b := by dsimp [b]; linarith [le_max_left p t, le_max_left (max p t) (max h l)]
  have htb : t < b := by dsimp [b]; linarith [le_max_right p t, le_max_left (max p t) (max h l)]
  have hhb : h < b := by dsimp [b]; linarith [le_max_left h l, le_max_right (max p t) (max h l)]
  have hlb : l < b := by dsimp [b]; linarith [le_max_right h l, le_max_right (max p t) (max h l)]
  have hab : a < b := hap.trans hpb
  have hsub : ∀ x ∈ Icc a b, x ∈ Ioo (0 : ℝ) 1 :=
    fun x hx => ⟨ha0.trans_le hx.1, hx.2.trans_lt hb1⟩
  have ha : a ∈ Ioo (0 : ℝ) 1 := hsub a ⟨le_rfl, hab.le⟩
  have hb : b ∈ Ioo (0 : ℝ) 1 := hsub b ⟨hab.le, le_rfl⟩
  have hden : ∀ z ∈ Icc a b ×ˢ Icc a b, 0 < (1 : ℝ)^2 - z.1^2 * z.2^2 := by
    intro z hz
    simpa using equalPeak_denom_pos (hsub z.1 hz.1) (hsub z.2 hz.2)
  let R : ℝ × ℝ → ℝ × ℝ := fun z =>
    (-rResidualOne p t 1 z.1 z.2, -rResidualThree 1 h l z.1 z.2)
  have hR : ContinuousOn R (Icc a b ×ˢ Icc a b) :=
    (continuousOn_rResidualOne_of_denom_pos (p := p) (t := t) hden).neg.prodMk
      (continuousOn_rResidualThree_of_denom_pos (h := h) (l := l) hden).neg
  obtain ⟨z, hz, hzero⟩ := poincare_miranda hab.le hab.le R hR
    (fun v hv => neg_nonpos.mpr (equalPeak_first_residual_pos hp1 ht1 ha (hsub v hv) hap hat).le)
    (fun v hv => neg_nonneg.mpr (equalPeak_first_residual_neg hp ht hb (hsub v hv) hpb htb).le)
    (fun u hu => by
      change -rResidualThree 1 h l u a ≤ 0
      rw [rResidualThree_eq_swap]
      exact neg_nonpos.mpr (equalPeak_first_residual_pos hl1 hh1 ha (hsub u hu) hal hah).le)
    (fun u hu => by
      change 0 ≤ -rResidualThree 1 h l u b
      rw [rResidualThree_eq_swap]
      exact neg_nonneg.mpr (equalPeak_first_residual_neg hl hh hb (hsub u hu) hlb hhb).le)
  refine ⟨z, ⟨hsub z.1 hz.1, hsub z.2 hz.2⟩, ?_⟩
  apply Complex.ext
  · have hF := congrArg Prod.fst hzero
    change -rResidualOne p t 1 z.1 z.2 = 0 at hF
    simpa only [r_residual_map_re, Complex.zero_re] using neg_eq_zero.mp hF
  · have hG := congrArg Prod.snd hzero
    change -rResidualThree 1 h l z.1 z.2 = 0 at hG
    simpa only [r_residual_map_im, Complex.zero_im] using neg_eq_zero.mp hG

private theorem equalPeak_native_zero_of_four_realization
    {u v a b c d : ℝ}
    (hc : closureGap (fourProfile 1 u 1 v) (fourProfile a b c d) = 0)
    (ht : turningSum (fourProfile 1 u 1 v) (fourProfile a b c d) = 2 * Real.pi) :
    nativeLengthController u u 1 v v ![a / 2, b / 2, c / 2, d / 2] = 0 := by
  let θ := lengthTurns u u 1 v v ![a / 2, b / 2, c / 2, d / 2]
  have h0 : turningAngle 0 (fourProfile 1 u 1 v) (fourProfile a b c d) 0 = θ 0 := by
    norm_num [turningAngle, θ, lengthTurns]
    rfl
  have h1 : turningAngle 0 (fourProfile 1 u 1 v) (fourProfile a b c d) 1 = θ 1 := by
    norm_num [turningAngle, θ, lengthTurns]
  have h2 : turningAngle 0 (fourProfile 1 u 1 v) (fourProfile a b c d) 2 = θ 2 := by
    norm_num [turningAngle, θ, lengthTurns]
  have h3 : turningAngle 0 (fourProfile 1 u 1 v) (fourProfile a b c d) 3 = θ 3 := by
    norm_num [turningAngle, θ, lengthTurns]
  have hturn : θ 0 + θ 1 + θ 2 + θ 3 = 2 * Real.pi := by
    unfold turningSum at ht
    rw [← sum_range_natCast_add (turningAngle 0 (fourProfile 1 u 1 v)
      (fourProfile a b c d)) 0] at ht
    simpa [Finset.sum_range_succ, h0, h1, h2, h3] using ht
  have hclosure := closure_gap_four_unit_phase (fourProfile 1 u 1 v) (fourProfile a b c d)
  rw [hc, h0, h1, h2, h3] at hclosure
  have hfactor : (2 : ℂ) * unitPhase (θ 0) *
      (nativeLengthController u u 1 v v ![a / 2, b / 2, c / 2, d / 2]).1 = 0 := by
    rw [hclosure]
    dsimp only [nativeLengthController]
    change (2 : ℂ) * unitPhase (θ 0) *
      ((a / 2 : ℝ) + (b / 2 : ℝ) * unitPhase (θ 1) +
        (c / 2 : ℝ) * unitPhase (θ 1 + θ 2) +
        (d / 2 : ℝ) * unitPhase (θ 1 + θ 2 + θ 3)) = _
    simp only [unitPhase_add, fourProfile_zero, fourProfile_one,
      fourProfile_two, fourProfile_three]
    push_cast
    ring
  apply Prod.ext
  · exact (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))
  · change θ 0 + θ 1 + θ 2 + θ 3 - 2 * Real.pi = 0
    linarith

/-- The original residuals preserve both mixed turns of an equal-peak core,
so its actual native closure and lifted full turn are unchanged. -/
theorem native_zero_of_repeated_r_zero {p t h l u v : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1)
    (hz : rResidualMap p t 1 h l (u, v) = 0) :
    nativeLengthController p t 1 h l (orderedCoreHalfLengths u 1 v) = 0 := by
  have hd := r_core_realization_data zero_lt_one hu.1 zero_lt_one hv.1
    hu.2 hu.2 hv.2 hv.2
  have hcore := equalPeak_native_zero_of_four_realization hd.2.1 hd.2.2.1
  have hr1 : rResidualOne p t 1 u v = 0 := by
    simpa [rResidualMap] using congrArg Complex.re hz
  have hr3 : rResidualThree 1 h l u v = 0 := by
    simpa [rResidualMap] using congrArg Complex.im hz
  rw [r_residual_one_eq_core_sides] at hr1
  rw [r_residual_three_eq_core_sides] at hr3
  have hturn : lengthTurns p t 1 h l (orderedCoreHalfLengths u 1 v) =
      lengthTurns u u 1 v v (orderedCoreHalfLengths u 1 v) := by
    ext i
    fin_cases i <;> dsimp [lengthTurns, orderedCoreHalfLengths] <;> linarith
  unfold nativeLengthController
  rw [hturn]
  exact hcore

/-- All eight actual endpoint walls are strict on an interior equal-peak core. -/
theorem repeatedMaximumCore_physical {p t h l u v : ℝ}
    (hp1 : p < 1) (ht1 : t < 1) (hh1 : h < 1) (hl1 : l < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    NativeLengthPhysical p t 1 h l (orderedCoreHalfLengths u 1 v) := by
  have hd := r_core_realization_data zero_lt_one hu.1 zero_lt_one hv.1
    hu.2 hu.2 hv.2 hv.2
  have hs := r_core_sides_pos zero_lt_one hu.1 zero_lt_one hv.1 hu.2 hu.2 hv.2 hv.2
  have hm := moderateArc_zero_iff.mp hd.1
  have hw0 := (hm (0 : ZMod 4)).2
  have hw2 := (hm (2 : ZMod 4)).2
  change |(1 : ℝ)| * (rCoreSideD 1 u 1 v / 2) < 1 ∧
    |(1 : ℝ)| * (rCoreSideA 1 u 1 v / 2) < 1 at hw0
  change |(1 : ℝ)| * (rCoreSideB 1 u 1 v / 2) < 1 ∧
    |(1 : ℝ)| * (rCoreSideC 1 u 1 v / 2) < 1 at hw2
  simp only [abs_one, one_mul] at hw0 hw2
  refine ⟨?_, hw0.2, ?_, ?_, ?_, ?_, ?_, ?_, hw0.1⟩
  · intro i
    fin_cases i
    · exact half_pos hs.1
    · exact half_pos hs.2.1
    · exact half_pos hs.2.2.1
    · exact half_pos hs.2.2.2
  · exact (mul_lt_mul_of_pos_right hp1 (half_pos hs.1)).trans (by simpa using hw0.2)
  · exact (mul_lt_mul_of_pos_right ht1 (half_pos hs.2.1)).trans (by simpa using hw2.1)
  · change 1 * (rCoreSideB 1 u 1 v / 2) < 1
    simpa only [one_mul] using hw2.1
  · change 1 * (rCoreSideC 1 u 1 v / 2) < 1
    simpa only [one_mul] using hw2.2
  · exact (mul_lt_mul_of_pos_right hh1 (half_pos hs.2.2.1)).trans (by simpa using hw2.2)
  · exact (mul_lt_mul_of_pos_right hl1 (half_pos hs.2.2.2)).trans (by simpa using hw0.1)

/-- Two actual repeated maxima produce a positive, strictly physical native
anchor, retaining all four original mixed endpoint readings. -/
theorem exists_nativeLength_anchor_of_repeated_maximum {p t h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hh1 : h < 1) (hl : 0 < l) (hl1 : l < 1) :
    ∃ u v : ℝ, u ∈ Ioo (0 : ℝ) 1 ∧ v ∈ Ioo (0 : ℝ) 1 ∧
      NativeLengthPhysical p t 1 h l (orderedCoreHalfLengths u 1 v) ∧
      rResidualMap p t 1 h l (u, v) = 0 ∧
      nativeLengthController p t 1 h l (orderedCoreHalfLengths u 1 v) = 0 := by
  obtain ⟨z, hz, hzero⟩ := exists_r_zero_of_repeated_maximum hp hp1 ht ht1 hh hh1 hl hl1
  exact ⟨z.1, z.2, hz.1, hz.2, repeatedMaximumCore_physical hp1 ht1 hh1 hl1 hz.1 hz.2,
    hzero, native_zero_of_repeated_r_zero hz.1 hz.2 hzero⟩

end Gluck.Discrete.NativeOppositePure
