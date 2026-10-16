module

public import Gluck.Discrete.NativeOppositePurePhysical
public import Gluck.Discrete.NativeFirstPairFlag
public import Gluck.Discrete.N6TypeAThreeCellR

/-!
# Native anchors from an ordered first failed pair

The crossed-rectangle existence theorem is reused with its original
principal residuals and all endpoint guards. No new winding argument is
introduced here.
-/

@[expose] public section

namespace Gluck.Discrete.NativeOppositePure

open Set N6TypeAThreeCell

/-- The preceding original flag is exactly the complementary corner of
the archived crossed rectangle. -/
theorem r_corner_eq_firstPairFlag {p t q l : ℝ}
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) :
    rResidualOne p t q 1 l = firstPairFlag p t q l := by
  rw [r_residual_one_bottom_right_eq hl.le (by linarith)]
  rw [firstPairFlag, firstPairSigma, Real.sqrt_div (by nlinarith : 0 ≤ 1 - l ^ 2)]
  ring

/-- Original current failure and previous strict success provide an
interior zero of both unmodified mixed-corner residuals. -/
theorem exists_ordered_r_zero
    {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hpt : p < t) (htq : t < q) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l)
    (hprev : firstPairFlag p t q l < 0) :
    h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2 ∧
      ∃ z ∈ Ioo p 1 ×ˢ Ioo l 1, rResidualMap p t q h l z = 0 := by
  let r := √(1 - p ^ 2)
  let a := √((h ^ 2 - 1) / (1 - l ^ 2))
  let s := firstPairSigma h l
  let rho := √(1 - p ^ 2) / √(q ^ 2 - p ^ 2)
  have hP : 0 < 1 - p ^ 2 := by nlinarith
  have hL : 0 < 1 - l ^ 2 := by nlinarith
  have hH : 0 < h ^ 2 - 1 := by nlinarith
  have hQ : 0 < q ^ 2 - p ^ 2 := by nlinarith
  have hr : 0 < r := Real.sqrt_pos.mpr hP
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos hH hL)
  have hr2 : r ^ 2 = 1 - p ^ 2 := Real.sq_sqrt hP.le
  have ha2 : a ^ 2 = (h ^ 2 - 1) / (1 - l ^ 2) :=
    Real.sq_sqrt (div_pos hH hL).le
  have haeq : a ^ 2 * (1 - l ^ 2) = h ^ 2 - 1 := by
    rw [ha2, div_mul_cancel₀ _ (ne_of_gt hL)]
  obtain ⟨hs, _hs1, hsig, _hswall⟩ := firstPairSigma_data (by linarith : 1 < h) hl hl1
  have hsp : s < p := (firstPairFlag_guard_and_bound hp hp1 hl hl1 hq hqh hflag).1
  have hseq : s ^ 2 * (1 + a ^ 2) = 1 := by
    have he : (1 + a ^ 2) * (1 - l ^ 2) = h ^ 2 - l ^ 2 := by nlinarith
    have hs' : s ^ 2 * (h ^ 2 - l ^ 2) = 1 - l ^ 2 := hsig
    apply (mul_left_inj' (ne_of_gt hL)).mp
    nlinarith [congrArg (fun z : ℝ => s ^ 2 * z) he]
  have hsq := firstPairFlag_square_bound hp hp1 hl hl1 hq hqh hflag
  have hcrit : p + r * a ≤ q := by
    have hprod : (r * a) ^ 2 * (1 - l ^ 2) =
        (1 - p ^ 2) * (h ^ 2 - 1) := by
      rw [mul_pow, hr2]
      nlinarith [congrArg (fun z : ℝ => (1 - p ^ 2) * z) haeq]
    have hsq' : (r * a) ^ 2 ≤ (q - p) ^ 2 := by
      nlinarith
    have hle := (sq_le_sq₀ (mul_pos hr ha).le (by linarith : 0 ≤ q - p)).mp hsq'
    linarith
  have hrho : 0 < rho := div_pos hr (Real.sqrt_pos.mpr hQ)
  have hrhosq : rho ^ 2 * (q ^ 2 - p ^ 2) = r ^ 2 := by
    dsimp [rho, r]
    rw [div_pow, Real.sq_sqrt hQ.le, div_mul_cancel₀ _ (ne_of_gt hQ)]
  have hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2 := by
    have hw := critical_hWall_pos hp hr ha hs hsp (by linarith) hl hl1 hr2 haeq hseq
    have hc := (sq_le_sq₀ (by positivity : 0 ≤ p + r * a)
      (by linarith : 0 ≤ q)).mpr hcrit
    rw [hr2] at hw
    exact hw.trans_le hc
  refine ⟨hbase, exists_r_residual_zero_of_failure hp hr ha hs hsp hpt htq
    (by linarith) hl hl1 hr2 haeq hseq hcrit hrho hrhosq rfl ?_⟩
  rwa [r_corner_eq_firstPairFlag hl hl1 hq]

/-- Cyclic half-lengths of the named orthogonal core. -/
noncomputable def orderedCoreHalfLengths (u q v : ℝ) : Fin 4 → ℝ :=
  ![rCoreSideA 1 u q v / 2, rCoreSideB 1 u q v / 2,
    rCoreSideC 1 u q v / 2, rCoreSideD 1 u q v / 2]

private theorem native_zero_of_four_realization
    {u q v a b c d : ℝ}
    (hc : closureGap (fourProfile 1 u q v) (fourProfile a b c d) = 0)
    (ht : turningSum (fourProfile 1 u q v) (fourProfile a b c d) = 2 * Real.pi) :
    nativeLengthController u u q v v ![a / 2, b / 2, c / 2, d / 2] = 0 := by
  let θ := lengthTurns u u q v v ![a / 2, b / 2, c / 2, d / 2]
  have h0 : turningAngle 0 (fourProfile 1 u q v) (fourProfile a b c d) 0 = θ 0 := by
    norm_num [turningAngle, θ, lengthTurns]
    rfl
  have h1 : turningAngle 0 (fourProfile 1 u q v) (fourProfile a b c d) 1 = θ 1 := by
    norm_num [turningAngle, θ, lengthTurns]
  have h2 : turningAngle 0 (fourProfile 1 u q v) (fourProfile a b c d) 2 = θ 2 := by
    norm_num [turningAngle, θ, lengthTurns]
  have h3 : turningAngle 0 (fourProfile 1 u q v) (fourProfile a b c d) 3 = θ 3 := by
    norm_num [turningAngle, θ, lengthTurns]
  have hturn : θ 0 + θ 1 + θ 2 + θ 3 = 2 * Real.pi := by
    unfold turningSum at ht
    rw [← sum_range_natCast_add (turningAngle 0 (fourProfile 1 u q v)
      (fourProfile a b c d)) 0] at ht
    simpa [Finset.sum_range_succ, h0, h1, h2, h3] using ht
  have hclosure := closure_gap_four_unit_phase (fourProfile 1 u q v) (fourProfile a b c d)
  rw [hc, h0, h1, h2, h3] at hclosure
  have hfactor : (2 : ℂ) * unitPhase (θ 0) *
      (nativeLengthController u u q v v ![a / 2, b / 2, c / 2, d / 2]).1 = 0 := by
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

/-- An original residual zero changes neither core turn, and therefore
preserves literal native closure and the lifted full turn. -/
theorem native_zero_of_ordered_r_zero {p t q h l u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hq : 1 < q) (hu1 : u < 1) (hv1 : v < 1)
    (hz : rResidualMap p t q h l (u, v) = 0) :
    nativeLengthController p t q h l (orderedCoreHalfLengths u q v) = 0 := by
  have hd := r_core_realization_data (q := q) zero_lt_one hu (by linarith) hv
    hu1 (by linarith) hv1 (by linarith)
  have hcore := native_zero_of_four_realization hd.2.1 hd.2.2.1
  have hr1 : rResidualOne p t q u v = 0 := by
    simpa [rResidualMap] using congrArg Complex.re hz
  have hr3 : rResidualThree q h l u v = 0 := by
    simpa [rResidualMap] using congrArg Complex.im hz
  rw [r_residual_one_eq_core_sides] at hr1
  rw [r_residual_three_eq_core_sides] at hr3
  have hturn : lengthTurns p t q h l (orderedCoreHalfLengths u q v) =
      lengthTurns u u q v v (orderedCoreHalfLengths u q v) := by
    ext i
    fin_cases i <;> dsimp [lengthTurns, orderedCoreHalfLengths] <;> linarith
  unfold nativeLengthController
  rw [hturn]
  exact hcore

/-- Every original incidence wall is strict throughout the interior of
the crossed rectangle, under its derived high-endpoint bound. -/
theorem orderedCoreHalfLengths_physical {p t q h l u v : ℝ}
    (hp : 0 < p) (hl : 0 < l) (hpt : p < t) (htq : t < q)
    (hq : 1 < q) (hqh : q < h)
    (hpu : p < u) (hu1 : u < 1) (hlv : l < v) (hv1 : v < 1)
    (hbase : h ^ 2 * (1 - p ^ 2) + p ^ 2 < q ^ 2) :
    NativeLengthPhysical p t q h l (orderedCoreHalfLengths u q v) := by
  have hu : 0 < u := hp.trans hpu
  have hv : 0 < v := hl.trans hlv
  have hd := r_core_realization_data (q := q) zero_lt_one hu (by linarith) hv
    hu1 (by linarith) hv1 (by linarith)
  have hs := r_core_sides_pos zero_lt_one hu (by linarith : 0 < q) hv
    hu1 (by linarith) hv1 (by linarith)
  have hm := moderateArc_zero_iff.mp hd.1
  have hw0 := (hm (0 : ZMod 4)).2
  have hw1 := (hm (1 : ZMod 4)).2
  have hw2 := (hm (2 : ZMod 4)).2
  have hw3 := (hm (3 : ZMod 4)).2
  change |(1 : ℝ)| * (rCoreSideD 1 u q v / 2) < 1 ∧
    |(1 : ℝ)| * (rCoreSideA 1 u q v / 2) < 1 at hw0
  change |u| * (rCoreSideA 1 u q v / 2) < 1 ∧
    |u| * (rCoreSideB 1 u q v / 2) < 1 at hw1
  change |q| * (rCoreSideB 1 u q v / 2) < 1 ∧
    |q| * (rCoreSideC 1 u q v / 2) < 1 at hw2
  change |v| * (rCoreSideC 1 u q v / 2) < 1 ∧
    |v| * (rCoreSideD 1 u q v / 2) < 1 at hw3
  simp only [abs_one, one_mul] at hw0
  rw [abs_of_pos hu] at hw1
  rw [abs_of_pos (by linarith : 0 < q)] at hw2
  rw [abs_of_pos hv] at hw3
  have htB := r_actual_t_sideB_wall_lt_one (hp.trans hpt) htq hq
    hu.le hu1.le hv.le hv1
  have hhC := r_actual_h_sideC_wall_lt_one hp.le hpu.le (by linarith)
    hu1 hv.le hv1.le hbase
  refine ⟨?_, hw0.2, ?_, (abs_lt.mp htB).2, hw2.1, hw2.2,
    (abs_lt.mp hhC).2, ?_, hw0.1⟩
  · intro i
    fin_cases i
    · exact half_pos hs.1
    · exact half_pos hs.2.1
    · exact half_pos hs.2.2.1
    · exact half_pos hs.2.2.2
  · exact (mul_lt_mul_of_pos_right hpu (half_pos hs.1)).trans hw1.1
  · exact (mul_lt_mul_of_pos_right hlv (half_pos hs.2.2.2)).trans hw3.2

/-- Ordered-entry first failure produces a positive, strictly physical
four-active native anchor for the original endpoint slots. -/
theorem exists_nativeLength_anchor_of_ordered_firstPair
    {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hpt : p < t) (htq : t < q) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l)
    (hprev : firstPairFlag p t q l < 0) :
    ∃ L : Fin 4 → ℝ, NativeLengthPhysical p t q h l L ∧
      nativeLengthController p t q h l L = 0 := by
  obtain ⟨hbase, z, hz, hzero⟩ :=
    exists_ordered_r_zero hp hp1 hl hl1 hpt htq hq hqh hflag hprev
  refine ⟨orderedCoreHalfLengths z.1 q z.2, ?_, ?_⟩
  · exact orderedCoreHalfLengths_physical hp hl hpt htq hq hqh
      hz.1.1 hz.1.2 hz.2.1 hz.2.2 hbase
  · exact native_zero_of_ordered_r_zero (hp.trans hz.1.1) (hl.trans hz.2.1)
      hq hz.1.2 hz.2.2 hzero

/-- The ordered-entry producer includes the actual native rank needed by
the arbitrary-word dormant opening theorem. -/
theorem exists_regular_nativeLength_anchor_of_ordered_firstPair
    {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hpt : p < t) (htq : t < q) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l)
    (hprev : firstPairFlag p t q l < 0) :
    ∃ L : Fin 4 → ℝ, NativeLengthPhysical p t q h l L ∧
      nativeLengthController p t q h l L = 0 ∧
      Function.Surjective (fderiv ℝ (nativeLengthController p t q h l) L) := by
  obtain ⟨L, hphys, hzero⟩ := exists_nativeLength_anchor_of_ordered_firstPair
    hp hp1 hl hl1 hpt htq hq hqh hflag hprev
  exact ⟨L, hphys, hzero, fderiv_nativeLengthController_surjective_of_physical
    hp hp1 (hp.trans hpt) htq hl hl1 hq hqh hphys hzero⟩

end Gluck.Discrete.NativeOppositePure
