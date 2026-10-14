import Gluck.Discrete.NativeOrderedFirstPair
import ForMathlib.Analysis.Complex.PoincareMiranda

/-!
# Original native anchors from two negative terminal corners

The clamped square map supplies a simultaneous zero of the two original
orthogonal residuals. Its boundary fixed points are excluded by the two
literal corner flags. No scalar-root uniqueness or effective replacement of
the target endpoint readings is assumed.
-/

namespace Gluck.Discrete.NativeOppositePure

open Set N6TypeAThreeCell

private def clampUnit (x : ℝ) : ℝ := max 0 (min 1 x)

private lemma clampUnit_bounds (x : ℝ) : 0 ≤ clampUnit x ∧ clampUnit x ≤ 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private lemma clampUnit_eq_zero_le {x : ℝ} (hx : clampUnit x = 0) : x ≤ 0 := by
  by_contra h
  have hp : 0 < min (1 : ℝ) x := lt_min zero_lt_one (lt_of_not_ge h)
  have := lt_of_lt_of_le hp (le_max_right 0 (min 1 x))
  rw [show max 0 (min 1 x) = 0 from hx] at this
  linarith

private lemma one_le_of_clampUnit_eq_one {x : ℝ} (hx : clampUnit x = 1) : 1 ≤ x := by
  by_contra h
  have hlt : x < 1 := lt_of_not_ge h
  have hm : max 0 (min (1 : ℝ) x) < 1 :=
    max_lt zero_lt_one (lt_of_le_of_lt (min_le_right _ _) hlt)
  rw [show max 0 (min 1 x) = 1 from hx] at hm
  linarith

private lemma eq_of_clampUnit_eq_interior {x z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hx : clampUnit x = z) : x = z := by
  have hx0 : 0 < x := by
    by_contra hh
    have hxle : x ≤ 0 := le_of_not_gt hh
    have hc : clampUnit x = 0 := by simp [clampUnit, min_eq_right (by linarith : x ≤ 1), hxle]
    linarith
  have hx1 : x < 1 := by
    by_contra hh
    have hxge : 1 ≤ x := le_of_not_gt hh
    have hc : clampUnit x = 1 := by simp [clampUnit, min_eq_left hxge]
    linarith
  simpa [clampUnit, min_eq_right hx1.le, max_eq_right hx0.le] using hx

/-- A square fixed-point argument tailored to two crossed terminal corners.
Only signs at boundary zeros are needed on the top and right edges. -/
theorem exists_zero_of_two_crossed_corners
    {F G : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 1 ×ˢ Icc 0 1))
    (hG : ContinuousOn G (Icc 0 1 ×ˢ Icc 0 1))
    (hleft : ∀ v ∈ Icc (0 : ℝ) 1, 0 < F (0, v))
    (hbottom : ∀ u ∈ Icc (0 : ℝ) 1, 0 < G (u, 0))
    (hright : ∀ v ∈ Icc (0 : ℝ) 1, G (1, v) = 0 → F (1, v) < 0)
    (htop : ∀ u ∈ Icc (0 : ℝ) 1, F (u, 1) = 0 → G (u, 1) < 0)
    (hcorner : G (1, 1) < 0) :
    ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, F z = 0 ∧ G z = 0 := by
  let R : ℝ × ℝ → ℝ × ℝ := fun z =>
    (z.1 - clampUnit (z.1 + F z), z.2 - clampUnit (z.2 + G z))
  have hR : ContinuousOn R (Icc 0 1 ×ˢ Icc 0 1) := by
    dsimp [R, clampUnit]
    fun_prop
  obtain ⟨z, hz, hzero⟩ := poincare_miranda
    (a₁ := 0) (a₂ := 1) (b₁ := 0) (b₂ := 1) zero_le_one zero_le_one R hR
    (fun v _ => by dsimp [R]; simp only [zero_add]; linarith [(clampUnit_bounds (F (0, v))).1])
    (fun v _ => by dsimp [R]; linarith [(clampUnit_bounds (1 + F (1, v))).2])
    (fun u _ => by dsimp [R]; simp only [zero_add]; linarith [(clampUnit_bounds (G (u, 0))).1])
    (fun u _ => by dsimp [R]; linarith [(clampUnit_bounds (1 + G (u, 1))).2])
  have hf : clampUnit (z.1 + F z) = z.1 := by
    have := congrArg Prod.fst hzero
    change z.1 - clampUnit (z.1 + F z) = 0 at this
    linarith
  have hg : clampUnit (z.2 + G z) = z.2 := by
    have := congrArg Prod.snd hzero
    change z.2 - clampUnit (z.2 + G z) = 0 at this
    linarith
  have hu0 : 0 < z.1 := by
    by_contra hh
    have he : z.1 = 0 := le_antisymm (le_of_not_gt hh) hz.1.1
    have hc := clampUnit_eq_zero_le (he ▸ hf)
    have hp := hleft z.2 hz.2
    have hpair : z = (0, z.2) := Prod.ext he rfl
    rw [hpair] at hc
    simp only [zero_add] at hc
    linarith
  have hv0 : 0 < z.2 := by
    by_contra hh
    have he : z.2 = 0 := le_antisymm (le_of_not_gt hh) hz.2.1
    have hc := clampUnit_eq_zero_le (he ▸ hg)
    have hp := hbottom z.1 hz.1
    have hpair : z = (z.1, 0) := Prod.ext rfl he
    rw [hpair] at hc
    simp only [zero_add] at hc
    linarith
  have hu1 : z.1 < 1 := by
    by_contra hh
    have he : z.1 = 1 := le_antisymm hz.1.2 (le_of_not_gt hh)
    have hfge := one_le_of_clampUnit_eq_one (he ▸ hf)
    by_cases hev : z.2 = 1
    · have hgge := one_le_of_clampUnit_eq_one (hev ▸ hg)
      have hpair : z = (1, 1) := Prod.ext he hev
      rw [hpair] at hgge
      change 1 ≤ 1 + G (1, 1) at hgge
      linarith
    · have hv1 : z.2 < 1 := lt_of_le_of_ne hz.2.2 hev
      have hgz : G z = 0 := by
        have := eq_of_clampUnit_eq_interior hv0 hv1 hg
        linarith
      have hpair : z = (1, z.2) := Prod.ext he rfl
      have hneg := hright z.2 hz.2 ((congrArg G hpair).symm.trans hgz)
      rw [hpair] at hfge
      change 1 ≤ 1 + F (1, z.2) at hfge
      linarith
  have hv1 : z.2 < 1 := by
    by_contra hh
    have he : z.2 = 1 := le_antisymm hz.2.2 (le_of_not_gt hh)
    have hgge := one_le_of_clampUnit_eq_one (he ▸ hg)
    have hfz : F z = 0 := by
      have := eq_of_clampUnit_eq_interior hu0 hu1 hf
      linarith
    have hpair : z = (z.1, 1) := Prod.ext rfl he
    have hneg := htop z.1 hz.1 ((congrArg F hpair).symm.trans hfz)
    rw [hpair] at hgge
    change 1 ≤ 1 + G (z.1, 1) at hgge
    linarith
  refine ⟨z, ⟨⟨hu0, hu1⟩, ⟨hv0, hv1⟩⟩, ?_, ?_⟩
  · have := eq_of_clampUnit_eq_interior hu0 hu1 hf
    linarith
  · have := eq_of_clampUnit_eq_interior hv0 hv1 hg
    linarith

/-- Reflection exchanges the two literal mixed residuals. -/
lemma rResidualThree_eq_swap (q h l u v : ℝ) :
    rResidualThree q h l u v = rResidualOne l h q v u := by
  unfold rResidualThree rResidualOne
  rw [mul_comm (v ^ 2) (u ^ 2)]
  ring

lemma rResidualOne_left_pos {p t q v : ℝ} (hp : 0 < p) (ht : 0 < t)
    (hq : 1 < q) (hv : v ∈ Icc (0 : ℝ) 1) : 0 < rResidualOne p t q 0 v := by
  have hrad : 0 < q ^ 2 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hden : 0 < Real.sqrt (q ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have ha := div_pos (Real.sqrt_pos.2 hrad) hden
  have hb : 0 ≤ Real.sqrt (1 - v ^ 2) / Real.sqrt (q ^ 2) := by positivity
  have hpa := Real.arcsin_pos.2 (mul_pos hp ha)
  have htb := Real.arcsin_nonneg.2 (mul_nonneg ht.le hb)
  simp only [rResidualOne, show (0 : ℝ) ^ 2 = 0 by norm_num,
    zero_mul, sub_zero, Real.arcsin_zero]
  linarith

/-- On the top side the unique zero of the first residual is the actual
pure-one neighbor `u=p`; this is a strict principal-arcsine comparison. -/
lemma rResidualOne_top_zero_iff {p t q u : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 < q) (hu : u ∈ Icc (0 : ℝ) 1) :
    rResidualOne p t q u 1 = 0 ↔ u = p := by
  let a := Real.sqrt (q ^ 2 - 1) / Real.sqrt (q ^ 2 - u ^ 2)
  have hnum : 0 < q ^ 2 - 1 := by nlinarith
  have hden : 0 < q ^ 2 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have ha0 : 0 < a := div_pos (Real.sqrt_pos.2 hnum) (Real.sqrt_pos.2 hden)
  have ha1 : a ≤ 1 := by
    apply (div_le_one (Real.sqrt_pos.2 hden)).2
    apply Real.sqrt_le_sqrt
    nlinarith [hu.1, hu.2]
  have hpaa : p * a ≤ 1 :=
    (mul_le_mul_of_nonneg_right hp1.le ha0.le).trans (by simpa using ha1)
  have huaa : u * a ≤ 1 :=
    (mul_le_mul_of_nonneg_right hu.2 ha0.le).trans (by simpa using ha1)
  have hexpr : rResidualOne p t q u 1 = Real.arcsin (p * a) - Real.arcsin (u * a) := by
    simp [rResidualOne, a]
  rw [hexpr, sub_eq_zero]
  constructor
  · intro he
    have heq := (Real.arcsin_inj (by nlinarith [mul_pos hp ha0] : -1 ≤ p * a) hpaa
      (by nlinarith [mul_nonneg hu.1 ha0.le] : -1 ≤ u * a) huaa).1 he
    nlinarith
  · intro he
    rw [he]

/-- Two negative original flags produce an interior simultaneous zero of
the unmodified orthogonal residuals, without endpoint-order assumptions. -/
theorem exists_r_zero_of_negative_corners {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (hh : 0 < h) (hq : 1 < q)
    (hflag : firstPairFlag p t q l < 0)
    (hreflected : firstPairFlag l h q p < 0) :
    ∃ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, rResidualMap p t q h l z = 0 := by
  have hden : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      0 < q ^ 2 - z.1 ^ 2 * z.2 ^ 2 :=
    fun z hz => r_denom_pos_aux hq hz.1.1 hz.1.2 hz.2.1 hz.2.2
  obtain ⟨z, hz, hF, hG⟩ := exists_zero_of_two_crossed_corners
    (continuousOn_rResidualOne_of_denom_pos (p := p) (t := t) hden)
    (continuousOn_rResidualThree_of_denom_pos (h := h) (l := l) hden)
    (fun v hv => rResidualOne_left_pos hp ht hq hv)
    (fun u hu => by rw [rResidualThree_eq_swap]; exact rResidualOne_left_pos hl hh hq hu)
    (fun v hv hG => by
      rw [rResidualThree_eq_swap] at hG
      have he := (rResidualOne_top_zero_iff hl hl1 hq hv).1 hG
      rw [he, r_corner_eq_firstPairFlag hl hl1 hq]
      exact hflag)
    (fun u hu hF => by
      have he := (rResidualOne_top_zero_iff hp hp1 hq hu).1 hF
      rw [he, rResidualThree_eq_swap, r_corner_eq_firstPairFlag hp hp1 hq]
      exact hreflected)
    (r_residual_three_right_neg hl.le hl1 le_rfl hq)
  refine ⟨z, hz, ?_⟩
  apply Complex.ext
  · simpa only [r_residual_map_re, Complex.zero_re] using hF
  · simpa only [r_residual_map_im, Complex.zero_im] using hG

/-- All original endpoint walls are strict for an interior core when every
mixed endpoint lies below its incident actual pure peak. -/
theorem negativeCornersCore_physical {p t q h l u v : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (_hl : 0 < l) (hl1 : l < 1)
    (_ht : 0 < t) (htq : t < q) (_hh : 0 < h) (hhq : h < q)
    (hq : 1 < q) (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    NativeLengthPhysical p t q h l (orderedCoreHalfLengths u q v) := by
  have hd := r_core_realization_data (q := q) zero_lt_one hu.1 (by linarith) hv.1
    hu.2 (by linarith [hu.2]) hv.2 (by linarith [hv.2])
  have hs := r_core_sides_pos zero_lt_one hu.1 (by linarith : 0 < q) hv.1
    hu.2 (by linarith [hu.2]) hv.2 (by linarith [hv.2])
  have hm := moderateArc_zero_iff.mp hd.1
  have hw0 := (hm (0 : ZMod 4)).2
  have hw2 := (hm (2 : ZMod 4)).2
  change |(1 : ℝ)| * (rCoreSideD 1 u q v / 2) < 1 ∧
    |(1 : ℝ)| * (rCoreSideA 1 u q v / 2) < 1 at hw0
  change |q| * (rCoreSideB 1 u q v / 2) < 1 ∧
    |q| * (rCoreSideC 1 u q v / 2) < 1 at hw2
  simp only [abs_one, one_mul] at hw0
  rw [abs_of_pos (by linarith : 0 < q)] at hw2
  refine ⟨?_, hw0.2, ?_, ?_, hw2.1, hw2.2, ?_, ?_, hw0.1⟩
  · intro i
    fin_cases i
    · exact half_pos hs.1
    · exact half_pos hs.2.1
    · exact half_pos hs.2.2.1
    · exact half_pos hs.2.2.2
  · exact (mul_lt_mul_of_pos_right hp1 (half_pos hs.1)).trans (by simpa using hw0.2)
  · exact (mul_lt_mul_of_pos_right htq (half_pos hs.2.1)).trans hw2.1
  · exact (mul_lt_mul_of_pos_right hhq (half_pos hs.2.2.1)).trans hw2.2
  · exact (mul_lt_mul_of_pos_right hl1 (half_pos hs.2.2.2)).trans (by simpa using hw0.1)

/-- Native existence under exactly the two negative original terminal flags.
All eight original incidence walls, positive lengths, closure and one full
lifted turn are conclusions. -/
theorem exists_nativeLength_anchor_of_negative_corners {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (ht : 0 < t) (htq : t < q) (hh : 0 < h) (hhq : h < q) (hq : 1 < q)
    (hflag : firstPairFlag p t q l < 0)
    (hreflected : firstPairFlag l h q p < 0) :
    ∃ u v : ℝ, u ∈ Ioo (0 : ℝ) 1 ∧ v ∈ Ioo (0 : ℝ) 1 ∧
      NativeLengthPhysical p t q h l (orderedCoreHalfLengths u q v) ∧
      rResidualMap p t q h l (u, v) = 0 ∧
      nativeLengthController p t q h l (orderedCoreHalfLengths u q v) = 0 := by
  obtain ⟨z, hz, hzero⟩ := exists_r_zero_of_negative_corners hp hp1 hl hl1 ht hh hq hflag hreflected
  exact ⟨z.1, z.2, hz.1, hz.2,
    negativeCornersCore_physical hp hp1 hl hl1 ht htq hh hhq hq hz.1 hz.2,
    hzero, native_zero_of_ordered_r_zero hz.1.1 hz.2.1 hq hz.1.2 hz.2.2 hzero⟩

end Gluck.Discrete.NativeOppositePure
