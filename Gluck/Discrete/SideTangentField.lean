/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import ForMathlib.Analysis.Complex.DiamondWinding
public import Mathlib.Tactic

/-!
# The rational field for a tangential square with side-contact labels

The four square corners carry alternating nonzero coefficients. Additional labels
may carry arbitrary coefficients at the four side contacts. These are the limiting
vertices of a strict tangential polygon, not the final polygon itself.
-/

@[expose] public section

namespace Gluck.Discrete.SideTangent

/-- The horizontal projection of the square field. The upper side contact has zero
horizontal contribution even where its denominator is small. -/
noncomputable def upperProjection (a b c d left right x y : ℝ) : ℝ :=
  a / (1 - x - y) + b / (1 + x - y) - c / (1 + x + y) - d / (1 - x + y) -
    left / (1 + x) + right / (1 - x)

/-- On the upper pair of half-faces, one upper corner denominator is exactly the inset. -/
theorem upper_denominators {ε x y : ℝ} (hε : 0 < ε)
    (hbd : |x| + y = 1 - ε) (htop : |x| ≤ y) :
    ε ≤ 1 - x - y ∧ ε ≤ 1 + x - y ∧
      1 ≤ 1 + x + y ∧ 1 ≤ 1 - x + y ∧
      1 / 2 ≤ 1 + x ∧ 1 / 2 ≤ 1 - x ∧
      (1 - x - y = ε ∨ 1 + x - y = ε) := by
  rcases le_total 0 x with hx | hx
  all_goals grind [abs_of_nonneg, abs_of_nonpos]

/-- A denominator bounded below by one half uniformly bounds an arbitrary signed term. -/
theorem abs_div_le_two_mul {u δ : ℝ} (hδ : 1 / 2 ≤ δ) : |u / δ| ≤ 2 * |u| := by
  rw [abs_div]
  have h := div_le_div_of_nonneg_left (abs_nonneg u)
    (show (0 : ℝ) < 1 / 2 by norm_num) (hδ.trans (le_abs_self δ))
  simpa [div_eq_mul_inv, mul_comm] using h

/-- Uniform lower bound along the entire upper arc, including both polar corners. -/
theorem upperProjection_lower_bound {ε a b c d left right x y : ℝ}
    (hε : 0 < ε) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hbd : |x| + y = 1 - ε) (htop : |x| ≤ y) :
    min a b / ε - c - d - 2 * |left| - 2 * |right| ≤
      upperProjection a b c d left right x y := by
  obtain ⟨h₀, h₁, h₂, h₃, hleft, hright, hactive⟩ := upper_denominators hε hbd htop
  have hlead : min a b / ε ≤ a / (1 - x - y) + b / (1 + x - y) := by
    rcases hactive with hactive | hactive
    all_goals rw [hactive]
    · exact (div_le_div_of_nonneg_right (min_le_left a b) hε.le).trans
        (le_add_of_nonneg_right (div_nonneg hb (hε.le.trans h₁)))
    · exact (div_le_div_of_nonneg_right (min_le_right a b) hε.le).trans
        (le_add_of_nonneg_left (div_nonneg ha (hε.le.trans h₀)))
  unfold upperProjection
  linarith only [hlead, div_le_self hc h₂, div_le_self hd h₃,
    abs_div_le_two_mul (u := left) hleft, abs_div_le_two_mul (u := right) hright,
    le_abs_self (left / (1 + x)), neg_abs_le (right / (1 - x))]

/-- A strict leading-term margin gives the needed upper-arc sign. -/
theorem upperProjection_pos {ε a b c d left right x y : ℝ}
    (hε : 0 < ε) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hbd : |x| + y = 1 - ε) (htop : |x| ≤ y)
    (hmargin : c + d + 2 * |left| + 2 * |right| < min a b / ε) :
    0 < upperProjection a b c d left right x y := by
  have h := upperProjection_lower_bound (left := left) (right := right)
    hε ha hb hc hd hbd htop
  linarith

/-- Absolute values of the four alternating corner coefficients, and the four arbitrary
side-contact coefficients. The actual corner signs are `+,-,+,-` in counterclockwise order. -/
structure SquareWeights where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  top : ℝ
  left : ℝ
  bottom : ℝ
  right : ℝ

/-- The rational field associated with the square corners and its side contacts. -/
noncomputable def SquareWeights.field (w : SquareWeights) (z : ℂ) : ℂ :=
  ⟨upperProjection w.a w.b w.c w.d w.left w.right z.re z.im,
    upperProjection w.a w.d w.c w.b w.bottom w.top z.im z.re⟩

/-- The four selected coefficients have alternating nonzero signs. -/
def SquareWeights.Positive (w : SquareWeights) : Prop :=
  0 < w.a ∧ 0 < w.b ∧ 0 < w.c ∧ 0 < w.d

/-- Opposite arcs use the same estimate with their corner and contact labels exchanged. -/
theorem upperProjection_opposite (a b c d left right x y : ℝ) :
    upperProjection c d a b right left (-x) (-y) =
      -upperProjection a b c d left right x y := by
  unfold upperProjection
  ring

/-- The four quantitative margins sufficient for the boundary signs. -/
structure SquareWeights.Margins (w : SquareWeights) (ε : ℝ) : Prop where
  top : w.c + w.d + 2 * |w.left| + 2 * |w.right| < min w.a w.b / ε
  left : w.a + w.d + 2 * |w.top| + 2 * |w.bottom| < min w.c w.b / ε
  bottom : w.a + w.b + 2 * |w.right| + 2 * |w.left| < min w.c w.d / ε
  right : w.c + w.b + 2 * |w.bottom| + 2 * |w.top| < min w.a w.d / ε

/-- The quantitative square-field estimates imply all four topological sign conditions. -/
theorem SquareWeights.diamondSigns {w : SquareWeights} {ε : ℝ}
    (hw : w.Positive) (hε : 0 < ε) (hm : w.Margins ε) :
    Complex.DiamondSigns w.field (1 - ε) := by
  rcases hw with ⟨ha, hb, hc, hd⟩
  constructor
  all_goals intro z hbd hside
  · exact upperProjection_pos hε ha.le hb.le hc.le hd.le
      (by simpa [abs_of_nonneg ((abs_nonneg z.re).trans hside)] using hbd)
      hside hm.top
  · have hp := upperProjection_pos (left := w.top) (right := w.bottom)
      (x := -z.im) (y := -z.re) hε hc.le hb.le ha.le hd.le
      (by simpa [abs_of_nonpos (neg_nonneg.mp ((abs_nonneg z.im).trans hside)),
        add_comm] using hbd)
      (by simpa using hside) hm.left
    exact neg_pos.mp ((upperProjection_opposite
      w.a w.d w.c w.b w.bottom w.top z.im z.re) ▸ hp)
  · have hp := upperProjection_pos (left := w.right) (right := w.left)
      (x := -z.re) (y := -z.im) hε hc.le hd.le ha.le hb.le
      (by simpa [abs_of_nonpos (neg_nonneg.mp ((abs_nonneg z.re).trans hside))]
        using hbd)
      (by simpa using hside) hm.bottom
    exact neg_pos.mp ((upperProjection_opposite
      w.a w.b w.c w.d w.left w.right z.re z.im) ▸ hp)
  · exact upperProjection_pos hε ha.le hd.le hc.le hb.le
      (by simpa [abs_of_nonneg ((abs_nonneg z.im).trans hside), add_comm] using hbd)
      hside hm.right

/-- Every positive set of corner magnitudes admits one inset satisfying all four margins.
The contact coefficients may have either sign and have no size restriction. -/
theorem SquareWeights.exists_margins {w : SquareWeights} (hw : w.Positive) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ w.Margins ε := by
  let m := min (min w.a w.b) (min w.c w.d)
  let M := w.a + w.b + w.c + w.d +
    2 * |w.top| + 2 * |w.left| + 2 * |w.bottom| + 2 * |w.right| + 1
  have hm : 0 < m := lt_min (lt_min hw.1 hw.2.1) (lt_min hw.2.2.1 hw.2.2.2)
  have hM : 0 < M := by
    dsimp [M]
    linarith [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, abs_nonneg w.top,
      abs_nonneg w.left, abs_nonneg w.bottom, abs_nonneg w.right]
  obtain ⟨ε, hε, hsmall⟩ := exists_between (lt_min zero_lt_one (div_pos hm hM))
  have hbound : M < m / ε := by
    apply (lt_div_iff₀ hε).mpr
    simpa [mul_comm] using (lt_div_iff₀ hM).mp (hsmall.trans_le (min_le_right _ _))
  refine ⟨ε, hε, hsmall.trans_le (min_le_left _ _), ?_⟩
  constructor <;> refine lt_of_le_of_lt ?_
    (lt_of_lt_of_le hbound (div_le_div_of_nonneg_right ?_ hε.le))
  all_goals grind [SquareWeights.Positive, abs_nonneg]

/-- Every denominator is strictly positive on the inset diamond. -/
theorem diamond_denominators {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z ∈ Complex.diamond (1 - ε)) :
    0 < 1 - z.re - z.im ∧ 0 < 1 + z.re - z.im ∧
      0 < 1 + z.re + z.im ∧ 0 < 1 - z.re + z.im ∧
      0 < 1 + z.re ∧ 0 < 1 - z.re ∧ 0 < 1 + z.im ∧ 0 < 1 - z.im := by
  change |z.re| + |z.im| ≤ 1 - ε at hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith [le_abs_self z.re, neg_abs_le z.re, le_abs_self z.im, neg_abs_le z.im,
      abs_nonneg z.re, abs_nonneg z.im]

/-- The rational field is continuous wherever the inset keeps its denominators positive. -/
theorem SquareWeights.continuousOn_field (w : SquareWeights) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn w.field (Complex.diamond (1 - ε)) := by
  apply continuousOn_of_forall_continuousAt
  intro z hz
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := diamond_denominators hε hz
  unfold SquareWeights.field upperProjection
  simp_rw [Complex.mk_eq_add_mul_I]
  fun_prop (disch := linarith)

/-- The alternating-corner square field always has a zero in the open diamond, even with
arbitrary signed coefficients at the four side contacts. -/
theorem SquareWeights.exists_zero {w : SquareWeights} (hw : w.Positive) :
    ∃ z : ℂ, |z.re| + |z.im| < 1 ∧ w.field z = 0 := by
  obtain ⟨ε, hε, hε₁, hm⟩ := exists_margins hw
  obtain ⟨z, hz, hzero⟩ := Complex.exists_zero_of_diamondSigns (sub_pos.mpr hε₁)
    w.field (w.continuousOn_field hε) (diamondSigns hw hε hm)
  exact ⟨z, lt_of_le_of_lt hz (sub_lt_self 1 hε), hzero⟩

end Gluck.Discrete.SideTangent
