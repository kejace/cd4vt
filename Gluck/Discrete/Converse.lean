/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.Convexity
public import Gluck.Discrete.LocalRegularity
public import Gluck.Discrete.N4Moderate

/-!
# The discrete converse (Euclidean, positive)

This file defines the discrete four-vertex window `DFV`, packages its plateau
extrema consequences, and proves the complete positive converse at `n = 4`.
The nonconstant branch uses the explicit orthogonal-diagonal quadrilateral;
the constant branch uses the regular polygon.

* `DFV` — four cyclically ordered indices alternating across a level `c`.
* `DiscreteFourVertexPos` — positivity plus (constant or DFV window).
* `DFV.plateau_extrema` — the window yields two disjoint plateau maximum
  runs and two disjoint plateau minimum runs (Dahlberg's conclusion class).
* `dfv_realizesR2_zmod4` — every positive four-point DFV profile has a strict
  moderate-arc Euclidean realization.
* `discreteGluckConverse_R2_pos_four` — the constant-or-DFV capstone at four
  points.

-/

@[expose] public section

namespace Gluck.Discrete

variable {n : ℕ}

/-! ## The discrete four-vertex window -/

/-- **Discrete four-vertex window**: the profile `κ : ZMod n → ℝ` admits four
cyclically ordered indices — represented by `ℕ`-lifts
`i₁ < i₂ < i₃ < i₄ < i₁ + n` — whose values alternate across the level `c`:
`κ i₂, κ i₄ < c < κ i₁, κ i₃`. The hypothesis shape matches
`dfv_plateau_extrema` verbatim. -/
def DFV (κ : ZMod n → ℝ) (c : ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ, i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
    c < κ ((i₁ : ℕ) : ZMod n) ∧ κ ((i₂ : ℕ) : ZMod n) < c ∧
    c < κ ((i₃ : ℕ) : ZMod n) ∧ κ ((i₄ : ℕ) : ZMod n) < c

/-- **Positive discrete four-vertex hypothesis**: all values positive, and the
profile is constant or admits a four-vertex window at some positive level. -/
def DiscreteFourVertexPos (κ : ZMod n → ℝ) : Prop :=
  (∀ i, 0 < κ i) ∧ ((∃ c, ∀ i, κ i = c) ∨ ∃ c > 0, DFV κ c)

/-! ## Immediate consequences of the definitions -/

/-- **The DFV window meets Dahlberg's conclusion class** (wrapped form of
`dfv_plateau_extrema`): a four-vertex window forces two disjoint plateau
maximum runs and two disjoint plateau minimum runs. -/
theorem DFV.plateau_extrema {κ : ZMod n → ℝ} {c : ℝ} (h : DFV κ c) :
    (∃ a₁ k₁ a₂ k₂ : ℕ, k₁ < n ∧ k₂ < n ∧
        PlateauMaxRun κ a₁ k₁ ∧ PlateauMaxRun κ a₂ k₂ ∧
        ∀ m₁, m₁ ≤ k₁ → ∀ m₂, m₂ ≤ k₂ →
          ((a₁ + m₁ : ℕ) : ZMod n) ≠ ((a₂ + m₂ : ℕ) : ZMod n)) ∧
    (∃ a₁ k₁ a₂ k₂ : ℕ, k₁ < n ∧ k₂ < n ∧
        PlateauMinRun κ a₁ k₁ ∧ PlateauMinRun κ a₂ k₂ ∧
        ∀ m₁, m₁ ≤ k₁ → ∀ m₂, m₂ ≤ k₂ →
          ((a₁ + m₁ : ℕ) : ZMod n) ≠ ((a₂ + m₂ : ℕ) : ZMod n)) := by
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, hκ1, hκ2, hκ3, hκ4⟩ := h
  exact dfv_plateau_extrema h12 h23 h34 h41 hκ1 hκ2 hκ3 hκ4

/-- A positive constant profile is realized by a regular moderate-arc
Euclidean polygon. -/
theorem realizesR2_of_const [NeZero n] (hn : 3 ≤ n) {k : ZMod n → ℝ}
    {c : ℝ} (hc : 0 < c) (hk : ∀ i, k i = c) : RealizesR2 k := by
  have hfun : k = fun _ : ZMod n => c := funext hk
  rw [hfun]
  exact realizesR2_const hn hc

/-- **Constant branch of the Menger converse**: a constant positive profile
is realized with the prescribed signed Menger curvatures. -/
theorem realizesMenger_of_const [NeZero n] (hn : 3 ≤ n) {κ : ZMod n → ℝ}
    {c : ℝ} (hc : 0 < c) (hκ : ∀ i, κ i = c) : RealizesMenger κ := by
  exact realizesR2_realizesMenger (realizesR2_of_const hn hc hκ)

/-! ## The complete four-point converse -/

/-- At four points, a strict DFV window has an exact simple moderate-arc
Euclidean realization, given by the orthogonal-diagonal quadrilateral. -/
theorem dfv_realizesR2_zmod4 {κ : ZMod 4 → ℝ} {c : ℝ}
    (hκ : ∀ i, 0 < κ i) (h : DFV κ c) : RealizesR2 κ := by
  obtain ⟨i₁, i₂, i₃, i₄, h₁₂, h₂₃, h₃₄, h₄₁,
    hκ₁, hκ₂, hκ₃, hκ₄⟩ := h
  have hi₂ : i₂ = i₁ + 1 := by omega
  have hi₃ : i₃ = i₁ + 2 := by omega
  have hi₄ : i₄ = i₁ + 3 := by omega
  subst i₂
  subst i₃
  subst i₄
  let a : ZMod 4 := (i₁ : ZMod 4)
  let κ' : ZMod 4 → ℝ := fun i => κ (i + a)
  have hκ' : ∀ i, 0 < κ' i := fun i => hκ (i + a)
  have hreal : RealizesR2 κ' :=
    realizesR2_zmod4_of_alternating_level hκ'
      (by simpa [κ', a, Nat.cast_add, Nat.cast_one] using hκ₁)
      (by simpa [κ', a, Nat.cast_add, Nat.cast_one, add_comm] using hκ₂)
      (by simpa [κ', a, Nat.cast_add, Nat.cast_ofNat, add_comm] using hκ₃)
      (by simpa [κ', a, Nat.cast_add, Nat.cast_ofNat, add_comm] using hκ₄)
  simpa [κ', a, add_assoc] using realizesR2_comp_add_zmod4 hκ' hreal (-a)

/-- Menger-curvature corollary of `dfv_realizesR2_zmod4`. -/
theorem dfv_realizesMenger_zmod4 {κ : ZMod 4 → ℝ} {c : ℝ}
    (hκ : ∀ i, 0 < κ i) (h : DFV κ c) : RealizesMenger κ :=
  realizesR2_realizesMenger (dfv_realizesR2_zmod4 hκ h)

/-- **The positive Euclidean discrete converse for `n = 4`.** Every positive
constant profile or strict four-vertex profile on `ZMod 4` has an exact simple
moderate-arc realization. -/
theorem discreteGluckConverse_R2_pos_four {κ : ZMod 4 → ℝ}
    (h : DiscreteFourVertexPos κ) : RealizesR2 κ := by
  obtain ⟨hκ, hconst | hdfv⟩ := h
  · obtain ⟨c, hc⟩ := hconst
    have hcpos : 0 < c := by simpa [hc 0] using hκ 0
    exact realizesR2_of_const (n := 4) (by norm_num) hcpos hc
  · obtain ⟨c, _hc, hwindow⟩ := hdfv
    exact dfv_realizesR2_zmod4 hκ hwindow

/-- Signed-Menger corollary of the complete four-point Euclidean converse. -/
theorem discreteGluckConverse_Menger_pos_four {κ : ZMod 4 → ℝ}
    (h : DiscreteFourVertexPos κ) : RealizesMenger κ :=
  realizesR2_realizesMenger (discreteGluckConverse_R2_pos_four h)

end Gluck.Discrete
