import Gluck.Curve
import Gluck.Curvature
import Gluck.SpaceForm.Defs
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Definitions for forward four-vertex theorems

This subtree is deliberately independent of the converse development.  It
packages the conclusions of the smooth and discrete forward four-vertex
theorems, together with Dahlberg's local regularity condition.
-/

namespace Gluck.Forward

open scoped Real

/-- A periodic real function is constant or has two cyclically alternating
local maxima and two cyclically alternating local minima.  Plateaux are handled
by Mathlib's non-strict `IsLocalMax` and `IsLocalMin`. -/
def SmoothFourVertex (κ : ℝ → ℝ) : Prop :=
  (∃ c, ∀ t, κ t = c) ∨
    ∃ p₁ q₁ p₂ q₂,
      p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * Real.pi ∧
      IsLocalMax κ p₁ ∧ IsLocalMin κ q₁ ∧ IsLocalMax κ p₂ ∧ IsLocalMin κ q₂

/-- The value-separated four-vertex condition used by the converse development
implies the ordinary forward four-vertex conclusion. -/
theorem smoothFourVertex_of_fourVertexCondition {κ : ℝ → ℝ}
    (hκ : Gluck.FourVertexCondition κ) : SmoothFourVertex κ := by
  rcases hκ with hconst | hextrema
  · exact Or.inl hconst
  · rcases hextrema with
      ⟨p₁, q₁, p₂, q₂, hpq, hqp, hpq', hcycle, hmax₁, hmax₂, hmin₁, hmin₂, _⟩
    exact Or.inr ⟨p₁, q₁, p₂, q₂, hpq, hqp, hpq', hcycle,
      hmax₁, hmin₁, hmax₂, hmin₂⟩

/-- Positive affine changes preserve the value-separated four-vertex
condition. -/
theorem fourVertexCondition_posAffine {κ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hfv : Gluck.FourVertexCondition κ) :
    Gluck.FourVertexCondition (fun t => a * κ t + b) := by
  have hmono : Monotone (fun x : ℝ => a * x + b) := by
    intro x y hxy
    nlinarith [mul_le_mul_of_nonneg_left hxy (le_of_lt ha)]
  rcases hfv with hconst | hextrema
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨a * c + b, fun t => by simp [hc t]⟩
  · rcases hextrema with
      ⟨p₁, q₁, p₂, q₂, hpq, hqp, hpq', hcycle, hmax₁, hmax₂, hmin₁, hmin₂, hsep⟩
    have hq₁p₁ : κ q₁ < κ p₁ :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hsep (min_le_left _ _))
    have hq₁p₂ : κ q₁ < κ p₂ :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hsep (min_le_right _ _))
    have hq₂p₁ : κ q₂ < κ p₁ :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hsep (min_le_left _ _))
    have hq₂p₂ : κ q₂ < κ p₂ :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hsep (min_le_right _ _))
    refine Or.inr ⟨p₁, q₁, p₂, q₂, hpq, hqp, hpq', hcycle,
      by simpa [Function.comp_def] using hmax₁.comp_mono hmono,
      by simpa [Function.comp_def] using hmax₂.comp_mono hmono,
      by simpa [Function.comp_def] using hmin₁.comp_mono hmono,
      by simpa [Function.comp_def] using hmin₂.comp_mono hmono, ?_⟩
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by nlinarith [mul_lt_mul_of_pos_left hq₁p₁ ha],
        by nlinarith [mul_lt_mul_of_pos_left hq₁p₂ ha]⟩,
      ⟨by nlinarith [mul_lt_mul_of_pos_left hq₂p₁ ha],
        by nlinarith [mul_lt_mul_of_pos_left hq₂p₂ ha]⟩⟩

/-- Positive affine changes preserve the value-separated four-vertex
condition exactly. -/
theorem fourVertexCondition_posAffine_iff {κ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) :
    Gluck.FourVertexCondition (fun t => a * κ t + b) ↔ Gluck.FourVertexCondition κ := by
  constructor
  · intro hfv
    have hscaled :=
      fourVertexCondition_posAffine (κ := fun t => a * κ t + b)
        (a := a⁻¹) (b := -b / a) (inv_pos.mpr ha) hfv
    convert hscaled using 1
    ext t
    field_simp [ha.ne']
    ring
  · exact fourVertexCondition_posAffine ha

/-- A smooth profile pointwise equal to a positive affine change of a
value-separated four-vertex profile inherits that condition. -/
theorem fourVertexCondition_of_eq_posAffine {κ μ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hμ : ∀ t, μ t = a * κ t + b) (hfv : Gluck.FourVertexCondition κ) :
    Gluck.FourVertexCondition μ := by
  have hscaled := fourVertexCondition_posAffine (κ := κ) (a := a) (b := b) ha hfv
  convert hscaled using 1
  ext t
  exact hμ t

/-- A smooth profile pointwise equal to a positive affine change has the same
value-separated four-vertex condition. -/
theorem fourVertexCondition_of_eq_posAffine_iff {κ μ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hμ : ∀ t, μ t = a * κ t + b) :
    Gluck.FourVertexCondition μ ↔ Gluck.FourVertexCondition κ := by
  constructor
  · intro hfv
    have hκ :
        ∀ t, κ t = a⁻¹ * μ t + (-b / a) := by
      intro t
      rw [hμ t]
      field_simp [ha.ne']
      ring
    exact fourVertexCondition_of_eq_posAffine (κ := μ) (μ := κ)
      (a := a⁻¹) (b := -b / a) (inv_pos.mpr ha) hκ hfv
  · exact fourVertexCondition_of_eq_posAffine ha hμ

/-- Pointwise equal smooth profiles have the same value-separated four-vertex
condition. -/
theorem fourVertexCondition_congr {κ μ : ℝ → ℝ} (hμ : ∀ t, μ t = κ t)
    (hfv : Gluck.FourVertexCondition κ) :
    Gluck.FourVertexCondition μ := by
  exact fourVertexCondition_of_eq_posAffine (a := 1) (b := 0) (by norm_num)
    (by intro t; simp [hμ t]) hfv

/-- Positive affine changes preserve the smooth forward four-vertex
conclusion. -/
theorem smoothFourVertex_posAffine {κ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hfv : SmoothFourVertex κ) :
    SmoothFourVertex (fun t => a * κ t + b) := by
  have hmono : Monotone (fun x : ℝ => a * x + b) := by
    intro x y hxy
    nlinarith [mul_le_mul_of_nonneg_left hxy (le_of_lt ha)]
  rcases hfv with hconst | hextrema
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨a * c + b, fun t => by simp [hc t]⟩
  · rcases hextrema with
      ⟨p₁, q₁, p₂, q₂, hpq, hqp, hpq', hcycle, hmax₁, hmin₁, hmax₂, hmin₂⟩
    exact Or.inr ⟨p₁, q₁, p₂, q₂, hpq, hqp, hpq', hcycle,
      by simpa [Function.comp_def] using hmax₁.comp_mono hmono,
      by simpa [Function.comp_def] using hmin₁.comp_mono hmono,
      by simpa [Function.comp_def] using hmax₂.comp_mono hmono,
      by simpa [Function.comp_def] using hmin₂.comp_mono hmono⟩

/-- Positive affine changes preserve the smooth forward four-vertex conclusion
exactly. -/
theorem smoothFourVertex_posAffine_iff {κ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) :
    SmoothFourVertex (fun t => a * κ t + b) ↔ SmoothFourVertex κ := by
  constructor
  · intro hfv
    have hscaled :=
      smoothFourVertex_posAffine (κ := fun t => a * κ t + b)
        (a := a⁻¹) (b := -b / a) (inv_pos.mpr ha) hfv
    convert hscaled using 1
    ext t
    field_simp [ha.ne']
    ring
  · exact smoothFourVertex_posAffine ha

/-- A smooth profile pointwise equal to a positive affine change of a
four-vertex profile inherits the smooth forward conclusion. -/
theorem smoothFourVertex_of_eq_posAffine {κ μ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hμ : ∀ t, μ t = a * κ t + b) (hfv : SmoothFourVertex κ) :
    SmoothFourVertex μ := by
  have hscaled := smoothFourVertex_posAffine (κ := κ) (a := a) (b := b) ha hfv
  convert hscaled using 1
  ext t
  exact hμ t

/-- A smooth profile pointwise equal to a positive affine change has the same
smooth forward four-vertex conclusion. -/
theorem smoothFourVertex_of_eq_posAffine_iff {κ μ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hμ : ∀ t, μ t = a * κ t + b) :
    SmoothFourVertex μ ↔ SmoothFourVertex κ := by
  constructor
  · intro hfv
    have hκ :
        ∀ t, κ t = a⁻¹ * μ t + (-b / a) := by
      intro t
      rw [hμ t]
      field_simp [ha.ne']
      ring
    exact smoothFourVertex_of_eq_posAffine (κ := μ) (μ := κ)
      (a := a⁻¹) (b := -b / a) (inv_pos.mpr ha) hκ hfv
  · exact smoothFourVertex_of_eq_posAffine ha hμ

/-- Pointwise equal smooth profiles have the same smooth forward four-vertex
conclusion. -/
theorem smoothFourVertex_congr {κ μ : ℝ → ℝ} (hμ : ∀ t, μ t = κ t)
    (hfv : SmoothFourVertex κ) :
    SmoothFourVertex μ := by
  exact smoothFourVertex_of_eq_posAffine (a := 1) (b := 0) (by norm_num)
    (by intro t; simp [hμ t]) hfv

/-- Four cyclic samples alternating strictly above and below a common level.
For a finite nonconstant cyclic sequence this is the level-set form of having
two distinct local maxima and two distinct local minima. -/
def AlternatesAcrossLevel {n : ℕ} (κ : ZMod n → ℝ) (c : ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ,
    i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      κ (i₂ : ZMod n) < c ∧ κ (i₄ : ZMod n) < c ∧
      c < κ (i₁ : ZMod n) ∧ c < κ (i₃ : ZMod n)

/-- The discrete forward four-vertex conclusion: constant curvature or an
alternating four-sample level window. -/
def DiscreteFourVertex {n : ℕ} (κ : ZMod n → ℝ) : Prop :=
  (∃ c, ∀ i, κ i = c) ∨ ∃ c, AlternatesAcrossLevel κ c

/-- Nonzero affine changes preserve the alternating four-sample level window,
with the cyclic order rotated when the scale is negative. -/
theorem alternatesAcrossLevel_affine {n : ℕ} {κ : ZMod n → ℝ} {a b c : ℝ}
    (ha : a ≠ 0) (halt : AlternatesAcrossLevel κ c) :
    AlternatesAcrossLevel (fun i => a * κ i + b) (a * c + b) := by
  rcases halt with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hlow₂, hlow₄, hhigh₁, hhigh₃⟩
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hwrap : ((i₁ + n : ℕ) : ZMod n) = (i₁ : ZMod n) := by
      rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    refine ⟨i₂, i₃, i₄, i₁ + n, hi₂₃, hi₃₄, hi₄₁,
      Nat.add_lt_add_right hi₁₂ n, ?_, ?_, ?_, ?_⟩
    · nlinarith
    · have hlow₁ : a * κ (i₁ : ZMod n) + b < a * c + b := by
        nlinarith
      simpa [hwrap] using hlow₁
    · nlinarith
    · nlinarith
  · exact ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Nonzero affine changes preserve the discrete level-window four-vertex
conclusion. -/
theorem discreteFourVertex_affine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hfv : DiscreteFourVertex κ) :
    DiscreteFourVertex (fun i => a * κ i + b) := by
  rcases hfv with hconst | halt
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨a * c + b, fun i => by simp [hc i]⟩
  · rcases halt with ⟨c, hc⟩
    exact Or.inr ⟨a * c + b, alternatesAcrossLevel_affine ha hc⟩

/-- Nonzero affine changes preserve the discrete level-window four-vertex
conclusion exactly. -/
theorem discreteFourVertex_affine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    DiscreteFourVertex (fun i => a * κ i + b) ↔ DiscreteFourVertex κ := by
  constructor
  · intro hfv
    have hscaled :=
      discreteFourVertex_affine (κ := fun i => a * κ i + b)
        (a := a⁻¹) (b := -b / a) (inv_ne_zero ha) hfv
    convert hscaled using 1
    ext i
    field_simp [ha]
    ring
  · exact discreteFourVertex_affine ha

/-- A profile pointwise equal to a nonzero affine change of a level-window
profile inherits the same alternating level window. -/
theorem alternatesAcrossLevel_of_eq_affine {n : ℕ} {κ μ : ZMod n → ℝ}
    {a b c : ℝ} (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (halt : AlternatesAcrossLevel κ c) :
    AlternatesAcrossLevel μ (a * c + b) := by
  have hscaled := alternatesAcrossLevel_affine (κ := κ) (a := a) (b := b) ha halt
  convert hscaled using 1
  ext i
  exact hμ i

/-- Pointwise equal cyclic profiles have the same alternating level window. -/
theorem alternatesAcrossLevel_congr {n : ℕ} {κ μ : ZMod n → ℝ} {c : ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i) (halt : AlternatesAcrossLevel κ c) :
    AlternatesAcrossLevel μ c := by
  simpa using alternatesAcrossLevel_of_eq_affine (a := 1) (b := 0) (c := c)
    (by norm_num) (by intro i; simp [hμ i]) halt

/-- A profile pointwise equal to a nonzero affine change of a discrete
level-window four-vertex profile inherits that conclusion. -/
theorem discreteFourVertex_of_eq_affine {n : ℕ} {κ μ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (hfv : DiscreteFourVertex κ) :
    DiscreteFourVertex μ := by
  have hscaled := discreteFourVertex_affine (κ := κ) (a := a) (b := b) ha hfv
  convert hscaled using 1
  ext i
  exact hμ i

/-- Pointwise equal cyclic profiles have the same discrete level-window
four-vertex conclusion. -/
theorem discreteFourVertex_congr {n : ℕ} {κ μ : ZMod n → ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i) (hfv : DiscreteFourVertex κ) :
    DiscreteFourVertex μ := by
  exact discreteFourVertex_of_eq_affine (a := 1) (b := 0) (by norm_num)
    (by intro i; simp [hμ i]) hfv

/-- The Dahlberg polygon-size hypothesis implies the neighbour-extrema size
hypothesis used by strict one-step constructors. -/
theorem two_le_of_four_le {n : ℕ} (hn : 4 ≤ n) : 2 ≤ n := by
  omega

/-- The Dahlberg polygon-size hypothesis also gives the nontriangle lower
bound used in geometric reductions. -/
theorem three_le_of_four_le {n : ℕ} (hn : 4 ≤ n) : 3 ≤ n := by
  omega

/-- A plateau-aware local maximum of a cyclic sequence.  Moving left and right
from `i`, the value remains constant until it becomes strictly smaller. -/
def DiscreteLocalMax {n : ℕ} (κ : ZMod n → ℝ) (i : ZMod n) : Prop :=
  ∃ l r : ℕ, 0 < l ∧ 0 < r ∧ l + r ≤ n ∧
    (∀ m < l, κ (i - (m : ZMod n)) = κ i) ∧
    (∀ m < r, κ (i + (m : ZMod n)) = κ i) ∧
    κ (i - (l : ZMod n)) < κ i ∧ κ (i + (r : ZMod n)) < κ i

/-- A plateau-aware local minimum of a cyclic sequence. -/
def DiscreteLocalMin {n : ℕ} (κ : ZMod n → ℝ) (i : ZMod n) : Prop :=
  ∃ l r : ℕ, 0 < l ∧ 0 < r ∧ l + r ≤ n ∧
    (∀ m < l, κ (i - (m : ZMod n)) = κ i) ∧
    (∀ m < r, κ (i + (m : ZMod n)) = κ i) ∧
    κ i < κ (i - (l : ZMod n)) ∧ κ i < κ (i + (r : ZMod n))

/-- A strict one-step cyclic peak is a plateau-aware discrete local maximum. -/
theorem discreteLocalMax_of_neighbors {n : ℕ} (hn : 2 ≤ n) {κ : ZMod n → ℝ}
    {i : ZMod n} (hleft : κ (i - 1) < κ i) (hright : κ (i + 1) < κ i) :
    DiscreteLocalMax κ i := by
  refine ⟨1, 1, by norm_num, by norm_num, hn, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have hm0 : m = 0 := by omega
    simp [hm0]
  · intro m hm
    have hm0 : m = 0 := by omega
    simp [hm0]
  · simpa using hleft
  · simpa using hright

/-- A strict one-step cyclic valley is a plateau-aware discrete local minimum. -/
theorem discreteLocalMin_of_neighbors {n : ℕ} (hn : 2 ≤ n) {κ : ZMod n → ℝ}
    {i : ZMod n} (hleft : κ i < κ (i - 1)) (hright : κ i < κ (i + 1)) :
    DiscreteLocalMin κ i := by
  refine ⟨1, 1, by norm_num, by norm_num, hn, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have hm0 : m = 0 := by omega
    simp [hm0]
  · intro m hm
    have hm0 : m = 0 := by omega
    simp [hm0]
  · simpa using hleft
  · simpa using hright

/-- An adjacent increase followed by an adjacent decrease gives a strict
one-step cyclic local maximum at the middle vertex. -/
theorem discreteLocalMax_of_succ_turn {n : ℕ} (hn : 2 ≤ n) {κ : ZMod n → ℝ}
    {i : ZMod n} (hinc : κ i < κ (i + 1))
    (hdec : κ (i + 1 + 1) < κ (i + 1)) :
    DiscreteLocalMax κ (i + 1) := by
  apply discreteLocalMax_of_neighbors hn
  · simpa [sub_eq_add_neg, add_assoc] using hinc
  · simpa [add_assoc] using hdec

/-- An adjacent decrease followed by an adjacent increase gives a strict
one-step cyclic local minimum at the middle vertex. -/
theorem discreteLocalMin_of_succ_turn {n : ℕ} (hn : 2 ≤ n) {κ : ZMod n → ℝ}
    {i : ZMod n} (hdec : κ (i + 1) < κ i)
    (hinc : κ (i + 1) < κ (i + 1 + 1)) :
    DiscreteLocalMin κ (i + 1) := by
  apply discreteLocalMin_of_neighbors hn
  · simpa [sub_eq_add_neg, add_assoc] using hdec
  · simpa [add_assoc] using hinc

/-- A plateau-aware local maximum has a strict adjacent increase at its left
boundary. -/
theorem DiscreteLocalMax.exists_left_boundary_increase {n : ℕ} {κ : ZMod n → ℝ}
    {i : ZMod n} (hmax : DiscreteLocalMax κ i) :
    ∃ j : ZMod n, κ j < κ (j + 1) := by
  rcases hmax with
    ⟨l, _r, hlpos, _hrpos, _hlr, hleft, _hright, hdrop, _⟩
  refine ⟨i - (l : ZMod n), ?_⟩
  have hlpred_lt : l - 1 < l := Nat.sub_one_lt (Nat.ne_of_gt hlpos)
  have hplateau : κ (i - ((l - 1 : ℕ) : ZMod n)) = κ i :=
    hleft (l - 1) hlpred_lt
  have hpred : ((l - 1 : ℕ) : ZMod n) = (l : ZMod n) - 1 := by
    have hl : l = l - 1 + 1 := (Nat.sub_add_cancel hlpos).symm
    rw [hl, Nat.cast_add, Nat.cast_one]
    abel
  have hsucc : i - ((l - 1 : ℕ) : ZMod n) = i - (l : ZMod n) + 1 := by
    rw [hpred]
    abel
  rwa [← hsucc, hplateau]

/-- A plateau-aware local maximum has a strict adjacent decrease at its right
boundary. -/
theorem DiscreteLocalMax.exists_right_boundary_decrease {n : ℕ} {κ : ZMod n → ℝ}
    {i : ZMod n} (hmax : DiscreteLocalMax κ i) :
    ∃ j : ZMod n, κ (j + 1) < κ j := by
  rcases hmax with
    ⟨_l, r, _hlpos, hrpos, _hlr, _hleft, hright, _hdrop_left, hdrop⟩
  refine ⟨i + ((r - 1 : ℕ) : ZMod n), ?_⟩
  have hrpred_lt : r - 1 < r := Nat.sub_one_lt (Nat.ne_of_gt hrpos)
  have hplateau : κ (i + ((r - 1 : ℕ) : ZMod n)) = κ i :=
    hright (r - 1) hrpred_lt
  have hpred : ((r - 1 : ℕ) : ZMod n) = (r : ZMod n) - 1 := by
    have hr : r = r - 1 + 1 := (Nat.sub_add_cancel hrpos).symm
    rw [hr, Nat.cast_add, Nat.cast_one]
    abel
  have hsucc : i + ((r - 1 : ℕ) : ZMod n) + 1 = i + (r : ZMod n) := by
    rw [hpred]
    abel
  rwa [hsucc, hplateau]

/-- A plateau-aware local minimum has a strict adjacent decrease at its left
boundary. -/
theorem DiscreteLocalMin.exists_left_boundary_decrease {n : ℕ} {κ : ZMod n → ℝ}
    {i : ZMod n} (hmin : DiscreteLocalMin κ i) :
    ∃ j : ZMod n, κ (j + 1) < κ j := by
  rcases hmin with
    ⟨l, _r, hlpos, _hrpos, _hlr, hleft, _hright, hdrop, _⟩
  refine ⟨i - (l : ZMod n), ?_⟩
  have hlpred_lt : l - 1 < l := Nat.sub_one_lt (Nat.ne_of_gt hlpos)
  have hplateau : κ (i - ((l - 1 : ℕ) : ZMod n)) = κ i :=
    hleft (l - 1) hlpred_lt
  have hpred : ((l - 1 : ℕ) : ZMod n) = (l : ZMod n) - 1 := by
    have hl : l = l - 1 + 1 := (Nat.sub_add_cancel hlpos).symm
    rw [hl, Nat.cast_add, Nat.cast_one]
    abel
  have hsucc : i - ((l - 1 : ℕ) : ZMod n) = i - (l : ZMod n) + 1 := by
    rw [hpred]
    abel
  rwa [← hsucc, hplateau]

/-- A plateau-aware local minimum has a strict adjacent increase at its right
boundary. -/
theorem DiscreteLocalMin.exists_right_boundary_increase {n : ℕ} {κ : ZMod n → ℝ}
    {i : ZMod n} (hmin : DiscreteLocalMin κ i) :
    ∃ j : ZMod n, κ j < κ (j + 1) := by
  rcases hmin with
    ⟨_l, r, _hlpos, hrpos, _hlr, _hleft, hright, _hdrop_left, hdrop⟩
  refine ⟨i + ((r - 1 : ℕ) : ZMod n), ?_⟩
  have hrpred_lt : r - 1 < r := Nat.sub_one_lt (Nat.ne_of_gt hrpos)
  have hplateau : κ (i + ((r - 1 : ℕ) : ZMod n)) = κ i :=
    hright (r - 1) hrpred_lt
  have hpred : ((r - 1 : ℕ) : ZMod n) = (r : ZMod n) - 1 := by
    have hr : r = r - 1 + 1 := (Nat.sub_add_cancel hrpos).symm
    rw [hr, Nat.cast_add, Nat.cast_one]
    abel
  have hsucc : i + ((r - 1 : ℕ) : ZMod n) + 1 = i + (r : ZMod n) := by
    rw [hpred]
    abel
  rwa [hsucc, hplateau]

/-- Dahlberg's source-form conclusion: two distinct local maxima and two
distinct local minima, alternating around the cyclic vertex set. -/
def DahlbergFourVertex {n : ℕ} (κ : ZMod n → ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ,
    i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      DiscreteLocalMax κ (i₁ : ZMod n) ∧
      DiscreteLocalMin κ (i₂ : ZMod n) ∧
      DiscreteLocalMax κ (i₃ : ZMod n) ∧
      DiscreteLocalMin κ (i₄ : ZMod n)

/-- Dahlberg's plateau-aware four-vertex conclusion contains actual strict
adjacent boundary turns around its extremal plateaux.

This does not claim the stronger ordered-adjacent-turn package used by
Dahlberg's Lemma 8/Lemma 9 route; it records the purely combinatorial
boundary-turn information that is already present in the plateau-aware local
extrema. -/
theorem DahlbergFourVertex.exists_boundary_turns {n : ℕ} {κ : ZMod n → ℝ}
    (hfv : DahlbergFourVertex κ) :
    (∃ i : ZMod n, κ i < κ (i + 1)) ∧
      (∃ i : ZMod n, κ (i + 1) < κ i) ∧
      (∃ i : ZMod n, κ i < κ (i + 1)) ∧
      (∃ i : ZMod n, κ (i + 1) < κ i) := by
  rcases hfv with
    ⟨_i₁, _i₂, _i₃, _i₄, _hi₁₂, _hi₂₃, _hi₃₄, _hi₄₁,
      hmax₁, hmin₂, hmax₃, _hmin₄⟩
  exact ⟨
    hmax₁.exists_left_boundary_increase,
    hmin₂.exists_left_boundary_decrease,
    hmin₂.exists_right_boundary_increase,
    hmax₃.exists_right_boundary_decrease⟩

/-- Dahlberg's four-vertex conclusion forces the cyclic profile to be
nonconstant. -/
theorem not_constant_of_dahlbergFourVertex {n : ℕ} {κ : ZMod n → ℝ}
    (hfv : DahlbergFourVertex κ) :
    ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  rintro ⟨c, hconst⟩
  rcases hfv with
    ⟨i₁, _i₂, _i₃, _i₄, _hi₁₂, _hi₂₃, _hi₃₄, _hi₄₁, hmax₁, _hmin₂, _hmax₃, _hmin₄⟩
  rcases hmax₁ with ⟨l, _r, _hlpos, _hrpos, _hlr, _hleft_eq, _hright_eq, hdrop, _⟩
  rw [hconst ((i₁ : ZMod n) - (l : ZMod n)), hconst (i₁ : ZMod n)] at hdrop
  exact (lt_irrefl c) hdrop

/-- A constant-or-Dahlberg conclusion upgrades to Dahlberg's conclusion as
soon as the profile is known to be nonconstant. -/
theorem dahlbergFourVertex_of_constant_or_of_not_constant {n : ℕ}
    {κ : ZMod n → ℝ}
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DahlbergFourVertex κ := by
  rcases h with hconst | hfv
  · exact False.elim (hnc hconst)
  · exact hfv

/-- Four ordered plateau-aware extrema in `min-max-min-max` order give
Dahlberg's source-form conclusion after rotating the cyclic order to start at
the first maximum. -/
theorem dahlbergFourVertex_of_localExtrema_min_max {n : ℕ} {κ : ZMod n → ℝ}
    {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁ : DiscreteLocalMin κ (i₁ : ZMod n))
    (hmax₂ : DiscreteLocalMax κ (i₂ : ZMod n))
    (hmin₃ : DiscreteLocalMin κ (i₃ : ZMod n))
    (hmax₄ : DiscreteLocalMax κ (i₄ : ZMod n)) :
    DahlbergFourVertex κ := by
  have hwrap : ((i₁ + n : ℕ) : ZMod n) = (i₁ : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  exact ⟨i₂, i₃, i₄, i₁ + n, hi₂₃, hi₃₄, hi₄₁,
    Nat.add_lt_add_right hi₁₂ n, hmax₂, hmin₃, hmax₄, by simpa [hwrap] using hmin₁⟩

/-- Negating a cyclic profile turns a plateau-aware local maximum into a
plateau-aware local minimum. -/
theorem discreteLocalMin_of_neg_localMax {n : ℕ} {κ : ZMod n → ℝ} {i : ZMod n}
    (hmax : DiscreteLocalMax (fun j => -κ j) i) :
    DiscreteLocalMin κ i := by
  rcases hmax with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact neg_inj.mp (hleft_eq m hm)
  · intro m hm
    exact neg_inj.mp (hright_eq m hm)
  · exact neg_lt_neg_iff.mp hleft
  · exact neg_lt_neg_iff.mp hright

/-- Negating a cyclic profile turns a plateau-aware local minimum into a
plateau-aware local maximum. -/
theorem discreteLocalMax_of_neg_localMin {n : ℕ} {κ : ZMod n → ℝ} {i : ZMod n}
    (hmin : DiscreteLocalMin (fun j => -κ j) i) :
    DiscreteLocalMax κ i := by
  rcases hmin with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact neg_inj.mp (hleft_eq m hm)
  · intro m hm
    exact neg_inj.mp (hright_eq m hm)
  · exact neg_lt_neg_iff.mp hleft
  · exact neg_lt_neg_iff.mp hright

/-- The plateau-aware Dahlberg four-vertex conclusion is invariant under
negating the cyclic profile.  Maxima and minima swap, so the cyclic order is
rotated from `min-max-min-max` back to `max-min-max-min`. -/
theorem dahlbergFourVertex_of_neg {n : ℕ} {κ : ZMod n → ℝ}
    (hfv : DahlbergFourVertex (fun i => -κ i)) :
    DahlbergFourVertex κ := by
  rcases hfv with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hmax₁, hmin₂, hmax₃, hmin₄⟩
  exact dahlbergFourVertex_of_localExtrema_min_max hi₁₂ hi₂₃ hi₃₄ hi₄₁
    (discreteLocalMin_of_neg_localMax hmax₁)
    (discreteLocalMax_of_neg_localMin hmin₂)
    (discreteLocalMin_of_neg_localMax hmax₃)
    (discreteLocalMax_of_neg_localMin hmin₄)

/-- The plateau-aware Dahlberg four-vertex conclusion is equivalent for a
profile and its negative. -/
theorem dahlbergFourVertex_neg_iff {n : ℕ} {κ : ZMod n → ℝ} :
    DahlbergFourVertex (fun i => -κ i) ↔ DahlbergFourVertex κ := by
  constructor
  · exact dahlbergFourVertex_of_neg
  · intro hfv
    have hfv' : DahlbergFourVertex (fun i => -(-κ i)) := by
      simpa using hfv
    exact dahlbergFourVertex_of_neg (κ := fun i => -κ i) hfv'

/-- Taking positive reciprocals turns a plateau-aware local maximum into a
plateau-aware local minimum. -/
theorem discreteLocalMin_of_inv_localMax {n : ℕ} {ρ : ZMod n → ℝ} {i : ZMod n}
    (hpos : ∀ j, 0 < ρ j) (hmax : DiscreteLocalMax ρ i) :
    DiscreteLocalMin (fun j => (ρ j)⁻¹) i := by
  rcases hmax with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    change (ρ (i - (m : ZMod n)))⁻¹ = (ρ i)⁻¹
    rw [hleft_eq m hm]
  · intro m hm
    change (ρ (i + (m : ZMod n)))⁻¹ = (ρ i)⁻¹
    rw [hright_eq m hm]
  · exact (inv_lt_inv₀ (hpos i) (hpos (i - (l : ZMod n)))).mpr hleft
  · exact (inv_lt_inv₀ (hpos i) (hpos (i + (r : ZMod n)))).mpr hright

/-- Taking positive reciprocals turns a plateau-aware local minimum into a
plateau-aware local maximum. -/
theorem discreteLocalMax_of_inv_localMin {n : ℕ} {ρ : ZMod n → ℝ} {i : ZMod n}
    (hpos : ∀ j, 0 < ρ j) (hmin : DiscreteLocalMin ρ i) :
    DiscreteLocalMax (fun j => (ρ j)⁻¹) i := by
  rcases hmin with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    change (ρ (i - (m : ZMod n)))⁻¹ = (ρ i)⁻¹
    rw [hleft_eq m hm]
  · intro m hm
    change (ρ (i + (m : ZMod n)))⁻¹ = (ρ i)⁻¹
    rw [hright_eq m hm]
  · exact (inv_lt_inv₀ (hpos (i - (l : ZMod n))) (hpos i)).mpr hleft
  · exact (inv_lt_inv₀ (hpos (i + (r : ZMod n))) (hpos i)).mpr hright

/-- Dahlberg's four-vertex conclusion is preserved by taking positive
reciprocals, with maxima/minima swapped and the cyclic order rotated. -/
theorem dahlbergFourVertex_inv_of_pos {n : ℕ} {ρ : ZMod n → ℝ}
    (hpos : ∀ i, 0 < ρ i) (hfv : DahlbergFourVertex ρ) :
    DahlbergFourVertex (fun i => (ρ i)⁻¹) := by
  rcases hfv with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hmax₁, hmin₂, hmax₃, hmin₄⟩
  exact dahlbergFourVertex_of_localExtrema_min_max hi₁₂ hi₂₃ hi₃₄ hi₄₁
    (discreteLocalMin_of_inv_localMax hpos hmax₁)
    (discreteLocalMax_of_inv_localMin hpos hmin₂)
    (discreteLocalMin_of_inv_localMax hpos hmax₃)
    (discreteLocalMax_of_inv_localMin hpos hmin₄)

/-- Positive affine changes of a cyclic profile preserve plateau-aware local
maxima. -/
theorem discreteLocalMax_posAffine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) {i : ZMod n} (hmax : DiscreteLocalMax κ i) :
    DiscreteLocalMax (fun j => a * κ j + b) i := by
  rcases hmax with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    simp [hleft_eq m hm]
  · intro m hm
    simp [hright_eq m hm]
  · nlinarith [mul_lt_mul_of_pos_left hleft ha]
  · nlinarith [mul_lt_mul_of_pos_left hright ha]

/-- Positive affine changes of a cyclic profile preserve plateau-aware local
minima. -/
theorem discreteLocalMin_posAffine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) {i : ZMod n} (hmin : DiscreteLocalMin κ i) :
    DiscreteLocalMin (fun j => a * κ j + b) i := by
  rcases hmin with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    simp [hleft_eq m hm]
  · intro m hm
    simp [hright_eq m hm]
  · nlinarith [mul_lt_mul_of_pos_left hleft ha]
  · nlinarith [mul_lt_mul_of_pos_left hright ha]

/-- The plateau-aware Dahlberg conclusion is invariant under positive affine
changes of the cyclic curvature profile. -/
theorem dahlbergFourVertex_posAffine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex (fun i => a * κ i + b) := by
  rcases hfv with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hmax₁, hmin₂, hmax₃, hmin₄⟩
  exact ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
    discreteLocalMax_posAffine ha hmax₁,
    discreteLocalMin_posAffine ha hmin₂,
    discreteLocalMax_posAffine ha hmax₃,
    discreteLocalMin_posAffine ha hmin₄⟩

/-- Positive affine changes of a cyclic curvature profile preserve the
plateau-aware Dahlberg conclusion exactly. -/
theorem dahlbergFourVertex_posAffine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) :
    DahlbergFourVertex (fun i => a * κ i + b) ↔ DahlbergFourVertex κ := by
  constructor
  · intro hfv
    have hscaled :=
      dahlbergFourVertex_posAffine (κ := fun i => a * κ i + b)
        (a := a⁻¹) (b := -b / a) (inv_pos.mpr ha) hfv
    convert hscaled using 1
    ext i
    field_simp [ha.ne']
    ring
  · exact dahlbergFourVertex_posAffine ha

/-- Nonzero affine changes of a cyclic curvature profile preserve the
plateau-aware Dahlberg conclusion.  Negative scale factors swap maxima and
minima via profile negation. -/
theorem dahlbergFourVertex_affine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex (fun i => a * κ i + b) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hfv_neg : DahlbergFourVertex (fun i => -κ i) :=
      dahlbergFourVertex_neg_iff.mpr hfv
    have hscaled :=
      dahlbergFourVertex_posAffine (κ := fun i => -κ i)
        (a := -a) (b := b) (neg_pos.mpr hneg) hfv_neg
    convert hscaled using 1
    ext i
    ring
  · exact dahlbergFourVertex_posAffine hpos hfv

/-- Nonzero affine changes of a cyclic curvature profile preserve the
plateau-aware Dahlberg conclusion exactly. -/
theorem dahlbergFourVertex_affine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    DahlbergFourVertex (fun i => a * κ i + b) ↔ DahlbergFourVertex κ := by
  constructor
  · intro hfv
    have hscaled :=
      dahlbergFourVertex_affine (κ := fun i => a * κ i + b)
        (a := a⁻¹) (b := -b / a) (inv_ne_zero ha) hfv
    convert hscaled using 1
    ext i
    field_simp [ha]
    ring
  · exact dahlbergFourVertex_affine ha

/-- Nonzero affine changes preserve a constant-or-Dahlberg conclusion. -/
theorem constant_or_dahlbergFourVertex_affine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ) :
    (∃ c, ∀ i : ZMod n, a * κ i + b = c) ∨
      DahlbergFourVertex (fun i => a * κ i + b) := by
  rcases h with hconst | hfv
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨a * c + b, fun i => by simp [hc i]⟩
  · exact Or.inr (dahlbergFourVertex_affine ha hfv)

/-- A profile pointwise equal to a nonzero affine change of a Dahlberg profile
inherits the plateau-aware Dahlberg conclusion. -/
theorem dahlbergFourVertex_of_eq_affine {n : ℕ} {κ μ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex μ := by
  have hscaled := dahlbergFourVertex_affine (κ := κ) (a := a) (b := b) ha hfv
  convert hscaled using 1
  ext i
  exact hμ i

/-- Pointwise equal cyclic profiles have the same plateau-aware Dahlberg
conclusion. -/
theorem dahlbergFourVertex_congr {n : ℕ} {κ μ : ZMod n → ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i) (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex μ := by
  exact dahlbergFourVertex_of_eq_affine (a := 1) (b := 0) (by norm_num)
    (by intro i; simp [hμ i]) hfv

/-- A profile pointwise equal to a nonzero affine change of a
constant-or-Dahlberg profile inherits the constant-or-Dahlberg conclusion. -/
theorem constant_or_dahlbergFourVertex_of_eq_affine {n : ℕ}
    {κ μ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ) :
    (∃ c, ∀ i : ZMod n, μ i = c) ∨ DahlbergFourVertex μ := by
  rcases constant_or_dahlbergFourVertex_affine (κ := κ) (a := a) (b := b) ha h with
    hconst | hfv
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨c, fun i => by rw [hμ i, hc i]⟩
  · exact Or.inr (by
      convert hfv using 1
      ext i
      exact hμ i)

/-- Pointwise equal cyclic profiles have the same constant-or-Dahlberg
conclusion. -/
theorem constant_or_dahlbergFourVertex_congr {n : ℕ} {κ μ : ZMod n → ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i)
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ) :
    (∃ c, ∀ i : ZMod n, μ i = c) ∨ DahlbergFourVertex μ := by
  exact constant_or_dahlbergFourVertex_of_eq_affine (a := 1) (b := 0) (by norm_num)
    (by intro i; simp [hμ i]) h

/-- Translating cyclic indices preserves plateau-aware local maxima. -/
theorem discreteLocalMax_translateIndex {n : ℕ} {κ : ZMod n → ℝ} {a i : ZMod n}
    (hmax : DiscreteLocalMax κ i) :
    DiscreteLocalMax (fun j => κ (j + a)) (i - a) := by
  rcases hmax with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    calc
      κ (((i - a) - (m : ZMod n)) + a) = κ (i - (m : ZMod n)) := by
        congr 1
        abel
      _ = κ i := hleft_eq m hm
      _ = κ ((i - a) + a) := by
        congr 1
        abel
  · intro m hm
    calc
      κ (((i - a) + (m : ZMod n)) + a) = κ (i + (m : ZMod n)) := by
        congr 1
        abel
      _ = κ i := hright_eq m hm
      _ = κ ((i - a) + a) := by
        congr 1
        abel
  · calc
      κ (((i - a) - (l : ZMod n)) + a) = κ (i - (l : ZMod n)) := by
        congr 1
        abel
      _ < κ i := hleft
      _ = κ ((i - a) + a) := by
        congr 1
        abel
  · calc
      κ (((i - a) + (r : ZMod n)) + a) = κ (i + (r : ZMod n)) := by
        congr 1
        abel
      _ < κ i := hright
      _ = κ ((i - a) + a) := by
        congr 1
        abel

/-- Translating cyclic indices preserves plateau-aware local minima. -/
theorem discreteLocalMin_translateIndex {n : ℕ} {κ : ZMod n → ℝ} {a i : ZMod n}
    (hmin : DiscreteLocalMin κ i) :
    DiscreteLocalMin (fun j => κ (j + a)) (i - a) := by
  rcases hmin with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨l, r, hlpos, hrpos, hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    calc
      κ (((i - a) - (m : ZMod n)) + a) = κ (i - (m : ZMod n)) := by
        congr 1
        abel
      _ = κ i := hleft_eq m hm
      _ = κ ((i - a) + a) := by
        congr 1
        abel
  · intro m hm
    calc
      κ (((i - a) + (m : ZMod n)) + a) = κ (i + (m : ZMod n)) := by
        congr 1
        abel
      _ = κ i := hright_eq m hm
      _ = κ ((i - a) + a) := by
        congr 1
        abel
  · calc
      κ ((i - a) + a) = κ i := by
        congr 1
        abel
      _ < κ (i - (l : ZMod n)) := hleft
      _ = κ (((i - a) - (l : ZMod n)) + a) := by
        congr 1
        abel
  · calc
      κ ((i - a) + a) = κ i := by
        congr 1
        abel
      _ < κ (i + (r : ZMod n)) := hright
      _ = κ (((i - a) + (r : ZMod n)) + a) := by
        congr 1
        abel

/-- Reversing cyclic indices preserves plateau-aware local maxima, with the
left and right plateau lengths exchanged. -/
theorem discreteLocalMax_negIndex {n : ℕ} {κ : ZMod n → ℝ} {i : ZMod n}
    (hmax : DiscreteLocalMax κ i) :
    DiscreteLocalMax (fun j => κ (-j)) (-i) := by
  rcases hmax with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨r, l, hrpos, hlpos, by simpa [add_comm] using hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hright_eq m hm
  · intro m hm
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hleft_eq m hm
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hright
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hleft

/-- Reversing cyclic indices preserves plateau-aware local minima, with the
left and right plateau lengths exchanged. -/
theorem discreteLocalMin_negIndex {n : ℕ} {κ : ZMod n → ℝ} {i : ZMod n}
    (hmin : DiscreteLocalMin κ i) :
    DiscreteLocalMin (fun j => κ (-j)) (-i) := by
  rcases hmin with ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft, hright⟩
  refine ⟨r, l, hrpos, hlpos, by simpa [add_comm] using hlr, ?_, ?_, ?_, ?_⟩
  · intro m hm
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hright_eq m hm
  · intro m hm
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hleft_eq m hm
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hright
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hleft

/-- Reflecting cyclic indices about an arbitrary origin preserves
plateau-aware local maxima. -/
theorem discreteLocalMax_reflectIndex {n : ℕ} {κ : ZMod n → ℝ} {a i : ZMod n}
    (hmax : DiscreteLocalMax κ i) :
    DiscreteLocalMax (fun j => κ (a - j)) (a - i) := by
  have hneg := discreteLocalMax_negIndex (κ := κ) hmax
  have htrans :=
    discreteLocalMax_translateIndex (κ := fun j : ZMod n => κ (-j)) (a := -a) hneg
  convert htrans using 1
  · ext j
    congr 1
    abel
  · abel

/-- Reflecting cyclic indices about an arbitrary origin preserves
plateau-aware local minima. -/
theorem discreteLocalMin_reflectIndex {n : ℕ} {κ : ZMod n → ℝ} {a i : ZMod n}
    (hmin : DiscreteLocalMin κ i) :
    DiscreteLocalMin (fun j => κ (a - j)) (a - i) := by
  have hneg := discreteLocalMin_negIndex (κ := κ) hmin
  have htrans :=
    discreteLocalMin_translateIndex (κ := fun j : ZMod n => κ (-j)) (a := -a) hneg
  convert htrans using 1
  · ext j
    congr 1
    abel
  · abel

/-- Translating cyclic indices preserves the plateau-aware Dahlberg
four-vertex conclusion. -/
theorem dahlbergFourVertex_translateIndex {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (a : ZMod n) (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex (fun j => κ (j + a)) := by
  rcases hfv with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hmax₁, hmin₂, hmax₃, hmin₄⟩
  let A := a.val
  let j₁ := i₁ + n - A
  let j₂ := i₂ + n - A
  let j₃ := i₃ + n - A
  let j₄ := i₄ + n - A
  have hAcast : (A : ZMod n) = a := by
    exact ZMod.natCast_zmod_val a
  have hAlt : A < n := ZMod.val_lt a
  have hA₁ : A ≤ i₁ + n := by omega
  have hA₂ : A ≤ i₂ + n := by omega
  have hA₃ : A ≤ i₃ + n := by omega
  have hA₄ : A ≤ i₄ + n := by omega
  refine ⟨j₁, j₂, j₃, j₄, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · have hmax := discreteLocalMax_translateIndex (κ := κ) (a := a) hmax₁
    have hj : ((j₁ : ℕ) : ZMod n) = (i₁ : ZMod n) - a := by
      dsimp [j₁, A]
      rw [Nat.cast_sub hA₁, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
    simpa [hj] using hmax
  · have hmin := discreteLocalMin_translateIndex (κ := κ) (a := a) hmin₂
    have hj : ((j₂ : ℕ) : ZMod n) = (i₂ : ZMod n) - a := by
      dsimp [j₂, A]
      rw [Nat.cast_sub hA₂, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
    simpa [hj] using hmin
  · have hmax := discreteLocalMax_translateIndex (κ := κ) (a := a) hmax₃
    have hj : ((j₃ : ℕ) : ZMod n) = (i₃ : ZMod n) - a := by
      dsimp [j₃, A]
      rw [Nat.cast_sub hA₃, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
    simpa [hj] using hmax
  · have hmin := discreteLocalMin_translateIndex (κ := κ) (a := a) hmin₄
    have hj : ((j₄ : ℕ) : ZMod n) = (i₄ : ZMod n) - a := by
      dsimp [j₄, A]
      rw [Nat.cast_sub hA₄, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
    simpa [hj] using hmin

/-- Translating cyclic indices preserves the plateau-aware Dahlberg
four-vertex conclusion exactly. -/
theorem dahlbergFourVertex_translateIndex_iff {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {a : ZMod n} :
    DahlbergFourVertex (fun j => κ (j + a)) ↔ DahlbergFourVertex κ := by
  constructor
  · intro hfv
    have hback :=
      dahlbergFourVertex_translateIndex (κ := fun j : ZMod n => κ (j + a)) (-a) hfv
    convert hback using 1
    ext j
    congr 1
    abel
  · exact dahlbergFourVertex_translateIndex a

/-- Reflecting cyclic indices preserves the plateau-aware Dahlberg
four-vertex conclusion. -/
theorem dahlbergFourVertex_reflectIndex {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (a : ZMod n) (hfv : DahlbergFourVertex κ) :
    DahlbergFourVertex (fun j => κ (a - j)) := by
  rcases hfv with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, hmax₁, hmin₂, hmax₃, hmin₄⟩
  let j₁ := i₁ + n - i₄
  let j₂ := i₁ + n - i₃
  let j₃ := i₁ + n - i₂
  let j₄ := i₁ + n - i₁
  have hi₄le : i₄ ≤ i₁ + n := Nat.le_of_lt hi₄₁
  have hi₃le : i₃ ≤ i₁ + n := by omega
  have hi₂le : i₂ ≤ i₁ + n := by omega
  have hi₁le : i₁ ≤ i₁ + n := by omega
  have hbase : DahlbergFourVertex (fun j => κ ((i₁ : ZMod n) - j)) := by
    apply dahlbergFourVertex_of_localExtrema_min_max
      (i₁ := j₁) (i₂ := j₂) (i₃ := j₃) (i₄ := j₄)
      (by omega) (by omega) (by omega) (by omega)
    · have hmin := discreteLocalMin_reflectIndex
        (κ := κ) (a := (i₁ : ZMod n)) hmin₄
      have hj : ((j₁ : ℕ) : ZMod n) = (i₁ : ZMod n) - (i₄ : ZMod n) := by
        dsimp [j₁]
        rw [Nat.cast_sub hi₄le, Nat.cast_add, ZMod.natCast_self, add_zero]
      simpa [hj] using hmin
    · have hmax := discreteLocalMax_reflectIndex
        (κ := κ) (a := (i₁ : ZMod n)) hmax₃
      have hj : ((j₂ : ℕ) : ZMod n) = (i₁ : ZMod n) - (i₃ : ZMod n) := by
        dsimp [j₂]
        rw [Nat.cast_sub hi₃le, Nat.cast_add, ZMod.natCast_self, add_zero]
      simpa [hj] using hmax
    · have hmin := discreteLocalMin_reflectIndex
        (κ := κ) (a := (i₁ : ZMod n)) hmin₂
      have hj : ((j₃ : ℕ) : ZMod n) = (i₁ : ZMod n) - (i₂ : ZMod n) := by
        dsimp [j₃]
        rw [Nat.cast_sub hi₂le, Nat.cast_add, ZMod.natCast_self, add_zero]
      simpa [hj] using hmin
    · have hmax := discreteLocalMax_reflectIndex
        (κ := κ) (a := (i₁ : ZMod n)) hmax₁
      have hj : ((j₄ : ℕ) : ZMod n) = (i₁ : ZMod n) - (i₁ : ZMod n) := by
        dsimp [j₄]
        rw [Nat.cast_sub hi₁le, Nat.cast_add, ZMod.natCast_self, add_zero]
      simpa [hj] using hmax
  have hshift :=
    dahlbergFourVertex_translateIndex
      (κ := fun j : ZMod n => κ ((i₁ : ZMod n) - j))
      ((i₁ : ZMod n) - a) hbase
  convert hshift using 1
  ext j
  congr 1
  abel

/-- Reflecting cyclic indices preserves the plateau-aware Dahlberg
four-vertex conclusion exactly. -/
theorem dahlbergFourVertex_reflectIndex_iff {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {a : ZMod n} :
    DahlbergFourVertex (fun j => κ (a - j)) ↔ DahlbergFourVertex κ := by
  constructor
  · intro hfv
    have hback :=
      dahlbergFourVertex_reflectIndex (κ := fun j : ZMod n => κ (a - j)) a hfv
    convert hback using 1
    ext j
    congr 1
    abel
  · exact dahlbergFourVertex_reflectIndex a

/-- A Dahlberg four-vertex conclusion for the orientation-reversed negated
profile transports back to the original profile. -/
theorem dahlbergFourVertex_of_neg_reflectIndex {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ}
    (hfv : DahlbergFourVertex (fun i => -κ (-i))) :
    DahlbergFourVertex κ := by
  have hfv_neg : DahlbergFourVertex (fun i => -κ i) := by
    exact (dahlbergFourVertex_reflectIndex_iff
      (κ := fun i : ZMod n => -κ i) (a := 0)).mp (by
        convert hfv using 1
        ext i
        congr 1
        abel_nf)
  exact dahlbergFourVertex_of_neg hfv_neg

/-- A constant-or-Dahlberg conclusion for the orientation-reversed negated
profile transports back to the original profile. -/
theorem constant_or_dahlbergFourVertex_of_neg_reflectIndex {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ}
    (h : (∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
      DahlbergFourVertex (fun i => -κ (-i))) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases h with hconst | hfv
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨-c, fun i => by
      have hi := congrArg Neg.neg (hc (-i))
      simpa using hi⟩
  · exact Or.inr (dahlbergFourVertex_of_neg_reflectIndex hfv)

/-- Four ordered strict one-step extrema give Dahlberg's plateau-aware
four-vertex conclusion. -/
theorem dahlbergFourVertex_of_strict_neighbors {n : ℕ} (hn : 2 ≤ n)
    {κ : ZMod n → ℝ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmax₁_left : κ ((i₁ : ZMod n) - 1) < κ (i₁ : ZMod n))
    (hmax₁_right : κ ((i₁ : ZMod n) + 1) < κ (i₁ : ZMod n))
    (hmin₂_left : κ (i₂ : ZMod n) < κ ((i₂ : ZMod n) - 1))
    (hmin₂_right : κ (i₂ : ZMod n) < κ ((i₂ : ZMod n) + 1))
    (hmax₃_left : κ ((i₃ : ZMod n) - 1) < κ (i₃ : ZMod n))
    (hmax₃_right : κ ((i₃ : ZMod n) + 1) < κ (i₃ : ZMod n))
    (hmin₄_left : κ (i₄ : ZMod n) < κ ((i₄ : ZMod n) - 1))
    (hmin₄_right : κ (i₄ : ZMod n) < κ ((i₄ : ZMod n) + 1)) :
    DahlbergFourVertex κ := by
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_⟩
  · exact discreteLocalMax_of_neighbors hn hmax₁_left hmax₁_right
  · exact discreteLocalMin_of_neighbors hn hmin₂_left hmin₂_right
  · exact discreteLocalMax_of_neighbors hn hmax₃_left hmax₃_right
  · exact discreteLocalMin_of_neighbors hn hmin₄_left hmin₄_right

/-- Four ordered strict one-step extrema in `min-max-min-max` order also give
Dahlberg's plateau-aware four-vertex conclusion, by rotating the cyclic order
to start at the first maximum. -/
theorem dahlbergFourVertex_of_strict_neighbors_min_max {n : ℕ} (hn : 2 ≤ n)
    {κ : ZMod n → ℝ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁_left : κ (i₁ : ZMod n) < κ ((i₁ : ZMod n) - 1))
    (hmin₁_right : κ (i₁ : ZMod n) < κ ((i₁ : ZMod n) + 1))
    (hmax₂_left : κ ((i₂ : ZMod n) - 1) < κ (i₂ : ZMod n))
    (hmax₂_right : κ ((i₂ : ZMod n) + 1) < κ (i₂ : ZMod n))
    (hmin₃_left : κ (i₃ : ZMod n) < κ ((i₃ : ZMod n) - 1))
    (hmin₃_right : κ (i₃ : ZMod n) < κ ((i₃ : ZMod n) + 1))
    (hmax₄_left : κ ((i₄ : ZMod n) - 1) < κ (i₄ : ZMod n))
    (hmax₄_right : κ ((i₄ : ZMod n) + 1) < κ (i₄ : ZMod n)) :
    DahlbergFourVertex κ := by
  have hwrap : ((i₁ + n : ℕ) : ZMod n) = (i₁ : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  exact dahlbergFourVertex_of_strict_neighbors hn
    hi₂₃ hi₃₄ hi₄₁ (Nat.add_lt_add_right hi₁₂ n)
    hmax₂_left hmax₂_right
    hmin₃_left hmin₃_right
    hmax₄_left hmax₄_right
    (by simpa [hwrap] using hmin₁_left)
    (by simpa [hwrap] using hmin₁_right)

/-- Four ordered adjacent turn points, alternating peak/valley/peak/valley,
give Dahlberg's plateau-aware four-vertex conclusion. -/
theorem dahlbergFourVertex_of_ordered_turns {n : ℕ} (hn : 2 ≤ n)
    {κ : ZMod n → ℝ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hinc₁ : κ (i₁ : ZMod n) < κ ((i₁ : ZMod n) + 1))
    (hdec₁ : κ (((i₁ : ZMod n) + 1) + 1) < κ ((i₁ : ZMod n) + 1))
    (hdec₂ : κ ((i₂ : ZMod n) + 1) < κ (i₂ : ZMod n))
    (hinc₂ : κ ((i₂ : ZMod n) + 1) < κ (((i₂ : ZMod n) + 1) + 1))
    (hinc₃ : κ (i₃ : ZMod n) < κ ((i₃ : ZMod n) + 1))
    (hdec₃ : κ (((i₃ : ZMod n) + 1) + 1) < κ ((i₃ : ZMod n) + 1))
    (hdec₄ : κ ((i₄ : ZMod n) + 1) < κ (i₄ : ZMod n))
    (hinc₄ : κ ((i₄ : ZMod n) + 1) < κ (((i₄ : ZMod n) + 1) + 1)) :
    DahlbergFourVertex κ := by
  apply dahlbergFourVertex_of_strict_neighbors hn
    (Nat.succ_lt_succ hi₁₂) (Nat.succ_lt_succ hi₂₃) (Nat.succ_lt_succ hi₃₄)
    (by omega)
  · simpa [Nat.cast_add, sub_eq_add_neg, add_assoc] using hinc₁
  · simpa [Nat.cast_add, add_assoc] using hdec₁
  · simpa [Nat.cast_add, sub_eq_add_neg, add_assoc] using hdec₂
  · simpa [Nat.cast_add, add_assoc] using hinc₂
  · simpa [Nat.cast_add, sub_eq_add_neg, add_assoc] using hinc₃
  · simpa [Nat.cast_add, add_assoc] using hdec₃
  · simpa [Nat.cast_add, sub_eq_add_neg, add_assoc] using hdec₄
  · simpa [Nat.cast_add, add_assoc] using hinc₄

/-- Four ordered adjacent turns of a cyclic profile, alternating
increase/decrease/decrease/increase.  This is the source witness extracted by
Dahlberg's geometric comparison arguments before the purely cyclic conversion
to plateau-aware local extrema. -/
def OrderedAdjacentTurns {n : ℕ} (κ : ZMod n → ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ,
    i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      κ (i₁ : ZMod n) < κ ((i₁ : ZMod n) + 1) ∧
      κ (((i₁ : ZMod n) + 1) + 1) < κ ((i₁ : ZMod n) + 1) ∧
      κ ((i₂ : ZMod n) + 1) < κ (i₂ : ZMod n) ∧
      κ ((i₂ : ZMod n) + 1) < κ (((i₂ : ZMod n) + 1) + 1) ∧
      κ (i₃ : ZMod n) < κ ((i₃ : ZMod n) + 1) ∧
      κ (((i₃ : ZMod n) + 1) + 1) < κ ((i₃ : ZMod n) + 1) ∧
      κ ((i₄ : ZMod n) + 1) < κ (i₄ : ZMod n) ∧
      κ ((i₄ : ZMod n) + 1) < κ (((i₄ : ZMod n) + 1) + 1)

/-- Four ordered adjacent turns imply Dahlberg's plateau-aware four-vertex
conclusion. -/
theorem dahlbergFourVertex_of_orderedAdjacentTurns {n : ℕ} (hn : 2 ≤ n)
    {κ : ZMod n → ℝ} (hturns : OrderedAdjacentTurns κ) :
    DahlbergFourVertex κ := by
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hinc₁, hdec₁, hdec₂, hinc₂, hinc₃, hdec₃, hdec₄, hinc₄⟩
  exact dahlbergFourVertex_of_ordered_turns hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hinc₁ hdec₁ hdec₂ hinc₂ hinc₃ hdec₃ hdec₄ hinc₄

/-- Four ordered adjacent turns imply Dahlberg's conclusion under the standard
`4 ≤ n` polygon-size hypothesis. -/
theorem dahlbergFourVertex_of_orderedAdjacentTurns_four_le {n : ℕ}
    (hn : 4 ≤ n) {κ : ZMod n → ℝ} (hturns : OrderedAdjacentTurns κ) :
    DahlbergFourVertex κ := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns (two_le_of_four_le hn) hturns

/-- A constant-or ordered-adjacent-turn witness gives the corresponding
constant-or Dahlberg conclusion. -/
theorem constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns {n : ℕ}
    (hn : 4 ≤ n) {κ : ZMod n → ℝ}
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases h with hconst | hturns
  · exact Or.inl hconst
  · exact Or.inr (dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn hturns)

/-- A constant-or-reflected ordered-turn conclusion transports to a
constant-or-Dahlberg conclusion for the original profile.  This is the
turn-level analogue of `constant_or_dahlbergFourVertex_of_neg_reflectIndex`
for negative-orientation discrete wrappers. -/
theorem constant_or_dahlbergFourVertex_of_constant_or_orderedAdjacentTurns_neg_reflectIndex
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {κ : ZMod n → ℝ}
    (h : (∃ c, ∀ i : ZMod n, -κ (-i) = c) ∨
      OrderedAdjacentTurns (fun i => -κ (-i))) :
    (∃ c, ∀ i : ZMod n, κ i = c) ∨ DahlbergFourVertex κ := by
  rcases h with hconst | hturns
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨-c, fun i => by
      have hi := congrArg Neg.neg (hc (-i))
      simpa using hi⟩
  · have hfv_reflected : DahlbergFourVertex (fun i => -κ (-i)) :=
      dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn hturns
    exact Or.inr (dahlbergFourVertex_of_neg_reflectIndex hfv_reflected)

/-- An ordered-adjacent-turn witness contains, in particular, an adjacent
strict increase and an adjacent strict decrease. -/
theorem exists_adjacent_increase_and_decrease_of_orderedAdjacentTurns {n : ℕ}
    {κ : ZMod n → ℝ} (hturns : OrderedAdjacentTurns κ) :
    (∃ i : ZMod n, κ i < κ (i + 1)) ∧
      ∃ i : ZMod n, κ (i + 1) < κ i := by
  rcases hturns with
    ⟨i₁, _i₂, _i₃, _i₄, _hi₁₂, _hi₂₃, _hi₃₄, _hi₄₁,
      hinc₁, hdec₁, _hdec₂, _hinc₂, _hinc₃, _hdec₃, _hdec₄, _hinc₄⟩
  refine ⟨⟨i₁, hinc₁⟩, ⟨(i₁ : ZMod n) + 1, ?_⟩⟩
  simpa [add_assoc] using hdec₁

/-- An ordered-adjacent-turn witness forces the cyclic profile to be
nonconstant. -/
theorem not_constant_of_orderedAdjacentTurns {n : ℕ} {κ : ZMod n → ℝ}
    (hturns : OrderedAdjacentTurns κ) :
    ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  rintro ⟨c, hconst⟩
  rcases exists_adjacent_increase_and_decrease_of_orderedAdjacentTurns hturns with
    ⟨⟨i, hinc⟩, _⟩
  rw [hconst i, hconst (i + 1)] at hinc
  exact (lt_irrefl c) hinc

/-- Positive affine changes preserve ordered adjacent turns. -/
theorem orderedAdjacentTurns_posAffine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) (hturns : OrderedAdjacentTurns κ) :
    OrderedAdjacentTurns (fun i => a * κ i + b) := by
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hinc₁, hdec₁, hdec₂, hinc₂, hinc₃, hdec₃, hdec₄, hinc₄⟩
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_lt_mul_of_pos_left hinc₁ ha]
  · nlinarith [mul_lt_mul_of_pos_left hdec₁ ha]
  · nlinarith [mul_lt_mul_of_pos_left hdec₂ ha]
  · nlinarith [mul_lt_mul_of_pos_left hinc₂ ha]
  · nlinarith [mul_lt_mul_of_pos_left hinc₃ ha]
  · nlinarith [mul_lt_mul_of_pos_left hdec₃ ha]
  · nlinarith [mul_lt_mul_of_pos_left hdec₄ ha]
  · nlinarith [mul_lt_mul_of_pos_left hinc₄ ha]

/-- A cyclic profile pointwise equal to a positive affine change of another
profile inherits ordered adjacent turns. -/
theorem orderedAdjacentTurns_of_eq_posAffine {n : ℕ} {κ μ : ZMod n → ℝ}
    {a b : ℝ} (ha : 0 < a) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (hturns : OrderedAdjacentTurns κ) :
    OrderedAdjacentTurns μ := by
  have hscaled := orderedAdjacentTurns_posAffine (κ := κ) (a := a) (b := b) ha hturns
  convert hscaled using 1
  ext i
  exact hμ i

/-- Pointwise equal cyclic profiles have the same ordered-adjacent-turn
witness. -/
theorem orderedAdjacentTurns_congr {n : ℕ} {κ μ : ZMod n → ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i) (hturns : OrderedAdjacentTurns κ) :
    OrderedAdjacentTurns μ := by
  exact orderedAdjacentTurns_of_eq_posAffine (a := 1) (b := 0) (by norm_num)
    (by intro i; simp [hμ i]) hturns

/-- Negating a cyclic profile preserves ordered adjacent turns, after rotating
the witness to start at the first original valley. -/
theorem orderedAdjacentTurns_neg {n : ℕ} {κ : ZMod n → ℝ}
    (hturns : OrderedAdjacentTurns κ) :
    OrderedAdjacentTurns (fun i => -κ i) := by
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hinc₁, hdec₁, hdec₂, hinc₂, hinc₃, hdec₃, hdec₄, hinc₄⟩
  have hwrap : ((i₁ + n : ℕ) : ZMod n) = (i₁ : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  refine ⟨i₂, i₃, i₄, i₁ + n, hi₂₃, hi₃₄, hi₄₁,
    Nat.add_lt_add_right hi₁₂ n, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact neg_lt_neg hdec₂
  · exact neg_lt_neg hinc₂
  · exact neg_lt_neg hinc₃
  · exact neg_lt_neg hdec₃
  · exact neg_lt_neg hdec₄
  · exact neg_lt_neg hinc₄
  · simpa [hwrap] using neg_lt_neg hinc₁
  · simpa [hwrap] using neg_lt_neg hdec₁

/-- Ordered adjacent turns are invariant under negating the cyclic profile. -/
theorem orderedAdjacentTurns_neg_iff {n : ℕ} {κ : ZMod n → ℝ} :
    OrderedAdjacentTurns (fun i => -κ i) ↔ OrderedAdjacentTurns κ := by
  constructor
  · intro hturns
    have hback := orderedAdjacentTurns_neg (κ := fun i : ZMod n => -κ i) hturns
    convert hback using 1
    ext i
    simp
  · exact orderedAdjacentTurns_neg

/-- Nonzero affine changes preserve ordered adjacent turns.  Negative scales
are handled by negating the profile, which swaps maxima and minima and rotates
the ordered witness. -/
theorem orderedAdjacentTurns_affine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hturns : OrderedAdjacentTurns κ) :
    OrderedAdjacentTurns (fun i => a * κ i + b) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hturns_neg : OrderedAdjacentTurns (fun i => -κ i) :=
      orderedAdjacentTurns_neg hturns
    have hscaled :=
      orderedAdjacentTurns_posAffine (κ := fun i : ZMod n => -κ i)
        (a := -a) (b := b) (neg_pos.mpr hneg) hturns_neg
    convert hscaled using 1
    ext i
    ring
  · exact orderedAdjacentTurns_posAffine hpos hturns

/-- Nonzero affine changes preserve ordered adjacent turns exactly. -/
theorem orderedAdjacentTurns_affine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    OrderedAdjacentTurns (fun i => a * κ i + b) ↔ OrderedAdjacentTurns κ := by
  constructor
  · intro hturns
    have hback :=
      orderedAdjacentTurns_affine (κ := fun i => a * κ i + b)
        (a := a⁻¹) (b := -b / a) (inv_ne_zero ha) hturns
    convert hback using 1
    ext i
    field_simp [ha]
    ring
  · exact orderedAdjacentTurns_affine ha

/-- A cyclic profile pointwise equal to a nonzero affine change of another
profile inherits ordered adjacent turns. -/
theorem orderedAdjacentTurns_of_eq_affine {n : ℕ} {κ μ : ZMod n → ℝ}
    {a b : ℝ} (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (hturns : OrderedAdjacentTurns κ) :
    OrderedAdjacentTurns μ := by
  have hscaled := orderedAdjacentTurns_affine (κ := κ) (a := a) (b := b) ha hturns
  convert hscaled using 1
  ext i
  exact hμ i

/-- Nonzero affine changes preserve a constant-or-ordered-turn conclusion. -/
theorem constant_or_orderedAdjacentTurns_affine {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0)
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ) :
    (∃ c, ∀ i : ZMod n, a * κ i + b = c) ∨
      OrderedAdjacentTurns (fun i => a * κ i + b) := by
  rcases h with hconst | hturns
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨a * c + b, fun i => by simp [hc i]⟩
  · exact Or.inr (orderedAdjacentTurns_affine ha hturns)

/-- A profile pointwise equal to a nonzero affine change of a
constant-or-ordered-turn profile inherits the same conclusion. -/
theorem constant_or_orderedAdjacentTurns_of_eq_affine {n : ℕ}
    {κ μ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b)
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ) :
    (∃ c, ∀ i : ZMod n, μ i = c) ∨ OrderedAdjacentTurns μ := by
  rcases constant_or_orderedAdjacentTurns_affine (κ := κ) (a := a) (b := b) ha h with
    hconst | hturns
  · rcases hconst with ⟨c, hc⟩
    exact Or.inl ⟨c, fun i => by rw [hμ i, hc i]⟩
  · exact Or.inr (by
      convert hturns using 1
      ext i
      exact hμ i)

/-- Pointwise equal cyclic profiles have the same constant-or-ordered-turn
conclusion. -/
theorem constant_or_orderedAdjacentTurns_congr {n : ℕ} {κ μ : ZMod n → ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i)
    (h : (∃ c, ∀ i : ZMod n, κ i = c) ∨ OrderedAdjacentTurns κ) :
    (∃ c, ∀ i : ZMod n, μ i = c) ∨ OrderedAdjacentTurns μ := by
  exact constant_or_orderedAdjacentTurns_of_eq_affine (a := 1) (b := 0) (by norm_num)
    (by intro i; simp [hμ i]) h

/-- Translating cyclic indices preserves ordered adjacent turns. -/
theorem orderedAdjacentTurns_translateIndex {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (a : ZMod n) (hturns : OrderedAdjacentTurns κ) :
    OrderedAdjacentTurns (fun j => κ (j + a)) := by
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hinc₁, hdec₁, hdec₂, hinc₂, hinc₃, hdec₃, hdec₄, hinc₄⟩
  let A := a.val
  let j₁ := i₁ + n - A
  let j₂ := i₂ + n - A
  let j₃ := i₃ + n - A
  let j₄ := i₄ + n - A
  have hAcast : (A : ZMod n) = a := ZMod.natCast_zmod_val a
  have hAlt : A < n := ZMod.val_lt a
  have hA₁ : A ≤ i₁ + n := by omega
  have hA₂ : A ≤ i₂ + n := by omega
  have hA₃ : A ≤ i₃ + n := by omega
  have hA₄ : A ≤ i₄ + n := by omega
  have hj₁ : ((j₁ : ℕ) : ZMod n) = (i₁ : ZMod n) - a := by
    dsimp [j₁, A]
    rw [Nat.cast_sub hA₁, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
  have hj₂ : ((j₂ : ℕ) : ZMod n) = (i₂ : ZMod n) - a := by
    dsimp [j₂, A]
    rw [Nat.cast_sub hA₂, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
  have hj₃ : ((j₃ : ℕ) : ZMod n) = (i₃ : ZMod n) - a := by
    dsimp [j₃, A]
    rw [Nat.cast_sub hA₃, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
  have hj₄ : ((j₄ : ℕ) : ZMod n) = (i₄ : ZMod n) - a := by
    dsimp [j₄, A]
    rw [Nat.cast_sub hA₄, Nat.cast_add, ZMod.natCast_self, add_zero, hAcast]
  refine ⟨j₁, j₂, j₃, j₄, by omega, by omega, by omega, by omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hinc₁ using 1
    all_goals (simp [hj₁]; try abel_nf)
  · convert hdec₁ using 1
    all_goals (simp [hj₁]; try abel_nf)
  · convert hdec₂ using 1
    all_goals (simp [hj₂]; try abel_nf)
  · convert hinc₂ using 1
    all_goals (simp [hj₂]; try abel_nf)
  · convert hinc₃ using 1
    all_goals (simp [hj₃]; try abel_nf)
  · convert hdec₃ using 1
    all_goals (simp [hj₃]; try abel_nf)
  · convert hdec₄ using 1
    all_goals (simp [hj₄]; try abel_nf)
  · convert hinc₄ using 1
    all_goals (simp [hj₄]; try abel_nf)

/-- Translating cyclic indices preserves ordered adjacent turns exactly. -/
theorem orderedAdjacentTurns_translateIndex_iff {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {a : ZMod n} :
    OrderedAdjacentTurns (fun j => κ (j + a)) ↔ OrderedAdjacentTurns κ := by
  constructor
  · intro hturns
    have hback :=
      orderedAdjacentTurns_translateIndex (κ := fun j : ZMod n => κ (j + a)) (-a) hturns
    convert hback using 1
    ext j
    congr 1
    abel
  · exact orderedAdjacentTurns_translateIndex a

/-- A cyclic real profile has a global maximum. -/
theorem exists_globalMax_zmod {n : ℕ} [NeZero n] (κ : ZMod n → ℝ) :
    ∃ i : ZMod n, ∀ j : ZMod n, κ j ≤ κ i := by
  obtain ⟨i, _hi_mem, hi⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (ZMod n)) κ Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- A cyclic real profile has a global minimum. -/
theorem exists_globalMin_zmod {n : ℕ} [NeZero n] (κ : ZMod n → ℝ) :
    ∃ i : ZMod n, ∀ j : ZMod n, κ i ≤ κ j := by
  obtain ⟨i, _hi_mem, hi⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (ZMod n)) κ Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- A nonconstant cyclic real profile has a global minimum and maximum with
strictly separated values. -/
theorem exists_globalMinMax_strict_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, κ i₀ ≤ κ j) ∧
      (∀ j : ZMod n, κ j ≤ κ i₁) ∧
      κ i₀ < κ i₁ := by
  obtain ⟨i₀, hmin⟩ := exists_globalMin_zmod κ
  obtain ⟨i₁, hmax⟩ := exists_globalMax_zmod κ
  refine ⟨i₀, i₁, hmin, hmax, ?_⟩
  by_contra hnot
  have hle : κ i₁ ≤ κ i₀ := le_of_not_gt hnot
  apply hnc
  refine ⟨κ i₀, fun j => ?_⟩
  exact le_antisymm ((hmax j).trans hle) (hmin j)

/-- A global maximum with some strictly lower value is a plateau-aware local
maximum.

The proof chooses the nearest strict drops to the left and right of the chosen
global maximum.  The two nearest-drop distances fit inside one cyclic period,
which is the finite plateau bookkeeping needed by Dahlberg's local-extrema
interface. -/
theorem discreteLocalMax_of_globalMax_of_exists_lt {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {i : ZMod n} (hmax : ∀ j : ZMod n, κ j ≤ κ i)
    (hdrop : ∃ j : ZMod n, κ j < κ i) :
    DiscreteLocalMax κ i := by
  classical
  have hright_exists :
      ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ κ (i + (r : ZMod n)) < κ i := by
    rcases hdrop with ⟨j, hj⟩
    let r : ℕ := (j - i).val
    have hrpos : 0 < r := by
      by_contra hr0not
      have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr0not
      have hji : j - i = 0 := by
        exact (ZMod.val_eq_zero (j - i)).mp hr0
      have hji' : j = i := by
        have := congrArg (fun x : ZMod n => x + i) hji
        simpa using this
      rw [hji'] at hj
      exact (lt_irrefl (κ i)) hj
    have hrle : r ≤ n := (ZMod.val_lt (j - i)).le
    have hidx : i + (r : ZMod n) = j := by
      dsimp [r]
      rw [ZMod.natCast_zmod_val (j - i)]
      abel
    exact ⟨r, hrpos, hrle, by simpa [hidx] using hj⟩
  have hleft_exists :
      ∃ l : ℕ, 0 < l ∧ l ≤ n ∧ κ (i - (l : ZMod n)) < κ i := by
    rcases hdrop with ⟨j, hj⟩
    let l : ℕ := (i - j).val
    have hlpos : 0 < l := by
      by_contra hl0not
      have hl0 : l = 0 := Nat.eq_zero_of_not_pos hl0not
      have hij : i - j = 0 := by
        exact (ZMod.val_eq_zero (i - j)).mp hl0
      have hji : j = i := by
        have := congrArg (fun x : ZMod n => x + j) hij
        simpa using this.symm
      rw [hji] at hj
      exact (lt_irrefl (κ i)) hj
    have hlle : l ≤ n := (ZMod.val_lt (i - j)).le
    have hidx : i - (l : ZMod n) = j := by
      dsimp [l]
      rw [ZMod.natCast_zmod_val (i - j)]
      abel
    exact ⟨l, hlpos, hlle, by simpa [hidx] using hj⟩
  let r : ℕ := Nat.find hright_exists
  let l : ℕ := Nat.find hleft_exists
  have hr_spec : 0 < r ∧ r ≤ n ∧ κ (i + (r : ZMod n)) < κ i := by
    simpa [r] using Nat.find_spec hright_exists
  have hl_spec : 0 < l ∧ l ≤ n ∧ κ (i - (l : ZMod n)) < κ i := by
    simpa [l] using Nat.find_spec hleft_exists
  have hright_eq : ∀ m < r, κ (i + (m : ZMod n)) = κ i := by
    intro m hm
    by_cases hm0 : m = 0
    · simp [hm0]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmle : m ≤ n := (le_of_lt hm).trans hr_spec.2.1
      have hnotlt : ¬ κ (i + (m : ZMod n)) < κ i := by
        intro hlt
        exact (Nat.find_min hright_exists hm) ⟨hmpos, hmle, hlt⟩
      exact le_antisymm (hmax _) (le_of_not_gt hnotlt)
  have hleft_eq : ∀ m < l, κ (i - (m : ZMod n)) = κ i := by
    intro m hm
    by_cases hm0 : m = 0
    · simp [hm0]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmle : m ≤ n := (le_of_lt hm).trans hl_spec.2.1
      have hnotlt : ¬ κ (i - (m : ZMod n)) < κ i := by
        intro hlt
        exact (Nat.find_min hleft_exists hm) ⟨hmpos, hmle, hlt⟩
      exact le_antisymm (hmax _) (le_of_not_gt hnotlt)
  have hl_lt_n : l < n := by
    refine lt_of_le_of_ne hl_spec.2.1 ?_
    intro hln
    have hidx : i - (l : ZMod n) = i := by
      rw [hln, ZMod.natCast_self, sub_zero]
    exact (lt_irrefl (κ i)) (by simpa [hidx] using hl_spec.2.2)
  have hlr : l + r ≤ n := by
    by_contra hnot
    have hlt : n < l + r := Nat.lt_of_not_ge hnot
    let m : ℕ := n - l
    have hmpos : 0 < m := Nat.sub_pos_of_lt hl_lt_n
    have hmle : m ≤ n := Nat.sub_le n l
    have hm_lt_r : m < r := by
      dsimp [m]
      omega
    have hcast : ((m : ℕ) : ZMod n) = -(l : ZMod n) := by
      dsimp [m]
      rw [Nat.cast_sub hl_spec.2.1, ZMod.natCast_self]
      abel
    have hdrop_m : κ (i + (m : ZMod n)) < κ i := by
      simpa [hcast, sub_eq_add_neg] using hl_spec.2.2
    exact (Nat.find_min hright_exists hm_lt_r) ⟨hmpos, hmle, hdrop_m⟩
  exact ⟨l, r, hl_spec.1, hr_spec.1, hlr, hleft_eq, hright_eq,
    hl_spec.2.2, hr_spec.2.2⟩

/-- A chosen global maximum of a nonconstant cyclic real profile is a
plateau-aware local maximum. -/
theorem discreteLocalMax_of_globalMax_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {i : ZMod n} (hmax : ∀ j : ZMod n, κ j ≤ κ i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DiscreteLocalMax κ i := by
  have hdrop : ∃ j : ZMod n, κ j < κ i := by
    by_contra hnone
    apply hnc
    refine ⟨κ i, fun j => ?_⟩
    exact le_antisymm (hmax j) (le_of_not_gt (fun hj => hnone ⟨j, hj⟩))
  exact discreteLocalMax_of_globalMax_of_exists_lt hmax hdrop

/-- A marked weak cyclic maximum is plateau-aware when the marking propagates
across equal adjacent values.

This packages the finite plateau argument used in Dahlberg's Lemma 9.  A
marked index is weakly maximal among its two neighbours.  If the mark passes
to an adjacent index whenever the two values agree, then a nonconstant cyclic
profile must eventually leave the marked plateau strictly downward on both
sides. -/
theorem discreteLocalMax_of_weak_neighbors_of_eq_propagates
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {P : ZMod n → Prop} {i : ZMod n}
    (hPi : P i)
    (hweak : ∀ j, P j → κ (j - 1) ≤ κ j ∧ κ (j + 1) ≤ κ j)
    (hpropRight : ∀ j, P j → κ j = κ (j + 1) → P (j + 1))
    (hpropLeft : ∀ j, P j → κ j = κ (j - 1) → P (j - 1))
    (hnc : ¬ ∃ c, ∀ j : ZMod n, κ j = c) :
    DiscreteLocalMax κ i := by
  classical
  have hrightExists :
      ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ κ (i + (r : ZMod n)) < κ i := by
    by_contra hnone
    have hplateau : ∀ m : ℕ, m ≤ n →
        κ (i + (m : ZMod n)) = κ i ∧ P (i + (m : ZMod n)) := by
      intro m hm
      induction m with
      | zero =>
          constructor
          · simp
          · simpa using hPi
      | succ m ih =>
          rcases ih (by omega) with ⟨hκm, hPm⟩
          have hle : κ (i + ((m + 1 : ℕ) : ZMod n)) ≤ κ i := by
            simpa [Nat.cast_add, add_assoc, hκm] using (hweak _ hPm).2
          have heq : κ (i + ((m + 1 : ℕ) : ZMod n)) = κ i := by
            apply le_antisymm hle
            apply le_of_not_gt
            intro hlt
            exact hnone ⟨m + 1, by omega, hm, hlt⟩
          refine ⟨heq, ?_⟩
          have hstep : κ (i + (m : ZMod n)) = κ (i + (m : ZMod n) + 1) := by
            rw [hκm]
            simpa [Nat.cast_add, add_assoc] using heq.symm
          simpa [Nat.cast_add, add_assoc] using hpropRight _ hPm hstep
    apply hnc
    refine ⟨κ i, fun j => ?_⟩
    let m : ℕ := (j - i).val
    have hmle : m ≤ n := (ZMod.val_lt (j - i)).le
    have hm := (hplateau m hmle).1
    have hidx : i + (m : ZMod n) = j := by
      dsimp [m]
      rw [ZMod.natCast_zmod_val (j - i)]
      abel
    simpa [hidx] using hm
  have hleftExists :
      ∃ l : ℕ, 0 < l ∧ l ≤ n ∧ κ (i - (l : ZMod n)) < κ i := by
    by_contra hnone
    have hplateau : ∀ m : ℕ, m ≤ n →
        κ (i - (m : ZMod n)) = κ i ∧ P (i - (m : ZMod n)) := by
      intro m hm
      induction m with
      | zero =>
          constructor
          · simp
          · simpa using hPi
      | succ m ih =>
          rcases ih (by omega) with ⟨hκm, hPm⟩
          have hle : κ (i - ((m + 1 : ℕ) : ZMod n)) ≤ κ i := by
            have hle' := (hweak _ hPm).1
            rw [hκm] at hle'
            convert hle' using 1
            norm_num
            abel_nf
          have heq : κ (i - ((m + 1 : ℕ) : ZMod n)) = κ i := by
            apply le_antisymm hle
            apply le_of_not_gt
            intro hlt
            exact hnone ⟨m + 1, by omega, hm, hlt⟩
          refine ⟨heq, ?_⟩
          have hstep : κ (i - (m : ZMod n)) = κ (i - (m : ZMod n) - 1) := by
            rw [hκm]
            convert heq.symm using 1
            norm_num
            abel_nf
          convert hpropLeft _ hPm hstep using 1
          norm_num
          abel_nf
    apply hnc
    refine ⟨κ i, fun j => ?_⟩
    let m : ℕ := (i - j).val
    have hmle : m ≤ n := (ZMod.val_lt (i - j)).le
    have hm := (hplateau m hmle).1
    have hidx : i - (m : ZMod n) = j := by
      dsimp [m]
      rw [ZMod.natCast_zmod_val (i - j)]
      abel
    simpa [hidx] using hm
  let r : ℕ := Nat.find hrightExists
  let l : ℕ := Nat.find hleftExists
  have hrSpec : 0 < r ∧ r ≤ n ∧ κ (i + (r : ZMod n)) < κ i := by
    simpa [r] using Nat.find_spec hrightExists
  have hlSpec : 0 < l ∧ l ≤ n ∧ κ (i - (l : ZMod n)) < κ i := by
    simpa [l] using Nat.find_spec hleftExists
  have hrightEqP : ∀ m < r,
      κ (i + (m : ZMod n)) = κ i ∧ P (i + (m : ZMod n)) := by
    intro m hm
    induction m with
    | zero =>
        constructor
        · simp
        · simpa using hPi
    | succ m ih =>
        rcases ih (by omega) with ⟨hκm, hPm⟩
        have hle : κ (i + ((m + 1 : ℕ) : ZMod n)) ≤ κ i := by
          simpa [Nat.cast_add, add_assoc, hκm] using (hweak _ hPm).2
        have heq : κ (i + ((m + 1 : ℕ) : ZMod n)) = κ i := by
          apply le_antisymm hle
          apply le_of_not_gt
          intro hlt
          exact (Nat.find_min hrightExists hm)
            ⟨by omega, (Nat.le_of_lt hm).trans hrSpec.2.1, hlt⟩
        refine ⟨heq, ?_⟩
        have hstep : κ (i + (m : ZMod n)) = κ (i + (m : ZMod n) + 1) := by
          rw [hκm]
          simpa [Nat.cast_add, add_assoc] using heq.symm
        simpa [Nat.cast_add, add_assoc] using hpropRight _ hPm hstep
  have hleftEqP : ∀ m < l,
      κ (i - (m : ZMod n)) = κ i ∧ P (i - (m : ZMod n)) := by
    intro m hm
    induction m with
    | zero =>
        constructor
        · simp
        · simpa using hPi
    | succ m ih =>
        rcases ih (by omega) with ⟨hκm, hPm⟩
        have hle : κ (i - ((m + 1 : ℕ) : ZMod n)) ≤ κ i := by
          have hle' := (hweak _ hPm).1
          rw [hκm] at hle'
          convert hle' using 1
          norm_num
          abel_nf
        have heq : κ (i - ((m + 1 : ℕ) : ZMod n)) = κ i := by
          apply le_antisymm hle
          apply le_of_not_gt
          intro hlt
          exact (Nat.find_min hleftExists hm)
            ⟨by omega, (Nat.le_of_lt hm).trans hlSpec.2.1, hlt⟩
        refine ⟨heq, ?_⟩
        have hstep : κ (i - (m : ZMod n)) = κ (i - (m : ZMod n) - 1) := by
          rw [hκm]
          convert heq.symm using 1
          norm_num
          abel_nf
        convert hpropLeft _ hPm hstep using 1
        norm_num
        abel_nf
  have hlLtN : l < n := by
    refine lt_of_le_of_ne hlSpec.2.1 ?_
    intro hln
    have hidx : i - (l : ZMod n) = i := by
      rw [hln, ZMod.natCast_self, sub_zero]
    exact (lt_irrefl (κ i)) (by simpa [hidx] using hlSpec.2.2)
  have hlr : l + r ≤ n := by
    by_contra hnot
    have hlt : n < l + r := Nat.lt_of_not_ge hnot
    let m : ℕ := n - l
    have hmpos : 0 < m := Nat.sub_pos_of_lt hlLtN
    have hmLtR : m < r := by
      dsimp [m]
      omega
    have hcast : (m : ZMod n) = -(l : ZMod n) := by
      dsimp [m]
      rw [Nat.cast_sub hlSpec.2.1, ZMod.natCast_self]
      abel
    have hdrop : κ (i + (m : ZMod n)) < κ i := by
      simpa [hcast, sub_eq_add_neg] using hlSpec.2.2
    rw [(hrightEqP m hmLtR).1] at hdrop
    exact (lt_irrefl (κ i)) hdrop
  exact ⟨l, r, hlSpec.1, hrSpec.1, hlr,
    fun m hm => (hleftEqP m hm).1,
    fun m hm => (hrightEqP m hm).1,
    hlSpec.2.2, hrSpec.2.2⟩

/-- A marked weak maximum cannot remain on its plateau all the way to an
unmarked endpoint. -/
theorem exists_strict_drop_forward_of_marked_weakMax
    {n : ℕ} {κ : ZMod n → ℝ} {P : ZMod n → Prop} {a b : ℕ}
    (hab : a < b)
    (hPa : P (a : ZMod n)) (hnotPb : ¬ P (b : ZMod n))
    (hweakRight : ∀ j, P j → κ (j + 1) ≤ κ j)
    (hpropRight : ∀ j, P j → κ j = κ (j + 1) → P (j + 1)) :
    ∃ k : ℕ, a < k ∧ k ≤ b ∧ κ (k : ZMod n) < κ (a : ZMod n) := by
  classical
  by_contra hnone
  have hwalk : ∀ t : ℕ, t ≤ b - a →
      κ (a + t : ZMod n) = κ (a : ZMod n) ∧ P (a + t : ZMod n) := by
    intro t ht
    induction t with
    | zero =>
        constructor
        · simp
        · simpa using hPa
    | succ t ih =>
        rcases ih (by omega) with ⟨hκt, hPt⟩
        have hle : κ (a + (t + 1) : ZMod n) ≤ κ (a : ZMod n) := by
          calc
            κ (a + (t + 1) : ZMod n) = κ ((a + t : ZMod n) + 1) := by
              congr 1
              ring
            _ ≤ κ (a + t : ZMod n) := hweakRight _ hPt
            _ = κ (a : ZMod n) := hκt
        have hnotlt : ¬ κ (a + (t + 1) : ZMod n) < κ (a : ZMod n) := by
          intro hlt
          apply hnone
          refine ⟨a + (t + 1), by omega, by omega, ?_⟩
          simpa [Nat.cast_add] using hlt
        have heq : κ (a + (t + 1) : ZMod n) = κ (a : ZMod n) :=
          le_antisymm hle (le_of_not_gt hnotlt)
        have heq' : κ (a + (t + 1 : ℕ) : ZMod n) = κ (a : ZMod n) := by
          simpa only [Nat.cast_add, Nat.cast_one] using heq
        refine ⟨heq', ?_⟩
        have hstep : κ (a + t : ZMod n) = κ ((a + t : ZMod n) + 1) := by
          rw [hκt]
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using heq.symm
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hpropRight _ hPt hstep
  have hend := (hwalk (b - a) (by omega)).2
  have hab_le : a ≤ b := Nat.le_of_lt hab
  rw [← Nat.cast_add, Nat.add_sub_of_le hab_le] at hend
  exact hnotPb hend

/-- Backward-facing version of
`exists_strict_drop_forward_of_marked_weakMax`. -/
theorem exists_strict_drop_backward_of_marked_weakMax
    {n : ℕ} {κ : ZMod n → ℝ} {P : ZMod n → Prop} {a b : ℕ}
    (hab : a < b)
    (hPb : P (b : ZMod n)) (hnotPa : ¬ P (a : ZMod n))
    (hweakLeft : ∀ j, P j → κ (j - 1) ≤ κ j)
    (hpropLeft : ∀ j, P j → κ j = κ (j - 1) → P (j - 1)) :
    ∃ k : ℕ, a ≤ k ∧ k < b ∧ κ (k : ZMod n) < κ (b : ZMod n) := by
  let A : ZMod n := (a + b : ℕ)
  let μ : ZMod n → ℝ := fun z => κ (A - z)
  let Q : ZMod n → Prop := fun z => P (A - z)
  have hQa : Q (a : ZMod n) := by
    dsimp [Q, A]
    convert hPb using 1
    push_cast
    abel
  have hnotQb : ¬ Q (b : ZMod n) := by
    intro hQb
    apply hnotPa
    dsimp [Q, A] at hQb
    convert hQb using 1
    push_cast
    abel
  have hweakQ : ∀ z, Q z → μ (z + 1) ≤ μ z := by
    intro z hz
    dsimp [Q, μ] at hz ⊢
    convert hweakLeft (A - z) hz using 1
    abel_nf
  have hpropQ : ∀ z, Q z → μ z = μ (z + 1) → Q (z + 1) := by
    intro z hz heq
    dsimp [Q, μ] at hz heq ⊢
    have hp : P (A - z - 1) := hpropLeft (A - z) hz (by
      convert heq using 1
      abel_nf)
    convert hp using 1
    abel
  rcases exists_strict_drop_forward_of_marked_weakMax
      hab hQa hnotQb hweakQ hpropQ with ⟨k, hak, hkb, hdrop⟩
  refine ⟨a + b - k, by omega, by omega, ?_⟩
  dsimp [μ, A] at hdrop
  have hk : k ≤ a + b := by omega
  have hidx : ((a + b - k : ℕ) : ZMod n) =
      ((a + b : ℕ) : ZMod n) - (k : ZMod n) := by
    rw [Nat.cast_sub hk]
  have hbidx : ((a + b : ℕ) : ZMod n) - (a : ZMod n) = (b : ZMod n) := by
    push_cast
    abel
  simpa [hidx, hbidx] using hdrop

/-- If a finite natural-index arc dips strictly below both endpoint values,
an interior minimum plateau of that arc is a cyclic discrete local minimum. -/
theorem exists_discreteLocalMin_between_of_strictly_below_endpoints
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {a b : ℕ}
    (hab : a < b)
    (hlowerA : ∃ k : ℕ, a ≤ k ∧ k ≤ b ∧
      κ (k : ZMod n) < κ (a : ZMod n))
    (hlowerB : ∃ k : ℕ, a ≤ k ∧ k ≤ b ∧
      κ (k : ZMod n) < κ (b : ZMod n))
    (hnc : ¬ ∃ c, ∀ z : ZMod n, κ z = c) :
    ∃ m : ℕ, a < m ∧ m < b ∧ DiscreteLocalMin κ (m : ZMod n) := by
  classical
  let S : Finset ℕ := Finset.Icc a b
  have hS : S.Nonempty := by
    refine ⟨a, ?_⟩
    simp [S, Nat.le_of_lt hab]
  obtain ⟨m, hmS, hmmin⟩ :=
    Finset.exists_min_image S (fun k : ℕ => κ (k : ZMod n)) hS
  have hm_bounds : a ≤ m ∧ m ≤ b := by
    simpa [S] using hmS
  have hm_lt_a : κ (m : ZMod n) < κ (a : ZMod n) := by
    rcases hlowerA with ⟨k, hak, hkb, hk⟩
    exact (hmmin k (by simpa [S] using And.intro hak hkb)).trans_lt hk
  have hm_lt_b : κ (m : ZMod n) < κ (b : ZMod n) := by
    rcases hlowerB with ⟨k, hak, hkb, hk⟩
    exact (hmmin k (by simpa [S] using And.intro hak hkb)).trans_lt hk
  have ham : a < m := lt_of_le_of_ne hm_bounds.1 (fun hma => by
    subst m
    exact (lt_irrefl _) hm_lt_a)
  have hmb : m < b := lt_of_le_of_ne hm_bounds.2 (fun hmb' => by
    subst b
    exact (lt_irrefl _) hm_lt_b)
  let R : ZMod n → Prop := fun z =>
    ∃ k : ℕ, k ∈ S ∧ (k : ZMod n) = z ∧
      κ (k : ZMod n) = κ (m : ZMod n)
  have hRm : R (m : ZMod n) := ⟨m, hmS, rfl, rfl⟩
  have hRinterior : ∀ z, R z → ∀ k : ℕ, k ∈ S → (k : ZMod n) = z →
      κ (k : ZMod n) = κ (m : ZMod n) → a < k ∧ k < b := by
    intro z _hz k hkS _hkz hkval
    have hk_bounds : a ≤ k ∧ k ≤ b := by simpa [S] using hkS
    constructor
    · exact lt_of_le_of_ne hk_bounds.1 (fun hka => by
        subst k
        rw [hkval] at hm_lt_a
        exact (lt_irrefl _) hm_lt_a)
    · exact lt_of_le_of_ne hk_bounds.2 (fun hkb' => by
        subst b
        rw [hkval] at hm_lt_b
        exact (lt_irrefl _) hm_lt_b)
  have hweak : ∀ z, R z →
      -κ (z - 1) ≤ -κ z ∧ -κ (z + 1) ≤ -κ z := by
    intro z hz
    rcases hz with ⟨k, hkS, hkz, hkval⟩
    have hinterior := hRinterior z ⟨k, hkS, hkz, hkval⟩ k hkS hkz hkval
    subst z
    constructor
    · apply neg_le_neg
      have hk1S : k - 1 ∈ S := by
        simp only [S, Finset.mem_Icc]
        omega
      have hmin := hmmin (k - 1) hk1S
      rw [hkval]
      convert hmin using 1
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    · apply neg_le_neg
      have hk1S : k + 1 ∈ S := by
        simp only [S, Finset.mem_Icc]
        omega
      have hmin := hmmin (k + 1) hk1S
      rw [hkval]
      simpa [Nat.cast_add] using hmin
  have hpropRight : ∀ z, R z → -κ z = -κ (z + 1) → R (z + 1) := by
    intro z hz heq
    rcases hz with ⟨k, hkS, hkz, hkval⟩
    have hinterior := hRinterior z ⟨k, hkS, hkz, hkval⟩ k hkS hkz hkval
    subst z
    have hk1S : k + 1 ∈ S := by
      simp only [S, Finset.mem_Icc]
      omega
    refine ⟨k + 1, hk1S, by simp [Nat.cast_add], ?_⟩
    have hκ := neg_inj.mp heq
    calc
      κ ((k + 1 : ℕ) : ZMod n) = κ ((k : ZMod n) + 1) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = κ (k : ZMod n) := hκ.symm
      _ = κ (m : ZMod n) := hkval
  have hpropLeft : ∀ z, R z → -κ z = -κ (z - 1) → R (z - 1) := by
    intro z hz heq
    rcases hz with ⟨k, hkS, hkz, hkval⟩
    have hinterior := hRinterior z ⟨k, hkS, hkz, hkval⟩ k hkS hkz hkval
    subst z
    have hk1S : k - 1 ∈ S := by
      simp only [S, Finset.mem_Icc]
      omega
    refine ⟨k - 1, hk1S, ?_, ?_⟩
    · rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    · have hκ := neg_inj.mp heq
      calc
        κ ((k - 1 : ℕ) : ZMod n) = κ ((k : ZMod n) - 1) := by
          rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        _ = κ (k : ZMod n) := hκ.symm
        _ = κ (m : ZMod n) := hkval
  have hncNeg : ¬ ∃ c, ∀ z : ZMod n, -κ z = c := by
    rintro ⟨c, hc⟩
    apply hnc
    refine ⟨-c, fun z => ?_⟩
    have hz := congrArg Neg.neg (hc z)
    simpa using hz
  have hmaxNeg : DiscreteLocalMax (fun z => -κ z) (m : ZMod n) :=
    discreteLocalMax_of_weak_neighbors_of_eq_propagates
      hRm hweak hpropRight hpropLeft hncNeg
  exact ⟨m, ham, hmb, discreteLocalMin_of_neg_localMax hmaxNeg⟩

/-- Two disjoint marked weak-maximum plateaux force two alternating minimum
plateaux, hence Dahlberg's four-vertex conclusion.  The first marked plateau
is normalized to index `0`; the second is represented by `d ∈ (0,n)`. -/
theorem dahlbergFourVertex_of_two_disjoint_marked_weakMaxima_zero
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    {P Q : ZMod n → Prop} {d : ℕ}
    (hdpos : 0 < d) (hdlt : d < n)
    (hP0 : P 0) (hQd : Q (d : ZMod n))
    (hdisjoint : ∀ z, ¬ (P z ∧ Q z))
    (hweakP : ∀ z, P z → κ (z - 1) ≤ κ z ∧ κ (z + 1) ≤ κ z)
    (hpropPRight : ∀ z, P z → κ z = κ (z + 1) → P (z + 1))
    (hpropPLeft : ∀ z, P z → κ z = κ (z - 1) → P (z - 1))
    (hweakQ : ∀ z, Q z → κ (z - 1) ≤ κ z ∧ κ (z + 1) ≤ κ z)
    (hpropQRight : ∀ z, Q z → κ z = κ (z + 1) → Q (z + 1))
    (hpropQLeft : ∀ z, Q z → κ z = κ (z - 1) → Q (z - 1))
    (hnc : ¬ ∃ c, ∀ z : ZMod n, κ z = c) :
    DahlbergFourVertex κ := by
  have hnotPd : ¬ P (d : ZMod n) := fun hPd => hdisjoint _ ⟨hPd, hQd⟩
  have hnotQ0 : ¬ Q 0 := fun hQ0 => hdisjoint 0 ⟨hP0, hQ0⟩
  have hPnat0 : P ((0 : ℕ) : ZMod n) := by simpa using hP0
  have hnotQnat0 : ¬ Q ((0 : ℕ) : ZMod n) := by simpa using hnotQ0
  have hmax0 : DiscreteLocalMax κ 0 :=
    discreteLocalMax_of_weak_neighbors_of_eq_propagates
      hP0 hweakP hpropPRight hpropPLeft hnc
  have hmaxd : DiscreteLocalMax κ (d : ZMod n) :=
    discreteLocalMax_of_weak_neighbors_of_eq_propagates
      hQd hweakQ hpropQRight hpropQLeft hnc
  have hlow0_arc1 : ∃ k : ℕ, 0 ≤ k ∧ k ≤ d ∧
      κ (k : ZMod n) < κ 0 := by
    rcases exists_strict_drop_forward_of_marked_weakMax
        hdpos hPnat0 hnotPd (fun z hz => (hweakP z hz).2) hpropPRight with
      ⟨k, hk0, hkd, hk⟩
    exact ⟨k, hk0.le, hkd, by simpa using hk⟩
  have hlowd_arc1 : ∃ k : ℕ, 0 ≤ k ∧ k ≤ d ∧
      κ (k : ZMod n) < κ (d : ZMod n) := by
    rcases exists_strict_drop_backward_of_marked_weakMax
        hdpos hQd hnotQnat0 (fun z hz => (hweakQ z hz).1) hpropQLeft with
      ⟨k, hk0, hkd, hk⟩
    exact ⟨k, hk0, hkd.le, hk⟩
  rcases exists_discreteLocalMin_between_of_strictly_below_endpoints
      hdpos (by simpa using hlow0_arc1) hlowd_arc1 hnc with
    ⟨m₁, hm₁0, hm₁d, hmin₁⟩
  have hPn : P (n : ZMod n) := by
    simpa using hP0
  have hnotQn : ¬ Q (n : ZMod n) := by
    simpa using hnotQ0
  have hlowd_arc2 : ∃ k : ℕ, d ≤ k ∧ k ≤ n ∧
      κ (k : ZMod n) < κ (d : ZMod n) := by
    rcases exists_strict_drop_forward_of_marked_weakMax
        hdlt hQd hnotQn (fun z hz => (hweakQ z hz).2) hpropQRight with
      ⟨k, hdk, hkn, hk⟩
    exact ⟨k, hdk.le, hkn, hk⟩
  have hlow0_arc2 : ∃ k : ℕ, d ≤ k ∧ k ≤ n ∧
      κ (k : ZMod n) < κ (n : ZMod n) := by
    rcases exists_strict_drop_backward_of_marked_weakMax
        hdlt hPn hnotPd (fun z hz => (hweakP z hz).1) hpropPLeft with
      ⟨k, hdk, hkn, hk⟩
    exact ⟨k, hdk, hkn.le, hk⟩
  rcases exists_discreteLocalMin_between_of_strictly_below_endpoints
      hdlt hlowd_arc2 hlow0_arc2 hnc with ⟨m₂, hdm₂, hm₂n, hmin₂⟩
  exact ⟨0, m₁, d, m₂, hm₁0, hm₁d, hdm₂, by omega,
    by simpa using hmax0, hmin₁, hmaxd, hmin₂⟩

/-- Two disjoint marked weak-maximum plateaux force Dahlberg's four-vertex
conclusion, without choosing a natural representative or cyclic origin. -/
theorem dahlbergFourVertex_of_two_disjoint_marked_weakMaxima
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    {P Q : ZMod n → Prop} {p q : ZMod n}
    (hpq : p ≠ q) (hPp : P p) (hQq : Q q)
    (hdisjoint : ∀ z, ¬ (P z ∧ Q z))
    (hweakP : ∀ z, P z → κ (z - 1) ≤ κ z ∧ κ (z + 1) ≤ κ z)
    (hpropPRight : ∀ z, P z → κ z = κ (z + 1) → P (z + 1))
    (hpropPLeft : ∀ z, P z → κ z = κ (z - 1) → P (z - 1))
    (hweakQ : ∀ z, Q z → κ (z - 1) ≤ κ z ∧ κ (z + 1) ≤ κ z)
    (hpropQRight : ∀ z, Q z → κ z = κ (z + 1) → Q (z + 1))
    (hpropQLeft : ∀ z, Q z → κ z = κ (z - 1) → Q (z - 1))
    (hnc : ¬ ∃ c, ∀ z : ZMod n, κ z = c) :
    DahlbergFourVertex κ := by
  let d : ℕ := (q - p).val
  let κ' : ZMod n → ℝ := fun z => κ (z + p)
  let P' : ZMod n → Prop := fun z => P (z + p)
  let Q' : ZMod n → Prop := fun z => Q (z + p)
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd0
    have hqp0 : q - p = 0 := (ZMod.val_eq_zero (q - p)).mp hd0
    apply hpq
    have := congrArg (fun z : ZMod n => z + p) hqp0
    simpa using this.symm
  have hdlt : d < n := ZMod.val_lt (q - p)
  have hdcast : (d : ZMod n) = q - p := by
    exact ZMod.natCast_zmod_val (q - p)
  have hP'0 : P' 0 := by simpa [P'] using hPp
  have hQ'd : Q' (d : ZMod n) := by
    dsimp [Q']
    rw [hdcast]
    convert hQq using 1
    abel
  have hdisjoint' : ∀ z, ¬ (P' z ∧ Q' z) := by
    intro z hz
    exact hdisjoint (z + p) hz
  have hweakP' : ∀ z, P' z →
      κ' (z - 1) ≤ κ' z ∧ κ' (z + 1) ≤ κ' z := by
    intro z hz
    rcases hweakP (z + p) hz with ⟨hl, hr⟩
    constructor
    · dsimp [κ']
      convert hl using 1
      abel_nf
    · dsimp [κ']
      convert hr using 1
      abel_nf
  have hpropP'Right : ∀ z, P' z →
      κ' z = κ' (z + 1) → P' (z + 1) := by
    intro z hz heq
    dsimp [P', κ'] at hz heq ⊢
    have hp := hpropPRight (z + p) hz (by
      convert heq using 1
      abel_nf)
    convert hp using 1
    abel
  have hpropP'Left : ∀ z, P' z →
      κ' z = κ' (z - 1) → P' (z - 1) := by
    intro z hz heq
    dsimp [P', κ'] at hz heq ⊢
    have hp := hpropPLeft (z + p) hz (by
      convert heq using 1
      abel_nf)
    convert hp using 1
    abel
  have hweakQ' : ∀ z, Q' z →
      κ' (z - 1) ≤ κ' z ∧ κ' (z + 1) ≤ κ' z := by
    intro z hz
    rcases hweakQ (z + p) hz with ⟨hl, hr⟩
    constructor
    · dsimp [κ']
      convert hl using 1
      abel_nf
    · dsimp [κ']
      convert hr using 1
      abel_nf
  have hpropQ'Right : ∀ z, Q' z →
      κ' z = κ' (z + 1) → Q' (z + 1) := by
    intro z hz heq
    dsimp [Q', κ'] at hz heq ⊢
    have hq := hpropQRight (z + p) hz (by
      convert heq using 1
      abel_nf)
    convert hq using 1
    abel
  have hpropQ'Left : ∀ z, Q' z →
      κ' z = κ' (z - 1) → Q' (z - 1) := by
    intro z hz heq
    dsimp [Q', κ'] at hz heq ⊢
    have hq := hpropQLeft (z + p) hz (by
      convert heq using 1
      abel_nf)
    convert hq using 1
    abel
  have hnc' : ¬ ∃ c, ∀ z : ZMod n, κ' z = c := by
    rintro ⟨c, hc⟩
    apply hnc
    refine ⟨c, fun z => ?_⟩
    have hz := hc (z - p)
    dsimp [κ'] at hz
    convert hz using 1
    abel_nf
  have hfv' : DahlbergFourVertex κ' :=
    dahlbergFourVertex_of_two_disjoint_marked_weakMaxima_zero
      hdpos hdlt hP'0 hQ'd hdisjoint' hweakP'
      hpropP'Right hpropP'Left hweakQ' hpropQ'Right hpropQ'Left hnc'
  exact (dahlbergFourVertex_translateIndex_iff (κ := κ) (a := p)).mp hfv'

/-- A nonconstant cyclic real profile has a plateau-aware local maximum. -/
theorem exists_discreteLocalMax_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i : ZMod n, DiscreteLocalMax κ i := by
  obtain ⟨i, hmax⟩ := exists_globalMax_zmod κ
  exact ⟨i, discreteLocalMax_of_globalMax_of_not_constant hmax hnc⟩

/-- If every adjacent cyclic value agrees, then the cyclic profile is
constant. -/
theorem exists_constant_of_forall_eq_succ {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hstep : ∀ i : ZMod n, κ i = κ (i + 1)) :
    ∃ c, ∀ i : ZMod n, κ i = c := by
  refine ⟨κ 0, fun i => ?_⟩
  have hnat : ∀ k : ℕ, κ (k : ZMod n) = κ 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hstep (k : ZMod n)
        have hcast : ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 := by norm_num
        rw [hcast]
        exact hs.symm.trans ih
  simpa [ZMod.natCast_rightInverse i] using hnat i.val

/-- A nonconstant cyclic profile has at least one adjacent change. -/
theorem exists_ne_succ_of_not_constant {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i : ZMod n, κ i ≠ κ (i + 1) := by
  by_contra hnone
  apply hnc
  apply exists_constant_of_forall_eq_succ
  intro i
  by_contra hne
  exact hnone ⟨i, hne⟩

/-- Negating a cyclic profile preserves nonconstancy. -/
theorem not_constant_neg_iff {n : ℕ} {κ : ZMod n → ℝ} :
    (¬ ∃ c, ∀ i : ZMod n, -κ i = c) ↔ ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro hneg hconst
    rcases hconst with ⟨c, hc⟩
    exact hneg ⟨-c, fun i => by simp [hc i]⟩
  · intro h hnegconst
    rcases hnegconst with ⟨c, hc⟩
    exact h ⟨-c, fun i => by
      have hi := congrArg Neg.neg (hc i)
      simpa using hi⟩

/-- A nonconstant cyclic real profile has a plateau-aware local minimum. -/
theorem exists_discreteLocalMin_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i : ZMod n, DiscreteLocalMin κ i := by
  have hneg : ¬ ∃ c, ∀ i : ZMod n, -κ i = c :=
    not_constant_neg_iff.mpr hnc
  rcases exists_discreteLocalMax_of_not_constant hneg with ⟨i, hmax⟩
  exact ⟨i, discreteLocalMin_of_neg_localMax hmax⟩

/-- A chosen global minimum of a nonconstant cyclic real profile is a
plateau-aware local minimum. -/
theorem discreteLocalMin_of_globalMin_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} {i : ZMod n} (hmin : ∀ j : ZMod n, κ i ≤ κ j)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    DiscreteLocalMin κ i := by
  have hneg : ¬ ∃ c, ∀ i : ZMod n, -κ i = c :=
    not_constant_neg_iff.mpr hnc
  have hmax_neg : ∀ j : ZMod n, -κ j ≤ -κ i := by
    intro j
    exact neg_le_neg (hmin j)
  exact discreteLocalMin_of_neg_localMax
    (discreteLocalMax_of_globalMax_of_not_constant hmax_neg hneg)

/-- A nonconstant cyclic real profile has global minimum and maximum witnesses
which are also plateau-aware local extrema at the same indices. -/
theorem exists_globalMinMax_localExtrema_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, κ i₀ ≤ κ j) ∧
      (∀ j : ZMod n, κ j ≤ κ i₁) ∧
      κ i₀ < κ i₁ ∧
      DiscreteLocalMin κ i₀ ∧
      DiscreteLocalMax κ i₁ := by
  rcases exists_globalMinMax_strict_of_not_constant hnc with
    ⟨i₀, i₁, hmin, hmax, hlt⟩
  exact ⟨i₀, i₁, hmin, hmax, hlt,
    discreteLocalMin_of_globalMin_of_not_constant hmin hnc,
    discreteLocalMax_of_globalMax_of_not_constant hmax hnc⟩

/-- A nonconstant cyclic real profile has both a plateau-aware local maximum
and a plateau-aware local minimum. -/
theorem exists_discreteLocalMax_and_min_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    (∃ imax : ZMod n, DiscreteLocalMax κ imax) ∧
      ∃ imin : ZMod n, DiscreteLocalMin κ imin := by
  exact ⟨exists_discreteLocalMax_of_not_constant hnc,
    exists_discreteLocalMin_of_not_constant hnc⟩

/-- Positive affine changes preserve nonconstancy of cyclic profiles. -/
theorem not_constant_posAffine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : 0 < a) :
    (¬ ∃ c, ∀ i : ZMod n, a * κ i + b = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro hscaled hconst
    rcases hconst with ⟨c, hc⟩
    exact hscaled ⟨a * c + b, fun i => by simp [hc i]⟩
  · intro h hscaledconst
    rcases hscaledconst with ⟨c, hc⟩
    apply h
    refine ⟨(c - b) / a, fun i => ?_⟩
    have hi := hc i
    field_simp [ha.ne'] at hi ⊢
    linarith

/-- Nonzero affine changes preserve nonconstancy of cyclic profiles. -/
theorem not_constant_affine_iff {n : ℕ} {κ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    (¬ ∃ c, ∀ i : ZMod n, a * κ i + b = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro hscaled hconst
    rcases hconst with ⟨c, hc⟩
    exact hscaled ⟨a * c + b, fun i => by simp [hc i]⟩
  · intro h hscaledconst
    rcases hscaledconst with ⟨c, hc⟩
    apply h
    refine ⟨(c - b) / a, fun i => ?_⟩
    have hi := hc i
    field_simp [ha] at hi ⊢
    linarith

/-- Pointwise equality to a nonzero affine change preserves nonconstancy. -/
theorem not_constant_of_eq_affine_iff {n : ℕ} {κ μ : ZMod n → ℝ} {a b : ℝ}
    (ha : a ≠ 0) (hμ : ∀ i : ZMod n, μ i = a * κ i + b) :
    (¬ ∃ c, ∀ i : ZMod n, μ i = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro hμnc hconst
    rcases hconst with ⟨c, hc⟩
    exact hμnc ⟨a * c + b, fun i => by rw [hμ i, hc i]⟩
  · intro hκnc hμconst
    rcases hμconst with ⟨c, hc⟩
    have hscaled_const :
        ∃ c, ∀ i : ZMod n, a * κ i + b = c :=
      ⟨c, fun i => by rw [← hμ i, hc i]⟩
    exact ((not_constant_affine_iff (κ := κ) (a := a) (b := b) ha).mpr
      hκnc) hscaled_const

/-- Pointwise equal cyclic profiles have the same nonconstancy condition. -/
theorem not_constant_congr_iff {n : ℕ} {κ μ : ZMod n → ℝ}
    (hμ : ∀ i : ZMod n, μ i = κ i) :
    (¬ ∃ c, ∀ i : ZMod n, μ i = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  exact not_constant_of_eq_affine_iff (a := 1) (b := 0) (by norm_num)
    (by intro i; simp [hμ i])

/-- Translating cyclic indices preserves nonconstancy. -/
theorem not_constant_translateIndex_iff {n : ℕ} {κ : ZMod n → ℝ} {a : ZMod n} :
    (¬ ∃ c, ∀ i : ZMod n, κ (i + a) = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro htrans hconst
    rcases hconst with ⟨c, hc⟩
    exact htrans ⟨c, fun i => hc (i + a)⟩
  · intro h htransconst
    rcases htransconst with ⟨c, hc⟩
    apply h
    refine ⟨c, fun i => ?_⟩
    have hi := hc (i - a)
    convert hi using 1
    abel_nf

/-- Reversing cyclic indices preserves nonconstancy. -/
theorem not_constant_negIndex_iff {n : ℕ} {κ : ZMod n → ℝ} :
    (¬ ∃ c, ∀ i : ZMod n, κ (-i) = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro hrev hconst
    rcases hconst with ⟨c, hc⟩
    exact hrev ⟨c, fun i => hc (-i)⟩
  · intro h hrevconst
    rcases hrevconst with ⟨c, hc⟩
    apply h
    refine ⟨c, fun i => ?_⟩
    have hi := hc (-i)
    simpa using hi

/-- Negating and reversing cyclic indices preserves nonconstancy. -/
theorem not_constant_neg_reflectIndex_iff {n : ℕ} {κ : ZMod n → ℝ} :
    (¬ ∃ c, ∀ i : ZMod n, -κ (-i) = c) ↔
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  constructor
  · intro href hconst
    rcases hconst with ⟨c, hc⟩
    exact href ⟨-c, fun i => by simp [hc (-i)]⟩
  · intro h hrefconst
    rcases hrefconst with ⟨c, hc⟩
    exact h ⟨-c, fun i => by
      have hi := congrArg Neg.neg (hc (-i))
      simpa using hi⟩

/-- If a cyclic real profile is weakly increasing at every adjacent step, then
it is constant. -/
theorem exists_constant_of_forall_le_succ {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hstep : ∀ i : ZMod n, κ i ≤ κ (i + 1)) :
    ∃ c, ∀ i : ZMod n, κ i = c := by
  obtain ⟨imax, hmax⟩ := exists_globalMax_zmod κ
  refine ⟨κ imax, fun i => ?_⟩
  have hnat : ∀ k : ℕ, κ (imax + (k : ZMod n)) = κ imax := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hle_step : κ (imax + (k : ZMod n)) ≤ κ (imax + (k : ZMod n) + 1) :=
          hstep (imax + (k : ZMod n))
        have hle_max : κ (imax + ((k + 1 : ℕ) : ZMod n)) ≤ κ imax :=
          hmax (imax + ((k + 1 : ℕ) : ZMod n))
        apply le_antisymm hle_max
        have hle_step' : κ imax ≤ κ (imax + (k : ZMod n) + 1) := by
          simpa [ih] using hle_step
        simpa [Nat.cast_add, add_assoc] using hle_step'
  let k : ℕ := (i - imax).val
  have hk := hnat k
  have hidx : imax + (k : ZMod n) = i := by
    dsimp [k]
    rw [ZMod.natCast_rightInverse (i - imax)]
    abel
  simpa [hidx] using hk

/-- If a cyclic real profile is weakly decreasing at every adjacent step, then
it is constant. -/
theorem exists_constant_of_forall_succ_le {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hstep : ∀ i : ZMod n, κ (i + 1) ≤ κ i) :
    ∃ c, ∀ i : ZMod n, κ i = c := by
  obtain ⟨imin, hmin⟩ := exists_globalMin_zmod κ
  refine ⟨κ imin, fun i => ?_⟩
  have hnat : ∀ k : ℕ, κ (imin + (k : ZMod n)) = κ imin := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hle_step : κ (imin + (k : ZMod n) + 1) ≤ κ (imin + (k : ZMod n)) :=
          hstep (imin + (k : ZMod n))
        have hle_min : κ imin ≤ κ (imin + ((k + 1 : ℕ) : ZMod n)) :=
          hmin (imin + ((k + 1 : ℕ) : ZMod n))
        apply le_antisymm
        · simpa [Nat.cast_add, add_assoc] using hle_step.trans (le_of_eq ih)
        · exact hle_min
  let k : ℕ := (i - imin).val
  have hk := hnat k
  have hidx : imin + (k : ZMod n) = i := by
    dsimp [k]
    rw [ZMod.natCast_rightInverse (i - imin)]
    abel
  simpa [hidx] using hk

/-- A cyclic real profile where every value lies between its two neighbours
must have at least one adjacent equality.  Equivalently, a closed cyclic
sequence with no adjacent plateau cannot be locally between-neighbour
monotone everywhere. -/
theorem exists_eq_succ_of_forall_mem_uIcc_neighbors {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ}
    (hbetween : ∀ i : ZMod n, κ i ∈ Set.uIcc (κ (i - 1)) (κ (i + 1))) :
    ∃ i : ZMod n, κ i = κ (i + 1) := by
  by_contra hnone
  have hne : ∀ i : ZMod n, κ i ≠ κ (i + 1) := by
    intro i hi
    exact hnone ⟨i, hi⟩
  rcases lt_or_gt_of_ne (hne 0) with hinc0 | hdec0
  · have hinc_nat : ∀ k : ℕ, κ (k : ZMod n) < κ ((k : ZMod n) + 1) := by
      intro k
      induction k with
      | zero =>
          simpa using hinc0
      | succ k ih =>
          have hb := hbetween ((k : ZMod n) + 1)
          rw [Set.mem_uIcc] at hb
          rcases hb with h | h
          · have hright :
                κ ((k + 1 : ℕ) : ZMod n) ≤ κ (((k + 1 : ℕ) : ZMod n) + 1) := by
              simpa [Nat.cast_add, add_assoc] using h.2
            exact lt_of_le_of_ne hright (hne (((k + 1 : ℕ) : ZMod n)))
          · have hleft : κ ((k : ZMod n) + 1) ≤ κ (k : ZMod n) := by
              simpa [sub_eq_add_neg, add_assoc] using h.2
            exact False.elim ((not_lt_of_ge hleft) ih)
    have hle : ∀ i : ZMod n, κ i ≤ κ (i + 1) := by
      intro i
      have hi := hinc_nat i.val
      simpa [ZMod.natCast_rightInverse i] using hi.le
    rcases exists_constant_of_forall_le_succ hle with ⟨c, hc⟩
    exact hne 0 (by rw [hc 0, hc (0 + 1)])
  · have hdec_nat : ∀ k : ℕ, κ ((k : ZMod n) + 1) < κ (k : ZMod n) := by
      intro k
      induction k with
      | zero =>
          simpa using hdec0
      | succ k ih =>
          have hb := hbetween ((k : ZMod n) + 1)
          rw [Set.mem_uIcc] at hb
          rcases hb with h | h
          · have hleft : κ (k : ZMod n) ≤ κ ((k : ZMod n) + 1) := by
              simpa [sub_eq_add_neg, add_assoc] using h.1
            exact False.elim ((not_lt_of_ge hleft) ih)
          · have hright :
                κ (((k + 1 : ℕ) : ZMod n) + 1) ≤ κ ((k + 1 : ℕ) : ZMod n) := by
              simpa [Nat.cast_add, add_assoc] using h.1
            exact lt_of_le_of_ne hright (hne (((k + 1 : ℕ) : ZMod n))).symm
    have hle : ∀ i : ZMod n, κ (i + 1) ≤ κ i := by
      intro i
      have hi := hdec_nat i.val
      simpa [ZMod.natCast_rightInverse i] using hi.le
    rcases exists_constant_of_forall_succ_le hle with ⟨c, hc⟩
    exact hne 0 (by rw [hc 0, hc (0 + 1)])

/-- If a cyclic real profile has no adjacent plateau, then it has a strict
one-step peak or a strict one-step valley.  This is the first finite cyclic
combinatorial ingredient in Dahlberg's “too few extrema imply monotone arcs”
argument. -/
theorem exists_strict_neighbor_extremum_of_forall_ne_succ {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hne : ∀ i : ZMod n, κ i ≠ κ (i + 1)) :
    ∃ i : ZMod n,
      (κ (i - 1) < κ i ∧ κ (i + 1) < κ i) ∨
        (κ i < κ (i - 1) ∧ κ i < κ (i + 1)) := by
  by_contra hnone
  have hbetween : ∀ i : ZMod n, κ i ∈ Set.uIcc (κ (i - 1)) (κ (i + 1)) := by
    intro i
    rw [Set.mem_uIcc]
    by_cases hleft : κ (i - 1) < κ i
    · by_cases hright : κ (i + 1) < κ i
      · exact False.elim (hnone ⟨i, Or.inl ⟨hleft, hright⟩⟩)
      · have hiright : κ i < κ (i + 1) := by
          exact lt_of_le_of_ne (le_of_not_gt hright) (hne i)
        exact Or.inl ⟨hleft.le, hiright.le⟩
    · have hileft : κ i < κ (i - 1) := by
        have hne_left : κ (i - 1) ≠ κ i := by
          simpa [sub_eq_add_neg, add_assoc] using hne (i - 1)
        exact lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hne_left)
      by_cases hright : κ i < κ (i + 1)
      · exact False.elim (hnone ⟨i, Or.inr ⟨hileft, hright⟩⟩)
      · exact Or.inr ⟨le_of_not_gt hright, hileft.le⟩
  rcases exists_eq_succ_of_forall_mem_uIcc_neighbors hbetween with ⟨i, hi⟩
  exact hne i hi

/-- If a cyclic real profile has no adjacent plateau, then a global maximum
is a strict one-step peak and a global minimum is a strict one-step valley. -/
theorem exists_strict_neighbor_peak_and_valley_of_forall_ne_succ {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hne : ∀ i : ZMod n, κ i ≠ κ (i + 1)) :
    ∃ imax imin : ZMod n,
      (κ (imax - 1) < κ imax ∧ κ (imax + 1) < κ imax) ∧
        (κ imin < κ (imin - 1) ∧ κ imin < κ (imin + 1)) := by
  obtain ⟨imax, hmax⟩ := exists_globalMax_zmod κ
  obtain ⟨imin, hmin⟩ := exists_globalMin_zmod κ
  have hmax_left_ne : κ (imax - 1) ≠ κ imax := by
    simpa [sub_eq_add_neg, add_assoc] using hne (imax - 1)
  have hmax_right_ne : κ (imax + 1) ≠ κ imax := Ne.symm (hne imax)
  have hmin_left_ne : κ imin ≠ κ (imin - 1) := by
    have h : κ (imin - 1) ≠ κ imin := by
      simpa [sub_eq_add_neg, add_assoc] using hne (imin - 1)
    exact Ne.symm h
  refine ⟨imax, imin, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_ne (hmax (imax - 1)) hmax_left_ne
  · exact lt_of_le_of_ne (hmax (imax + 1)) hmax_right_ne
  · exact lt_of_le_of_ne (hmin (imin - 1)) hmin_left_ne
  · exact lt_of_le_of_ne (hmin (imin + 1)) (hne imin)

/-- A cyclic real profile with no adjacent plateau has a plateau-aware local
maximum or local minimum. -/
theorem exists_discreteLocalExtremum_of_forall_ne_succ {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) {κ : ZMod n → ℝ} (hne : ∀ i : ZMod n, κ i ≠ κ (i + 1)) :
    ∃ i : ZMod n, DiscreteLocalMax κ i ∨ DiscreteLocalMin κ i := by
  rcases exists_strict_neighbor_extremum_of_forall_ne_succ (κ := κ) hne with
    ⟨i, hpeak | hvalley⟩
  · exact ⟨i, Or.inl (discreteLocalMax_of_neighbors hn hpeak.1 hpeak.2)⟩
  · exact ⟨i, Or.inr (discreteLocalMin_of_neighbors hn hvalley.1 hvalley.2)⟩

/-- A cyclic real profile with no adjacent plateau has both a plateau-aware
local maximum and a plateau-aware local minimum. -/
theorem exists_discreteLocalMax_and_min_of_forall_ne_succ {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) {κ : ZMod n → ℝ} (hne : ∀ i : ZMod n, κ i ≠ κ (i + 1)) :
    (∃ imax : ZMod n, DiscreteLocalMax κ imax) ∧
      ∃ imin : ZMod n, DiscreteLocalMin κ imin := by
  rcases exists_strict_neighbor_peak_and_valley_of_forall_ne_succ (κ := κ) hne with
    ⟨imax, imin, hpeak, hvalley⟩
  exact ⟨⟨imax, discreteLocalMax_of_neighbors hn hpeak.1 hpeak.2⟩,
    ⟨imin, discreteLocalMin_of_neighbors hn hvalley.1 hvalley.2⟩⟩

/-- A nonconstant cyclic profile has at least one strict adjacent increase. -/
theorem exists_adjacent_lt_succ_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i : ZMod n, κ i < κ (i + 1) := by
  by_contra hnone
  apply hnc
  apply exists_constant_of_forall_succ_le
  intro i
  exact le_of_not_gt (fun hlt => hnone ⟨i, hlt⟩)

/-- A nonconstant cyclic profile has at least one strict adjacent decrease. -/
theorem exists_adjacent_succ_lt_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i : ZMod n, κ (i + 1) < κ i := by
  by_contra hnone
  apply hnc
  apply exists_constant_of_forall_le_succ
  intro i
  exact le_of_not_gt (fun hlt => hnone ⟨i, hlt⟩)

/-- A nonconstant cyclic profile has both a strict adjacent increase and a
strict adjacent decrease. -/
theorem exists_adjacent_increase_and_decrease_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    (∃ i : ZMod n, κ i < κ (i + 1)) ∧
      ∃ i : ZMod n, κ (i + 1) < κ i := by
  exact ⟨exists_adjacent_lt_succ_of_not_constant hnc,
    exists_adjacent_succ_lt_of_not_constant hnc⟩

/-- A nonconstant cyclic profile has an adjacent strict increase or strict
decrease. -/
theorem exists_adjacent_lt_or_gt_of_not_constant {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} (hnc : ¬ ∃ c, ∀ i : ZMod n, κ i = c) :
    ∃ i : ZMod n, κ i < κ (i + 1) ∨ κ (i + 1) < κ i := by
  obtain ⟨i, hi⟩ := exists_ne_succ_of_not_constant hnc
  rcases lt_trichotomy (κ i) (κ (i + 1)) with hlt | heq | hgt
  · exact ⟨i, Or.inl hlt⟩
  · exact False.elim (hi heq)
  · exact ⟨i, Or.inr hgt⟩

/-- A Euclidean circle with centre `O` and positive radius `R` through a triple. -/
def CircumcircleR2 (A B C O : ℂ) (R : ℝ) : Prop :=
  0 < R ∧ dist O A = R ∧ dist O B = R ∧ dist O C = R

/-- A positive circumcircle is equivalently a bundled Euclidean sphere containing
the three points. The positive-radius condition remains explicit. -/
theorem circumcircleR2_iff_pos_and_mem_sphere (A B C O : ℂ) (R : ℝ) :
    CircumcircleR2 A B C O R ↔
      0 < R ∧ A ∈ (⟨O, R⟩ : EuclideanGeometry.Sphere ℂ) ∧
        B ∈ (⟨O, R⟩ : EuclideanGeometry.Sphere ℂ) ∧
          C ∈ (⟨O, R⟩ : EuclideanGeometry.Sphere ℂ) := by
  simp only [CircumcircleR2, EuclideanGeometry.mem_sphere']

/-- The closed convex vertex cone at `B`, spanned by the rays toward `A` and
`C`.  Dahlberg's regularity asks that the circumcenter lie in this cone. -/
def InVertexCone (A B C O : ℂ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
    O - B = (a : ℂ) * (A - B) + (b : ℂ) * (C - B)

end Gluck.Forward
