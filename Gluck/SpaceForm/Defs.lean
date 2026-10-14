/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Curvature
import Gluck.Curve
import Gluck.Euclidean.FourVertex
import Gluck.Euclidean.Reduction
import Gluck.Euclidean.Simplicity
import Gluck.Euclidean.StepReduction
import Gluck.Winding
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The space-form converse (constant-curvature model, definition layer)

This file generalizes the spherical development `Gluck/Sphere/*.lean` over the
**ambient curvature** `K ∈ {+1, −1, 0}` (the constant sectional curvature of
the space form). The sphere `S²` (round metric `4/(1+|z|²)²`) is `K = +1`; the
hyperbolic plane `H²` (Poincaré metric `4/(1−|z|²)²`) is `K = −1`. Both live in
the open unit disk `{|z| < 1} ⊆ ℂ` in the tangent-angle gauge.

The single unifying object is the **space-form gauge speed**
`spaceFormSpeed K κ θ z = (1 + K‖z‖²) / (2(κ(θ) − K⟪z, i·e^{iθ}⟫_ℝ))`,
the algebraic solution of the conformal geodesic-curvature relation for the
speed `‖z'‖` in the gauge `φ(θ) = θ`. At `K = +1` it is the existing
`Gluck.sphericalSpeed`; at `K = −1`, `spaceFormSpeed (−1)` is the
corresponding hyperbolic speed, without a separate model-specific definition.
Both the metric factor `1 + K‖z‖²` and the inner-product term `−K⟪·⟫` flip with
`K`; the two sign flips are a single parameter (the linchpin verified in the
model-circle lemma `spaceFormSpeed_circle`).

Almost every downstream fact is `K`-uniform: denominator positivity holds for
any `|K| ≤ 1` under `‖z‖ ≤ R < κ`; the model geodesic circle carries constant
`κ = (1 − Kr²)/(2r)` with gauge speed exactly `r`; the confinement radius is
the appropriate root of `Kr² + 2cr − 1 = 0`. The sign of `K` enters only where
the admissibility lower bound is *established* per model (S²: compactness of a
strictly positive `κ`; H²: the escape-velocity bound `κ > 1`).

-/

namespace Gluck.SpaceForm

open scoped Real InnerProductSpace NNReal

/-- The normal-term coordinate identity: for `z ∈ ℂ` and `φ ∈ ℝ`,
`⟪z, i·e^{iφ}⟫_ℝ = -(Re z)·sin φ + (Im z)·cos φ`. Model-independent
(no `K`). -/
lemma spaceFormNormal_inner_eq (z : ℂ) (φ : ℝ) :
    ⟪z, Complex.I * Complex.exp ((φ : ℂ) * Complex.I)⟫_ℝ
      = -z.re * Real.sin φ + z.im * Real.cos φ := by
  rw [Complex.inner]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  ring

/-- A curve `γ : ℝ → ℂ` *realizes the space-form curvature function* `κ` at
ambient curvature `K` when it is `C¹`, regular, confined to the open disk, and
there is a differentiable tangent-angle `φ` with `γ'(t) = ‖γ'(t)‖·e^{iφ(t)}` and
`(1 + K‖γ(t)‖²)/2 · φ'(t) = (κ(t) − K⟪γ(t), i·e^{iφ(t)}⟫_ℝ)·‖γ'(t)‖`.
At `K = +1` this is `Gluck.RealizesSphericalCurvature`; at `K = −1` the
hyperbolic analogue. -/
def Realizes (K : ℝ) (γ : ℝ → ℂ) (κ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 γ ∧ (∀ t, deriv γ t ≠ 0) ∧ (∀ t, ‖γ t‖ < 1) ∧
    ∃ φ : ℝ → ℝ, Differentiable ℝ φ ∧
      (∀ t, deriv γ t = (↑‖deriv γ t‖ : ℂ) * Complex.exp ((φ t : ℂ) * Complex.I)) ∧
      (∀ t, (1 + K * ‖γ t‖ ^ 2) / 2 * deriv φ t =
        (κ t - K * ⟪γ t, Complex.I * Complex.exp ((φ t : ℂ) * Complex.I)⟫_ℝ) *
          ‖deriv γ t‖)

/-- The `K`-generic four-vertex admissibility hypothesis. `IsCurvatureFunction`
(continuous, `2π`-periodic, strictly positive) plus the value-separated
`FourVertexCondition`, plus — for the non-spherical members `K ≤ 0` — the
uniform confinement floor `κ > (1 − K)/2`. At `K = +1` the last clause is
vacuous, so this is `Gluck.SphereFourVertex` (with a trivially-true extra
conjunct); at `K = −1` it is the hyperbolic escape-velocity bound `κ > 1`; at
`K = 0` it is the flat threshold `κ > 1/2`, exactly what makes the model circle
of curvature level `c` (coordinate radius `centeredRadius 0 c = 1/(2c)`) fit in
the open unit disk (`centeredRadius_lt_one_iff`). -/
def SpaceFormFourVertex (K : ℝ) (κ : ℝ → ℝ) : Prop :=
  IsCurvatureFunction κ ∧ FourVertexCondition κ ∧ (K ≤ 0 → ∀ θ, (1 - K) / 2 < κ θ)

/-- The *space-form gauge speed*
`q_{K,κ}(θ, z) = (1 + K‖z‖²) / (2(κ(θ) − K⟪z, i·e^{iθ}⟫_ℝ))`. Junk-value total
function; every lemma about it carries the admissibility hypotheses
`‖z‖ ≤ R < κ(θ)` (with `|K| ≤ 1`) making the denominator positive. -/
noncomputable def spaceFormSpeed (K : ℝ) (κ : ℝ → ℝ) (θ : ℝ) (z : ℂ) : ℝ :=
  (1 + K * ‖z‖ ^ 2) /
    (2 * (κ θ - K * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ))

/-- **`K`-uniform denominator positivity.** For `|K| ≤ 1` and `‖z‖ ≤ R < κ(θ)`,
the bracket `κ(θ) − K⟪z, i·e^{iθ}⟫_ℝ` is strictly positive: by Cauchy–Schwarz
`|K⟪z, i·e^{iθ}⟫_ℝ| ≤ |K|·‖z‖ ≤ ‖z‖ ≤ R < κ`. Recovers `sphere_denom_pos`
(K=1) and the hyperbolic denominator bound (K=−1). -/
lemma denom_pos {K : ℝ} (hK : |K| ≤ 1) {κ : ℝ → ℝ} {R θ : ℝ} {z : ℂ}
    (hz : ‖z‖ ≤ R) (hR : R < κ θ) :
    0 < κ θ - K * ⟪z, Complex.I * Complex.exp ((θ : ℂ) * Complex.I)⟫_ℝ := by
  set v := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hcs := abs_real_inner_le_norm z v
  rw [hvnorm, mul_one] at hcs
  have hKi : |K * ⟪z, v⟫_ℝ| ≤ R := by
    rw [abs_mul]
    calc |K| * |⟪z, v⟫_ℝ| ≤ 1 * ‖z‖ :=
          mul_le_mul hK (hcs.trans (le_refl _)) (abs_nonneg _) (by norm_num)
      _ = ‖z‖ := one_mul _
      _ ≤ R := hz
  have := (abs_le.mp hKi).2
  linarith

/-- **`K`-uniform positive speed.** Under `‖z‖ ≤ R < κ(θ)` (with `|K| ≤ 1`) and a
positive numerator, the gauge speed is strictly positive. For `|K| ≤ 1` and
`‖z‖ < 1` the numerator `1 + K‖z‖²` is automatically positive. -/
lemma spaceFormSpeed_pos {K : ℝ} (hK : |K| ≤ 1) {κ : ℝ → ℝ} {R θ : ℝ} {z : ℂ}
    (hz : ‖z‖ ≤ R) (hR : R < κ θ) (hnum : 0 < 1 + K * ‖z‖ ^ 2) :
    0 < spaceFormSpeed K κ θ z :=
  div_pos hnum (by have := denom_pos hK hz hR; linarith)

/-- **`K`-uniform numerator positivity** for confined points: if `|K| ≤ 1` and
`‖z‖ < 1` then `0 < 1 + K‖z‖²` (at `K = −1`, `1 − ‖z‖² > 0`). -/
lemma one_add_mul_normSq_pos {K : ℝ} (hK : |K| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    0 < 1 + K * ‖z‖ ^ 2 := by
  have h1 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have h2 : -1 ≤ K := (abs_le.mp hK).1
  nlinarith [sq_nonneg ‖z‖, norm_nonneg z]

/-- **Speed continuity.** For continuous `κ` with a uniform lower bound
`R < κ(θ)` and `|K| ≤ 1`, the gauge speed `(θ, z) ↦ q_{K,κ}(θ, z)` is
continuous on the slab `{‖z‖ ≤ R}`. -/
lemma spaceFormSpeed_continuousOn {K : ℝ} (hK : |K| ≤ 1) {κ : ℝ → ℝ} {R : ℝ}
    (hκ : Continuous κ) (hR : ∀ θ, R < κ θ) :
    ContinuousOn (fun p : ℝ × ℂ => spaceFormSpeed K κ p.1 p.2)
      {p : ℝ × ℂ | ‖p.2‖ ≤ R} := by
  have hexp : Continuous fun p : ℝ × ℂ =>
      Complex.I * Complex.exp ((p.1 : ℂ) * Complex.I) :=
    continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))
  have hnum : Continuous fun p : ℝ × ℂ => 1 + K * ‖p.2‖ ^ 2 :=
    continuous_const.add (continuous_const.mul (continuous_snd.norm.pow 2))
  have hden : Continuous fun p : ℝ × ℂ =>
      2 * (κ p.1 - K * ⟪p.2, Complex.I * Complex.exp ((p.1 : ℂ) * Complex.I)⟫_ℝ) :=
    continuous_const.mul ((hκ.comp continuous_fst).sub
      (continuous_const.mul (continuous_snd.inner hexp)))
  unfold spaceFormSpeed
  exact hnum.continuousOn.div hden.continuousOn fun p hp =>
    ne_of_gt (by have := denom_pos hK (R := R) hp (hR p.1); linarith)

/-- **Speed periodicity.** For `2π`-periodic `κ` the gauge speed is
`2π`-periodic in `θ`: both numerator and denominator are unchanged since
`κ(θ + 2π) = κ(θ)` and `e^{i(θ+2π)} = e^{iθ}`. -/
lemma spaceFormSpeed_periodic {K : ℝ} {κ : ℝ → ℝ}
    (hper : Function.Periodic κ (2 * π)) (θ : ℝ) (z : ℂ) :
    spaceFormSpeed K κ (θ + 2 * π) z = spaceFormSpeed K κ θ z := by
  have hexp : Complex.exp (((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  unfold spaceFormSpeed
  rw [hper θ, hexp]

/-- **Model geodesic-circle anchor (sign linchpin).** The Euclidean circle of
radius `r` traversed in the tangent-angle gauge sits at
`z(θ) = (-r) • (i·e^{iθ})` and carries constant space-form curvature
`κ = (1 − Kr²)/(2r)`; its gauge speed comes out to exactly `r`. Recovers the
sphere circle `κ_S = (1 − r²)/(2r) = cot ρ` (K=1) and the hyperbolic circle
`κ_H = (1 + r²)/(2r) = coth ρ` (K=−1). The opposite inner-product sign would
give junk — this pins the two-signs-are-one-parameter convention. -/
lemma spaceFormSpeed_circle (K : ℝ) {r : ℝ} (hr : 0 < r)
    (hne : (1 : ℝ) + K * r ^ 2 ≠ 0) (θ : ℝ) :
    spaceFormSpeed K (fun _ => (1 - K * r ^ 2) / (2 * r)) θ
      ((-r) • (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) = r := by
  set v := Complex.I * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hinner : ⟪(-r) • v, v⟫_ℝ = -r := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hvnorm]; ring
  have hznorm : ‖(-r) • v‖ = r := by
    rw [norm_smul, hvnorm, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hr]
  unfold spaceFormSpeed
  rw [hinner, hznorm]
  have hden : 2 * ((1 - K * r ^ 2) / (2 * r) - K * -r) = (1 + K * r ^ 2) / r := by
    field_simp; ring
  rw [hden, div_div_eq_mul_div, mul_comm (1 + K * r ^ 2) r, mul_div_assoc,
    div_self hne, mul_one]

/-- The **space-form centered radius** `r*(K, c) = 1/(√(c² + K) + c)`: the root
in `(0, 1)` of `K r² + 2c r − 1 = 0`, i.e. the Euclidean radius of the model
geodesic circle of constant curvature `c`. The single rationalized closed form
recovers the sphere radius `√(1 + c²) − c` (K=1), the hyperbolic radius
`c − √(c² − 1)` (K=−1, for `c > 1`), and — unlike the unrationalized form
`K(√(c²+K) − c)`, which vanishes identically at `K = 0` — the flat radius
`1/(2c)` (K=0, for `c > 1/2`). -/
noncomputable def centeredRadius (K c : ℝ) : ℝ :=
  (Real.sqrt (c ^ 2 + K) + c)⁻¹

/-- For `K ∈ {1, -1, 0}`, `|K| ≤ 1`: the `K`-generic replacement for the
`|K| = 1` facts of the two-sign engine. -/
lemma eps_abs_le_one {K : ℝ} (hK : K = 1 ∨ K = -1 ∨ K = 0) : |K| ≤ 1 := by
  rcases hK with h | h | h <;> subst h <;> norm_num

/-- `|K·x| ≤ |x|` for `|K| ≤ 1`: the workhorse inequality replacing the
`|K| = 1`-based `rw`s of the two-sign engine. -/
lemma abs_eps_mul_le {K : ℝ} (hK : |K| ≤ 1) (x : ℝ) : |K * x| ≤ |x| := by
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg x) hK

/-- **Window facts.** For an admissible level `c` — `c > 0` at `K = 1`,
`c > 1` at `K = −1`, `c > 1/2` at `K = 0` (the flat threshold making
`r*(0, c) = 1/(2c) < 1`) — the level is positive, the discriminant `c² + K` is
strictly positive, and the rationalizing denominator `√(c² + K) + c` exceeds
`1`. -/
lemma window_pos {K c : ℝ}
    (hc : (K = 1 ∧ 0 < c) ∨ (K = -1 ∧ 1 < c) ∨ (K = 0 ∧ 1 / 2 < c)) :
    0 < c ∧ 0 < c ^ 2 + K ∧ 1 < Real.sqrt (c ^ 2 + K) + c := by
  obtain ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ := hc <;> subst h
  · have h1 : Real.sqrt 1 ≤ Real.sqrt (c ^ 2 + 1) := Real.sqrt_le_sqrt (by nlinarith)
    rw [Real.sqrt_one] at h1
    exact ⟨hc, by positivity, by linarith⟩
  · exact ⟨by linarith, by nlinarith,
      by linarith [Real.sqrt_nonneg (c ^ 2 + (-1 : ℝ))]⟩
  · refine ⟨by linarith, by nlinarith, ?_⟩
    rw [add_zero, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ c)]
    linarith

/-- **Rationalized form agrees with the legacy form at `K = ±1`.**
`1/(√(c²+K) + c) = K(√(c²+K) − c)`, since
`(√(c²+K) − c)(√(c²+K) + c) = K` and `K² = 1`. This is the patch lemma for
proofs written against the old definition; it is genuinely `|K| = 1`-only (the
right-hand side vanishes at `K = 0` while the left is `1/(2c) ≠ 0`). -/
lemma centeredRadius_eq {K c : ℝ} (hK : K = 1 ∨ K = -1)
    (hc : (K = 1 ∧ 0 < c) ∨ (K = -1 ∧ 1 < c)) :
    centeredRadius K c = K * (Real.sqrt (c ^ 2 + K) - c) := by
  obtain ⟨-, hpos, hlt⟩ := window_pos (hc.imp_right Or.inl)
  have hs : Real.sqrt (c ^ 2 + K) ^ 2 = c ^ 2 + K := Real.sq_sqrt hpos.le
  have he2 : K * K = 1 := by rcases hK with h | h <;> subst h <;> norm_num
  rw [centeredRadius]
  refine (inv_eq_of_mul_eq_one_right ?_)
  linear_combination K * hs + he2

/-- Recovers the sphere centered radius `√(1 + c²) − c`. -/
lemma centeredRadius_one (c : ℝ) : centeredRadius 1 c = Real.sqrt (c ^ 2 + 1) - c := by
  have hs : Real.sqrt (c ^ 2 + 1) ^ 2 = c ^ 2 + 1 := Real.sq_sqrt (by positivity)
  rw [centeredRadius]
  exact inv_eq_of_mul_eq_one_right (by linear_combination hs)

/-- Recovers the hyperbolic centered radius `c − √(c² − 1)` (for `c ≥ 1`; below
the escape threshold the two sides are genuinely different junk values). -/
lemma centeredRadius_neg_one {c : ℝ} (hc : 1 ≤ c) :
    centeredRadius (-1) c = c - Real.sqrt (c ^ 2 - 1) := by
  have hs : Real.sqrt (c ^ 2 - 1) ^ 2 = c ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  rw [centeredRadius, show c ^ 2 + (-1 : ℝ) = c ^ 2 - 1 from by ring]
  exact inv_eq_of_mul_eq_one_right (by linear_combination -hs)

/-- The flat centered radius: `centeredRadius 0 c = 1/(2c)`, the coordinate
radius of the Euclidean circle of geodesic curvature `c` in the flat conformal
metric `λ = 2` (where `κ_euclidean = 2·κ_g`). -/
lemma centeredRadius_zero {c : ℝ} (hc : 0 ≤ c) :
    centeredRadius 0 c = (2 * c)⁻¹ := by
  rw [centeredRadius, add_zero, Real.sqrt_sq hc, two_mul]

/-- **Centered-radius solves the model quadratic.** `r = centeredRadius K c`
satisfies `K r² + 2c r − 1 = 0`, hence `(1 − Kr²)/(2r) = c`: the model circle of
radius `r` has curvature exactly `c`. (`K ∈ {+1,−1,0}`, `c` admissible.) -/
lemma centeredRadius_solves (K c : ℝ) (_hK : K = 1 ∨ K = -1 ∨ K = 0)
    (hc : (K = 1 ∧ 0 < c) ∨ (K = -1 ∧ 1 < c) ∨ (K = 0 ∧ 1 / 2 < c)) :
    K * centeredRadius K c ^ 2 + 2 * c * centeredRadius K c - 1 = 0 := by
  obtain ⟨-, hpos, hlt⟩ := window_pos hc
  have hs : Real.sqrt (c ^ 2 + K) ^ 2 = c ^ 2 + K := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (c ^ 2 + K) + c ≠ 0 := by linarith
  rw [centeredRadius]
  field_simp
  linear_combination -hs

/-- **Centered-radius lies in the open disk.** For an admissible curvature level
`c`, `0 < r*(K, c) < 1`. Sphere: `0 < √(1+c²) − c < 1` for `c > 0`. Hyperbolic:
`0 < c − √(c²−1) < 1` for `c > 1`. Flat: `0 < 1/(2c) < 1` for `c > 1/2`. -/
lemma centeredRadius_mem_Ioo (K c : ℝ) (_hK : K = 1 ∨ K = -1 ∨ K = 0)
    (hc : (K = 1 ∧ 0 < c) ∨ (K = -1 ∧ 1 < c) ∨ (K = 0 ∧ 1 / 2 < c)) :
    0 < centeredRadius K c ∧ centeredRadius K c < 1 := by
  obtain ⟨-, -, hlt⟩ := window_pos hc
  have h0 : (0 : ℝ) < Real.sqrt (c ^ 2 + K) + c := by linarith
  exact ⟨inv_pos.mpr h0, inv_lt_one_of_one_lt₀ hlt⟩

/-- **Uniform confinement threshold.** For a positive level `c`, the centered
radius fits in the open unit disk iff the level clears the uniform threshold
`(1 − K)/2`: `0` on the sphere (`K = 1`), `1` on the hyperbolic plane
(`K = −1`, the escape velocity), `1/2` on the flat plane (`K = 0`). This single
inequality is the `K`-generic form of the window clauses of `window_pos` and of
the floor conjunct of `SpaceFormFourVertex`. -/
lemma centeredRadius_lt_one_iff {K : ℝ} (hK : K = 1 ∨ K = -1 ∨ K = 0) {c : ℝ}
    (hc : 0 < c) : centeredRadius K c < 1 ↔ (1 - K) / 2 < c := by
  rcases hK with rfl | rfl | rfl
  · rw [centeredRadius_one]
    have hs : Real.sqrt (c ^ 2 + 1) ^ 2 = c ^ 2 + 1 := Real.sq_sqrt (by positivity)
    have hs0 : 0 < Real.sqrt (c ^ 2 + 1) := Real.sqrt_pos.mpr (by positivity)
    constructor
    · intro _; linarith
    · intro _
      nlinarith [hs, hs0, sq_nonneg (Real.sqrt (c ^ 2 + 1) - c - 1)]
  · constructor
    · intro h
      by_contra hle
      push Not at hle
      have hc1 : c ≤ 1 := by linarith
      have hzero : Real.sqrt (c ^ 2 + -1) = 0 :=
        Real.sqrt_eq_zero'.mpr (by nlinarith)
      rw [centeredRadius, hzero, zero_add] at h
      have := (inv_lt_one_iff₀).mp h
      rcases this with h' | h'
      · linarith
      · linarith
    · intro h
      have h1c : 1 < c := by linarith
      exact (centeredRadius_mem_Ioo (-1) c (Or.inr (Or.inl rfl))
        (Or.inr (Or.inl ⟨rfl, h1c⟩))).2
  · rw [centeredRadius_zero hc.le, sub_zero]
    rw [inv_lt_one_iff₀]
    constructor
    · rintro (h | h) <;> linarith
    · intro h; right; linarith

/-- **Bracket value at the centered circle.** `c + K·r*(K, c) = √(c² + K)`
(uniform in `K ∈ {+1,−1,0}`): the denominator `κ − K⟪z, i·e^{iθ}⟫` evaluated at
the level-`c` model circle `z = −r*·i·e^{iθ}` (where `⟪z, i·e^{iθ}⟫ = −r*`).
For the sphere (`K=+1`) this is `√(1+c²) ≥ 1` — an absolute lower bound; for
the hyperbolic plane (`K=−1`) it is `√(c²−1)`, positive for `c > 1` but tending
to `0` as `c → 1⁺` (the escape-velocity boundary); for the flat plane (`K=0`)
it is `c` itself. Margin constants scaled by this bracket are therefore
`c`-dependent, not absolute. -/
lemma centeredRadius_bracket (K c : ℝ) (_hK : K = 1 ∨ K = -1 ∨ K = 0)
    (hc : (K = 1 ∧ 0 < c) ∨ (K = -1 ∧ 1 < c) ∨ (K = 0 ∧ 1 / 2 < c)) :
    c + K * centeredRadius K c = Real.sqrt (c ^ 2 + K) := by
  obtain ⟨-, hpos, hlt⟩ := window_pos hc
  have hs : Real.sqrt (c ^ 2 + K) ^ 2 = c ^ 2 + K := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (c ^ 2 + K) + c ≠ 0 := by linarith
  rw [centeredRadius]
  field_simp
  linear_combination -hs

/-- **Admissible uniform lower bound.** From `SpaceFormFourVertex K κ` (any
`K`; only the `IsCurvatureFunction` conjunct is used) there is a confinement
radius `R` with `0 < R < 1` and
`R < κ(θ)` for all `θ`. The proof is uniform in `K`: it takes a minimum
value `κ(θ₀)` on one compact period and chooses
`R = min (κ θ₀) 1 / 2`. This `R` makes the denominator
`κ − K⟪z, i·e^{iθ}⟫` strictly positive on `{‖z‖ ≤ R}` (`denom_pos`). -/
lemma exists_admissible_lower_bound {K : ℝ} {κ : ℝ → ℝ}
    (hκ : SpaceFormFourVertex K κ) :
    ∃ R, 0 < R ∧ R < 1 ∧ ∀ θ, R < κ θ := by
  obtain ⟨hcont, hper, hpos⟩ := hκ.1
  obtain ⟨θ₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 2 * π)) hcont.continuousOn
  have h1 : min (κ θ₀) 1 ≤ κ θ₀ := min_le_left _ _
  have h2 : (0 : ℝ) < min (κ θ₀) 1 := lt_min (hpos θ₀) one_pos
  refine ⟨min (κ θ₀) 1 / 2, by linarith, by linarith [min_le_right (κ θ₀) 1], fun θ => ?_⟩
  obtain ⟨y, hy, hyθ⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos θ
  have hym : κ θ₀ ≤ κ y := hmin ⟨hy.1, hy.2.le⟩
  rw [hyθ]
  linarith

end Gluck.SpaceForm
