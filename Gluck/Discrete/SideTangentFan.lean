module

public import Gluck.Discrete.SideTangentSquareLabels
public import Gluck.Discrete.CircleParameterGeometry

/-!
# Tangent intersections for the finite side-tangent construction

The vertices are actual intersections of consecutive unit-circle tangent lines.
The formulas remain continuous when a pair of normals coalesces, which gives
exactly the side-contact limits used in the square perturbation argument.
-/

@[expose] public section

open scoped InnerProductSpace Topology

namespace Gluck.Discrete.SideTangent

/-- A unit outward normal with a real angle lift. -/
noncomputable abbrev normal (θ : ℝ) : ℂ := circlePoint 0 1 θ

@[simp] lemma normal_re (θ : ℝ) : (normal θ).re = Real.cos θ := by simp [normal]
@[simp] lemma normal_im (θ : ℝ) : (normal θ).im = Real.sin θ := by simp [normal]

@[simp] lemma norm_normal (θ : ℝ) : ‖normal θ‖ = 1 := by
  simp [normal]

lemma inner_normal (α β : ℝ) : ⟪normal α, normal β⟫_ℝ = Real.cos (β - α) := by
  simp [Complex.inner, Real.cos_sub]

/-- The intersection of two unit tangent lines, extended to coincident normals. -/
noncomputable def tangentIntersection (u v : ℂ) : ℂ :=
  (1 + ⟪u, v⟫_ℝ)⁻¹ • (u + v)

lemma tangentIntersection_comm (u v : ℂ) :
    tangentIntersection u v = tangentIntersection v u := by
  simp only [tangentIntersection, real_inner_comm u v, add_comm u v]

lemma inner_tangentIntersection_left {u v : ℂ} (hu : ‖u‖ = 1)
    (hd : 1 + ⟪u, v⟫_ℝ ≠ 0) : ⟪u, tangentIntersection u v⟫_ℝ = 1 := by
  simp only [tangentIntersection, real_inner_smul_right, inner_add_right,
    real_inner_self_eq_norm_sq, hu, one_pow, inv_mul_cancel₀ hd]

lemma inner_tangentIntersection_right {u v : ℂ} (hv : ‖v‖ = 1)
    (hd : 1 + ⟪u, v⟫_ℝ ≠ 0) : ⟪v, tangentIntersection u v⟫_ℝ = 1 := by
  rw [tangentIntersection_comm]
  exact inner_tangentIntersection_left hv (by rwa [real_inner_comm])

/-- Gaps smaller than a half-turn have positive tangent-intersection denominators. -/
lemma normal_denominator_pos {α β : ℝ} (h₀ : α ≤ β) (hπ : β - α < Real.pi) :
    0 < 1 + ⟪normal α, normal β⟫_ℝ := by
  rw [inner_normal]
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (sub_nonneg.mpr h₀) le_rfl hπ
  rw [Real.cos_pi] at h
  linarith

/-- Duality between an oriented circle chord and its tangent intersection. -/
lemma cross_eq_tangent_support {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hd : 1 + ⟪u, v⟫_ℝ ≠ 0) (w : ℂ) :
    crossR2 u v w = crossR2 0 u v * (1 - ⟪w, tangentIntersection u v⟫_ℝ) := by
  have hu' : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := Complex.sq_norm u
    rw [hu, Complex.normSq_apply] at h
    nlinarith only [h]
  have hv' : v.re ^ 2 + v.im ^ 2 = 1 := by
    have h := Complex.sq_norm v
    rw [hv, Complex.normSq_apply] at h
    nlinarith only [h]
  simp only [tangentIntersection, real_inner_smul_right, inner_add_right]
  field_simp
  simp [crossR2, Complex.inner]
  linear_combination (u.re * w.im - u.im * w.re) * hv' -
    (v.re * w.im - v.im * w.re) * hu'

lemma cross_normal (α β : ℝ) :
    crossR2 0 (normal α) (normal β) = Real.sin (β - α) := by
  simp [crossR2, Real.sin_sub]
  ring

/-- A normal outside a consecutive angular gap strictly supports its tangent vertex. -/
lemma normal_support_lt_of_ordered {α β γ : ℝ} (hαβ : α < β)
    (hgap : β - α < Real.pi) (hβγ : β < γ) (hspan : γ < α + 2 * Real.pi) :
    ⟪normal γ, tangentIntersection (normal α) (normal β)⟫_ℝ < 1 := by
  have h := crossR2_circlePoint_pos_of_ordered 0 (by norm_num : (1 : ℝ) ≠ 0)
    hαβ hβγ hspan
  rw [cross_eq_tangent_support (norm_normal α) (norm_normal β)
    (normal_denominator_pos hαβ.le hgap).ne', cross_normal] at h
  have hs := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hαβ) hgap
  nlinarith

/-- The same strict support holds for a normal before the consecutive pair. -/
lemma normal_support_lt_of_wrapped {α β γ : ℝ} (hγα : γ < α)
    (hαβ : α < β) (hgap : β - α < Real.pi) (hspan : β < γ + 2 * Real.pi) :
    ⟪normal γ, tangentIntersection (normal α) (normal β)⟫_ℝ < 1 := by
  have h := normal_support_lt_of_ordered hαβ hgap hspan
    (by linarith : γ + 2 * Real.pi < α + 2 * Real.pi)
  simpa only [normal, circlePoint_add_two_pi] using h

lemma continuous_normal : Continuous normal := by
  change Continuous (circleMap 0 1)
  fun_prop

lemma continuousAt_tangentIntersection {u v : ℂ} (hd : 1 + ⟪u, v⟫_ℝ ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ ↦ tangentIntersection p.1 p.2) (u, v) := by
  have hc : ContinuousAt (fun p : ℂ × ℂ ↦ 1 + ⟪p.1, p.2⟫_ℝ) (u, v) :=
    continuousAt_const.add (continuous_fst.inner continuous_snd).continuousAt
  exact (hc.inv₀ hd).smul (continuous_fst.add continuous_snd).continuousAt

end Gluck.Discrete.SideTangent
