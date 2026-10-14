import Mathlib.Topology.Basic
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Curvature functions on the circle

This file scaffolds the curvature-function data for Gluck's converse to the Four
Vertex Theorem (strictly positive curvature case; Gluck 1971, DeTurck–Gluck
survey §III–IV).

A curvature function is the preassigned datum of the converse theorem: a
`2π`-periodic, continuous, strictly positive map `κ : ℝ → ℝ`, thought of as a
function on the circle `S¹ = ℝ / 2πℤ`. From it we build the radius of curvature
`ρ = 1/κ` (the integrand weight of the reconstruction integral) and the
four-vertex condition under which the curve closes up.

-/

namespace Gluck

open scoped Real

/-- A *curvature function* is a continuous, `2π`-periodic, strictly positive map
`κ : ℝ → ℝ`. This is the class of preassigned curvatures treated in Gluck's
positive case (DeTurck–Gluck §III–4). -/
def IsCurvatureFunction (κ : ℝ → ℝ) : Prop :=
  Continuous κ ∧ Function.Periodic κ (2 * Real.pi) ∧ ∀ θ, 0 < κ θ

/-- The *radius of curvature* of a curvature function `κ` is `ρ = 1/κ`, i.e.
`ρ θ = 1 / κ θ`. It is the integrand weight `1/κ(θ)` appearing in the
reconstruction formula `α(θ) = ∫₀^θ e^{iθ} dθ / κ(θ)`. -/
noncomputable def radius (κ : ℝ → ℝ) : ℝ → ℝ := fun θ => 1 / κ θ

/-- The radius of curvature `ρ = 1/κ` of a curvature function is itself
continuous, `2π`-periodic and strictly positive. -/
lemma radius_pos {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ) :
    Continuous (radius κ) ∧ Function.Periodic (radius κ) (2 * Real.pi) ∧
      ∀ θ, 0 < radius κ θ := by
  obtain ⟨hc, hp, hpos⟩ := hκ
  refine ⟨continuous_const.div hc (fun x => (hpos x).ne'), ?_, ?_⟩
  · intro θ; simp only [radius]; rw [hp θ]
  · intro θ; simp only [radius]; exact one_div_pos.mpr (hpos θ)

/-- A curvature function `κ` satisfies the *four-vertex condition* if either it
is constant, or it has *two value-separated, alternating local extrema*: four
points `p₁ < q₁ < p₂ < q₂` in a single fundamental period (`q₂ < p₁ + 2π`) with
`p₁, p₂` local maxima, `q₁, q₂` local minima, and the two minimum values lying
strictly below the two maximum values
(`max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)`).

The strict value-separation is Dahlberg's hypothesis in Theorem 1.1 (2005),
not a project-added refinement. The DeTurck--Gluck survey's informal rendering
as "at least two local maxima and two local minima" omits that clause. See
`blueprint/src/chapters/Gluck_Curvature.tex` (`def:four_vertex_condition`). -/
def FourVertexCondition (κ : ℝ → ℝ) : Prop :=
  (∃ c, ∀ θ, κ θ = c) ∨
    (∃ p₁ q₁ p₂ q₂, p₁ < q₁ ∧ q₁ < p₂ ∧ p₂ < q₂ ∧ q₂ < p₁ + 2 * Real.pi ∧
      IsLocalMax κ p₁ ∧ IsLocalMax κ p₂ ∧ IsLocalMin κ q₁ ∧ IsLocalMin κ q₂ ∧
      max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂))

/-- A curvature function whose extrema satisfy the strict value-separation
`max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)` cannot be constant: a constant `κ`
would force `c < c`. Consumed by the positive converse `Gluck.gluck_converse`
and the flat space-form mixed converse `Gluck.SpaceForm.dahlberg_converse_flat`. -/
lemma not_constant_of_separation {κ : ℝ → ℝ} {p₁ q₁ p₂ q₂ : ℝ}
    (hsep : max (κ q₁) (κ q₂) < min (κ p₁) (κ p₂)) :
    ¬ ∃ c, ∀ θ, κ θ = c := by
  rintro ⟨c, hc⟩
  rw [hc q₁, hc q₂, hc p₁, hc p₂] at hsep
  simp at hsep

/-- Intermediate value theorem packaged for a closed real interval and a value
lying between the two endpoint values (in either order): a continuous `f` on
`[p, q]` (with `p ≤ q`) attains every value `v` between `f p` and `f q` at some
point of `[p, q]`. -/
lemma ivt_hits {f : ℝ → ℝ} (hf : Continuous f) {p q v : ℝ} (hpq : p ≤ q)
    (hv : v ∈ Set.Icc (min (f p) (f q)) (max (f p) (f q))) :
    ∃ x ∈ Set.Icc p q, f x = v := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_uIcc (f := f) (a := p) (b := q) hf.continuousOn hv
  rw [Set.uIcc_of_le hpq] at hx
  exact ⟨x, hx, hfx⟩

/-- If a non-constant curvature function `κ` satisfies the four-vertex
condition, then there exist `0 < a < b` and four points
`θ₁ < θ₂ < θ₃ < θ₄` in a single fundamental period (`θ₄ < θ₁ + 2π`) at which `κ`
takes the values `a, b, a, b` in order around the circle. -/
lemma exists_abab_of_fourVertex {κ : ℝ → ℝ} (hκ : IsCurvatureFunction κ)
    (hnc : ¬ ∃ c, ∀ θ, κ θ = c) (hfv : FourVertexCondition κ) :
    ∃ a b, 0 < a ∧ a < b ∧ ∃ θ₁ θ₂ θ₃ θ₄,
      θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₄ ∧ θ₄ < θ₁ + 2 * Real.pi ∧
      κ θ₁ = a ∧ κ θ₂ = b ∧ κ θ₃ = a ∧ κ θ₄ = b := by
  obtain ⟨hcont, hper, hpos⟩ := hκ
  rcases hfv with hconst |
    ⟨p₁, q₁, p₂, q₂, hp1q1, hq1p2, hp2q2, hq2p1, _hmaxp1, _hmaxp2, _hminq1, _hminq2, hsep⟩
  · exact absurd hconst hnc
  set a := max (κ q₁) (κ q₂) with ha
  set b := min (κ p₁) (κ p₂) with hb
  have hab : a < b := hsep
  have ha_pos : 0 < a := lt_of_lt_of_le (hpos q₁) (le_max_left _ _)
  have hq1a : κ q₁ ≤ a := le_max_left _ _
  have hq2a : κ q₂ ≤ a := le_max_right _ _
  have hbp1 : b ≤ κ p₁ := min_le_left _ _
  have hbp2 : b ≤ κ p₂ := min_le_right _ _
  have hperp1 : κ (p₁ + 2 * Real.pi) = κ p₁ := hper p₁
  have h1 : p₁ ≤ q₁ := hp1q1.le
  have h2 : q₁ ≤ p₂ := hq1p2.le
  have h3 : p₂ ≤ q₂ := hp2q2.le
  have h4 : q₂ ≤ p₁ + 2 * Real.pi := hq2p1.le
  obtain ⟨θ₁, hθ₁mem, hθ₁⟩ := ivt_hits hcont h1 (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_right _ _).trans hq1a,
           (hab.le.trans hbp1).trans (le_max_left _ _)⟩)
  obtain ⟨θ₂, hθ₂mem, hθ₂⟩ := ivt_hits hcont h2 (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_left _ _).trans (hq1a.trans hab.le),
           hbp2.trans (le_max_right _ _)⟩)
  obtain ⟨θ₃, hθ₃mem, hθ₃⟩ := ivt_hits hcont h3 (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_right _ _).trans hq2a,
           (hab.le.trans hbp2).trans (le_max_left _ _)⟩)
  obtain ⟨θ₄, hθ₄mem, hθ₄⟩ := ivt_hits hcont h4 (by
    rw [Set.mem_Icc]
    exact ⟨(min_le_left _ _).trans (hq2a.trans hab.le),
           (hbp1.trans (le_of_eq hperp1.symm)).trans (le_max_right _ _)⟩)
  refine ⟨a, b, ha_pos, hab, θ₁, θ₂, θ₃, θ₄, ?_, ?_, ?_, ?_, hθ₁, hθ₂, hθ₃, hθ₄⟩
  · refine lt_of_le_of_ne (hθ₁mem.2.trans hθ₂mem.1) ?_
    intro h; apply (ne_of_lt hab); rw [← hθ₁, ← hθ₂, h]
  · refine lt_of_le_of_ne (hθ₂mem.2.trans hθ₃mem.1) ?_
    intro h; apply (ne_of_lt hab); rw [← hθ₃, ← hθ₂, h]
  · refine lt_of_le_of_ne (hθ₃mem.2.trans hθ₄mem.1) ?_
    intro h; apply (ne_of_lt hab); rw [← hθ₃, ← hθ₄, h]
  · have hp1θ1 : p₁ < θ₁ := by
      refine lt_of_le_of_ne hθ₁mem.1 ?_
      intro h; rw [← h] at hθ₁
      exact absurd hθ₁ (ne_of_gt (lt_of_lt_of_le hab hbp1))
    have hθ4le : θ₄ ≤ p₁ + 2 * Real.pi := hθ₄mem.2
    linarith

end Gluck
