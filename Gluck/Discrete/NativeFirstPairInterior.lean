import Gluck.Discrete.NativeOppositePureDefs
import Gluck.Discrete.CompactBoundaryIVT
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# An explicit inward chart for the first-pair construction

The low seam and common-diagonal equation can be solved by an acute
arctangent chart even away from the temporary `α = π / 2` boundary.
This avoids an implicit-continuation hypothesis for these two equations.
Existence of a zero of the remaining high seam is a separate step.
-/

open Set
open scoped Topology

namespace Gluck.Discrete.NativeOppositePure

noncomputable def interiorD (p t q α γ : ℝ) : ℝ :=
  q * Real.cos (lowTurn p t q α γ - α) - Real.cos γ

noncomputable def interiorN (p t q α γ : ℝ) : ℝ :=
  Real.sin γ - q * Real.sin (lowTurn p t q α γ - α)

noncomputable def interiorDelta (p t q α γ : ℝ) : ℝ :=
  Real.arctan (interiorN p t q α γ / interiorD p t q α γ)

noncomputable def interiorBeta (p t q α γ : ℝ) : ℝ :=
  Real.pi - interiorDelta p t q α γ - lowTurn p t q α γ

noncomputable def interiorHigh (p t q h l α γ : ℝ) : ℝ :=
  seamHigh q h l α (interiorBeta p t q α γ) γ (interiorDelta p t q α γ)

/-- The strict physical inequalities other than the two free angles. The
free angles may lie on their temporary construction boundaries. -/
def InteriorPhysical (p t q h α γ : ℝ) : Prop :=
  0 < interiorD p t q α γ ∧ 0 < interiorN p t q α γ ∧
    interiorBeta p t q α γ ∈ Ioo 0 (Real.pi / 2) ∧
    (h / q) * Real.sin (interiorDelta p t q α γ) < 1

theorem interior_seamLow (p t q α γ : ℝ) :
    seamLow p t q α (interiorBeta p t q α γ) γ
      (interiorDelta p t q α γ) = 0 := by
  unfold seamLow interiorBeta
  ring

theorem chord_eliminated {p t q α γ δ : ℝ} (hq : q ≠ 0) :
    q * chord q α (Real.pi - δ - lowTurn p t q α γ) γ δ =
      interiorD p t q α γ * Real.sin δ - interiorN p t q α γ * Real.cos δ := by
  unfold chord interiorD interiorN
  rw [show α + (Real.pi - δ - lowTurn p t q α γ) =
      Real.pi - (δ + (lowTurn p t q α γ - α)) by ring,
    Real.sin_pi_sub, Real.sin_add, Real.sin_add]
  field_simp
  ring

theorem interior_chord {p t q α γ : ℝ} (hq : q ≠ 0)
    (hD : interiorD p t q α γ ≠ 0) :
    chord q α (interiorBeta p t q α γ) γ (interiorDelta p t q α γ) = 0 := by
  have hc := chord_eliminated (p := p) (t := t) (α := α) (γ := γ)
    (δ := interiorDelta p t q α γ) hq
  have hzero : interiorD p t q α γ * Real.sin (interiorDelta p t q α γ) -
      interiorN p t q α γ * Real.cos (interiorDelta p t q α γ) = 0 := by
    unfold interiorDelta
    rw [Real.sin_arctan, Real.cos_arctan]
    field_simp
    ring
  rw [hzero] at hc
  exact (mul_eq_zero.mp hc).resolve_left hq

theorem interiorDelta_pos {p t q α γ : ℝ}
    (hD : 0 < interiorD p t q α γ) (hN : 0 < interiorN p t q α γ) :
    0 < interiorDelta p t q α γ :=
  Real.arctan_pos.mpr (div_pos hN hD)

theorem interiorDelta_lt_pi_div_two (p t q α γ : ℝ) :
    interiorDelta p t q α γ < Real.pi / 2 := Real.arctan_lt_pi_div_two _

theorem strictAngles_of_interiorPhysical {p t q h α γ : ℝ}
    (hα : α ∈ Ioo 0 (Real.pi / 2)) (hγ : γ ∈ Ioo 0 (Real.pi / 2))
    (hP : InteriorPhysical p t q h α γ) :
    StrictAngles q h α (interiorBeta p t q α γ) γ (interiorDelta p t q α γ) :=
  ⟨hα, hP.2.2.1, hγ,
    ⟨interiorDelta_pos hP.1 hP.2.1, interiorDelta_lt_pi_div_two ..⟩, hP.2.2.2⟩

theorem continuous_lowTurn (p t q : ℝ) :
    Continuous (fun z : ℝ × ℝ ↦ lowTurn p t q z.1 z.2) := by
  unfold lowTurn angleAtom
  fun_prop

theorem continuous_interiorD (p t q : ℝ) :
    Continuous (fun z : ℝ × ℝ ↦ interiorD p t q z.1 z.2) := by
  exact (continuous_const.mul (Real.continuous_cos.comp
    ((continuous_lowTurn p t q).sub continuous_fst))).sub
      (Real.continuous_cos.comp continuous_snd)

theorem continuous_interiorN (p t q : ℝ) :
    Continuous (fun z : ℝ × ℝ ↦ interiorN p t q z.1 z.2) := by
  exact (Real.continuous_sin.comp continuous_snd).sub
    (continuous_const.mul (Real.continuous_sin.comp
      ((continuous_lowTurn p t q).sub continuous_fst)))

theorem continuousAt_interiorDelta {p t q : ℝ} {z : ℝ × ℝ}
    (hD : interiorD p t q z.1 z.2 ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ ↦ interiorDelta p t q z.1 z.2) z := by
  exact Real.continuous_arctan.continuousAt.comp
    ((continuous_interiorN p t q).continuousAt.div
      (continuous_interiorD p t q).continuousAt hD)

theorem continuousAt_interiorBeta {p t q : ℝ} {z : ℝ × ℝ}
    (hD : interiorD p t q z.1 z.2 ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ ↦ interiorBeta p t q z.1 z.2) z :=
  (continuousAt_const.sub (continuousAt_interiorDelta hD)).sub
    (continuous_lowTurn p t q).continuousAt

theorem continuousAt_interiorHigh {p t q h l : ℝ} {z : ℝ × ℝ}
    (hD : interiorD p t q z.1 z.2 ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ ↦ interiorHigh p t q h l z.1 z.2) z := by
  have hβ := continuousAt_interiorBeta hD
  have hδ := continuousAt_interiorDelta hD
  unfold interiorHigh seamHigh highTurn angleAtom
  exact (continuousAt_fst.add continuousAt_snd |>.add
    ((Real.continuous_arcsin.continuousAt.comp
      (continuousAt_const.mul (Real.continuous_sin.continuousAt.comp hδ))).add
      (Real.continuous_arcsin.continuousAt.comp
        (continuousAt_const.mul (Real.continuous_sin.continuousAt.comp hβ))))).sub
        continuousAt_const

theorem isOpen_interiorPhysical (p t q h : ℝ) :
    IsOpen {z : ℝ × ℝ | InteriorPhysical p t q h z.1 z.2} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hD := (continuous_interiorD p t q).continuousAt.eventually
    (eventually_gt_nhds hz.1)
  have hN := (continuous_interiorN p t q).continuousAt.eventually
    (eventually_gt_nhds hz.2.1)
  have hβ := continuousAt_interiorBeta (ne_of_gt hz.1)
  have hβ0 := hβ.eventually (eventually_gt_nhds hz.2.2.1.1)
  have hβ1 := hβ.eventually (eventually_lt_nhds hz.2.2.1.2)
  have hwallcont : ContinuousAt
      (fun w : ℝ × ℝ ↦ (h / q) * Real.sin (interiorDelta p t q w.1 w.2)) z :=
    continuousAt_const.mul (Real.continuous_sin.continuousAt.comp
      (continuousAt_interiorDelta (ne_of_gt hz.1)))
  have hwall := hwallcont.eventually (eventually_lt_nhds hz.2.2.2)
  filter_upwards [hD, hN, hβ0, hβ1, hwall] with w hwD hwN hwβ0 hwβ1 hwwall
  exact ⟨hwD, hwN, ⟨hwβ0, hwβ1⟩, hwwall⟩

theorem continuousOn_interiorHigh (p t q h l : ℝ) :
    ContinuousOn (Function.uncurry (interiorHigh p t q h l))
      {z : ℝ × ℝ | InteriorPhysical p t q h z.1 z.2} :=
  continuousOn_of_forall_continuousAt (fun _ hz ↦ continuousAt_interiorHigh (ne_of_gt hz.1))

/-- The exact interior chart turns a physical boundary strip and its inward
sign into a strict zero of all three native equations. The separate wall
producer must supply the strip and the equality-case derivative. -/
theorem exists_strict_root_of_interior_strip {p t q h l γhi : ℝ}
    (hq : q ≠ 0) (hhi : γhi ∈ Ioo 0 (Real.pi / 2))
    (hphysical : ∀ γ ∈ Icc 0 γhi, InteriorPhysical p t q h (Real.pi / 2) γ)
    (hleft : interiorHigh p t q h l (Real.pi / 2) 0 ≤ 0)
    (hright : 0 < interiorHigh p t q h l (Real.pi / 2) γhi)
    (hderiv : interiorHigh p t q h l (Real.pi / 2) 0 = 0 →
      ∃ d > 0, HasDerivAt (fun α ↦ interiorHigh p t q h l α 0) d (Real.pi / 2)) :
    ∃ α β γ δ : ℝ, StrictAngles q h α β γ δ ∧
      seamLow p t q α β γ δ = 0 ∧ seamHigh q h l α β γ δ = 0 ∧
      chord q α β γ δ = 0 := by
  obtain ⟨α, hα, γ, hγ, hP, hzero⟩ :=
    CompactBoundaryIVT.exists_inward_zero_of_boundary_derivative
      (amin := 0) (lo := 0) (by positivity : (0 : ℝ) < Real.pi / 2) hhi.1
      (isOpen_interiorPhysical p t q h) hphysical
      (continuousOn_interiorHigh p t q h l) hleft hright hderiv
  refine ⟨α, interiorBeta p t q α γ, γ, interiorDelta p t q α γ,
    strictAngles_of_interiorPhysical hα ⟨hγ.1, hγ.2.trans hhi.2⟩ hP,
    interior_seamLow .., hzero, ?_⟩
  exact interior_chord hq (ne_of_gt hP.1)

end Gluck.Discrete.NativeOppositePure
