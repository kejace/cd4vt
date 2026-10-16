module

public import Gluck.Discrete.CurvatureLinkage
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Native equations for an opposite-pure quadrilateral

The original corner slots are `(1,1), (p,t), (q,q), (h,l)`.
The pure-`1` half-angles are `α,β` and the pure-`q` half-angles are `γ,δ`.
The cyclic half-lengths are `sin α, sin γ/q, sin δ/q, sin β`.
These definitions impose no orthogonality condition and retain the original
mixed endpoint arcs. Positivity and principal-branch guards are hypotheses
of theorems, rather than alterations to the native residuals.
-/

@[expose] public section

namespace Gluck.Discrete.NativeOppositePure

/-- An original endpoint's principal half-angle in a pure-angle coordinate. -/
noncomputable def angleAtom (a z : ℝ) : ℝ := Real.arcsin (a * Real.sin z)

/-- The angular deficit of an endpoint below its incident pure curvature. -/
noncomputable def angleDefect (a z : ℝ) : ℝ := z - angleAtom a z

/-- The angular excess of an endpoint above its incident pure curvature. -/
noncomputable def angleExcess (a z : ℝ) : ℝ := angleAtom a z - z

/-- The original turn at the first mixed corner. -/
noncomputable def lowTurn (p t q α γ : ℝ) : ℝ :=
  angleAtom p α + angleAtom (t / q) γ

/-- The original turn at the second mixed corner. -/
noncomputable def highTurn (q h l β δ : ℝ) : ℝ :=
  angleAtom (h / q) δ + angleAtom l β

/-- First mixed corner's exact seam equation. -/
noncomputable def seamLow (p t q α β γ δ : ℝ) : ℝ :=
  β + δ + lowTurn p t q α γ - Real.pi

/-- Second mixed corner's exact seam equation. -/
noncomputable def seamHigh (q h l α β γ δ : ℝ) : ℝ :=
  α + γ + highTurn q h l β δ - Real.pi

/-- Equality of the two common half-diagonals, retaining both pure-turn branches. -/
noncomputable def chord (q α β γ δ : ℝ) : ℝ :=
  Real.sin (α + β) - Real.sin (γ + δ) / q

/-- Original full-turn defect in split-angle coordinates. -/
noncomputable def turnDefect (p t q h l α β γ δ : ℝ) : ℝ :=
  (α + β) + (γ + δ) + lowTurn p t q α γ + highTurn q h l β δ -
    2 * Real.pi

/-- Half-length closure with the first actual active edge given heading zero. -/
noncomputable def nativeHalfClosure (p t q h l α β γ δ : ℝ) : ℂ :=
  (Real.sin α : ℂ) +
    ((Real.sin γ / q : ℝ) : ℂ) * unitPhase (lowTurn p t q α γ) +
    ((Real.sin δ / q : ℝ) : ℂ) * unitPhase (lowTurn p t q α γ + (γ + δ)) +
    (Real.sin β : ℂ) *
      unitPhase (lowTurn p t q α γ + (γ + δ) + highTurn q h l β δ)

/-- Strict split angles and the additional original high-endpoint incidence wall. -/
def StrictAngles (q h α β γ δ : ℝ) : Prop :=
  α ∈ Set.Ioo 0 (Real.pi / 2) ∧ β ∈ Set.Ioo 0 (Real.pi / 2) ∧
    γ ∈ Set.Ioo 0 (Real.pi / 2) ∧ δ ∈ Set.Ioo 0 (Real.pi / 2) ∧
      (h / q) * Real.sin δ < 1

/-- The two exact seam defects sum to the lifted native turn defect. -/
theorem seamLow_add_seamHigh (p t q h l α β γ δ : ℝ) :
    seamLow p t q α β γ δ + seamHigh q h l α β γ δ =
      turnDefect p t q h l α β γ δ := by
  unfold seamLow seamHigh turnDefect
  ring

/-- Writing the low seam with deficits exposes its two monotone split variables. -/
theorem seamLow_eq_defects (p t q α β γ δ : ℝ) :
    seamLow p t q α β γ δ =
      (α + β + (γ + δ) - Real.pi) - angleDefect p α - angleDefect (t / q) γ := by
  unfold seamLow lowTurn angleDefect
  ring

/-- Writing the high seam exposes its increasing excess at the actual high endpoint. -/
theorem seamHigh_eq_defect_excess (q h l α β γ δ : ℝ) :
    seamHigh q h l α β γ δ =
      (α + β + (γ + δ) - Real.pi) - angleDefect l β + angleExcess (h / q) δ := by
  unfold seamHigh highTurn angleDefect angleExcess
  ring

end Gluck.Discrete.NativeOppositePure
