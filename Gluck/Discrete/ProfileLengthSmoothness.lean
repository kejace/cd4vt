import Gluck.Discrete.RegularDormantOpening

/-!
# Joint smoothness of discrete polygon reconstruction

The profile and the edge lengths are independent finite-dimensional variables.
All orders of differentiability hold strictly inside the arcsine walls, even
when some lengths are zero. These lemmas do not assert closure or simplicity.
-/

namespace Gluck.Discrete

open scoped ContDiff

variable {n : ℕ} [NeZero n] {r : ℕ∞ω} {κ ℓ : ZMod n → ℝ}

/-- The moderate turning law is smooth jointly in the two input vectors. -/
theorem contDiffAt_turningAngle_joint (i : ZMod n)
    (hw₁ : |κ i * (ℓ (i - 1) / 2)| < 1)
    (hw₂ : |κ i * (ℓ i / 2)| < 1) :
    ContDiffAt ℝ r (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) =>
      turningAngle 0 p.1 p.2 i) (κ, ℓ) := by
  rw [abs_lt] at hw₁ hw₂
  have h₁ : ContDiffAt ℝ r
      (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => p.1 i * (p.2 (i - 1) / 2))
      (κ, ℓ) := by fun_prop
  have h₂ : ContDiffAt ℝ r
      (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => p.1 i * (p.2 i / 2))
      (κ, ℓ) := by fun_prop
  simpa only [Function.comp_apply, turningAngle, tK_zero] using
    ((Real.contDiffAt_arcsin (ne_of_gt hw₁.1) (ne_of_lt hw₁.2)).comp (κ, ℓ) h₁).add
      ((Real.contDiffAt_arcsin (ne_of_gt hw₂.1) (ne_of_lt hw₂.2)).comp (κ, ℓ) h₂)

/-- All headings are smooth on the same strict-wall domain. -/
theorem contDiffAt_heading_joint (j : ℕ)
    (hw : ∀ i, |κ i * (ℓ (i - 1) / 2)| < 1 ∧ |κ i * (ℓ i / 2)| < 1) :
    ContDiffAt ℝ r (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => heading p.1 p.2 j)
      (κ, ℓ) := by
  unfold heading
  exact ContDiffAt.sum fun i _ => contDiffAt_turningAngle_joint _ (hw _).1 (hw _).2

/-- Developed vertices depend smoothly on both curvature and length. -/
theorem contDiffAt_vertexR2_joint (j : ℕ)
    (hw : ∀ i, |κ i * (ℓ (i - 1) / 2)| < 1 ∧ |κ i * (ℓ i / 2)| < 1) :
    ContDiffAt ℝ r (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => vertexR2 p.1 p.2 j)
      (κ, ℓ) := by
  unfold vertexR2
  apply ContDiffAt.sum
  intro k _
  have hl : ContDiffAt ℝ r (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) =>
      (p.2 (k : ZMod n) : ℂ)) (κ, ℓ) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (κ, ℓ) (by fun_prop)
  have hh : ContDiffAt ℝ r (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) =>
      (heading p.1 p.2 k : ℂ)) (κ, ℓ) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (κ, ℓ) (contDiffAt_heading_joint k hw)
  exact hl.mul ((hh.mul contDiffAt_const).cexp)

/-- The full labelled vertex tuple is jointly smooth. -/
theorem contDiffAt_polygonR2_joint
    (hw : ∀ i, |κ i * (ℓ (i - 1) / 2)| < 1 ∧ |κ i * (ℓ i / 2)| < 1) :
    ContDiffAt ℝ r (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => polygonR2 p.1 p.2)
      (κ, ℓ) :=
  contDiffAt_pi.mpr fun i => contDiffAt_vertexR2_joint i.val hw

/-- The three closure constraints are jointly smooth at a strict-wall datum. -/
theorem contDiffAt_closureMapR3_joint
    (hw : ∀ i, |κ i * (ℓ (i - 1) / 2)| < 1 ∧ |κ i * (ℓ i / 2)| < 1) :
    ContDiffAt ℝ r closureMapR3 (κ, ℓ) := by
  have ht : ContDiffAt ℝ r (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) =>
      turningSum p.1 p.2) (κ, ℓ) := by
    unfold turningSum
    exact ContDiffAt.sum fun i _ => contDiffAt_turningAngle_joint _ (hw i).1 (hw i).2
  exact (contDiffAt_vertexR2_joint n hw).prodMk (ht.sub contDiffAt_const)

/-- The length partial derivative of the joint map is the native length derivative. -/
theorem fderiv_closureMapR3_inr
    (hw : ∀ i, |κ i * (ℓ (i - 1) / 2)| < 1 ∧ |κ i * (ℓ i / 2)| < 1) :
    fderiv ℝ closureMapR3 (κ, ℓ) ∘L
        ContinuousLinearMap.inr ℝ (ZMod n → ℝ) (ZMod n → ℝ) =
      fderiv ℝ (fun L => closureMapR3 (κ, L)) ℓ := by
  have hf := (contDiffAt_closureMapR3_joint (r := 1) hw).hasStrictFDerivAt one_ne_zero
  have hi : HasFDerivAt (fun L : ZMod n → ℝ => (κ, L))
      (ContinuousLinearMap.inr ℝ (ZMod n → ℝ) (ZMod n → ℝ)) ℓ := by
    rw [show ContinuousLinearMap.inr ℝ (ZMod n → ℝ) (ZMod n → ℝ) =
        (0 : (ZMod n → ℝ) →L[ℝ] (ZMod n → ℝ)).prod
          (ContinuousLinearMap.id ℝ (ZMod n → ℝ)) by ext L <;> rfl]
    exact (hasFDerivAt_const κ ℓ).prodMk (hasFDerivAt_id ℓ)
  exact (hf.hasFDerivAt.comp ℓ hi).fderiv.symm

end Gluck.Discrete
