/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4PositiveChain
import Gluck.Discrete.CircleMeshChordSupport

/-!
# A uniform inner radius for the positive chain in Dahlberg Section 4

The vertices strictly between the two minimal-circle contacts form a finite,
nonempty chain.  Their maximum distance from the minimal-disk centre is
therefore a single radius `ρ < R`.  A sufficiently fine chord mesh on the
minimal circle then strictly supports every one of these retained vertices.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- The natural-coordinate indices of the strictly interior retained chain
are nonempty. -/
theorem internalIndexSet_nonempty :
    (Finset.Icc run.a run.b).Nonempty := by
  exact ⟨run.a, Finset.mem_Icc.mpr ⟨le_rfl, run.a_le_b⟩⟩

/-- Maximum distance from `O` among the strictly interior retained vertices. -/
noncomputable def chainInnerRadius : ℝ :=
  (Finset.Icc run.a run.b).sup' run.internalIndexSet_nonempty
    (fun k ↦ dist O (run.point k))

/-- Every strictly interior retained vertex lies in the closed disk of radius
`chainInnerRadius`. -/
theorem dist_point_le_chainInnerRadius {k : ℕ}
    (hak : run.a ≤ k) (hkb : k ≤ run.b) :
    dist O (run.point k) ≤ run.chainInnerRadius := by
  unfold chainInnerRadius
  exact Finset.le_sup' (fun j ↦ dist O (run.point j))
    (Finset.mem_Icc.mpr ⟨hak, hkb⟩)


/-- The uniform inner radius is strictly smaller than the radius of the
minimal enclosing disk. -/
theorem chainInnerRadius_lt
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    run.chainInnerRadius < R := by
  unfold chainInnerRadius
  rw [Finset.sup'_lt_iff]
  intro k hk
  exact run.internal_dist_lt hΔ (Finset.mem_Icc.mp hk).1
    (Finset.mem_Icc.mp hk).2

/-- A short positively oriented circle chord strictly supports every retained
interior chain vertex once its chord-inner radius exceeds the chain's uniform
inner radius.  This is the direct bridge to `CircleMeshChordSupport`. -/
theorem crossR2_circlePoint_pos_of_chainInnerRadius_lt
    (hR : 0 < R) {k : ℕ} (hak : run.a ≤ k) (hkb : k ≤ run.b)
    {θ₀ θ₁ : ℝ} (h₀₁ : θ₀ < θ₁) (hspan : θ₁ < θ₀ + Real.pi)
    (hρ : run.chainInnerRadius < R * Real.cos ((θ₁ - θ₀) / 2)) :
    0 < crossR2 (circlePoint O R θ₀) (circlePoint O R θ₁)
      (run.point k) := by
  exact crossR2_circlePoint_pos_of_dist_le_of_innerRadius_lt
    O (run.point k) hR h₀₁ hspan
      (run.dist_point_le_chainInnerRadius hak hkb) hρ


end Section4PositiveRunCertificate

end Gluck.Forward
