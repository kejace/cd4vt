module

public import Gluck.Discrete.ConstantRunAnchorReduction
public import Gluck.Discrete.TabachnikovReduction

/-!
# The remaining adjacent-unequal producer for the coherent converse

Finite restoration of constant runs and the existing regular dormant
opener reduce the original universal theorem to producing a regular
four-edge anchor for every positive adjacent-unequal DFV word. The
producer is explicit below and is not asserted by this file.
-/

@[expose] public section

namespace Gluck.Discrete

/-- The unchanged coherent problem follows once the adjacent-unequal
regular-anchor producer is supplied. No compactness or limiting premise
for realizations is required. -/
theorem tabachnikovProblem2_of_adjacent_unequal_regular_anchors
    (hproducer : ∀ (m : ℕ) (μ : ZMod m → ℝ) (c : ℝ),
      4 ≤ m → (∀ i, 0 < μ i) → DFV μ c →
      (∀ i, μ i ≠ μ (i + 1)) → Nonempty (RegularFourAnchor μ))
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) : TabachnikovProblem2 n := by
  intro κ hκ
  obtain ⟨hpositive, hconst | hdfv⟩ := hκ
  · obtain ⟨c, hc⟩ := hconst
    exact realizesR2_of_const (by omega) (by simpa only [hc 0] using hpositive 0) hc
  · obtain ⟨c, _, hd⟩ := hdfv
    obtain ⟨A⟩ := ConstantRun.nonempty_regularFourAnchor_of_adjacent_unequal_producer
      hproducer hpositive hd
    exact A.realizesR2 hpositive

end Gluck.Discrete
