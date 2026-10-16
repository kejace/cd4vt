module

public import Gluck.Discrete.UniversalRegularFourAnchor
public import Gluck.Discrete.RegularFourAnchorConverse

/-!
# The coherent discrete converse for every polygon size at least four

Every nonconstant positive strict-DFV profile has a regular anchor on four
actual edges. The finite constant-run reduction restores repeated adjacent
readings before the native implicit-function opener makes every edge
positive. Positive constant profiles use the regular polygon.

The conclusion is the original `TabachnikovProblem2`: all original
curvatures, moderate arcs, closure, lifted full turn, and simplicity.
-/

@[expose] public section

namespace Gluck.Discrete

/-- A regular four-edge anchor for every positive strict-DFV profile,
including arbitrary constant runs and arbitrary numbers of distinct values. -/
theorem nonempty_regularFourAnchor_of_dfv
    {n : ℕ} {κ : ZMod n → ℝ} {c : ℝ}
    (hκ : ∀ i, 0 < κ i) (hdfv : DFV κ c) : Nonempty (RegularFourAnchor κ) :=
  ConstantRun.nonempty_regularFourAnchor_of_adjacent_unequal_producer
    (fun _ _ _ hn hp hd ha => nonempty_regularFourAnchor_of_adjacent_unequal_dfv hn hp hd ha)
    hκ hdfv

/-- Every positive strict-DFV profile has the original coherent Euclidean
realization, with every prescribed reading retained. -/
theorem realizesR2_of_dfv_fourActive
    {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {c : ℝ}
    (hκ : ∀ i, 0 < κ i) (hdfv : DFV κ c) : RealizesR2 κ := by
  obtain ⟨A⟩ := nonempty_regularFourAnchor_of_dfv hκ hdfv
  exact A.realizesR2 hκ

/-- Tabachnikov's coherent discrete converse for every `n ≥ 4`.
There is no additional geometric producer or regularity hypothesis. -/
theorem tabachnikovProblem2_all {n : ℕ} [NeZero n] (hn : 4 ≤ n) :
    TabachnikovProblem2 n :=
  tabachnikovProblem2_of_adjacent_unequal_regular_anchors
    (fun _ _ _ hm hp hd ha => nonempty_regularFourAnchor_of_adjacent_unequal_dfv hm hp hd ha) hn

end Gluck.Discrete
