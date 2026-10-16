module

public import Gluck.Discrete.NativeFirstPairAnchor
public import Gluck.Discrete.NativeOrderedFirstPair

/-!
# Every first transition to a nonnegative flag has a regular anchor

The predecessor `t` may be below, equal to, or above the marked low
reading `p`. The two proved producers cover this exhaustive split.
-/

@[expose] public section

namespace Gluck.Discrete.NativeOppositePure

theorem exists_regular_anchor_of_firstPair_transition {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l)
    (hprev : firstPairFlag p t q l < 0) :
    ∃ L : Fin 4 → ℝ, NativeLengthPhysical p t q h l L ∧
      nativeLengthController p t q h l L = 0 ∧
      Function.Surjective (fderiv ℝ (nativeLengthController p t q h l) L) := by
  rcases le_or_gt t p with htp | hpt
  · exact exists_regular_anchor_of_firstPairFlag_of_le hp hp1 ht htp hl hl1 hq hqh hflag
  · exact exists_regular_nativeLength_anchor_of_ordered_firstPair hp hp1 hl hl1
      hpt htq hq hqh hflag hprev

end Gluck.Discrete.NativeOppositePure
