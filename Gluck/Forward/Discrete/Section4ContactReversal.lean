/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4MinimalDisk

/-!
# Reversal of the minimal-disk contact argument

The local turns along a connected contact run have a common nonzero sign.
This file removes the choice of that sign from the connected-contact
contradiction: the negative case is reduced to the positive one by reversing
the cyclic polygon.
-/

namespace Gluck.Forward




/-- A local turn of the reversed cyclic polygon is the negative reflected
turn of the original polygon. -/
theorem reverseCyclicPolygon_cross {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) :
    Gluck.Discrete.crossR2
        (ReverseCyclicPolygon v (i - 1))
        (ReverseCyclicPolygon v i)
        (ReverseCyclicPolygon v (i + 1)) =
      -Gluck.Discrete.crossR2 (v (-i - 1)) (v (-i)) (v (-i + 1)) := by
  change Gluck.Discrete.crossR2 (v (-(i - 1))) (v (-i)) (v (-(i + 1))) = _
  rw [show (-(i - 1) : ZMod n) = -i + 1 by abel,
    show (-(i + 1) : ZMod n) = -i - 1 by abel,
    polygonCross_reverse_vertex (v := v) (-i)]

/-- Negative local turns at every contact become positive local turns at
every reflected contact after reversing cyclic order. -/
theorem reverseCyclicPolygon_contact_cross_pos_of_neg {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hneg : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    ∀ i : ZMod n, OnDiskBoundaryR2 (ReverseCyclicPolygon v) O R i →
      0 < Gluck.Discrete.crossR2
        (ReverseCyclicPolygon v (i - 1))
        (ReverseCyclicPolygon v i)
        (ReverseCyclicPolygon v (i + 1)) := by
  intro i hi
  rw [reverseCyclicPolygon_cross]
  apply neg_pos.mpr
  apply hneg (-i)
  simpa [OnDiskBoundaryR2, ReverseCyclicPolygon] using hi


end Gluck.Forward
