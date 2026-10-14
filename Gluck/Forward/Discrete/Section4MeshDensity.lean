/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleSplice
import Gluck.Discrete.CircleMeshChordSupport

/-!
# A sufficiently fine circle mesh

Continuity of cosine at zero and the Archimedean property give a finite
subdivision of any positive arc shorter than one full turn whose chords
strictly support a prescribed concentric inner disk.  The final theorem
combines this density choice with `CircleMeshChordSupport`.
-/

open Set Metric Filter
open scoped Topology

namespace Gluck.Forward.Section4PositiveRunCertificate

/-- Consecutive values of `circleMeshAngle` differ by the constant mesh
step. -/
theorem circleMeshAngle_succ_sub
    (q j : ℕ) (θB θA : ℝ) :
    circleMeshAngle q (j + 1) θB θA -
        circleMeshAngle q j θB θA =
      (θA - θB) / (q + 1 : ℕ) := by
  have hden : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold circleMeshAngle
  field_simp
  push_cast
  ring




end Gluck.Forward.Section4PositiveRunCertificate
