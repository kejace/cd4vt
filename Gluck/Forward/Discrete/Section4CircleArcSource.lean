/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleArcPaperSource
import Gluck.Forward.Discrete.Section4ThreeContactCertificate
import Gluck.Forward.Discrete.Section4TwoContactArc

/-!
# The source-free oriented circle arc in Dahlberg Section 4

The minimal circle has at least two polygonal contacts.  Exactly two contacts
are antipodal, while three or more contacts supply the ordered complementary
arc through the three-contact orientation anchor.
-/

namespace Gluck.Forward

open Gluck.Discrete

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}

/-- Every positive run in a simple polygon's positive minimal disk has the
oriented complementary-circle arc required by the finite Section 4 splice. -/
theorem nonempty_circleArcCertificate_of_minimalEnclosingDisk
    (run : Section4PositiveRunCertificate v O R) (hsimple : IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R) (hR : 0 < R) :
    Nonempty (Section4CircleArcCertificate run) := by
  have htwo : 2 ≤ (circleContactSet v O R).card :=
    two_le_card_circleContactSet_of_minimalEnclosingDiskR2
      hΔ hR (Metric.mem_sphere'.mpr (mem_circleContactSet.mp run.contact))
  by_cases hthree : 3 ≤ (circleContactSet v O R).card
  · exact run.nonempty_circleArcCertificate_of_three_contacts
      hsimple hΔ hR hthree
  · have hcard : (circleContactSet v O R).card = 2 := by omega
    exact run.circleArcCertificate_of_contactSet_card_eq_two
      hsimple hΔ hR hcard

end Section4PositiveRunCertificate

private theorem dahlbergE2_orientedCircleArcSource_aux : DahlbergE2OrientedCircleArcSource := by
  intro _n _ _hn _v _O _R hsimple _hregular hΔ hR run
  exact run.nonempty_circleArcCertificate_of_minimalEnclosingDisk hsimple hΔ hR

/-- Source-free theorem-facing paper sources for Dahlberg's Euclidean D4VT. -/
theorem dahlbergE2_paperSources : DahlbergE2PaperSources :=
  dahlbergE2PaperSources_of_orientedCircleArcSource dahlbergE2_orientedCircleArcSource_aux


end Gluck.Forward
