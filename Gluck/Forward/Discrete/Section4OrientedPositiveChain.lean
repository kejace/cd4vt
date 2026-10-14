/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4GlobalContactOrientation
import Gluck.Forward.Discrete.Section4PositiveChain

/-!
# WLOG orientation of Dahlberg's Section 4 positive chain

All minimal-circle contacts have one common strict turn sign.  In the
negative case, reversal changes that sign and preserves every hypothesis and
the failure of the four-vertex conclusion.  Thus the finite positive run is
available for the original polygon or its reversal, with no orientation
assumption in the theorem statement.
-/

namespace Gluck.Forward

/-- The source-free WLOG reduction which supplies a positive-run certificate
for `v` or for its cyclic reversal. -/
theorem exists_section4PositiveRunCertificate_or_reverse
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict :
      ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v))
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hnot : ¬ DahlbergFourVertex (SignedMengerProfile v)) :
    Nonempty (Section4PositiveRunCertificate v O R) ∨
      Nonempty (Section4PositiveRunCertificate
        (ReverseCyclicPolygon v) O R) := by
  rcases circleContactSet_cross_uniform hn hsimple hregular hΔ with hpos | hneg
  · left
    exact exists_section4PositiveRunCertificate
      hsimple hregular hnoncircle hnonstrict hΔ hpos hnot
  · right
    let w : ZMod n → ℂ := ReverseCyclicPolygon v
    have hsimpleW : Gluck.Discrete.IsSimplePolygon w :=
      isSimplePolygon_reverseCyclicPolygon hsimple
    have hregularW : DahlbergRegular w :=
      dahlbergRegular_reverseCyclicPolygon hregular
    have hnoncircleW : ¬ Concyclic w := by
      intro hcyc
      exact hnoncircle (concyclic_reverseCyclicPolygon_iff.mp hcyc)
    have hnonstrictW :
        ¬ (PositivePolygonOrientation w ∨ NegativePolygonOrientation w) :=
      not_strictPolygonOrientation_reverseCyclicPolygon hnonstrict
    have hΔW : MinimalEnclosingDiskR2 w O R :=
      (minimalEnclosingDiskR2_reverseCyclicPolygon_iff).mpr hΔ
    have hposW : ∀ i : ZMod n, OnDiskBoundaryR2 w O R i →
        0 < Gluck.Discrete.crossR2
          (w (i - 1)) (w i) (w (i + 1)) :=
      reverseCyclicPolygon_contact_cross_pos_of_neg hneg
    have hnotW : ¬ DahlbergFourVertex (SignedMengerProfile w) := by
      intro hfv
      apply hnot
      exact dahlbergFourVertex_of_neg_reflectIndex
        (κ := SignedMengerProfile v) (by
          convert hfv using 1
          ext i
          exact (SignedMengerProfile_reverseCyclicPolygon v i).symm)
    exact exists_section4PositiveRunCertificate
      hsimpleW hregularW hnoncircleW hnonstrictW hΔW hposW hnotW

end Gluck.Forward
