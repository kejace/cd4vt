/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4OrientedPositiveChain
import Gluck.Forward.Discrete.Section4CircleArcSpliceContradiction

/-!
# Dahlberg Section 4 from an oriented circle arc

This module isolates the final logical assembly of Dahlberg's non-strict
branch.  The remaining global input is the ordinary complementary-circle arc
selected by the orientation of the minimal-circle contacts.  All support,
mesh, endpoint-curvature, simplicity, and exact-Theorem-6 arguments are
discharged by `Section4PositiveRunCertificate.false_of_circleArcCertificate`.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- The global circle-order output consumed by the finite Section 4 splice. -/
def DahlbergE2OrientedCircleArcSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ} {O : ℂ} {R : ℝ},
    IsSimplePolygon v → DahlbergRegular v → MinimalEnclosingDiskR2 v O R → 0 < R →
    ∀ run : Section4PositiveRunCertificate v O R, Nonempty (Section4CircleArcCertificate run)

/-- An oriented complementary-circle arc implies the paper's Section 4 source. -/
private theorem dahlbergE2Section4Source_of_orientedCircleArcSource_aux
    (harc : DahlbergE2OrientedCircleArcSource) :
    DahlbergE2Section4Source := by
  intro n hne hn v hsimple hregular hnoncircle hnonstrict
  letI : NeZero n := hne
  by_contra hnot
  obtain ⟨O, R, hΔ⟩ := exists_minimalEnclosingDiskR2 v
  have hR : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  rcases exists_section4PositiveRunCertificate_or_reverse
      hn hsimple hregular hnoncircle hnonstrict hΔ hnot with
    ⟨⟨run⟩⟩ | ⟨⟨run⟩⟩
  · rcases harc hn hsimple hregular hΔ hR run with ⟨arc⟩
    exact run.false_of_circleArcCertificate hsimple hΔ hR arc
  · let w : ZMod n → ℂ := ReverseCyclicPolygon v
    have hsimpleW : IsSimplePolygon w :=
      isSimplePolygon_reverseCyclicPolygon hsimple
    have hregularW : DahlbergRegular w :=
      dahlbergRegular_reverseCyclicPolygon hregular
    have hΔW : MinimalEnclosingDiskR2 w O R :=
      (minimalEnclosingDiskR2_reverseCyclicPolygon_iff).mpr hΔ
    rcases harc hn hsimpleW hregularW hΔW hR run with ⟨arc⟩
    exact run.false_of_circleArcCertificate hsimpleW hΔW hR arc

/-- An oriented-circle-arc source supplies the theorem-facing paper sources. -/
theorem dahlbergE2PaperSources_of_orientedCircleArcSource
    (harc : DahlbergE2OrientedCircleArcSource) :
    DahlbergE2PaperSources where
  theorem6 := dahlbergE2_theorem6_exact_paper_source
  lemma9 := dahlbergE2_lemma9_paper_bridge_source
  section4 := dahlbergE2Section4Source_of_orientedCircleArcSource_aux harc

end Gluck.Forward
