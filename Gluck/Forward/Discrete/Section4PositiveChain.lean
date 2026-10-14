/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4PositiveGap

/-!
# The finite positive-curvature chain in Dahlberg Section 4

This file repackages the maximal complementary run selected in Section 4 as
the exact finite chain consumed by the auxiliary-circle splice.
-/

namespace Gluck.Forward

/-- The selected noncontact run, together with its two boundary contacts and
the reciprocal-radius curvature gap on the closed one-vertex enlargement. -/
structure Section4PositiveRunCertificate {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) where
  c : ZMod n
  J : Finset (ZMod n)
  a : ℕ
  b : ℕ
  contact : c ∈ circleContactSet v O R
  maximal : Gluck.IsMaximalCyclicRunAt c
    (Finset.univ \ circleContactSet v O R) J
  a_pos : 0 < a
  a_le_b : a ≤ b
  b_lt : b < n
  run_short : b - a + 1 < n
  run_eq : J = Gluck.mapCut c (Finset.Icc a b)
  left_contact : Gluck.cyclicLift c (a - 1) ∈ circleContactSet v O R
  right_contact : Gluck.cyclicLift c (b + 1) ∈ circleContactSet v O R
  curvature_gap : ∀ k : ℕ, a - 1 ≤ k → k ≤ b + 1 →
    1 / R < SignedMengerProfile v (Gluck.cyclicLift c k)

/-- Failure of D4VT produces the finite positive run used in Dahlberg's
auxiliary-polygon construction. -/
theorem exists_section4PositiveRunCertificate
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hnonstrict :
      ¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v))
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hcontactCross : ∀ i : ZMod n,
      OnDiskBoundaryR2 v O R i →
        0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hnot : ¬ DahlbergFourVertex (SignedMengerProfile v)) :
    Nonempty (Section4PositiveRunCertificate v O R) := by
  obtain ⟨c, J, a, b, hc, hmax, ha, hab, hbn, hshort, hrun,
      _hdisjoint, hleft, hright, hgap⟩ :=
    exists_section4_positive_gap hsimple hregular hnoncircle hnonstrict hΔ
      hcontactCross hnot
  exact ⟨{
    c := c
    J := J
    a := a
    b := b
    contact := hc
    maximal := hmax
    a_pos := ha
    a_le_b := hab
    b_lt := hbn
    run_short := hshort
    run_eq := hrun
    left_contact := hleft
    right_contact := hright
    curvature_gap := hgap }⟩

namespace Section4PositiveRunCertificate

variable {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (run : Section4PositiveRunCertificate v O R)

/-- The natural-coordinate vertex of the enlarged run. -/
def point (k : ℕ) : ℂ := v (Gluck.cyclicLift run.c k)

/-- Both endpoints of the enlarged run lie on the minimal circle. -/
theorem endpoints_boundary :
    OnDiskBoundaryR2 v O R (Gluck.cyclicLift run.c (run.a - 1)) ∧
      OnDiskBoundaryR2 v O R (Gluck.cyclicLift run.c (run.b + 1)) := by
  exact ⟨Metric.mem_sphere'.mpr (mem_circleContactSet.mp run.left_contact),
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp run.right_contact)⟩

/-- Every vertex in the open run is a strict interior point of the minimal
disk. -/
theorem internal_dist_lt
    (hΔ : MinimalEnclosingDiskR2 v O R)
    {k : ℕ} (hak : run.a ≤ k) (hkb : k ≤ run.b) :
    dist O (run.point k) < R := by
  have hkJ : Gluck.cyclicLift run.c k ∈ run.J := by
    rw [run.run_eq]
    exact Finset.mem_image.mpr
      ⟨k, Finset.mem_Icc.mpr ⟨hak, hkb⟩, rfl⟩
  have hkNotContact :
      Gluck.cyclicLift run.c k ∉ circleContactSet v O R := by
    have hkComplement := run.maximal.properties.2.2 hkJ
    simpa using hkComplement
  exact lt_of_le_of_ne (Metric.mem_closedBall'.mp (hΔ.2.1 _)) fun heq =>
    hkNotContact (mem_circleContactSet.mpr heq)

/-- The reciprocal-radius gap is in particular positive curvature. -/
theorem signedMengerProfile_pos
    (hR : 0 < R) {k : ℕ}
    (hleft : run.a - 1 ≤ k) (hright : k ≤ run.b + 1) :
    0 < SignedMengerProfile v (Gluck.cyclicLift run.c k) := by
  exact (one_div_pos.mpr hR).trans
    (run.curvature_gap k hleft hright)

/-- Every consecutive original triple centred in the enlarged run turns
strictly left. -/
theorem cross_pos
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hR : 0 < R) {k : ℕ}
    (hleft : run.a - 1 ≤ k) (hright : k ≤ run.b + 1) :
    0 < Gluck.Discrete.crossR2
      (v (Gluck.cyclicLift run.c k - 1))
      (v (Gluck.cyclicLift run.c k))
      (v (Gluck.cyclicLift run.c k + 1)) := by
  exact crossR2_pos_of_signedMengerR2_pos
    (by simpa using hsimple.1 (Gluck.cyclicLift run.c k - 1))
    (run.signedMengerProfile_pos hR hleft hright)

end Section4PositiveRunCertificate

end Gluck.Forward
