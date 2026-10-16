module

public import Gluck.Forward.Discrete.DahlbergRegions

/-!
# Dahlberg's discrete four-vertex theorem

Continuation of `Gluck.Forward.Discrete.DahlbergRegions`: equal-curvature
rigidity over a shared edge, signed-Menger profiles of concyclic and oriented
polygons, and Dahlberg's Euclidean discrete four-vertex kernel.
-/

@[expose] public section

namespace Gluck.Forward

/-! ## Equal-curvature rigidity over a shared positive edge -/

/-- If two noncollinear triples over the same oriented edge have the same
canonical edge parameter, then their canonical edge circles are the same
circle. -/
theorem edgeCommonCircumcircle_of_parameter_eq {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P ≠ 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q ≠ 0)
    (hy : edgeCircumcenterParameter A B P = edgeCircumcenterParameter A B Q) :
    ∃ O R,
      CircumcircleR2 A B P O R ∧ CircumcircleR2 A B Q O R := by
  refine ⟨edgeCircleCenter A B (edgeCircumcenterParameter A B P),
    normalizedCircleRadius (chordHalfLength A B) (edgeCircumcenterParameter A B P),
    circumcircleR2_edge_parameter hAB hPcross, ?_⟩
  rw [hy]
  exact circumcircleR2_edge_parameter hAB hQcross

/-- A shared canonical edge circle packages the four incident vertices as
concyclic metric data. -/
theorem exists_common_circle_of_edgeCommonCircumcircle {A B P Q O : ℂ} {R : ℝ}
    (hP : CircumcircleR2 A B P O R) (hQ : CircumcircleR2 A B Q O R) :
    0 < R ∧ dist O P = R ∧ dist O A = R ∧ dist O B = R ∧ dist O Q = R := by
  exact ⟨hP.1, hP.2.2.2, hP.2.1, hP.2.2.1, hQ.2.2.2⟩

/-- Over a fixed oriented edge, two positive locally regular endpoint triples
with the same signed Menger curvature have the same canonical circumcenter
parameter. -/
theorem edgeCircumcenterParameter_eq_of_endpoint_regular_pos_eq {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P =
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgeCircumcenterParameter A B P = edgeCircumcenterParameter A B Q := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne'
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne'
  have hyP : 0 ≤ edgeCircumcenterParameter A B P :=
    edgeCircumcenterParameter_nonneg_of_regular hAB hPcross hcircleP hconeP
  have hyQ : 0 ≤ edgeCircumcenterParameter A B Q :=
    edgeCircumcenterParameter_nonneg_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) =
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) := by
    calc
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P)
          = Gluck.Discrete.signedMengerR2 A B P :=
            (signedMengerR2_edge_parameter_of_pos hAB hPcross).symm
      _ = Gluck.Discrete.signedMengerR2 A B Q := hκ
      _ = normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) :=
            signedMengerR2_edge_parameter_of_pos hAB hQcross
  apply le_antisymm
  · exact parameter_le_of_curvature_le_nonneg
      (a := chordHalfLength A B) (yP := edgeCircumcenterParameter A B Q)
      (yQ := edgeCircumcenterParameter A B P) (chordHalfLength_pos hAB).ne'
      hyQ (le_of_eq hcurv.symm)
  · exact parameter_le_of_curvature_le_nonneg
      (a := chordHalfLength A B) (yP := edgeCircumcenterParameter A B P)
      (yQ := edgeCircumcenterParameter A B Q) (chordHalfLength_pos hAB).ne'
      hyP (le_of_eq hcurv)

/-- Polygon-indexed equal-curvature rigidity over the shared edge
`v i → v (i+1)` on the positive branch. -/
theorem polygonEdgeCircumcenterParameter_eq_of_endpoint_pos_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)) =
      edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) =
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [← polygonSignedMenger_eq_edgePrev i]
    exact hκ
  exact edgeCircumcenterParameter_eq_of_endpoint_regular_pos_eq
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Profile-facing equal-curvature rigidity over the shared edge
`v i → v (i+1)` on the positive branch. -/
theorem signedMengerProfile_edgeCircumcenterParameter_eq_of_endpoint_pos_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < SignedMengerProfile v i)
    (hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1)) :
    edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)) =
      edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)) := by
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple
    (by simpa [SignedMengerProfile] using hPκpos)
  have hQκpos : 0 < SignedMengerProfile v (i + 1) := by
    rwa [← hκ]
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    have hAB : v i ≠ v (i + 1) := hsimple.1 i
    have hQκ' : 0 <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
      simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκpos
    exact crossR2_pos_of_signedMengerR2_pos hAB hQκ'
  exact polygonEdgeCircumcenterParameter_eq_of_endpoint_pos_eq hsimple hregular i
    hPcross hQcross
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Equal positive endpoint signed-Menger curvatures over a shared edge give a
common Euclidean circle through the two edge endpoints and the two adjacent
third vertices. -/
theorem edgeCommonCircumcircle_of_endpoint_regular_pos_eq {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : 0 < Gluck.Discrete.crossR2 A B P)
    (hQcross : 0 < Gluck.Discrete.crossR2 A B Q)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P =
      Gluck.Discrete.signedMengerR2 A B Q) :
    ∃ O R,
      CircumcircleR2 A B P O R ∧ CircumcircleR2 A B Q O R := by
  exact edgeCommonCircumcircle_of_parameter_eq hAB hPcross.ne' hQcross.ne'
    (edgeCircumcenterParameter_eq_of_endpoint_regular_pos_eq
      hAB hPcross hQcross hPreg hQreg hκ)

/-- Polygon-indexed positive common-circle consequence for equal adjacent
signed-Menger curvatures. -/
theorem polygonEdgeCommonCircumcircle_of_endpoint_pos_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) =
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [← polygonSignedMenger_eq_edgePrev i]
    exact hκ
  exact edgeCommonCircumcircle_of_endpoint_regular_pos_eq
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Profile-facing positive common-circle consequence for equal adjacent
signed-Menger values. -/
theorem signedMengerProfile_edgeCommonCircumcircle_of_endpoint_pos_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < SignedMengerProfile v i)
    (hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1)) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  have hPcross := polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple
    (by simpa [SignedMengerProfile] using hPκpos)
  have hQκpos : 0 < SignedMengerProfile v (i + 1) := by
    rwa [← hκ]
  have hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    have hAB : v i ≠ v (i + 1) := hsimple.1 i
    have hQκ' : 0 <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
      simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκpos
    exact crossR2_pos_of_signedMengerR2_pos hAB hQκ'
  exact polygonEdgeCommonCircumcircle_of_endpoint_pos_eq hsimple hregular i
    hPcross hQcross
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Over a fixed oriented edge, two negative locally regular endpoint triples
with the same signed Menger curvature have the same canonical circumcenter
parameter. -/
theorem edgeCircumcenterParameter_eq_of_endpoint_regular_neg_eq {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P =
      Gluck.Discrete.signedMengerR2 A B Q) :
    edgeCircumcenterParameter A B P = edgeCircumcenterParameter A B Q := by
  obtain ⟨OP, RP, hcircleP, hconeP⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero hPreg hPcross.ne
  obtain ⟨OQ, RQ, hcircleQ, hconeQ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right hQreg hQcross.ne
  have hyP : edgeCircumcenterParameter A B P ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular hAB hPcross hcircleP hconeP
  have hyQ : edgeCircumcenterParameter A B Q ≤ 0 :=
    edgeCircumcenterParameter_nonpos_of_regular_right hAB hQcross hcircleQ hconeQ
  have hcurv :
      normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P) =
        normalizedCircleCurvature (chordHalfLength A B)
          (edgeCircumcenterParameter A B Q) := by
    have hneg :
        -normalizedCircleCurvature (chordHalfLength A B)
            (edgeCircumcenterParameter A B P) =
          -normalizedCircleCurvature (chordHalfLength A B)
            (edgeCircumcenterParameter A B Q) := by
      calc
        -normalizedCircleCurvature (chordHalfLength A B) (edgeCircumcenterParameter A B P)
            = Gluck.Discrete.signedMengerR2 A B P :=
              (signedMengerR2_edge_parameter_of_neg hAB hPcross).symm
        _ = Gluck.Discrete.signedMengerR2 A B Q := hκ
        _ = -normalizedCircleCurvature (chordHalfLength A B)
            (edgeCircumcenterParameter A B Q) :=
              signedMengerR2_edge_parameter_of_neg hAB hQcross
    linarith
  apply le_antisymm
  · exact parameter_le_of_curvature_ge_nonpos
      (a := chordHalfLength A B) (yP := edgeCircumcenterParameter A B Q)
      (yQ := edgeCircumcenterParameter A B P) (chordHalfLength_pos hAB).ne'
      hyP (le_of_eq hcurv)
  · exact parameter_le_of_curvature_ge_nonpos
      (a := chordHalfLength A B) (yP := edgeCircumcenterParameter A B P)
      (yQ := edgeCircumcenterParameter A B Q) (chordHalfLength_pos hAB).ne'
      hyQ (le_of_eq hcurv.symm)

/-- Polygon-indexed equal-curvature rigidity over the shared edge
`v i → v (i+1)` on the negative branch. -/
theorem polygonEdgeCircumcenterParameter_eq_of_endpoint_neg_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)) =
      edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)) := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) =
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [← polygonSignedMenger_eq_edgePrev i]
    exact hκ
  exact edgeCircumcenterParameter_eq_of_endpoint_regular_neg_eq
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Profile-facing equal-curvature rigidity over the shared edge
`v i → v (i+1)` on the negative branch. -/
theorem signedMengerProfile_edgeCircumcenterParameter_eq_of_endpoint_neg_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : SignedMengerProfile v i < 0)
    (hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1)) :
    edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)) =
      edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)) := by
  have hPcross := polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple
    (by simpa [SignedMengerProfile] using hPκneg)
  have hQκneg : SignedMengerProfile v (i + 1) < 0 := by
    rwa [← hκ]
  have hQcross :
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
    have hAB : v i ≠ v (i + 1) := hsimple.1 i
    have hQκ' :
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
      simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκneg
    exact crossR2_neg_of_signedMengerR2_neg hAB hQκ'
  exact polygonEdgeCircumcenterParameter_eq_of_endpoint_neg_eq hsimple hregular i
    hPcross hQcross
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Equal negative endpoint signed-Menger curvatures over a shared edge give a
common Euclidean circle through the two edge endpoints and the two adjacent
third vertices. -/
theorem edgeCommonCircumcircle_of_endpoint_regular_neg_eq {A B P Q : ℂ}
    (hAB : A ≠ B)
    (hPcross : Gluck.Discrete.crossR2 A B P < 0)
    (hQcross : Gluck.Discrete.crossR2 A B Q < 0)
    (hPreg : DahlbergRegularAt P A B) (hQreg : DahlbergRegularAt A B Q)
    (hκ : Gluck.Discrete.signedMengerR2 A B P =
      Gluck.Discrete.signedMengerR2 A B Q) :
    ∃ O R,
      CircumcircleR2 A B P O R ∧ CircumcircleR2 A B Q O R := by
  exact edgeCommonCircumcircle_of_parameter_eq hAB hPcross.ne hQcross.ne
    (edgeCircumcenterParameter_eq_of_endpoint_regular_neg_eq
      hAB hPcross hQcross hPreg hQreg hκ)

/-- Polygon-indexed negative common-circle consequence for equal adjacent
signed-Menger curvatures. -/
theorem polygonEdgeCommonCircumcircle_of_endpoint_neg_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hκ : Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) =
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  have hPreg : DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1)) := hregular i
  have hQreg : DahlbergRegularAt (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa using hregular (i + 1)
  have hκ' :
      Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) =
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    rw [← polygonSignedMenger_eq_edgePrev i]
    exact hκ
  exact edgeCommonCircumcircle_of_endpoint_regular_neg_eq
    (hsimple.1 i) hPcross hQcross hPreg hQreg hκ'

/-- Profile-facing negative common-circle consequence for equal adjacent
signed-Menger values. -/
theorem signedMengerProfile_edgeCommonCircumcircle_of_endpoint_neg_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : SignedMengerProfile v i < 0)
    (hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1)) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  have hPcross := polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple
    (by simpa [SignedMengerProfile] using hPκneg)
  have hQκneg : SignedMengerProfile v (i + 1) < 0 := by
    rwa [← hκ]
  have hQcross :
      Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
    have hAB : v i ≠ v (i + 1) := hsimple.1 i
    have hQκ' :
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
      simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκneg
    exact crossR2_neg_of_signedMengerR2_neg hAB hQκ'
  exact polygonEdgeCommonCircumcircle_of_endpoint_neg_eq hsimple hregular i
    hPcross hQcross
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- A globally constant positive signed-Menger profile gives a common circle
on every adjacent four-point window. -/
theorem signedMengerProfile_edgeCommonCircumcircle_of_constant_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκpos : ∀ i : ZMod n, 0 < SignedMengerProfile v i)
    (hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  rcases hconst with ⟨c, hc⟩
  apply signedMengerProfile_edgeCommonCircumcircle_of_endpoint_pos_eq hsimple hregular i
  · exact hκpos i
  · rw [hc i, hc (i + 1)]

/-- A globally constant negative signed-Menger profile gives a common circle
on every adjacent four-point window. -/
theorem signedMengerProfile_edgeCommonCircumcircle_of_constant_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκneg : ∀ i : ZMod n, SignedMengerProfile v i < 0)
    (hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R ∧
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) O R := by
  rcases hconst with ⟨c, hc⟩
  apply signedMengerProfile_edgeCommonCircumcircle_of_endpoint_neg_eq hsimple hregular i
  · exact hκneg i
  · rw [hc i, hc (i + 1)]

/-- A globally constant positive signed-Menger profile on a locally regular
simple polygon forces all vertices onto one Euclidean circle. -/
theorem concyclic_of_constant_signedMengerProfile_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκpos : ∀ i : ZMod n, 0 < SignedMengerProfile v i)
    (hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    Concyclic v := by
  classical
  have hlocal :=
    signedMengerProfile_edgeCommonCircumcircle_of_constant_pos hsimple hregular hκpos hconst
  choose O R hOR using hlocal
  have hsucc : ∀ i : ZMod n, O i = O (i + 1) ∧ R i = R (i + 1) := by
    intro i
    have hcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
      have hAB : v i ≠ v (i + 1) := hsimple.1 i
      have hκ : 0 <
          Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
        simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκpos (i + 1)
      exact crossR2_pos_of_signedMengerR2_pos hAB hκ
    have hleft :
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) (O i) (R i) :=
      (hOR i).2
    have hright :
        CircumcircleR2 (v (i + 1)) (v (i + 1 + 1)) (v i) (O (i + 1)) (R (i + 1)) := by
      simpa [sub_eq_add_neg, add_assoc] using (hOR (i + 1)).1
    exact circumcircleR2_unique_of_cyclic_reorder (hsimple.1 i) hcross.ne' hleft hright
  have hnat : ∀ k : ℕ, O 0 = O (k : ZMod n) ∧ R 0 = R (k : ZMod n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hsucc (k : ZMod n)
        have hOstep : O (k : ZMod n) = O ((k + 1 : ℕ) : ZMod n) := by
          simpa [Nat.cast_add] using hs.1
        have hRstep : R (k : ZMod n) = R ((k + 1 : ℕ) : ZMod n) := by
          simpa [Nat.cast_add] using hs.2
        constructor
        · exact ih.1.trans hOstep
        · exact ih.2.trans hRstep
  refine ⟨O 0, R 0, (hOR 0).1.1, fun i => ?_⟩
  have hi := hnat i.val
  have hO : O 0 = O i := by
    simpa [ZMod.natCast_rightInverse i] using hi.1
  have hR : R 0 = R i := by
    simpa [ZMod.natCast_rightInverse i] using hi.2
  rw [hO, hR]
  exact (hOR i).1.2.1

/-- A globally constant negative signed-Menger profile on a locally regular
simple polygon forces all vertices onto one Euclidean circle. -/
theorem concyclic_of_constant_signedMengerProfile_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκneg : ∀ i : ZMod n, SignedMengerProfile v i < 0)
    (hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    Concyclic v := by
  classical
  have hlocal :=
    signedMengerProfile_edgeCommonCircumcircle_of_constant_neg hsimple hregular hκneg hconst
  choose O R hOR using hlocal
  have hsucc : ∀ i : ZMod n, O i = O (i + 1) ∧ R i = R (i + 1) := by
    intro i
    have hcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
      have hAB : v i ≠ v (i + 1) := hsimple.1 i
      have hκ :
          Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0 := by
        simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκneg (i + 1)
      exact crossR2_neg_of_signedMengerR2_neg hAB hκ
    have hleft :
        CircumcircleR2 (v i) (v (i + 1)) (v (i + 1 + 1)) (O i) (R i) :=
      (hOR i).2
    have hright :
        CircumcircleR2 (v (i + 1)) (v (i + 1 + 1)) (v i) (O (i + 1)) (R (i + 1)) := by
      simpa [sub_eq_add_neg, add_assoc] using (hOR (i + 1)).1
    exact circumcircleR2_unique_of_cyclic_reorder (hsimple.1 i) hcross.ne hleft hright
  have hnat : ∀ k : ℕ, O 0 = O (k : ZMod n) ∧ R 0 = R (k : ZMod n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hsucc (k : ZMod n)
        have hOstep : O (k : ZMod n) = O ((k + 1 : ℕ) : ZMod n) := by
          simpa [Nat.cast_add] using hs.1
        have hRstep : R (k : ZMod n) = R ((k + 1 : ℕ) : ZMod n) := by
          simpa [Nat.cast_add] using hs.2
        constructor
        · exact ih.1.trans hOstep
        · exact ih.2.trans hRstep
  refine ⟨O 0, R 0, (hOR 0).1.1, fun i => ?_⟩
  have hi := hnat i.val
  have hO : O 0 = O i := by
    simpa [ZMod.natCast_rightInverse i] using hi.1
  have hR : R 0 = R i := by
    simpa [ZMod.natCast_rightInverse i] using hi.2
  rw [hO, hR]
  exact (hOR i).1.2.1

/-- Positive same-sign contrapositive: a nonconcyclic locally regular simple
polygon has nonconstant signed-Menger profile. -/
theorem not_constant_signedMengerProfile_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκpos : ∀ i : ZMod n, 0 < SignedMengerProfile v i)
    (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  intro hconst
  exact hnoncircle (concyclic_of_constant_signedMengerProfile_pos
    hsimple hregular hκpos hconst)

/-- Negative same-sign contrapositive: a nonconcyclic locally regular simple
polygon has nonconstant signed-Menger profile. -/
theorem not_constant_signedMengerProfile_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hκneg : ∀ i : ZMod n, SignedMengerProfile v i < 0)
    (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  intro hconst
  exact hnoncircle (concyclic_of_constant_signedMengerProfile_neg
    hsimple hregular hκneg hconst)

/-- A nonzero constant signed-Menger profile on a locally regular simple
polygon forces all vertices onto one Euclidean circle. -/
theorem concyclic_of_constant_signedMengerProfile_ne_zero
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    {c : ℝ} (hc : ∀ i : ZMod n, SignedMengerProfile v i = c) (hc0 : c ≠ 0) :
    Concyclic v := by
  rcases lt_trichotomy c 0 with hcneg | hczero | hcpos
  · exact concyclic_of_constant_signedMengerProfile_neg hsimple hregular
      (fun i => by simpa [hc i] using hcneg) ⟨c, hc⟩
  · exact False.elim (hc0 hczero)
  · exact concyclic_of_constant_signedMengerProfile_pos hsimple hregular
      (fun i => by simpa [hc i] using hcpos) ⟨c, hc⟩

/-- Contrapositive form: on a nonconcyclic locally regular simple polygon, a
constant signed-Menger profile must be the zero profile. -/
theorem constant_signedMengerProfile_eq_zero_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    {c : ℝ} (hc : ∀ i : ZMod n, SignedMengerProfile v i = c) :
    c = 0 := by
  by_contra hc0
  exact hnoncircle (concyclic_of_constant_signedMengerProfile_ne_zero
    hsimple hregular hc hc0)

/-- A nonconcyclic locally regular simple polygon has nonconstant
signed-Menger profile.  The zero constant is ruled out by the subdivision
obstruction. -/
theorem not_constant_signedMengerProfile_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  rintro ⟨c, hc⟩
  have hc0 : c = 0 :=
    constant_signedMengerProfile_eq_zero_of_not_concyclic hsimple hregular hnoncircle hc
  have hκzero : ∀ i : ZMod n, SignedMengerProfile v i = 0 := by
    intro i
    exact (hc i).trans hc0
  exact not_constant_signedMengerProfile_zero_of_isSimplePolygon hsimple hregular hκzero

/-- On a nonconcyclic locally regular simple polygon, one nonzero
signed-Menger value already forces the profile to be nonconstant. -/
theorem not_constant_signedMengerProfile_of_not_concyclic_of_exists_ne_zero
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hne : ∃ i : ZMod n, SignedMengerProfile v i ≠ 0) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  rintro ⟨c, hc⟩
  have hc0 : c = 0 :=
    constant_signedMengerProfile_eq_zero_of_not_concyclic hsimple hregular hnoncircle hc
  rcases hne with ⟨i, hi⟩
  exact hi ((hc i).trans hc0)

/-! ## Profile-facing endpoint order wrappers -/

/-- Positive signed-Menger profile at a polygon vertex gives positive
orientation over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_pos_of_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : 0 < SignedMengerProfile v i) :
    0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgePrev_cross_pos_of_vertex_signedMenger_pos hsimple
    (by simpa [SignedMengerProfile] using hκ)

/-- Negative signed-Menger profile at a polygon vertex gives negative
orientation over the outgoing edge with the previous vertex as third point. -/
theorem polygonEdgePrev_cross_neg_of_signedMengerProfile_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : SignedMengerProfile v i < 0) :
    Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0 := by
  exact polygonEdgePrev_cross_neg_of_vertex_signedMenger_neg hsimple
    (by simpa [SignedMengerProfile] using hκ)

/-- Profile-facing own-region membership over the outgoing edge from nonzero
signed Menger curvature at the left endpoint. -/
theorem signedMengerProfile_edgePrev_mem_own_dahlbergRegion_of_ne_zero {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) {i : ZMod n}
    (hκ : SignedMengerProfile v i ≠ 0) :
    v (i - 1) ∈ edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgePrev_mem_own_dahlbergRegion_of_vertex_menger_ne_zero hsimple
    (by simpa [SignedMengerProfile] using hκ)

/-- Profile-facing form of Dahlberg Lemma 8(1) for the left endpoint of the
edge `i → i+1`. -/
theorem signedMengerProfile_edgePrev_region_subset_halfPlane_of_nonneg {n : ℕ}
    {v : ZMod n → ℂ} {i : ZMod n}
    (hk : 0 ≤ SignedMengerProfile v i) :
    edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) ⊆
      edgeHalfPlane (v i) (v (i + 1)) := by
  exact polygonEdgePrev_region_subset_halfPlane_of_nonneg
    (by simpa [SignedMengerProfile] using hk)

/-- Profile-facing form of Dahlberg Lemma 8(2) for the left endpoint of the
edge `i → i+1`. -/
theorem signedMengerProfile_edgePrev_halfPlane_subset_region_of_nonpos {n : ℕ}
    {v : ZMod n → ℂ} {i : ZMod n}
    (hk : SignedMengerProfile v i ≤ 0) :
    edgeHalfPlane (v i) (v (i + 1)) ⊆
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgePrev_halfPlane_subset_region_of_nonpos
    (by simpa [SignedMengerProfile] using hk)

/-- Profile-facing endpoint form of Dahlberg Lemma 8 for the oriented edge
from `v i` to `v (i+1)`. -/
theorem signedMengerProfile_edgeDahlbergRegion_anti_of_endpoint_order
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hκ : SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1)) :
    edgePointDahlbergRegion (v i) (v (i + 1)) (v (i + 1 + 1)) ⊆
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgeDahlbergRegion_anti_of_endpoint_order hsimple hregular i
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Profile-facing incidence corollary of endpoint nesting. -/
theorem signedMengerProfile_edgePoint_mem_region_of_endpoint_order
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hκ : SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1))
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) ≠ 0) :
    v (i + 1 + 1) ∈
      edgePointDahlbergRegion (v i) (v (i + 1)) (v (i - 1)) := by
  exact polygonEdgePoint_mem_region_of_endpoint_order hsimple hregular i
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ) hQcross

/-- Positive profile-facing incidence into the ordinary curvature disk. -/
theorem signedMengerProfile_edgePoint_mem_edgeClosedDisk_of_endpoint_order_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < SignedMengerProfile v i)
    (hκ : SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1)) :
    v (i + 1 + 1) ∈
      edgeClosedDisk (v i) (v (i + 1))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgePoint_mem_edgeClosedDisk_of_endpoint_order_pos_of_vertex_menger_pos
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκpos)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Positive profile-facing radius comparison along one oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_antitone_of_endpoint_order_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < SignedMengerProfile v i)
    (hκ : SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgeCircleRadius_antitone_of_endpoint_order_pos_of_vertex_menger_pos
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκpos)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Positive profile-facing strict radius comparison along one oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictAnti_of_endpoint_order_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκpos : 0 < SignedMengerProfile v i)
    (hκ : SignedMengerProfile v i < SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgeCircleRadius_strictAnti_of_endpoint_order_pos_of_vertex_menger_pos
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκpos)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Positive profile-facing reverse strict radius comparison along one oriented
edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictAnti_rev_of_endpoint_order_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hQκpos : 0 < SignedMengerProfile v (i + 1))
    (hκ : SignedMengerProfile v (i + 1) < SignedMengerProfile v i) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  exact polygonEdgeCircleRadius_strictAnti_rev_of_endpoint_order_pos_of_vertex_menger_pos
    hsimple hregular i
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκpos)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Positive profile-facing converse: a strict radius drop over the edge
`i → i+1` gives a strict adjacent signed-Menger increase. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))) :
    SignedMengerProfile v i < SignedMengerProfile v (i + 1) := by
  have hκ := signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_pos
    (hsimple.1 i) hPcross hQcross hR
  rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))] at hκ
  simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ

/-- Positive profile-facing converse in the reverse adjacent direction. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_pos_rev
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n)
    (hPcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)))
    (hQcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)))
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))) :
    SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  have hκ := signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_pos_rev
    (hsimple.1 i) hPcross hQcross hR
  rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))] at hκ
  simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ

/-- Negative profile-facing radius comparison along one oriented edge.  In the
negative branch, signed Menger curvature is `-1/R`, so adjacent signed-curvature
order gives monotone radius order. -/
theorem signedMengerProfile_edgeCircleRadius_mono_of_endpoint_order_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : SignedMengerProfile v i < 0)
    (hQκneg : SignedMengerProfile v (i + 1) < 0)
    (hκ : SignedMengerProfile v i ≤ SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) ≤
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  exact polygonEdgeCircleRadius_mono_of_endpoint_order_neg_of_vertex_menger_neg
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Negative profile-facing strict radius comparison along one oriented edge.
In the negative branch, signed Menger curvature is `-1/R`, so adjacent
signed-curvature order gives monotone radius order. -/
theorem signedMengerProfile_edgeCircleRadius_strictMono_of_endpoint_order_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : SignedMengerProfile v i < 0)
    (hQκneg : SignedMengerProfile v (i + 1) < 0)
    (hκ : SignedMengerProfile v i < SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  exact polygonEdgeCircleRadius_strictMono_of_endpoint_order_neg_of_vertex_menger_neg
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Negative profile-facing reverse strict radius comparison along one
oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictMono_rev_of_endpoint_order_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (i : ZMod n)
    (hPκneg : SignedMengerProfile v i < 0)
    (hQκneg : SignedMengerProfile v (i + 1) < 0)
    (hκ : SignedMengerProfile v (i + 1) < SignedMengerProfile v i) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact polygonEdgeCircleRadius_strictMono_rev_of_endpoint_order_neg_of_vertex_menger_neg
    hsimple hregular i
    (by simpa [SignedMengerProfile] using hPκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hQκneg)
    (by simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ)

/-- Negative profile-facing converse: a strict radius increase over the edge
`i → i+1` gives a strict adjacent signed-Menger increase. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))) :
    SignedMengerProfile v i < SignedMengerProfile v (i + 1) := by
  have hκ := signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_neg
    (hsimple.1 i) hPcross hQcross hR
  rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))] at hκ
  simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ

/-- Negative profile-facing converse in the reverse adjacent direction. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_neg_rev
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n)
    (hPcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) < 0)
    (hQcross : Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) < 0)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))) :
    SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  have hκ := signedMengerR2_lt_of_edgeCircleRadius_lt_endpoint_neg_rev
    (hsimple.1 i) hPcross hQcross hR
  rw [signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))] at hκ
  simpa [SignedMengerProfile, sub_eq_add_neg, add_assoc] using hκ

/-! ## Concyclic polygons and signed Menger curvature -/

/-- A concyclic polygon gives a circumcircle for every oriented vertex triple. -/
theorem circumcircleR2_of_concyclic_triple {n : ℕ} {v : ZMod n → ℂ}
    (hcyc : Concyclic v) (i : ZMod n) :
    ∃ O R, CircumcircleR2 (v (i - 1)) (v i) (v (i + 1)) O R := by
  rcases hcyc with ⟨O, R, hR, hdist⟩
  exact ⟨O, R, hR, hdist (i - 1), hdist i, hdist (i + 1)⟩

/-- A concyclic polygon gives a circumcircle for the cyclically reordered
vertex triple used by the edge-radius API. -/
theorem circumcircleR2_of_concyclic_edgePrev {n : ℕ} {v : ZMod n → ℂ}
    (hcyc : Concyclic v) (i : ZMod n) :
    ∃ O R, CircumcircleR2 (v (i + 1)) (v (i - 1)) (v i) O R := by
  rcases hcyc with ⟨O, R, hR, hdist⟩
  exact ⟨O, R, hR, hdist (i + 1), hdist (i - 1), hdist i⟩

/-- On a concyclic polygon, a positively oriented noncollinear vertex has
signed Menger curvature equal to the reciprocal of the common radius. -/
theorem polygonSignedMenger_eq_inv_radius_of_concyclic_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    {O : ℂ} {R : ℝ} (hR : 0 < R) (hdist : ∀ i, dist O (v i) = R)
    (i : ZMod n)
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = 1 / R := by
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact signedMengerR2_eq_inv_circumradius_of_pos hAB hcross
    ⟨hR, hdist (i + 1), hdist (i - 1), hdist i⟩

/-- On a concyclic polygon, a negatively oriented noncollinear vertex has
signed Menger curvature equal to minus the reciprocal of the common radius. -/
theorem polygonSignedMenger_eq_neg_inv_radius_of_concyclic_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    {O : ℂ} {R : ℝ} (hR : 0 < R) (hdist : ∀ i, dist O (v i) = R)
    (i : ZMod n)
    (hcross : Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = -(1 / R) := by
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  exact signedMengerR2_eq_neg_inv_circumradius_of_neg hAB hcross
    ⟨hR, hdist (i + 1), hdist (i - 1), hdist i⟩

/-- A consistently positively oriented concyclic simple polygon has constant
signed Menger curvature. -/
theorem exists_constant_signedMenger_of_concyclic_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (hcross : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ∃ c, ∀ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = c := by
  rcases hcyc with ⟨O, R, hR, hdist⟩
  refine ⟨1 / R, fun i => ?_⟩
  exact polygonSignedMenger_eq_inv_radius_of_concyclic_pos hsimple hR hdist i (hcross i)

/-- A consistently negatively oriented concyclic simple polygon has constant
signed Menger curvature. -/
theorem exists_constant_signedMenger_of_concyclic_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (hcross : ∀ i, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    ∃ c, ∀ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = c := by
  rcases hcyc with ⟨O, R, hR, hdist⟩
  refine ⟨-(1 / R), fun i => ?_⟩
  exact polygonSignedMenger_eq_neg_inv_radius_of_concyclic_neg hsimple hR hdist i (hcross i)

/-- Profile form: on a concyclic polygon, a positively oriented noncollinear
vertex has signed Menger curvature equal to the reciprocal of the common
radius. -/
theorem signedMengerProfile_eq_inv_radius_of_concyclic_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    {O : ℂ} {R : ℝ} (hR : 0 < R) (hdist : ∀ i, dist O (v i) = R)
    (i : ZMod n)
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    SignedMengerProfile v i = 1 / R := by
  exact polygonSignedMenger_eq_inv_radius_of_concyclic_pos hsimple hR hdist i hcross

/-- Profile form: on a concyclic polygon, a negatively oriented noncollinear
vertex has signed Menger curvature equal to minus the reciprocal of the common
radius. -/
theorem signedMengerProfile_eq_neg_inv_radius_of_concyclic_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    {O : ℂ} {R : ℝ} (hR : 0 < R) (hdist : ∀ i, dist O (v i) = R)
    (i : ZMod n)
    (hcross : Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    SignedMengerProfile v i = -(1 / R) := by
  exact polygonSignedMenger_eq_neg_inv_radius_of_concyclic_neg hsimple hR hdist i hcross

/-- A consistently positively oriented concyclic simple polygon has constant
signed-Menger profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (hcross : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact exists_constant_signedMenger_of_concyclic_pos hsimple hcyc hcross

/-- A consistently negatively oriented concyclic simple polygon has constant
signed-Menger profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (hcross : ∀ i, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact exists_constant_signedMenger_of_concyclic_neg hsimple hcyc hcross

/-- A positively oriented concyclic simple polygon has constant signed-Menger
profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v) (horient : PositivePolygonOrientation v) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact exists_constant_signedMengerProfile_of_concyclic_pos hsimple hcyc horient

/-- A negatively oriented concyclic simple polygon has constant signed-Menger
profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v) (horient : NegativePolygonOrientation v) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact exists_constant_signedMengerProfile_of_concyclic_neg hsimple hcyc horient

/-- A strictly oriented concyclic simple polygon has constant signed-Menger
profile. -/
theorem exists_constant_signedMengerProfile_of_concyclic_strict_orientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hcyc : Concyclic v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  rcases horient with hpos | hneg
  · exact exists_constant_signedMengerProfile_of_concyclic_positiveOrientation
      hsimple hcyc hpos
  · exact exists_constant_signedMengerProfile_of_concyclic_negativeOrientation
      hsimple hcyc hneg

/-- For a simple locally regular strictly oriented polygon, concyclicity is
equivalent to constancy of the signed-Menger profile. -/
theorem concyclic_iff_exists_constant_signedMengerProfile_strict_orientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    Concyclic v ↔ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  constructor
  · intro hcyc
    exact exists_constant_signedMengerProfile_of_concyclic_strict_orientation
      hsimple hcyc horient
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro hczero
      have hzero : ∀ i : ZMod n, SignedMengerProfile v i = 0 := by
        intro i
        rw [hc i, hczero]
      exact not_constant_signedMengerProfile_zero_of_isSimplePolygon
        hsimple hregular hzero
    exact concyclic_of_constant_signedMengerProfile_ne_zero hsimple hregular hc hc0

/-- For a simple locally regular strictly oriented polygon, nonconcyclicity is
equivalent to nonconstancy of the signed-Menger profile. -/
theorem not_concyclic_iff_not_constant_signedMengerProfile_strict_orientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    (¬ Concyclic v) ↔ ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  constructor
  · intro hnoncircle
    exact not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle
  · intro hnc hcyc
    exact hnc
      (exists_constant_signedMengerProfile_of_concyclic_strict_orientation
        hsimple hcyc horient)

/-- Under consistent positive orientation, a nonconstant signed-Menger profile
rules out concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (hcross : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ¬ Concyclic v := by
  intro hcyc
  exact hnc (exists_constant_signedMengerProfile_of_concyclic_pos hsimple hcyc hcross)

/-- Under consistent negative orientation, a nonconstant signed-Menger profile
rules out concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (hcross : ∀ i, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    ¬ Concyclic v := by
  intro hcyc
  exact hnc (exists_constant_signedMengerProfile_of_concyclic_neg hsimple hcyc hcross)

/-- Under positive orientation, a nonconstant signed-Menger profile rules out
concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (horient : PositivePolygonOrientation v) :
    ¬ Concyclic v := by
  exact not_concyclic_of_not_constant_signedMengerProfile_pos hsimple hnc horient

/-- Under negative orientation, a nonconstant signed-Menger profile rules out
concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (horient : NegativePolygonOrientation v) :
    ¬ Concyclic v := by
  exact not_concyclic_of_not_constant_signedMengerProfile_neg hsimple hnc horient

/-- Under either strict orientation, a nonconstant signed-Menger profile rules
out concyclicity. -/
theorem not_concyclic_of_not_constant_signedMengerProfile_strict_orientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    ¬ Concyclic v := by
  intro hcyc
  exact hnc
    (exists_constant_signedMengerProfile_of_concyclic_strict_orientation
      hsimple hcyc horient)

/-- Dahlberg's four-vertex conclusion makes the signed-Menger profile
nonconstant. -/
theorem not_constant_signedMengerProfile_of_dahlbergFourVertex {n : ℕ}
    {v : ZMod n → ℂ} (hfv : DahlbergFourVertex (SignedMengerProfile v)) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_of_dahlbergFourVertex hfv

/-- Under consistent positive orientation, Dahlberg's four-vertex conclusion
rules out concyclicity. -/
theorem not_concyclic_of_dahlbergFourVertex_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v))
    (hcross : ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ¬ Concyclic v := by
  exact not_concyclic_of_not_constant_signedMengerProfile_pos hsimple
    (not_constant_signedMengerProfile_of_dahlbergFourVertex hfv) hcross

/-- Under consistent negative orientation, Dahlberg's four-vertex conclusion
rules out concyclicity. -/
theorem not_concyclic_of_dahlbergFourVertex_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v))
    (hcross : ∀ i, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0) :
    ¬ Concyclic v := by
  exact not_concyclic_of_not_constant_signedMengerProfile_neg hsimple
    (not_constant_signedMengerProfile_of_dahlbergFourVertex hfv) hcross

/-- Under positive orientation, Dahlberg's four-vertex conclusion rules out
concyclicity. -/
theorem not_concyclic_of_dahlbergFourVertex_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v))
    (horient : PositivePolygonOrientation v) :
    ¬ Concyclic v := by
  exact not_concyclic_of_dahlbergFourVertex_pos hsimple hfv horient

/-- Under negative orientation, Dahlberg's four-vertex conclusion rules out
concyclicity. -/
theorem not_concyclic_of_dahlbergFourVertex_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v))
    (horient : NegativePolygonOrientation v) :
    ¬ Concyclic v := by
  exact not_concyclic_of_dahlbergFourVertex_neg hsimple hfv horient

/-- Under either strict orientation, Dahlberg's four-vertex conclusion rules
out concyclicity. -/
theorem not_concyclic_of_dahlbergFourVertex_strict_orientation {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v))
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v) :
    ¬ Concyclic v := by
  rcases horient with hpos | hneg
  · exact not_concyclic_of_dahlbergFourVertex_positiveOrientation hsimple hfv hpos
  · exact not_concyclic_of_dahlbergFourVertex_negativeOrientation hsimple hfv hneg

/-! ## Signed-Menger signs and polygon orientation -/

/-- Positive polygon orientation is exactly pointwise positivity of the signed-Menger profile. -/
theorem positivePolygonOrientation_iff_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} :
    PositivePolygonOrientation v ↔ ∀ i : ZMod n, 0 < SignedMengerProfile v i := by
  constructor
  · intro h i
    exact Gluck.Discrete.signedMengerR2_pos_iff_crossR2_pos.mpr (h i)
  · intro h i
    exact Gluck.Discrete.signedMengerR2_pos_iff_crossR2_pos.mp (h i)

/-- Negative polygon orientation is exactly pointwise negativity of the signed-Menger profile. -/
theorem negativePolygonOrientation_iff_signedMengerProfile_neg {n : ℕ}
    {v : ZMod n → ℂ} :
    NegativePolygonOrientation v ↔ ∀ i : ZMod n, SignedMengerProfile v i < 0 := by
  constructor
  · intro h i
    exact Gluck.Discrete.signedMengerR2_neg_iff_crossR2_neg.mpr (h i)
  · intro h i
    exact Gluck.Discrete.signedMengerR2_neg_iff_crossR2_neg.mp (h i)

/-- Positive polygon orientation gives pointwise positive signed-Menger
profile. -/
theorem signedMengerProfile_pos_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (_hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) :
    ∀ i : ZMod n, 0 < SignedMengerProfile v i := by
  exact positivePolygonOrientation_iff_signedMengerProfile_pos.mp horient

/-- Negative polygon orientation gives pointwise negative signed-Menger
profile. -/
theorem signedMengerProfile_neg_of_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (_hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : NegativePolygonOrientation v) :
    ∀ i : ZMod n, SignedMengerProfile v i < 0 := by
  exact negativePolygonOrientation_iff_signedMengerProfile_neg.mp horient

/-- Positive-orientation strict adjacent-turn radius comparison along one
oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictAnti_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hκ : SignedMengerProfile v i < SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  exact signedMengerProfile_edgeCircleRadius_strictAnti_of_endpoint_order_pos
    hsimple hregular i
    (signedMengerProfile_pos_of_positiveOrientation hsimple horient i)
    hκ

/-- Positive-orientation reverse strict adjacent-turn radius comparison along
one oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictAnti_rev_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hκ : SignedMengerProfile v (i + 1) < SignedMengerProfile v i) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  exact signedMengerProfile_edgeCircleRadius_strictAnti_rev_of_endpoint_order_pos
    hsimple hregular i
    (signedMengerProfile_pos_of_positiveOrientation hsimple horient (i + 1))
    hκ

/-- Positive-orientation converse: a strict radius drop over the edge
`i → i+1` gives a strict adjacent signed-Menger increase. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (horient : PositivePolygonOrientation v)
    (i : ZMod n)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))) :
    SignedMengerProfile v i < SignedMengerProfile v (i + 1) := by
  exact signedMengerProfile_lt_of_edgeCircleRadius_lt_pos hsimple i
    (polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient i))
    (by simpa [sub_eq_add_neg, add_assoc] using horient (i + 1))
    hR

/-- Positive-orientation reverse converse: a strict radius drop in the reverse
adjacent direction gives a strict adjacent signed-Menger decrease. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_positiveOrientation_rev
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (horient : PositivePolygonOrientation v)
    (i : ZMod n)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))) :
    SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_lt_of_edgeCircleRadius_lt_pos_rev hsimple i
    (polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient i))
    (by simpa [sub_eq_add_neg, add_assoc] using horient (i + 1))
    hR

/-- Negative-orientation strict adjacent-turn radius comparison along one
oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictMono_of_negativeOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (i : ZMod n)
    (hκ : SignedMengerProfile v i < SignedMengerProfile v (i + 1)) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) := by
  have hneg := signedMengerProfile_neg_of_negativeOrientation hsimple horient
  exact signedMengerProfile_edgeCircleRadius_strictMono_of_endpoint_order_neg
    hsimple hregular i (hneg i) (hneg (i + 1)) hκ

/-- Negative-orientation reverse strict adjacent-turn radius comparison along
one oriented edge. -/
theorem signedMengerProfile_edgeCircleRadius_strictMono_rev_of_negativeOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (i : ZMod n)
    (hκ : SignedMengerProfile v (i + 1) < SignedMengerProfile v i) :
    normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
  have hneg := signedMengerProfile_neg_of_negativeOrientation hsimple horient
  exact signedMengerProfile_edgeCircleRadius_strictMono_rev_of_endpoint_order_neg
    hsimple hregular i (hneg i) (hneg (i + 1)) hκ

/-- Negative-orientation converse: a strict radius increase over the edge
`i → i+1` gives a strict adjacent signed-Menger increase. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_negativeOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (horient : NegativePolygonOrientation v)
    (i : ZMod n)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))) :
    SignedMengerProfile v i < SignedMengerProfile v (i + 1) := by
  exact signedMengerProfile_lt_of_edgeCircleRadius_lt_neg hsimple i
    (polygonEdgePrev_cross_neg_of_vertex_cross_neg (horient i))
    (by simpa [sub_eq_add_neg, add_assoc] using horient (i + 1))
    hR

/-- Negative-orientation reverse converse: a strict radius drop in the reverse
adjacent direction gives a strict adjacent signed-Menger decrease. -/
theorem signedMengerProfile_lt_of_edgeCircleRadius_lt_negativeOrientation_rev
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (horient : NegativePolygonOrientation v)
    (i : ZMod n)
    (hR : normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1))) <
      normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))) :
    SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_lt_of_edgeCircleRadius_lt_neg_rev hsimple i
    (polygonEdgePrev_cross_neg_of_vertex_cross_neg (horient i))
    (by simpa [sub_eq_add_neg, add_assoc] using horient (i + 1))
    hR

/-- Pointwise positive signed-Menger profile forces positive polygon
orientation. -/
theorem positiveOrientation_of_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} (_hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, 0 < SignedMengerProfile v i) :
    PositivePolygonOrientation v := by
  exact positivePolygonOrientation_iff_signedMengerProfile_pos.mpr hκ

/-- Pointwise negative signed-Menger profile forces negative polygon
orientation. -/
theorem negativeOrientation_of_signedMengerProfile_neg {n : ℕ}
    {v : ZMod n → ℂ} (_hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i < 0) :
    NegativePolygonOrientation v := by
  exact negativePolygonOrientation_iff_signedMengerProfile_neg.mpr hκ

/-! ## Same-sign nonconcyclic profiles -/

/-- Positive orientation version of the constant-profile contrapositive:
a nonconcyclic locally regular simple polygon has nonconstant signed-Menger
profile. -/
theorem not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_signedMengerProfile_of_not_concyclic_pos hsimple hregular
    (signedMengerProfile_pos_of_positiveOrientation hsimple horient) hnoncircle

/-- Negative orientation version of the constant-profile contrapositive:
a nonconcyclic locally regular simple polygon has nonconstant signed-Menger
profile. -/
theorem not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_signedMengerProfile_of_not_concyclic_neg hsimple hregular
    (signedMengerProfile_neg_of_negativeOrientation hsimple horient) hnoncircle

/-! ## Oriented regular vertices are genuine circle vertices -/

/-- Positive orientation forces each Dahlberg-regular vertex into the genuine
circle/cone branch. -/
theorem dahlbergRegular_circle_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v (i - 1)) (v i) (v (i + 1)) O R ∧
        InVertexCone (v (i - 1)) (v i) (v (i + 1)) O := by
  exact dahlbergRegularAt_circle_of_cross_ne_zero_right (hregular i) (horient i).ne'

/-- Negative orientation also forces each Dahlberg-regular vertex into the
genuine circle/cone branch. -/
theorem dahlbergRegular_circle_of_negativeOrientation {n : ℕ}
    {v : ZMod n → ℂ} (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v (i - 1)) (v i) (v (i + 1)) O R ∧
        InVertexCone (v (i - 1)) (v i) (v (i + 1)) O := by
  exact dahlbergRegularAt_circle_of_cross_ne_zero_right (hregular i) (horient i).ne

/-- Pointwise positive signed-Menger profile turns Dahlberg regularity into
genuine circle/cone data at every vertex. -/
theorem dahlbergRegular_circle_of_signedMengerProfile_pos {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, 0 < SignedMengerProfile v i) (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v (i - 1)) (v i) (v (i + 1)) O R ∧
        InVertexCone (v (i - 1)) (v i) (v (i + 1)) O := by
  exact dahlbergRegular_circle_of_positiveOrientation hregular
    (positiveOrientation_of_signedMengerProfile_pos hsimple hκ) i

/-- Pointwise negative signed-Menger profile turns Dahlberg regularity into
genuine circle/cone data at every vertex. -/
theorem dahlbergRegular_circle_of_signedMengerProfile_neg {n : ℕ}
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hκ : ∀ i : ZMod n, SignedMengerProfile v i < 0) (i : ZMod n) :
    ∃ O R,
      CircumcircleR2 (v (i - 1)) (v i) (v (i + 1)) O R ∧
        InVertexCone (v (i - 1)) (v i) (v (i + 1)) O := by
  exact dahlbergRegular_circle_of_negativeOrientation hregular
    (negativeOrientation_of_signedMengerProfile_neg hsimple hκ) i

/-! ## Signed-Menger profiles and discrete realizability -/

/-- A simple polygon realizes its own signed-Menger profile. -/
theorem realizesMenger_signedMengerProfile {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    Gluck.Discrete.RealizesMenger (SignedMengerProfile v) := by
  exact ⟨v, hsimple, fun i => rfl⟩

/-- If a simple polygon has signed-Menger profile `κ`, then it realizes `κ` in
the project-local Menger sense. -/
theorem realizesMenger_of_signedMengerProfile_eq {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} {κ : ZMod n → ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hκ : SignedMengerProfile v = κ) :
    Gluck.Discrete.RealizesMenger κ := by
  subst hκ
  exact realizesMenger_signedMengerProfile hsimple

/-- Menger realizability is equivalently realization by the named
signed-Menger profile of a simple polygon. -/
theorem realizesMenger_iff_exists_signedMengerProfile_eq {n : ℕ} [NeZero n]
    {κ : ZMod n → ℝ} :
    Gluck.Discrete.RealizesMenger κ ↔
      ∃ v : ZMod n → ℂ, Gluck.Discrete.IsSimplePolygon v ∧
        SignedMengerProfile v = κ := by
  constructor
  · intro h
    rcases h with ⟨v, hsimple, hκ⟩
    refine ⟨v, hsimple, ?_⟩
    funext i
    exact hκ i
  · rintro ⟨v, hsimple, hκ⟩
    exact realizesMenger_of_signedMengerProfile_eq hsimple hκ

/-! ## Finite cyclic signed-Menger profile API -/

/-- A nonconstant polygon signed-Menger profile has both a strict adjacent
increase and a strict adjacent decrease. -/
theorem signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact exists_adjacent_increase_and_decrease_of_not_constant
    (κ := SignedMengerProfile v) hnc

/-- A nonconstant signed-Menger profile has a global minimum and maximum with
strictly separated values. -/
theorem signedMengerProfile_exists_globalMinMax_strict_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact exists_globalMinMax_strict_of_not_constant (κ := SignedMengerProfile v) hnc

/-- A chosen global maximum of a nonconstant signed-Menger profile is a
plateau-aware local maximum. -/
theorem signedMengerProfile_discreteLocalMax_of_globalMax_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hmax : ∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    DiscreteLocalMax (SignedMengerProfile v) i := by
  exact discreteLocalMax_of_globalMax_of_not_constant
    (κ := SignedMengerProfile v) hmax hnc

/-- A chosen global minimum of a nonconstant signed-Menger profile is a
plateau-aware local minimum. -/
theorem signedMengerProfile_discreteLocalMin_of_globalMin_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hmin : ∀ j : ZMod n, SignedMengerProfile v i ≤ SignedMengerProfile v j)
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    DiscreteLocalMin (SignedMengerProfile v) i := by
  exact discreteLocalMin_of_globalMin_of_not_constant
    (κ := SignedMengerProfile v) hmin hnc

/-- A nonconstant signed-Menger profile has global minimum and maximum
witnesses which are also plateau-aware local extrema at the same indices. -/
theorem signedMengerProfile_exists_globalMinMax_localExtrema_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ ∧
      DiscreteLocalMin (SignedMengerProfile v) i₀ ∧
      DiscreteLocalMax (SignedMengerProfile v) i₁ := by
  exact exists_globalMinMax_localExtrema_of_not_constant
    (κ := SignedMengerProfile v) hnc

/-- A nonconstant signed-Menger profile has both a plateau-aware local maximum
and a plateau-aware local minimum. -/
theorem signedMengerProfile_exists_discreteLocalMax_and_min_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) :
    (∃ imax : ZMod n, DiscreteLocalMax (SignedMengerProfile v) imax) ∧
      ∃ imin : ZMod n, DiscreteLocalMin (SignedMengerProfile v) imin := by
  exact exists_discreteLocalMax_and_min_of_not_constant
    (κ := SignedMengerProfile v) hnc

/-- A signed-Menger profile with no adjacent plateau has both a plateau-aware
local maximum and a plateau-aware local minimum. -/
theorem signedMengerProfile_exists_discreteLocalMax_and_min_of_forall_ne_succ
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) {v : ZMod n → ℂ}
    (hne : ∀ i : ZMod n,
      SignedMengerProfile v i ≠ SignedMengerProfile v (i + 1)) :
    (∃ imax : ZMod n, DiscreteLocalMax (SignedMengerProfile v) imax) ∧
      ∃ imin : ZMod n, DiscreteLocalMin (SignedMengerProfile v) imin := by
  exact exists_discreteLocalMax_and_min_of_forall_ne_succ
    (κ := SignedMengerProfile v) hn hne

/-- A no-plateau signed-Menger profile has explicit strict one-step global
peak and valley witnesses. -/
theorem signedMengerProfile_exists_strict_neighbor_peak_and_valley_of_forall_ne_succ
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hne : ∀ i : ZMod n,
      SignedMengerProfile v i ≠ SignedMengerProfile v (i + 1)) :
    ∃ imax imin : ZMod n,
      (SignedMengerProfile v (imax - 1) < SignedMengerProfile v imax ∧
          SignedMengerProfile v (imax + 1) < SignedMengerProfile v imax) ∧
        (SignedMengerProfile v imin < SignedMengerProfile v (imin - 1) ∧
          SignedMengerProfile v imin < SignedMengerProfile v (imin + 1)) := by
  exact exists_strict_neighbor_peak_and_valley_of_forall_ne_succ
    (κ := SignedMengerProfile v) hne

/-- A nonconcyclic locally regular simple polygon has both an adjacent strict
increase and an adjacent strict decrease. -/
theorem signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A nonconcyclic locally regular simple polygon has strictly separated
global minimum and maximum signed-Menger values. -/
theorem signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A chosen global maximum of a nonconcyclic locally regular simple polygon's
signed-Menger profile is a plateau-aware local maximum. -/
theorem signedMengerProfile_discreteLocalMax_of_globalMax_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hmax : ∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i) :
    DiscreteLocalMax (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMax_of_globalMax_of_not_constant hmax
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A chosen global minimum of a nonconcyclic locally regular simple polygon's
signed-Menger profile is a plateau-aware local minimum. -/
theorem signedMengerProfile_discreteLocalMin_of_globalMin_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hmin : ∀ j : ZMod n, SignedMengerProfile v i ≤ SignedMengerProfile v j) :
    DiscreteLocalMin (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMin_of_globalMin_of_not_constant hmin
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A nonconcyclic locally regular simple polygon has global signed-Menger
minimum and maximum witnesses which are also plateau-aware local extrema at
the same indices. -/
theorem signedMengerProfile_exists_globalMinMax_localExtrema_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ ∧
      DiscreteLocalMin (SignedMengerProfile v) i₀ ∧
      DiscreteLocalMax (SignedMengerProfile v) i₁ := by
  exact signedMengerProfile_exists_globalMinMax_localExtrema_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A nonconcyclic locally regular simple polygon has at least one
plateau-aware local maximum and one plateau-aware local minimum of signed
Menger curvature. -/
theorem signedMengerProfile_exists_discreteLocalMax_and_min_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    (∃ imax : ZMod n, DiscreteLocalMax (SignedMengerProfile v) imax) ∧
      ∃ imin : ZMod n, DiscreteLocalMin (SignedMengerProfile v) imin := by
  exact signedMengerProfile_exists_discreteLocalMax_and_min_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic hsimple hregular hnoncircle)

/-- A nonconcyclic locally regular simple polygon with at least one nonzero
signed-Menger value has both an adjacent strict increase and an adjacent
strict decrease. -/
theorem signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic_of_exists_ne_zero
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hne : ∃ i : ZMod n, SignedMengerProfile v i ≠ 0) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_of_exists_ne_zero
      hsimple hregular hnoncircle hne)

/-- A nonconcyclic locally regular simple polygon with at least one nonzero
signed-Menger value has strictly separated global minimum and maximum
signed-Menger values. -/
theorem signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic_of_exists_ne_zero
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v)
    (hne : ∃ i : ZMod n, SignedMengerProfile v i ≠ 0) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_of_exists_ne_zero
      hsimple hregular hnoncircle hne)

/-- A positive-orientation nonconcyclic locally regular simple polygon has
both an adjacent strict increase and an adjacent strict decrease of signed
Menger curvature. -/
theorem signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- A negative-orientation nonconcyclic locally regular simple polygon has
both an adjacent strict increase and an adjacent strict decrease of signed
Menger curvature. -/
theorem signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    (∃ i : ZMod n, SignedMengerProfile v i < SignedMengerProfile v (i + 1)) ∧
      ∃ i : ZMod n, SignedMengerProfile v (i + 1) < SignedMengerProfile v i := by
  exact signedMengerProfile_exists_adjacent_increase_and_decrease_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
      hsimple hregular horient hnoncircle)

/-- A positive-orientation nonconcyclic locally regular simple polygon has
strictly separated global minimum and maximum signed-Menger values. -/
theorem signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- A chosen global maximum of a positive-orientation nonconcyclic locally
regular simple polygon's signed-Menger profile is a plateau-aware local
maximum. -/
theorem signedMengerProfile_discreteLocalMax_of_globalMax_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v)
    (hmax : ∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i) :
    DiscreteLocalMax (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMax_of_globalMax_of_not_constant hmax
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- A chosen global minimum of a positive-orientation nonconcyclic locally
regular simple polygon's signed-Menger profile is a plateau-aware local
minimum. -/
theorem signedMengerProfile_discreteLocalMin_of_globalMin_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v)
    (hmin : ∀ j : ZMod n, SignedMengerProfile v i ≤ SignedMengerProfile v j) :
    DiscreteLocalMin (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMin_of_globalMin_of_not_constant hmin
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- A positive-orientation nonconcyclic locally regular simple polygon has
global signed-Menger minimum and maximum witnesses which are also
plateau-aware local extrema at the same indices. -/
theorem signedMengerProfile_exists_globalMinMax_localExtrema_of_not_concyclic_pos
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ ∧
      DiscreteLocalMin (SignedMengerProfile v) i₀ ∧
      DiscreteLocalMax (SignedMengerProfile v) i₁ := by
  exact signedMengerProfile_exists_globalMinMax_localExtrema_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- A negative-orientation nonconcyclic locally regular simple polygon has
strictly separated global minimum and maximum signed-Menger values. -/
theorem signedMengerProfile_exists_globalMinMax_strict_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ := by
  exact signedMengerProfile_exists_globalMinMax_strict_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
      hsimple hregular horient hnoncircle)

/-- A chosen global maximum of a negative-orientation nonconcyclic locally
regular simple polygon's signed-Menger profile is a plateau-aware local
maximum. -/
theorem signedMengerProfile_discreteLocalMax_of_globalMax_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v)
    (hmax : ∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i) :
    DiscreteLocalMax (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMax_of_globalMax_of_not_constant hmax
    (not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
      hsimple hregular horient hnoncircle)

/-- A chosen global minimum of a negative-orientation nonconcyclic locally
regular simple polygon's signed-Menger profile is a plateau-aware local
minimum. -/
theorem signedMengerProfile_discreteLocalMin_of_globalMin_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {i : ZMod n}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v)
    (hmin : ∀ j : ZMod n, SignedMengerProfile v i ≤ SignedMengerProfile v j) :
    DiscreteLocalMin (SignedMengerProfile v) i := by
  exact signedMengerProfile_discreteLocalMin_of_globalMin_of_not_constant hmin
    (not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
      hsimple hregular horient hnoncircle)

/-- A negative-orientation nonconcyclic locally regular simple polygon has
global signed-Menger minimum and maximum witnesses which are also
plateau-aware local extrema at the same indices. -/
theorem signedMengerProfile_exists_globalMinMax_localExtrema_of_not_concyclic_neg
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v) (hnoncircle : ¬ Concyclic v) :
    ∃ i₀ i₁ : ZMod n,
      (∀ j : ZMod n, SignedMengerProfile v i₀ ≤ SignedMengerProfile v j) ∧
      (∀ j : ZMod n, SignedMengerProfile v j ≤ SignedMengerProfile v i₁) ∧
      SignedMengerProfile v i₀ < SignedMengerProfile v i₁ ∧
      DiscreteLocalMin (SignedMengerProfile v) i₀ ∧
      DiscreteLocalMax (SignedMengerProfile v) i₁ := by
  exact signedMengerProfile_exists_globalMinMax_localExtrema_of_not_constant
    (not_constant_signedMengerProfile_of_not_concyclic_negativeOrientation
      hsimple hregular horient hnoncircle)

/-- A nonconstant polygon signed-Menger profile has both a strict adjacent
increase and a strict adjacent decrease. -/
theorem polygonSignedMenger_exists_adjacent_increase_and_decrease_of_not_constant
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hnc : ¬ ∃ c, ∀ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = c) :
    (∃ i : ZMod n,
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) <
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1))) ∧
      ∃ i : ZMod n,
        Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i + 1 + 1)) <
          Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) := by
  simpa [sub_eq_add_neg, add_assoc] using
    (exists_adjacent_increase_and_decrease_of_not_constant
      (κ := fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) hnc)

/-- Profile-level constructor for Dahlberg's conclusion from four ordered
strict one-step signed-Menger extrema. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_neighbors {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmax₁_left : SignedMengerProfile v ((i₁ : ZMod n) - 1) <
      SignedMengerProfile v (i₁ : ZMod n))
    (hmax₁_right : SignedMengerProfile v ((i₁ : ZMod n) + 1) <
      SignedMengerProfile v (i₁ : ZMod n))
    (hmin₂_left : SignedMengerProfile v (i₂ : ZMod n) <
      SignedMengerProfile v ((i₂ : ZMod n) - 1))
    (hmin₂_right : SignedMengerProfile v (i₂ : ZMod n) <
      SignedMengerProfile v ((i₂ : ZMod n) + 1))
    (hmax₃_left : SignedMengerProfile v ((i₃ : ZMod n) - 1) <
      SignedMengerProfile v (i₃ : ZMod n))
    (hmax₃_right : SignedMengerProfile v ((i₃ : ZMod n) + 1) <
      SignedMengerProfile v (i₃ : ZMod n))
    (hmin₄_left : SignedMengerProfile v (i₄ : ZMod n) <
      SignedMengerProfile v ((i₄ : ZMod n) - 1))
    (hmin₄_right : SignedMengerProfile v (i₄ : ZMod n) <
      SignedMengerProfile v ((i₄ : ZMod n) + 1)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_strict_neighbors hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmax₁_left hmax₁_right hmin₂_left hmin₂_right
    hmax₃_left hmax₃_right hmin₄_left hmin₄_right

/-- Profile-level constructor for Dahlberg's conclusion from four ordered
strict one-step signed-Menger extrema in `min-max-min-max` order. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_neighbors_min_max {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁_left : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) - 1))
    (hmin₁_right : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hmax₂_left : SignedMengerProfile v ((i₂ : ZMod n) - 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hmax₂_right : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hmin₃_left : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) - 1))
    (hmin₃_right : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hmax₄_left : SignedMengerProfile v ((i₄ : ZMod n) - 1) <
      SignedMengerProfile v (i₄ : ZMod n))
    (hmax₄_right : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (i₄ : ZMod n)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_strict_neighbors_min_max hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmin₁_left hmin₁_right hmax₂_left hmax₂_right
    hmin₃_left hmin₃_right hmax₄_left hmax₄_right

/-- Profile-level strict-extrema constructor using Dahlberg's polygon-size
hypothesis directly. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_neighbors_four_le {n : ℕ}
    (hn : 4 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmax₁_left : SignedMengerProfile v ((i₁ : ZMod n) - 1) <
      SignedMengerProfile v (i₁ : ZMod n))
    (hmax₁_right : SignedMengerProfile v ((i₁ : ZMod n) + 1) <
      SignedMengerProfile v (i₁ : ZMod n))
    (hmin₂_left : SignedMengerProfile v (i₂ : ZMod n) <
      SignedMengerProfile v ((i₂ : ZMod n) - 1))
    (hmin₂_right : SignedMengerProfile v (i₂ : ZMod n) <
      SignedMengerProfile v ((i₂ : ZMod n) + 1))
    (hmax₃_left : SignedMengerProfile v ((i₃ : ZMod n) - 1) <
      SignedMengerProfile v (i₃ : ZMod n))
    (hmax₃_right : SignedMengerProfile v ((i₃ : ZMod n) + 1) <
      SignedMengerProfile v (i₃ : ZMod n))
    (hmin₄_left : SignedMengerProfile v (i₄ : ZMod n) <
      SignedMengerProfile v ((i₄ : ZMod n) - 1))
    (hmin₄_right : SignedMengerProfile v (i₄ : ZMod n) <
      SignedMengerProfile v ((i₄ : ZMod n) + 1)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_strict_neighbors
    (two_le_of_four_le hn) hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmax₁_left hmax₁_right hmin₂_left hmin₂_right
    hmax₃_left hmax₃_right hmin₄_left hmin₄_right

/-- Profile-level `min-max-min-max` strict-extrema constructor using
Dahlberg's polygon-size hypothesis directly. -/
theorem signedMengerProfile_dahlbergFourVertex_of_strict_neighbors_min_max_four_le
    {n : ℕ} (hn : 4 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁_left : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) - 1))
    (hmin₁_right : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hmax₂_left : SignedMengerProfile v ((i₂ : ZMod n) - 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hmax₂_right : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hmin₃_left : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) - 1))
    (hmin₃_right : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hmax₄_left : SignedMengerProfile v ((i₄ : ZMod n) - 1) <
      SignedMengerProfile v (i₄ : ZMod n))
    (hmax₄_right : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (i₄ : ZMod n)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_strict_neighbors_min_max
    (two_le_of_four_le hn) hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmin₁_left hmin₁_right hmax₂_left hmax₂_right
    hmin₃_left hmin₃_right hmax₄_left hmax₄_right

/-- Profile-level constructor from four ordered adjacent signed-Menger turns,
alternating peak/valley/peak/valley. -/
theorem signedMengerProfile_dahlbergFourVertex_of_ordered_turns {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hinc₁ : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hdec₁ : SignedMengerProfile v (((i₁ : ZMod n) + 1) + 1) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hdec₂ : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hinc₂ : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (((i₂ : ZMod n) + 1) + 1))
    (hinc₃ : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hdec₃ : SignedMengerProfile v (((i₃ : ZMod n) + 1) + 1) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hdec₄ : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (i₄ : ZMod n))
    (hinc₄ : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (((i₄ : ZMod n) + 1) + 1)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_ordered_turns hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hinc₁ hdec₁ hdec₂ hinc₂ hinc₃ hdec₃ hdec₄ hinc₄

/-- Profile-level adjacent-turn constructor using Dahlberg's polygon-size
hypothesis directly. -/
theorem signedMengerProfile_dahlbergFourVertex_of_ordered_turns_four_le {n : ℕ}
    (hn : 4 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hinc₁ : SignedMengerProfile v (i₁ : ZMod n) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hdec₁ : SignedMengerProfile v (((i₁ : ZMod n) + 1) + 1) <
      SignedMengerProfile v ((i₁ : ZMod n) + 1))
    (hdec₂ : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (i₂ : ZMod n))
    (hinc₂ : SignedMengerProfile v ((i₂ : ZMod n) + 1) <
      SignedMengerProfile v (((i₂ : ZMod n) + 1) + 1))
    (hinc₃ : SignedMengerProfile v (i₃ : ZMod n) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hdec₃ : SignedMengerProfile v (((i₃ : ZMod n) + 1) + 1) <
      SignedMengerProfile v ((i₃ : ZMod n) + 1))
    (hdec₄ : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (i₄ : ZMod n))
    (hinc₄ : SignedMengerProfile v ((i₄ : ZMod n) + 1) <
      SignedMengerProfile v (((i₄ : ZMod n) + 1) + 1)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact signedMengerProfile_dahlbergFourVertex_of_ordered_turns
    (two_le_of_four_le hn) hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hinc₁ hdec₁ hdec₂ hinc₂ hinc₃ hdec₃ hdec₄ hinc₄

/-- Polygon-facing constructor for Dahlberg's conclusion from four ordered
strict one-step signed-Menger extrema. -/
theorem polygonDahlbergFourVertex_of_strict_signedMenger_neighbors {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmax₁_left :
      Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) - 1) - 1))
          (v ((i₁ : ZMod n) - 1)) (v (((i₁ : ZMod n) - 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₁ : ZMod n) - 1)) (v (i₁ : ZMod n))
          (v ((i₁ : ZMod n) + 1)))
    (hmax₁_right :
      Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) + 1) - 1))
          (v ((i₁ : ZMod n) + 1)) (v (((i₁ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₁ : ZMod n) - 1)) (v (i₁ : ZMod n))
          (v ((i₁ : ZMod n) + 1)))
    (hmin₂_left :
      Gluck.Discrete.signedMengerR2 (v ((i₂ : ZMod n) - 1)) (v (i₂ : ZMod n))
          (v ((i₂ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) - 1) - 1))
          (v ((i₂ : ZMod n) - 1)) (v (((i₂ : ZMod n) - 1) + 1)))
    (hmin₂_right :
      Gluck.Discrete.signedMengerR2 (v ((i₂ : ZMod n) - 1)) (v (i₂ : ZMod n))
          (v ((i₂ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) + 1) - 1))
          (v ((i₂ : ZMod n) + 1)) (v (((i₂ : ZMod n) + 1) + 1)))
    (hmax₃_left :
      Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) - 1) - 1))
          (v ((i₃ : ZMod n) - 1)) (v (((i₃ : ZMod n) - 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₃ : ZMod n) - 1)) (v (i₃ : ZMod n))
          (v ((i₃ : ZMod n) + 1)))
    (hmax₃_right :
      Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) + 1) - 1))
          (v ((i₃ : ZMod n) + 1)) (v (((i₃ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₃ : ZMod n) - 1)) (v (i₃ : ZMod n))
          (v ((i₃ : ZMod n) + 1)))
    (hmin₄_left :
      Gluck.Discrete.signedMengerR2 (v ((i₄ : ZMod n) - 1)) (v (i₄ : ZMod n))
          (v ((i₄ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) - 1) - 1))
          (v ((i₄ : ZMod n) - 1)) (v (((i₄ : ZMod n) - 1) + 1)))
    (hmin₄_right :
      Gluck.Discrete.signedMengerR2 (v ((i₄ : ZMod n) - 1)) (v (i₄ : ZMod n))
          (v ((i₄ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) + 1) - 1))
          (v ((i₄ : ZMod n) + 1)) (v (((i₄ : ZMod n) + 1) + 1))) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  exact dahlbergFourVertex_of_strict_neighbors hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmax₁_left hmax₁_right hmin₂_left hmin₂_right
    hmax₃_left hmax₃_right hmin₄_left hmin₄_right

/-- Polygon-facing constructor for Dahlberg's conclusion from four ordered
strict one-step signed-Menger extrema in `min-max-min-max` order. -/
theorem polygonDahlbergFourVertex_of_strict_signedMenger_neighbors_min_max {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁_left :
      Gluck.Discrete.signedMengerR2 (v ((i₁ : ZMod n) - 1)) (v (i₁ : ZMod n))
          (v ((i₁ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) - 1) - 1))
          (v ((i₁ : ZMod n) - 1)) (v (((i₁ : ZMod n) - 1) + 1)))
    (hmin₁_right :
      Gluck.Discrete.signedMengerR2 (v ((i₁ : ZMod n) - 1)) (v (i₁ : ZMod n))
          (v ((i₁ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) + 1) - 1))
          (v ((i₁ : ZMod n) + 1)) (v (((i₁ : ZMod n) + 1) + 1)))
    (hmax₂_left :
      Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) - 1) - 1))
          (v ((i₂ : ZMod n) - 1)) (v (((i₂ : ZMod n) - 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₂ : ZMod n) - 1)) (v (i₂ : ZMod n))
          (v ((i₂ : ZMod n) + 1)))
    (hmax₂_right :
      Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) + 1) - 1))
          (v ((i₂ : ZMod n) + 1)) (v (((i₂ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₂ : ZMod n) - 1)) (v (i₂ : ZMod n))
          (v ((i₂ : ZMod n) + 1)))
    (hmin₃_left :
      Gluck.Discrete.signedMengerR2 (v ((i₃ : ZMod n) - 1)) (v (i₃ : ZMod n))
          (v ((i₃ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) - 1) - 1))
          (v ((i₃ : ZMod n) - 1)) (v (((i₃ : ZMod n) - 1) + 1)))
    (hmin₃_right :
      Gluck.Discrete.signedMengerR2 (v ((i₃ : ZMod n) - 1)) (v (i₃ : ZMod n))
          (v ((i₃ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) + 1) - 1))
          (v ((i₃ : ZMod n) + 1)) (v (((i₃ : ZMod n) + 1) + 1)))
    (hmax₄_left :
      Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) - 1) - 1))
          (v ((i₄ : ZMod n) - 1)) (v (((i₄ : ZMod n) - 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₄ : ZMod n) - 1)) (v (i₄ : ZMod n))
          (v ((i₄ : ZMod n) + 1)))
    (hmax₄_right :
      Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) + 1) - 1))
          (v ((i₄ : ZMod n) + 1)) (v (((i₄ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₄ : ZMod n) - 1)) (v (i₄ : ZMod n))
          (v ((i₄ : ZMod n) + 1))) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  exact dahlbergFourVertex_of_strict_neighbors_min_max hn hi₁₂ hi₂₃ hi₃₄ hi₄₁
    hmin₁_left hmin₁_right hmax₂_left hmax₂_right
    hmin₃_left hmin₃_right hmax₄_left hmax₄_right

/-- Polygon-facing constructor from four ordered adjacent signed-Menger turns,
alternating peak/valley/peak/valley. -/
theorem polygonDahlbergFourVertex_of_ordered_signedMenger_turns {n : ℕ}
    (hn : 2 ≤ n) {v : ZMod n → ℂ} {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hinc₁ :
      Gluck.Discrete.signedMengerR2 (v ((i₁ : ZMod n) - 1)) (v (i₁ : ZMod n))
          (v ((i₁ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) + 1) - 1))
          (v ((i₁ : ZMod n) + 1)) (v (((i₁ : ZMod n) + 1) + 1)))
    (hdec₁ :
      Gluck.Discrete.signedMengerR2 (v ((((i₁ : ZMod n) + 1) + 1) - 1))
          (v (((i₁ : ZMod n) + 1) + 1)) (v ((((i₁ : ZMod n) + 1) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₁ : ZMod n) + 1) - 1))
          (v ((i₁ : ZMod n) + 1)) (v (((i₁ : ZMod n) + 1) + 1)))
    (hdec₂ :
      Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) + 1) - 1))
          (v ((i₂ : ZMod n) + 1)) (v (((i₂ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₂ : ZMod n) - 1)) (v (i₂ : ZMod n))
          (v ((i₂ : ZMod n) + 1)))
    (hinc₂ :
      Gluck.Discrete.signedMengerR2 (v (((i₂ : ZMod n) + 1) - 1))
          (v ((i₂ : ZMod n) + 1)) (v (((i₂ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((((i₂ : ZMod n) + 1) + 1) - 1))
          (v (((i₂ : ZMod n) + 1) + 1)) (v ((((i₂ : ZMod n) + 1) + 1) + 1)))
    (hinc₃ :
      Gluck.Discrete.signedMengerR2 (v ((i₃ : ZMod n) - 1)) (v (i₃ : ZMod n))
          (v ((i₃ : ZMod n) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) + 1) - 1))
          (v ((i₃ : ZMod n) + 1)) (v (((i₃ : ZMod n) + 1) + 1)))
    (hdec₃ :
      Gluck.Discrete.signedMengerR2 (v ((((i₃ : ZMod n) + 1) + 1) - 1))
          (v (((i₃ : ZMod n) + 1) + 1)) (v ((((i₃ : ZMod n) + 1) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v (((i₃ : ZMod n) + 1) - 1))
          (v ((i₃ : ZMod n) + 1)) (v (((i₃ : ZMod n) + 1) + 1)))
    (hdec₄ :
      Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) + 1) - 1))
          (v ((i₄ : ZMod n) + 1)) (v (((i₄ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((i₄ : ZMod n) - 1)) (v (i₄ : ZMod n))
          (v ((i₄ : ZMod n) + 1)))
    (hinc₄ :
      Gluck.Discrete.signedMengerR2 (v (((i₄ : ZMod n) + 1) - 1))
          (v ((i₄ : ZMod n) + 1)) (v (((i₄ : ZMod n) + 1) + 1)) <
        Gluck.Discrete.signedMengerR2 (v ((((i₄ : ZMod n) + 1) + 1) - 1))
          (v (((i₄ : ZMod n) + 1) + 1)) (v ((((i₄ : ZMod n) + 1) + 1) + 1))) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  change DahlbergFourVertex (SignedMengerProfile v)
  exact signedMengerProfile_dahlbergFourVertex_of_ordered_turns hn
    hi₁₂ hi₂₃ hi₃₄ hi₄₁
    (by simpa [SignedMengerProfile] using hinc₁)
    (by simpa [SignedMengerProfile] using hdec₁)
    (by simpa [SignedMengerProfile] using hdec₂)
    (by simpa [SignedMengerProfile] using hinc₂)
    (by simpa [SignedMengerProfile] using hinc₃)
    (by simpa [SignedMengerProfile] using hdec₃)
    (by simpa [SignedMengerProfile] using hdec₄)
    (by simpa [SignedMengerProfile] using hinc₄)

/-! ## Dahlberg's Euclidean discrete four-vertex kernel -/

/-- Radius of the circle through `v (i-1), v i, v (i+1)`, expressed over the
outgoing edge `v i → v (i+1)`. -/
noncomputable def EdgePrevCircleRadiusProfile {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : ℝ :=
  normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
    (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))

/-- Center of the circle through `v (i-1), v i, v (i+1)`, expressed over the
outgoing edge `v i → v (i+1)`. -/
noncomputable def EdgePrevCircleCenterProfile {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : ℂ :=
  edgeCircleCenter (v i) (v (i + 1))
    (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))

/-- The canonical previous-vertex circle is the circumcircle of the three
adjacent vertices in the positive-orientation branch. -/
theorem edgePrevCircle_circumcircleR2_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    CircumcircleR2 (v (i - 1)) (v i) (v (i + 1))
      (EdgePrevCircleCenterProfile v i) (EdgePrevCircleRadiusProfile v i) := by
  have hcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient i)
  have hcircle :
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1))
        (EdgePrevCircleCenterProfile v i) (EdgePrevCircleRadiusProfile v i) := by
    simpa [EdgePrevCircleCenterProfile, EdgePrevCircleRadiusProfile] using
      (circumcircleR2_edge_parameter (hsimple.1 i) hcross.ne')
  exact ⟨hcircle.1, hcircle.2.2.2, hcircle.2.1, hcircle.2.2.1⟩

/-- The previous defining vertex lies on the previous-vertex curvature
circle. -/
theorem edgePrevCircle_dist_prev_eq_radius_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    dist (EdgePrevCircleCenterProfile v i) (v (i - 1)) =
      EdgePrevCircleRadiusProfile v i := by
  exact (edgePrevCircle_circumcircleR2_of_positiveOrientation hsimple horient i).2.1

/-- The center vertex lies on the previous-vertex curvature circle. -/
theorem edgePrevCircle_dist_self_eq_radius_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    dist (EdgePrevCircleCenterProfile v i) (v i) =
      EdgePrevCircleRadiusProfile v i := by
  exact (edgePrevCircle_circumcircleR2_of_positiveOrientation hsimple horient i).2.2.1

/-- The next defining vertex lies on the previous-vertex curvature circle. -/
theorem edgePrevCircle_dist_next_eq_radius_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    dist (EdgePrevCircleCenterProfile v i) (v (i + 1)) =
      EdgePrevCircleRadiusProfile v i := by
  exact (edgePrevCircle_circumcircleR2_of_positiveOrientation hsimple horient i).2.2.2

/-- The previous-vertex curvature disk contains all vertices.  This is the
Lean-side spelling of Dahlberg's conclusion `V(γ) ⊆ ω(P)`. -/
def EdgePrevCurvatureDiskContainsAll {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : Prop :=
  PolygonInClosedDiskR2 v (EdgePrevCircleCenterProfile v i)
    (EdgePrevCircleRadiusProfile v i)

/-- The previous-vertex curvature disk has no vertex in its interior.  This is
the Lean-side spelling of Dahlberg's conclusion
`Int(ω(P)) ∩ V(γ) = ∅`. -/
def EdgePrevCurvatureDiskInteriorMissesAll {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : Prop :=
  ∀ j : ZMod n, EdgePrevCircleRadiusProfile v i ≤
    dist (EdgePrevCircleCenterProfile v i) (v j)

/-- The centre/radius data of the previous-vertex curvature circle. -/
noncomputable def EdgePrevCurvatureCircleData {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : ℂ × ℝ :=
  (EdgePrevCircleCenterProfile v i, EdgePrevCircleRadiusProfile v i)

/-- Two previous-vertex curvature circles are distinct when their centre/radius
data differ. -/
def EdgePrevCurvatureCirclesDistinct {n : ℕ} (v : ZMod n → ℂ)
    (i j : ZMod n) : Prop :=
  EdgePrevCurvatureCircleData v i ≠ EdgePrevCurvatureCircleData v j

/-- Distinctness of previous-vertex curvature circles is symmetric. -/
theorem EdgePrevCurvatureCirclesDistinct.symm {n : ℕ} {v : ZMod n → ℂ}
    {i j : ZMod n} (h : EdgePrevCurvatureCirclesDistinct v i j) :
    EdgePrevCurvatureCirclesDistinct v j i := by
  intro hji
  exact h hji.symm

/-- A previous-vertex curvature disk that misses all vertex interiors also
contains its own three defining vertices on the boundary. -/
theorem edgePrevCurvatureDiskInteriorMissesAll_self {n : ℕ}
    {v : ZMod n → ℂ} {i : ZMod n}
    (hmiss : EdgePrevCurvatureDiskInteriorMissesAll v i) :
    EdgePrevCircleRadiusProfile v i ≤
      dist (EdgePrevCircleCenterProfile v i) (v i) := by
  exact hmiss i

/-- A previous-vertex curvature disk containing all vertices contains its own
vertex. -/
theorem edgePrevCurvatureDiskContainsAll_self {n : ℕ}
    {v : ZMod n → ℂ} {i : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i) :
    dist (EdgePrevCircleCenterProfile v i) (v i) ≤
      EdgePrevCircleRadiusProfile v i := by
  exact Metric.mem_closedBall'.mp (hcontains i)

/-- In the positive-orientation branch, a previous curvature disk has its
center vertex on the disk boundary. -/
theorem edgePrevCurvatureDisk_self_boundary_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v i)
      (EdgePrevCircleRadiusProfile v i) i := by
  exact Metric.mem_sphere'.mpr
    (edgePrevCircle_dist_self_eq_radius_of_positiveOrientation hsimple horient i)

/-- In the positive-orientation branch, the previous defining vertex of a
curvature disk is on the disk boundary. -/
theorem edgePrevCurvatureDisk_prev_boundary_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v i)
      (EdgePrevCircleRadiusProfile v i) (i - 1) := by
  exact Metric.mem_sphere'.mpr
    (edgePrevCircle_dist_prev_eq_radius_of_positiveOrientation hsimple horient i)

/-- In the positive-orientation branch, the next defining vertex of a
curvature disk is on the disk boundary. -/
theorem edgePrevCurvatureDisk_next_boundary_of_positiveOrientation {n : ℕ}
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v i)
      (EdgePrevCircleRadiusProfile v i) (i + 1) := by
  exact Metric.mem_sphere'.mpr
    (edgePrevCircle_dist_next_eq_radius_of_positiveOrientation hsimple horient i)

/-- Three consecutive positive-turn contacts determine the canonical
previous-vertex curvature-circle data. -/
theorem edgePrevCurvatureCircleData_eq_of_three_boundaries_of_cross_pos
    {n : ℕ} {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (hR : 0 < R)
    {i : ZMod n}
    (hprev : OnDiskBoundaryR2 v O R (i - 1))
    (hself : OnDiskBoundaryR2 v O R i)
    (hnext : OnDiskBoundaryR2 v O R (i + 1))
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    EdgePrevCurvatureCircleData v i = (O, R) := by
  have hcross' : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos hcross
  have hcanonical :
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1))
        (EdgePrevCircleCenterProfile v i) (EdgePrevCircleRadiusProfile v i) := by
    simpa [EdgePrevCircleCenterProfile, EdgePrevCircleRadiusProfile] using
      circumcircleR2_edge_parameter (hsimple.1 i) hcross'.ne'
  have hdisk : CircumcircleR2 (v i) (v (i + 1)) (v (i - 1)) O R :=
    ⟨hR, Metric.mem_sphere'.mp hself, Metric.mem_sphere'.mp hnext,
      Metric.mem_sphere'.mp hprev⟩
  have heq := circumcircleR2_unique_of_noncollinear
    (hsimple.1 i) hcross'.ne' hcanonical hdisk
  exact Prod.ext heq.1 heq.2

/-- If the canonical curvature disk at `i` contains the polygon, its signed
Menger curvature is at most the reciprocal radius of a minimal enclosing
disk. -/
theorem signedMengerProfile_le_inv_minimalRadius_of_curvatureDiskContainsAll
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    {i : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i)
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    SignedMengerProfile v i ≤ 1 / R := by
  have hRpos : 0 < R :=
    radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple
  have hcross' : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos hcross
  have hcanonical :
      CircumcircleR2 (v i) (v (i + 1)) (v (i - 1))
        (EdgePrevCircleCenterProfile v i) (EdgePrevCircleRadiusProfile v i) := by
    simpa [EdgePrevCircleCenterProfile, EdgePrevCircleRadiusProfile] using
      circumcircleR2_edge_parameter (hsimple.1 i) hcross'.ne'
  have hRρ : R ≤ EdgePrevCircleRadiusProfile v i :=
    minimalEnclosingDiskR2_le_of_polygonInClosedDiskR2 hΔ hcanonical.1.le hcontains
  have hAB : v (i - 1) ≠ v i := by
    simpa using hsimple.1 (i - 1)
  have hcircle' :
      CircumcircleR2 (v (i + 1)) (v (i - 1)) (v i)
        (EdgePrevCircleCenterProfile v i) (EdgePrevCircleRadiusProfile v i) :=
    ⟨hcanonical.1, hcanonical.2.2.1, hcanonical.2.2.2, hcanonical.2.1⟩
  have hκ :
      SignedMengerProfile v i = 1 / EdgePrevCircleRadiusProfile v i := by
    simpa [SignedMengerProfile] using
      signedMengerR2_eq_inv_circumradius_of_pos hAB hcross hcircle'
  rw [hκ]
  exact one_div_le_one_div_of_le hRpos hRρ

/-- Three consecutive contacts with a minimal enclosing disk identify the
canonical curvature disk and therefore make it contain every vertex. -/
theorem edgePrevCurvatureDiskContainsAll_of_three_boundaries_of_cross_pos
    {n : ℕ} {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hΔ : MinimalEnclosingDiskR2 v O R)
    {i : ZMod n}
    (hprev : OnDiskBoundaryR2 v O R (i - 1))
    (hself : OnDiskBoundaryR2 v O R i)
    (hnext : OnDiskBoundaryR2 v O R (i + 1))
    (hcross : 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    EdgePrevCurvatureDiskContainsAll v i := by
  have hR : 0 < R := by
    by_contra hRnonpos
    have hRzero : R = 0 := le_antisymm (le_of_not_gt hRnonpos) hΔ.1
    have hdistPrev : dist O (v (i - 1)) = 0 := by
      simpa [hRzero] using Metric.mem_sphere'.mp hprev
    have hdistSelf : dist O (v i) = 0 := by
      simpa [hRzero] using Metric.mem_sphere'.mp hself
    have hprevEq : v (i - 1) = v i :=
      (dist_eq_zero.mp hdistPrev).symm.trans (dist_eq_zero.mp hdistSelf)
    exact (hsimple.1 (i - 1)) (by simpa using hprevEq)
  have hdata := edgePrevCurvatureCircleData_eq_of_three_boundaries_of_cross_pos
    hsimple hR hprev hself hnext hcross
  have hcenter : EdgePrevCircleCenterProfile v i = O :=
    congrArg Prod.fst hdata
  have hradius : EdgePrevCircleRadiusProfile v i = R :=
    congrArg Prod.snd hdata
  simp only [EdgePrevCurvatureDiskContainsAll]
  intro j
  rw [hcenter, hradius]
  exact hΔ.2.1 j

/-- A containing three-contact disk whose contact set is cyclically connected
is one of the polygon's canonical previous-vertex curvature disks.  This is
the terminal step in Dahlberg's proof of Lemma 5. -/
theorem exists_edgePrevCurvatureDiskContainsAll_of_containing_contacts_interval
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (U : DahlbergContainingThreeContactDiskR2 v)
    (hinterval : Gluck.IsCyclicInterval
      (circleContactSet v U.center U.radius)) :
    ∃ i : ZMod n,
      EdgePrevCurvatureCircleData v i = (U.center, U.radius) ∧
      EdgePrevCurvatureDiskContainsAll v i := by
  obtain ⟨i, hprev, hself, hnext⟩ :=
    hinterval.exists_three_consecutive U.three_contacts
  have hprev' : OnDiskBoundaryR2 v U.center U.radius (i - 1) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hprev)
  have hself' : OnDiskBoundaryR2 v U.center U.radius i :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hself)
  have hnext' : OnDiskBoundaryR2 v U.center U.radius (i + 1) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hnext)
  have hdata := edgePrevCurvatureCircleData_eq_of_three_boundaries_of_cross_pos
    hsimple U.radius_pos hprev' hself' hnext' (horient i)
  refine ⟨i, hdata, ?_⟩
  have hcenter : EdgePrevCircleCenterProfile v i = U.center :=
    congrArg Prod.fst hdata
  have hradius : EdgePrevCircleRadiusProfile v i = U.radius :=
    congrArg Prod.snd hdata
  simp only [EdgePrevCurvatureDiskContainsAll]
  intro j
  rw [hcenter, hradius]
  exact U.contains j

/-- An interior-missing three-contact disk whose contact set is cyclically
connected is one of the polygon's canonical previous-vertex curvature disks.
This is the terminal step in Dahlberg's proof of Lemma 7. -/
theorem exists_edgePrevCurvatureDiskInteriorMissesAll_of_missing_contacts_interval
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (U : DahlbergInteriorMissingThreeContactDiskR2 v)
    (hinterval : Gluck.IsCyclicInterval
      (circleContactSet v U.center U.radius)) :
    ∃ i : ZMod n,
      EdgePrevCurvatureCircleData v i = (U.center, U.radius) ∧
      EdgePrevCurvatureDiskInteriorMissesAll v i := by
  obtain ⟨i, hprev, hself, hnext⟩ :=
    hinterval.exists_three_consecutive U.three_contacts
  have hprev' : OnDiskBoundaryR2 v U.center U.radius (i - 1) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hprev)
  have hself' : OnDiskBoundaryR2 v U.center U.radius i :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hself)
  have hnext' : OnDiskBoundaryR2 v U.center U.radius (i + 1) :=
    Metric.mem_sphere'.mpr (mem_circleContactSet.mp hnext)
  have hdata := edgePrevCurvatureCircleData_eq_of_three_boundaries_of_cross_pos
    hsimple U.radius_pos hprev' hself' hnext' (horient i)
  refine ⟨i, hdata, ?_⟩
  have hcenter : EdgePrevCircleCenterProfile v i = U.center :=
    congrArg Prod.fst hdata
  have hradius : EdgePrevCircleRadiusProfile v i = U.radius :=
    congrArg Prod.snd hdata
  simpa [EdgePrevCurvatureDiskInteriorMissesAll, hcenter, hradius] using U.misses

/-- Dahlberg §3 Lemma 5 certificate: two distinct curvature disks contain all
vertices. -/
structure DahlbergE2Theorem6ContainingDisksCertificate {n : ℕ}
    (v : ZMod n → ℂ) where
  i : ZMod n
  j : ZMod n
  contains_i : EdgePrevCurvatureDiskContainsAll v i
  contains_j : EdgePrevCurvatureDiskContainsAll v j
  distinct : EdgePrevCurvatureCirclesDistinct v i j

/-- Dahlberg §3 Lemma 7 certificate: two distinct curvature disks have no
vertex in their interiors. -/
structure DahlbergE2Theorem6InteriorMissingDisksCertificate {n : ℕ}
    (v : ZMod n → ℂ) where
  i : ZMod n
  j : ZMod n
  misses_i : EdgePrevCurvatureDiskInteriorMissesAll v i
  misses_j : EdgePrevCurvatureDiskInteriorMissesAll v j
  distinct : EdgePrevCurvatureCirclesDistinct v i j

/-- In the nonconcyclic branch no positive-radius circle can contain every
vertex on its boundary. -/
theorem circleContactSet_ne_univ_of_not_concyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hR : 0 < R) (hnoncircle : ¬ Concyclic v) :
    circleContactSet v O R ≠ Finset.univ := by
  intro heq
  apply hnoncircle
  refine ⟨O, R, hR, ?_⟩
  intro i
  apply mem_circleContactSet.mp
  rw [heq]
  simp

/-- Source-free pointwise form of Dahlberg §3 Lemma 5.  The finite disk
family and cut-gap descent produce two terminal contact intervals, which
identify two distinct curvature disks containing every vertex. -/
theorem dahlbergE2Theorem6Lemma5ContainingDisks
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hsupport : StrictConvexEdgeSupport v)
    (hgeom : StrictConvexCyclicChordGeometry v)
    (hnoncircle : ¬ Concyclic v) :
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) := by
  classical
  let contacts : DahlbergContainingThreeContactDiskR2 v → Finset (ZMod n) :=
    fun U => circleContactSet v U.center U.radius
  have hthree : ∀ U : DahlbergContainingThreeContactDiskR2 v,
      3 ≤ (contacts U).card := by
    intro U
    exact U.three_contacts
  have hproper : ∀ U : DahlbergContainingThreeContactDiskR2 v,
      contacts U ≠ Finset.univ := by
    intro U
    exact circleContactSet_ne_univ_of_not_concyclic U.radius_pos hnoncircle
  have hchoose : ∀ i : ZMod n,
      ∃ W : DahlbergContainingThreeContactDiskR2 v, i ∈ contacts W := by
    intro i
    exact exists_dahlbergContainingThreeContactDiskR2_at_of_strictConvexEdgeSupport
      hn hsupport i
  have hlocalize :
      ∀ (U W : DahlbergContainingThreeContactDiskR2 v) (c : ZMod n)
        {p k q : ℕ},
        p < k → k < q → q < n →
        Gluck.cyclicLift c p ∈ contacts U →
        Gluck.cyclicLift c q ∈ contacts U →
        Gluck.cyclicLift c k ∉ contacts U →
        Gluck.cyclicLift c k ∈ contacts W →
        contacts W ⊆ Gluck.mapCut c (Finset.Icc p q) := by
    intro U W c p k q hpk hkq hqn hpU hqU hkNotU hkW
    exact circleContactSet_subset_of_containingDisk_cutGap
      hgeom U W c hpk hkq hqn hpU hqU hkNotU hkW
  obtain ⟨U₀, _h0⟩ := hchoose 0
  obtain ⟨U, W, hUinterval, hWinterval, hcontactsNe⟩ :=
    exists_two_cyclicInterval_contacts_ne_of_cutGap_shrink
      contacts hthree hproper hchoose hlocalize U₀
  obtain ⟨i, hdataU, hcontainsU⟩ :=
    exists_edgePrevCurvatureDiskContainsAll_of_containing_contacts_interval
      hsimple horient U hUinterval
  obtain ⟨j, hdataW, hcontainsW⟩ :=
    exists_edgePrevCurvatureDiskContainsAll_of_containing_contacts_interval
      hsimple horient W hWinterval
  have hdistinct : EdgePrevCurvatureCirclesDistinct v i j := by
    intro hij
    apply hcontactsNe
    apply circleContactSet_eq_of_circleData_eq
    exact hdataU.symm.trans (hij.trans hdataW)
  exact ⟨⟨i, j, hcontainsU, hcontainsW, hdistinct⟩⟩

/-- Source-free pointwise form of Dahlberg §3 Lemma 7.  The same finite
descent, using the exterior-circle localization, produces two distinct
curvature disks whose interiors contain no polygon vertex. -/
theorem dahlbergE2Theorem6Lemma7InteriorMissingDisks
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hsupport : StrictConvexEdgeSupport v)
    (hgeom : StrictConvexCyclicChordGeometry v)
    (hnoncircle : ¬ Concyclic v) :
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) := by
  classical
  let contacts : DahlbergInteriorMissingThreeContactDiskR2 v → Finset (ZMod n) :=
    fun U => circleContactSet v U.center U.radius
  have hthree : ∀ U : DahlbergInteriorMissingThreeContactDiskR2 v,
      3 ≤ (contacts U).card := by
    intro U
    exact U.three_contacts
  have hproper : ∀ U : DahlbergInteriorMissingThreeContactDiskR2 v,
      contacts U ≠ Finset.univ := by
    intro U
    exact circleContactSet_ne_univ_of_not_concyclic U.radius_pos hnoncircle
  have hchoose : ∀ i : ZMod n,
      ∃ W : DahlbergInteriorMissingThreeContactDiskR2 v, i ∈ contacts W := by
    intro i
    exact exists_dahlbergInteriorMissingThreeContactDiskR2_at_of_strictConvexEdgeSupport
      hn hsupport i
  have hlocalize :
      ∀ (U W : DahlbergInteriorMissingThreeContactDiskR2 v) (c : ZMod n)
        {p k q : ℕ},
        p < k → k < q → q < n →
        Gluck.cyclicLift c p ∈ contacts U →
        Gluck.cyclicLift c q ∈ contacts U →
        Gluck.cyclicLift c k ∉ contacts U →
        Gluck.cyclicLift c k ∈ contacts W →
        contacts W ⊆ Gluck.mapCut c (Finset.Icc p q) := by
    intro U W c p k q hpk hkq hqn hpU hqU hkNotU hkW
    exact circleContactSet_subset_of_missingDisk_cutGap
      hgeom U W c hpk hkq hqn hpU hqU hkNotU hkW
  obtain ⟨U₀, _h0⟩ := hchoose 0
  obtain ⟨U, W, hUinterval, hWinterval, hcontactsNe⟩ :=
    exists_two_cyclicInterval_contacts_ne_of_cutGap_shrink
      contacts hthree hproper hchoose hlocalize U₀
  obtain ⟨i, hdataU, hmissesU⟩ :=
    exists_edgePrevCurvatureDiskInteriorMissesAll_of_missing_contacts_interval
      hsimple horient U hUinterval
  obtain ⟨j, hdataW, hmissesW⟩ :=
    exists_edgePrevCurvatureDiskInteriorMissesAll_of_missing_contacts_interval
      hsimple horient W hWinterval
  have hdistinct : EdgePrevCurvatureCirclesDistinct v i j := by
    intro hij
    apply hcontactsNe
    apply circleContactSet_eq_of_circleData_eq
    exact hdataU.symm.trans (hij.trans hdataW)
  exact ⟨⟨i, j, hmissesU, hmissesW, hdistinct⟩⟩

/-- Exact certificate for Dahlberg's Theorem 6 (CDFV).

The paper supplies two curvature disks containing all polygon vertices and
two curvature disks whose interiors contain no polygon vertex.  The four
curvature circles are pairwise distinct, but the theorem does not assert a
cyclic alternation of these witnesses and does not attach local-extremum data
to the same four indices. -/
structure DahlbergE2Theorem6PaperCertificate {n : ℕ} (v : ZMod n → ℂ) where
  containing : DahlbergE2Theorem6ContainingDisksCertificate v
  interiorMissing : DahlbergE2Theorem6InteriorMissingDisksCertificate v
  containing_i_ne_missing_i :
    EdgePrevCurvatureCirclesDistinct v containing.i interiorMissing.i
  containing_i_ne_missing_j :
    EdgePrevCurvatureCirclesDistinct v containing.i interiorMissing.j
  containing_j_ne_missing_i :
    EdgePrevCurvatureCirclesDistinct v containing.j interiorMissing.i
  containing_j_ne_missing_j :
    EdgePrevCurvatureCirclesDistinct v containing.j interiorMissing.j

/-- A Lean-side certificate for Dahlberg's Theorem 6 / CDFV.

The paper states the result using four curvature disks: two whose interiors
miss all vertices and two which contain all vertices, with pairwise distinct
curvature circles.  This certificate keeps those geometric facts and records
the corresponding plateau-aware extrema of the previous-radius profile, which
is the formal interface used by the rest of the file. -/
structure DahlbergE2Theorem6CdfvCertificate {n : ℕ} (v : ZMod n → ℂ) where
  i₁ : ℕ
  i₂ : ℕ
  i₃ : ℕ
  i₄ : ℕ
  i₁_lt_i₂ : i₁ < i₂
  i₂_lt_i₃ : i₂ < i₃
  i₃_lt_i₄ : i₃ < i₄
  i₄_lt_wrap : i₄ < i₁ + n
  contains₁ : EdgePrevCurvatureDiskContainsAll v (i₁ : ZMod n)
  misses₂ : EdgePrevCurvatureDiskInteriorMissesAll v (i₂ : ZMod n)
  contains₃ : EdgePrevCurvatureDiskContainsAll v (i₃ : ZMod n)
  misses₄ : EdgePrevCurvatureDiskInteriorMissesAll v (i₄ : ZMod n)
  circle₁_ne₂ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₂ : ZMod n)
  circle₁_ne₃ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₃ : ZMod n)
  circle₁_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₄ : ZMod n)
  circle₂_ne₃ :
    EdgePrevCurvatureCirclesDistinct v (i₂ : ZMod n) (i₃ : ZMod n)
  circle₂_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₂ : ZMod n) (i₄ : ZMod n)
  circle₃_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₃ : ZMod n) (i₄ : ZMod n)
  localMax₁ : DiscreteLocalMax (EdgePrevCircleRadiusProfile v) (i₁ : ZMod n)
  localMin₂ : DiscreteLocalMin (EdgePrevCircleRadiusProfile v) (i₂ : ZMod n)
  localMax₃ : DiscreteLocalMax (EdgePrevCircleRadiusProfile v) (i₃ : ZMod n)
  localMin₄ : DiscreteLocalMin (EdgePrevCircleRadiusProfile v) (i₄ : ZMod n)

/-- Ordered geometric disk data in Dahlberg's Theorem 6 / CDFV, before
attaching the radius-profile local-extremum proof. -/
structure DahlbergE2Theorem6OrderedDiskCertificate {n : ℕ} (v : ZMod n → ℂ) where
  i₁ : ℕ
  i₂ : ℕ
  i₃ : ℕ
  i₄ : ℕ
  i₁_lt_i₂ : i₁ < i₂
  i₂_lt_i₃ : i₂ < i₃
  i₃_lt_i₄ : i₃ < i₄
  i₄_lt_wrap : i₄ < i₁ + n
  contains₁ : EdgePrevCurvatureDiskContainsAll v (i₁ : ZMod n)
  misses₂ : EdgePrevCurvatureDiskInteriorMissesAll v (i₂ : ZMod n)
  contains₃ : EdgePrevCurvatureDiskContainsAll v (i₃ : ZMod n)
  misses₄ : EdgePrevCurvatureDiskInteriorMissesAll v (i₄ : ZMod n)
  circle₁_ne₂ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₂ : ZMod n)
  circle₁_ne₃ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₃ : ZMod n)
  circle₁_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₄ : ZMod n)
  circle₂_ne₃ :
    EdgePrevCurvatureCirclesDistinct v (i₂ : ZMod n) (i₃ : ZMod n)
  circle₂_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₂ : ZMod n) (i₄ : ZMod n)
  circle₃_ne₄ :
    EdgePrevCurvatureCirclesDistinct v (i₃ : ZMod n) (i₄ : ZMod n)

/-- Alternating ordered disk data before the formally automatic
cross-distinctness fields are attached.

The two same-type distinctness assumptions are exactly the distinctness data
coming from Dahlberg's Lemma 5 (the two containing disks) and Lemma 7 (the two
interior-missing disks).  Distinctness between a containing disk and an
interior-missing disk is proved below from nonconcyclicity. -/
structure DahlbergE2Theorem6AlternatingDiskCertificate {n : ℕ}
    (v : ZMod n → ℂ) where
  i₁ : ℕ
  i₂ : ℕ
  i₃ : ℕ
  i₄ : ℕ
  i₁_lt_i₂ : i₁ < i₂
  i₂_lt_i₃ : i₂ < i₃
  i₃_lt_i₄ : i₃ < i₄
  i₄_lt_wrap : i₄ < i₁ + n
  contains₁ : EdgePrevCurvatureDiskContainsAll v (i₁ : ZMod n)
  misses₂ : EdgePrevCurvatureDiskInteriorMissesAll v (i₂ : ZMod n)
  contains₃ : EdgePrevCurvatureDiskContainsAll v (i₃ : ZMod n)
  misses₄ : EdgePrevCurvatureDiskInteriorMissesAll v (i₄ : ZMod n)
  contains_distinct :
    EdgePrevCurvatureCirclesDistinct v (i₁ : ZMod n) (i₃ : ZMod n)
  misses_distinct :
    EdgePrevCurvatureCirclesDistinct v (i₂ : ZMod n) (i₄ : ZMod n)

/-- Forget the formally filled cross-distinctness fields from an ordered-disk
certificate, leaving the alternating data and same-type distinctness. -/
def dahlbergE2Theorem6AlternatingDiskCertificate_of_orderedDiskCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6OrderedDiskCertificate v) :
    DahlbergE2Theorem6AlternatingDiskCertificate v :=
  { i₁ := cert.i₁
    i₂ := cert.i₂
    i₃ := cert.i₃
    i₄ := cert.i₄
    i₁_lt_i₂ := cert.i₁_lt_i₂
    i₂_lt_i₃ := cert.i₂_lt_i₃
    i₃_lt_i₄ := cert.i₃_lt_i₄
    i₄_lt_wrap := cert.i₄_lt_wrap
    contains₁ := cert.contains₁
    misses₂ := cert.misses₂
    contains₃ := cert.contains₃
    misses₄ := cert.misses₄
    contains_distinct := cert.circle₁_ne₃
    misses_distinct := cert.circle₂_ne₄ }

/-- Radius-profile local-extremum proof attached to a fixed ordered CDFV disk
certificate. -/
structure DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate {n : ℕ}
    {v : ZMod n → ℂ} (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    Prop where
  localMax₁ : DiscreteLocalMax (EdgePrevCircleRadiusProfile v) (disk.i₁ : ZMod n)
  localMin₂ : DiscreteLocalMin (EdgePrevCircleRadiusProfile v) (disk.i₂ : ZMod n)
  localMax₃ : DiscreteLocalMax (EdgePrevCircleRadiusProfile v) (disk.i₃ : ZMod n)
  localMin₄ : DiscreteLocalMin (EdgePrevCircleRadiusProfile v) (disk.i₄ : ZMod n)

/-- Weak one-step radius inequalities formally forced by the four ordered
curvature disks in Dahlberg's Theorem 6 / CDFV.

The two containing disks give weak local-maximum inequalities; the two
interior-missing disks give weak local-minimum inequalities.  The upgrade from
these weak inequalities to plateau-aware local extrema is the remaining global
cyclic/plateau extraction step in the paper. -/
structure DahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate {n : ℕ}
    {v : ZMod n → ℂ} (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    Prop where
  weakMax₁_left :
    EdgePrevCircleRadiusProfile v ((disk.i₁ : ZMod n) - 1) ≤
      EdgePrevCircleRadiusProfile v (disk.i₁ : ZMod n)
  weakMax₁_right :
    EdgePrevCircleRadiusProfile v ((disk.i₁ : ZMod n) + 1) ≤
      EdgePrevCircleRadiusProfile v (disk.i₁ : ZMod n)
  weakMin₂_left :
    EdgePrevCircleRadiusProfile v (disk.i₂ : ZMod n) ≤
      EdgePrevCircleRadiusProfile v ((disk.i₂ : ZMod n) - 1)
  weakMin₂_right :
    EdgePrevCircleRadiusProfile v (disk.i₂ : ZMod n) ≤
      EdgePrevCircleRadiusProfile v ((disk.i₂ : ZMod n) + 1)
  weakMax₃_left :
    EdgePrevCircleRadiusProfile v ((disk.i₃ : ZMod n) - 1) ≤
      EdgePrevCircleRadiusProfile v (disk.i₃ : ZMod n)
  weakMax₃_right :
    EdgePrevCircleRadiusProfile v ((disk.i₃ : ZMod n) + 1) ≤
      EdgePrevCircleRadiusProfile v (disk.i₃ : ZMod n)
  weakMin₄_left :
    EdgePrevCircleRadiusProfile v (disk.i₄ : ZMod n) ≤
      EdgePrevCircleRadiusProfile v ((disk.i₄ : ZMod n) - 1)
  weakMin₄_right :
    EdgePrevCircleRadiusProfile v (disk.i₄ : ZMod n) ≤
      EdgePrevCircleRadiusProfile v ((disk.i₄ : ZMod n) + 1)

/-- Explicit plateau-resolution data for a local maximum of a cyclic real
profile.

This is the finite bookkeeping hidden in the plateau-aware definition:
moving left and right from the chosen index, the profile stays constant until
it exits the plateau strictly downward.  Keeping the data as a named
structure gives the remaining Dahlberg §3 plateau argument a concrete target
which is finer than simply asserting `DiscreteLocalMax`. -/
structure PlateauLocalMaxResolution {n : ℕ} (κ : ZMod n → ℝ)
    (i : ZMod n) where
  leftSteps : ℕ
  rightSteps : ℕ
  left_pos : 0 < leftSteps
  right_pos : 0 < rightSteps
  span_le : leftSteps + rightSteps ≤ n
  left_eq :
    ∀ m < leftSteps, κ (i - (m : ZMod n)) = κ i
  right_eq :
    ∀ m < rightSteps, κ (i + (m : ZMod n)) = κ i
  left_drop : κ (i - (leftSteps : ZMod n)) < κ i
  right_drop : κ (i + (rightSteps : ZMod n)) < κ i

/-- Explicit plateau-resolution data for a local minimum of a cyclic real
profile.  The profile stays constant across the selected plateau and exits
strictly upward on both sides. -/
structure PlateauLocalMinResolution {n : ℕ} (κ : ZMod n → ℝ)
    (i : ZMod n) where
  leftSteps : ℕ
  rightSteps : ℕ
  left_pos : 0 < leftSteps
  right_pos : 0 < rightSteps
  span_le : leftSteps + rightSteps ≤ n
  left_eq :
    ∀ m < leftSteps, κ (i - (m : ZMod n)) = κ i
  right_eq :
    ∀ m < rightSteps, κ (i + (m : ZMod n)) = κ i
  left_rise : κ i < κ (i - (leftSteps : ZMod n))
  right_rise : κ i < κ (i + (rightSteps : ZMod n))

/-- Plateau-resolution data is exactly the witness package needed by the
plateau-aware local-maximum definition. -/
theorem discreteLocalMax_of_plateauLocalMaxResolution {n : ℕ}
    {κ : ZMod n → ℝ} {i : ZMod n}
    (h : PlateauLocalMaxResolution κ i) :
    DiscreteLocalMax κ i := by
  rcases h with
    ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft_drop, hright_drop⟩
  exact ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq,
    hleft_drop, hright_drop⟩

/-- A plateau-aware local maximum is exactly explicit plateau-resolution
data.  Since the local-maximum predicate is `Prop`-valued while the explicit
resolution is data-carrying, extracting the witnesses uses classical choice. -/
noncomputable def plateauLocalMaxResolution_of_discreteLocalMax {n : ℕ}
    {κ : ZMod n → ℝ} {i : ZMod n}
    (h : DiscreteLocalMax κ i) :
    PlateauLocalMaxResolution κ i := by
  let l : ℕ := Classical.choose h
  let hl : ∃ r : ℕ, 0 < l ∧ 0 < r ∧ l + r ≤ n ∧
      (∀ m < l, κ (i - (m : ZMod n)) = κ i) ∧
      (∀ m < r, κ (i + (m : ZMod n)) = κ i) ∧
      κ (i - (l : ZMod n)) < κ i ∧
      κ (i + (r : ZMod n)) < κ i := Classical.choose_spec h
  let r : ℕ := Classical.choose hl
  let hr := Classical.choose_spec hl
  exact
    { leftSteps := l
      rightSteps := r
      left_pos := hr.1
      right_pos := hr.2.1
      span_le := hr.2.2.1
      left_eq := hr.2.2.2.1
      right_eq := hr.2.2.2.2.1
      left_drop := hr.2.2.2.2.2.1
      right_drop := hr.2.2.2.2.2.2 }

/-- Plateau-resolution data is exactly the witness package needed by the
plateau-aware local-minimum definition. -/
theorem discreteLocalMin_of_plateauLocalMinResolution {n : ℕ}
    {κ : ZMod n → ℝ} {i : ZMod n}
    (h : PlateauLocalMinResolution κ i) :
    DiscreteLocalMin κ i := by
  rcases h with
    ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq, hleft_rise, hright_rise⟩
  exact ⟨l, r, hlpos, hrpos, hlr, hleft_eq, hright_eq,
    hleft_rise, hright_rise⟩

/-- A plateau-aware local minimum is exactly explicit plateau-resolution
data.  Since the local-minimum predicate is `Prop`-valued while the explicit
resolution is data-carrying, extracting the witnesses uses classical choice. -/
noncomputable def plateauLocalMinResolution_of_discreteLocalMin {n : ℕ}
    {κ : ZMod n → ℝ} {i : ZMod n}
    (h : DiscreteLocalMin κ i) :
    PlateauLocalMinResolution κ i := by
  let l : ℕ := Classical.choose h
  let hl : ∃ r : ℕ, 0 < l ∧ 0 < r ∧ l + r ≤ n ∧
      (∀ m < l, κ (i - (m : ZMod n)) = κ i) ∧
      (∀ m < r, κ (i + (m : ZMod n)) = κ i) ∧
      κ i < κ (i - (l : ZMod n)) ∧
      κ i < κ (i + (r : ZMod n)) := Classical.choose_spec h
  let r : ℕ := Classical.choose hl
  let hr := Classical.choose_spec hl
  exact
    { leftSteps := l
      rightSteps := r
      left_pos := hr.1
      right_pos := hr.2.1
      span_le := hr.2.2.1
      left_eq := hr.2.2.2.1
      right_eq := hr.2.2.2.2.1
      left_rise := hr.2.2.2.2.2.1
      right_rise := hr.2.2.2.2.2.2 }

/-- Plateau-resolution data attached to the four ordered disks in Dahlberg's
Theorem 6.

The weak one-step inequalities from the disk-containment/missing hypotheses
are proved formally above.  What remains from Dahlberg's §3 plateau argument
is precisely the existence of these four left/right plateau exits for the
same ordered disks. -/
structure DahlbergE2Theorem6PlateauResolutionForOrderedDiskCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (disk : DahlbergE2Theorem6OrderedDiskCertificate v) where
  max₁ :
    PlateauLocalMaxResolution (EdgePrevCircleRadiusProfile v)
      (disk.i₁ : ZMod n)
  min₂ :
    PlateauLocalMinResolution (EdgePrevCircleRadiusProfile v)
      (disk.i₂ : ZMod n)
  max₃ :
    PlateauLocalMaxResolution (EdgePrevCircleRadiusProfile v)
      (disk.i₃ : ZMod n)
  min₄ :
    PlateauLocalMinResolution (EdgePrevCircleRadiusProfile v)
      (disk.i₄ : ZMod n)

/-- The explicit plateau-resolution certificate supplies the local-extremum
package used by the CDFV certificate. -/
theorem dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_plateauResolution
    {n : ℕ} {v : ZMod n → ℂ}
    {disk : DahlbergE2Theorem6OrderedDiskCertificate v}
    (h : DahlbergE2Theorem6PlateauResolutionForOrderedDiskCertificate disk) :
    DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk := by
  exact
    { localMax₁ := discreteLocalMax_of_plateauLocalMaxResolution h.max₁
      localMin₂ := discreteLocalMin_of_plateauLocalMinResolution h.min₂
      localMax₃ := discreteLocalMax_of_plateauLocalMaxResolution h.max₃
      localMin₄ := discreteLocalMin_of_plateauLocalMinResolution h.min₄ }

/-- The local-extremum package for a fixed ordered disk certificate supplies
the explicit plateau-resolution data. -/
noncomputable def dahlbergE2Theorem6PlateauResolution_of_radiusExtremaForOrderedDiskCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    {disk : DahlbergE2Theorem6OrderedDiskCertificate v}
    (h : DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk) :
    DahlbergE2Theorem6PlateauResolutionForOrderedDiskCertificate disk :=
  { max₁ := plateauLocalMaxResolution_of_discreteLocalMax h.localMax₁
    min₂ := plateauLocalMinResolution_of_discreteLocalMin h.localMin₂
    max₃ := plateauLocalMaxResolution_of_discreteLocalMax h.localMax₃
    min₄ := plateauLocalMinResolution_of_discreteLocalMin h.localMin₄ }

/-- Boundary incidence for the four ordered curvature disks appearing in
Dahlberg's Theorem 6 / CDFV.  Each curvature circle passes through the three
vertices that define it. -/
structure DahlbergE2Theorem6OrderedDiskBoundaryIncidence {n : ℕ}
    {v : ZMod n → ℂ} (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    Prop where
  boundary₁_prev :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₁ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₁ : ZMod n))
      ((disk.i₁ : ZMod n) - 1)
  boundary₁_self :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₁ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₁ : ZMod n)) (disk.i₁ : ZMod n)
  boundary₁_next :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₁ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₁ : ZMod n))
      ((disk.i₁ : ZMod n) + 1)
  boundary₂_prev :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₂ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₂ : ZMod n))
      ((disk.i₂ : ZMod n) - 1)
  boundary₂_self :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₂ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₂ : ZMod n)) (disk.i₂ : ZMod n)
  boundary₂_next :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₂ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₂ : ZMod n))
      ((disk.i₂ : ZMod n) + 1)
  boundary₃_prev :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₃ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₃ : ZMod n))
      ((disk.i₃ : ZMod n) - 1)
  boundary₃_self :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₃ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₃ : ZMod n)) (disk.i₃ : ZMod n)
  boundary₃_next :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₃ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₃ : ZMod n))
      ((disk.i₃ : ZMod n) + 1)
  boundary₄_prev :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₄ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₄ : ZMod n))
      ((disk.i₄ : ZMod n) - 1)
  boundary₄_self :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₄ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₄ : ZMod n)) (disk.i₄ : ZMod n)
  boundary₄_next :
    OnDiskBoundaryR2 v (EdgePrevCircleCenterProfile v (disk.i₄ : ZMod n))
      (EdgePrevCircleRadiusProfile v (disk.i₄ : ZMod n))
      ((disk.i₄ : ZMod n) + 1)

/-- Ordered CDFV disk data automatically carries the boundary-incidence facts
for its four defining triples in the positive-orientation branch. -/
theorem dahlbergE2Theorem6OrderedDiskBoundaryIncidence_of_positiveOrientation
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    DahlbergE2Theorem6OrderedDiskBoundaryIncidence disk := by
  exact
    { boundary₁_prev :=
        edgePrevCurvatureDisk_prev_boundary_of_positiveOrientation hsimple horient
          (disk.i₁ : ZMod n)
      boundary₁_self :=
        edgePrevCurvatureDisk_self_boundary_of_positiveOrientation hsimple horient
          (disk.i₁ : ZMod n)
      boundary₁_next :=
        edgePrevCurvatureDisk_next_boundary_of_positiveOrientation hsimple horient
          (disk.i₁ : ZMod n)
      boundary₂_prev :=
        edgePrevCurvatureDisk_prev_boundary_of_positiveOrientation hsimple horient
          (disk.i₂ : ZMod n)
      boundary₂_self :=
        edgePrevCurvatureDisk_self_boundary_of_positiveOrientation hsimple horient
          (disk.i₂ : ZMod n)
      boundary₂_next :=
        edgePrevCurvatureDisk_next_boundary_of_positiveOrientation hsimple horient
          (disk.i₂ : ZMod n)
      boundary₃_prev :=
        edgePrevCurvatureDisk_prev_boundary_of_positiveOrientation hsimple horient
          (disk.i₃ : ZMod n)
      boundary₃_self :=
        edgePrevCurvatureDisk_self_boundary_of_positiveOrientation hsimple horient
          (disk.i₃ : ZMod n)
      boundary₃_next :=
        edgePrevCurvatureDisk_next_boundary_of_positiveOrientation hsimple horient
          (disk.i₃ : ZMod n)
      boundary₄_prev :=
        edgePrevCurvatureDisk_prev_boundary_of_positiveOrientation hsimple horient
          (disk.i₄ : ZMod n)
      boundary₄_self :=
        edgePrevCurvatureDisk_self_boundary_of_positiveOrientation hsimple horient
          (disk.i₄ : ZMod n)
      boundary₄_next :=
        edgePrevCurvatureDisk_next_boundary_of_positiveOrientation hsimple horient
          (disk.i₄ : ZMod n) }

/-- Forget the radius-profile extrema from a full CDFV certificate. -/
def dahlbergE2Theorem6OrderedDiskCertificate_of_cdfvCertificate {n : ℕ}
    {v : ZMod n → ℂ} (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6OrderedDiskCertificate v :=
  { i₁ := cert.i₁
    i₂ := cert.i₂
    i₃ := cert.i₃
    i₄ := cert.i₄
    i₁_lt_i₂ := cert.i₁_lt_i₂
    i₂_lt_i₃ := cert.i₂_lt_i₃
    i₃_lt_i₄ := cert.i₃_lt_i₄
    i₄_lt_wrap := cert.i₄_lt_wrap
    contains₁ := cert.contains₁
    misses₂ := cert.misses₂
    contains₃ := cert.contains₃
    misses₄ := cert.misses₄
    circle₁_ne₂ := cert.circle₁_ne₂
    circle₁_ne₃ := cert.circle₁_ne₃
    circle₁_ne₄ := cert.circle₁_ne₄
    circle₂_ne₃ := cert.circle₂_ne₃
    circle₂_ne₄ := cert.circle₂_ne₄
    circle₃_ne₄ := cert.circle₃_ne₄ }

/-- A full CDFV certificate supplies the radius-extremum proof for its ordered
disk certificate. -/
theorem dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_cdfvCertificate
    {n : ℕ} {v : ZMod n → ℂ} (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate
      (dahlbergE2Theorem6OrderedDiskCertificate_of_cdfvCertificate cert) := by
  exact ⟨cert.localMax₁, cert.localMin₂, cert.localMax₃, cert.localMin₄⟩

/-- Rebuild a full CDFV certificate from ordered disk data and the matching
radius-profile local-extremum proof. -/
def dahlbergE2Theorem6CdfvCertificate_of_orderedDiskCertificate {n : ℕ}
    {v : ZMod n → ℂ} (disk : DahlbergE2Theorem6OrderedDiskCertificate v)
    (hext : DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk) :
    DahlbergE2Theorem6CdfvCertificate v :=
  { i₁ := disk.i₁
    i₂ := disk.i₂
    i₃ := disk.i₃
    i₄ := disk.i₄
    i₁_lt_i₂ := disk.i₁_lt_i₂
    i₂_lt_i₃ := disk.i₂_lt_i₃
    i₃_lt_i₄ := disk.i₃_lt_i₄
    i₄_lt_wrap := disk.i₄_lt_wrap
    contains₁ := disk.contains₁
    misses₂ := disk.misses₂
    contains₃ := disk.contains₃
    misses₄ := disk.misses₄
    circle₁_ne₂ := disk.circle₁_ne₂
    circle₁_ne₃ := disk.circle₁_ne₃
    circle₁_ne₄ := disk.circle₁_ne₄
    circle₂_ne₃ := disk.circle₂_ne₃
    circle₂_ne₄ := disk.circle₂_ne₄
    circle₃_ne₄ := disk.circle₃_ne₄
    localMax₁ := hext.localMax₁
    localMin₂ := hext.localMin₂
    localMax₃ := hext.localMax₃
    localMin₄ := hext.localMin₄ }

/-- Geometric assembly certificate for Dahlberg §3 Theorem 6 / CDFV: ordered
disk data, the formal incidence of each curvature circle with its defining
triple, and the matching radius-profile local extrema. -/
structure DahlbergE2Theorem6GeometricAssemblyCertificate {n : ℕ}
    (v : ZMod n → ℂ) where
  disk : DahlbergE2Theorem6OrderedDiskCertificate v
  incidence : DahlbergE2Theorem6OrderedDiskBoundaryIncidence disk
  extrema : DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk

/-- Weak geometric assembly certificate for Dahlberg §3 Theorem 6 / CDFV:
ordered disk data, formal incidence with the defining triples, and the
one-step weak radius inequalities that are now proved from the disk hypotheses.

The remaining upgrade from this weak package to plateau-aware local extrema is
the global cyclic/plateau part of Dahlberg's §3 assembly argument. -/
structure DahlbergE2Theorem6WeakGeometricAssemblyCertificate {n : ℕ}
    (v : ZMod n → ℂ) where
  disk : DahlbergE2Theorem6OrderedDiskCertificate v
  incidence : DahlbergE2Theorem6OrderedDiskBoundaryIncidence disk
  weakExtrema : DahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate disk

/-- Ordered disk data plus radius extrema automatically form the geometric
assembly certificate once positive orientation supplies the boundary
incidence facts. -/
def dahlbergE2Theorem6GeometricAssemblyCertificate_of_orderedDiskCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (disk : DahlbergE2Theorem6OrderedDiskCertificate v)
    (hext : DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk) :
    DahlbergE2Theorem6GeometricAssemblyCertificate v :=
  { disk := disk
    incidence :=
      dahlbergE2Theorem6OrderedDiskBoundaryIncidence_of_positiveOrientation
        hsimple horient disk
    extrema := hext }

/-- A full CDFV certificate gives the sharper geometric assembly certificate
in the positive-orientation branch. -/
def dahlbergE2Theorem6GeometricAssemblyCertificate_of_cdfvCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6GeometricAssemblyCertificate v :=
  dahlbergE2Theorem6GeometricAssemblyCertificate_of_orderedDiskCertificate
    hsimple horient
    (dahlbergE2Theorem6OrderedDiskCertificate_of_cdfvCertificate cert)
    (dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_cdfvCertificate cert)

/-- Forget the boundary-incidence proof from the sharper geometric assembly
certificate and recover the full CDFV certificate used downstream. -/
def dahlbergE2Theorem6CdfvCertificate_of_geometricAssemblyCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6GeometricAssemblyCertificate v) :
    DahlbergE2Theorem6CdfvCertificate v :=
  dahlbergE2Theorem6CdfvCertificate_of_orderedDiskCertificate cert.disk cert.extrema

/-- Radius of the circle through `v i, v (i+1), v (i+2)`, expressed over the
outgoing edge `v i → v (i+1)`. -/
noncomputable def EdgeNextCircleRadiusProfile {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : ℝ :=
  normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))
    (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))

/-- Center of the circle through `v i, v (i+1), v (i+2)`, expressed over the
outgoing edge `v i → v (i+1)`. -/
noncomputable def EdgeNextCircleCenterProfile {n : ℕ} (v : ZMod n → ℂ)
    (i : ZMod n) : ℂ :=
  edgeCircleCenter (v i) (v (i + 1))
    (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i + 1 + 1)))

/-- In a positively oriented simple polygon, the outgoing-edge next-radius
profile is the previous-radius profile at the next vertex.  The two sides use
different edge coordinates, so this is a genuine circumcircle-radius
uniqueness statement rather than a definitional rewrite. -/
theorem EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    EdgeNextCircleRadiusProfile v i = EdgePrevCircleRadiusProfile v (i + 1) := by
  let A := v i
  let B := v (i + 1)
  let C := v (i + 1 + 1)
  have hAB : A ≠ B := hsimple.1 i
  have hBC : B ≠ C := by
    simpa [A, B, C, add_assoc] using hsimple.1 (i + 1)
  have hcross : 0 < Gluck.Discrete.crossR2 A B C := by
    simpa [A, B, C, sub_eq_add_neg, add_assoc] using horient (i + 1)
  have hcrossBC : Gluck.Discrete.crossR2 B C A ≠ 0 := by
    rw [crossR2_cycle]
    exact hcross.ne'
  have hcircle₁ :
      CircumcircleR2 A B C
        (edgeCircleCenter A B (edgeCircumcenterParameter A B C))
        (normalizedCircleRadius (chordHalfLength A B)
          (edgeCircumcenterParameter A B C)) :=
    circumcircleR2_edge_parameter hAB hcross.ne'
  have hcircle₂ :
      CircumcircleR2 B C A
        (edgeCircleCenter B C (edgeCircumcenterParameter B C A))
        (normalizedCircleRadius (chordHalfLength B C)
          (edgeCircumcenterParameter B C A)) :=
    circumcircleR2_edge_parameter hBC hcrossBC
  have hradius := (circumcircleR2_unique_of_cyclic_reorder hAB hcross.ne'
    hcircle₁ hcircle₂).2
  simpa [EdgeNextCircleRadiusProfile, EdgePrevCircleRadiusProfile, A, B, C,
    sub_eq_add_neg, add_assoc] using hradius

/-- In a positively oriented simple polygon, the outgoing-edge next-center is
the previous-center at the next vertex. -/
theorem EdgeNextCircleCenterProfile_eq_edgePrevCircleCenterProfile_succ_of_positiveOrientation
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    EdgeNextCircleCenterProfile v i = EdgePrevCircleCenterProfile v (i + 1) := by
  let A := v i
  let B := v (i + 1)
  let C := v (i + 1 + 1)
  have hAB : A ≠ B := hsimple.1 i
  have hBC : B ≠ C := by
    simpa [A, B, C, add_assoc] using hsimple.1 (i + 1)
  have hcross : 0 < Gluck.Discrete.crossR2 A B C := by
    simpa [A, B, C, sub_eq_add_neg, add_assoc] using horient (i + 1)
  have hcrossBC : Gluck.Discrete.crossR2 B C A ≠ 0 := by
    rw [crossR2_cycle]
    exact hcross.ne'
  have hcircle₁ :
      CircumcircleR2 A B C
        (edgeCircleCenter A B (edgeCircumcenterParameter A B C))
        (normalizedCircleRadius (chordHalfLength A B)
          (edgeCircumcenterParameter A B C)) :=
    circumcircleR2_edge_parameter hAB hcross.ne'
  have hcircle₂ :
      CircumcircleR2 B C A
        (edgeCircleCenter B C (edgeCircumcenterParameter B C A))
        (normalizedCircleRadius (chordHalfLength B C)
          (edgeCircumcenterParameter B C A)) :=
    circumcircleR2_edge_parameter hBC hcrossBC
  have hcenter := (circumcircleR2_unique_of_cyclic_reorder hAB hcross.ne'
    hcircle₁ hcircle₂).1
  simpa [EdgeNextCircleCenterProfile, EdgePrevCircleCenterProfile, A, B, C,
    sub_eq_add_neg, add_assoc] using hcenter

/-- The previous-vertex circle-radius profile is positive on a simple polygon. -/
theorem EdgePrevCircleRadiusProfile_pos {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v) (i : ZMod n) :
    0 < EdgePrevCircleRadiusProfile v i := by
  exact normalizedCircleRadius_pos (chordHalfLength_pos (hsimple.1 i)).ne' _

/-- A containing curvature disk and an interior-missing curvature disk cannot
be the same circle in the nonconcyclic branch.

If the two centre/radius data agreed, the containing inequality and the
interior-missing inequality would squeeze every vertex onto that common
circle, making the polygon concyclic. -/
theorem edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v) {i j : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i)
    (hmisses : EdgePrevCurvatureDiskInteriorMissesAll v j) :
    EdgePrevCurvatureCirclesDistinct v i j := by
  intro heq
  apply hnoncircle
  have hcenter :
      EdgePrevCircleCenterProfile v i = EdgePrevCircleCenterProfile v j :=
    congrArg Prod.fst heq
  have hradius :
      EdgePrevCircleRadiusProfile v i = EdgePrevCircleRadiusProfile v j :=
    congrArg Prod.snd heq
  refine ⟨EdgePrevCircleCenterProfile v i, EdgePrevCircleRadiusProfile v i,
    EdgePrevCircleRadiusProfile_pos hsimple i, ?_⟩
  intro k
  exact le_antisymm (Metric.mem_closedBall'.mp (hcontains k))
    (by simpa [hcenter, hradius] using hmisses k)

/-- The two same-type disk certificates from Dahlberg's Lemmas 5 and 7 form
the exact Theorem 6 certificate.  The four cross-type distinctness statements
are formal consequences of nonconcyclicity. -/
def dahlbergE2Theorem6PaperCertificate_of_splitCertificates
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (containing : DahlbergE2Theorem6ContainingDisksCertificate v)
    (interiorMissing : DahlbergE2Theorem6InteriorMissingDisksCertificate v) :
    DahlbergE2Theorem6PaperCertificate v :=
  { containing := containing
    interiorMissing := interiorMissing
    containing_i_ne_missing_i :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle containing.contains_i interiorMissing.misses_i
    containing_i_ne_missing_j :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle containing.contains_i interiorMissing.misses_j
    containing_j_ne_missing_i :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle containing.contains_j interiorMissing.misses_i
    containing_j_ne_missing_j :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle containing.contains_j interiorMissing.misses_j }

/-- Alternating containing/missing disk data upgrades to the full ordered-disk
certificate: the only missing fields are the four cross distinctness
statements, and these follow formally from nonconcyclicity. -/
def dahlbergE2Theorem6OrderedDiskCertificate_of_alternatingDiskCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (cert : DahlbergE2Theorem6AlternatingDiskCertificate v) :
    DahlbergE2Theorem6OrderedDiskCertificate v :=
  { i₁ := cert.i₁
    i₂ := cert.i₂
    i₃ := cert.i₃
    i₄ := cert.i₄
    i₁_lt_i₂ := cert.i₁_lt_i₂
    i₂_lt_i₃ := cert.i₂_lt_i₃
    i₃_lt_i₄ := cert.i₃_lt_i₄
    i₄_lt_wrap := cert.i₄_lt_wrap
    contains₁ := cert.contains₁
    misses₂ := cert.misses₂
    contains₃ := cert.contains₃
    misses₄ := cert.misses₄
    circle₁_ne₂ :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle cert.contains₁ cert.misses₂
    circle₁_ne₃ := cert.contains_distinct
    circle₁_ne₄ :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle cert.contains₁ cert.misses₄
    circle₂_ne₃ :=
      (edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle cert.contains₃ cert.misses₂).symm
    circle₂_ne₄ := cert.misses_distinct
    circle₃_ne₄ :=
      edgePrevCurvatureCirclesDistinct_of_containsAll_of_interiorMissesAll
        hsimple hnoncircle cert.contains₃ cert.misses₄ }

/-- If the previous curvature disk at `i` contains the next-next vertex, then
the next previous-radius is no larger than the radius at `i`. -/
theorem edgePrevCircleRadiusProfile_succ_le_of_containsAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i) :
    EdgePrevCircleRadiusProfile v (i + 1) ≤ EdgePrevCircleRadiusProfile v i := by
  have hAB : v i ≠ v (i + 1) := hsimple.1 i
  have hcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa [sub_eq_add_neg, add_assoc] using horient (i + 1)
  obtain ⟨O, R, hcircle, hcone⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right
      (by simpa using hregular (i + 1)) hcross.ne'
  have hmem :
      v (i + 1 + 1) ∈
        edgeClosedDisk (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
    refine (mem_edgeClosedDisk_iff_dist_le hAB
      (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))).mpr ?_
    simpa [EdgePrevCircleCenterProfile, EdgePrevCircleRadiusProfile] using
      Metric.mem_closedBall'.mp (hcontains (i + 1 + 1))
  have hleNext :
      EdgeNextCircleRadiusProfile v i ≤ EdgePrevCircleRadiusProfile v i := by
    simpa [EdgeNextCircleRadiusProfile, EdgePrevCircleRadiusProfile] using
      (edgeRegularCircleRadius_le_of_mem_edgeClosedDisk_right
        (A := v i) (B := v (i + 1)) (C := v (i + 1 + 1))
        (O := O) (R := R)
        hAB hcross hcircle hcone hmem)
  calc
    EdgePrevCircleRadiusProfile v (i + 1) = EdgeNextCircleRadiusProfile v i := by
      exact (EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient i).symm
    _ ≤ EdgePrevCircleRadiusProfile v i := hleNext

/-- If the previous curvature disk at `i` contains the previous-previous
vertex, then the previous previous-radius is no larger than the radius at
`i`. -/
theorem edgePrevCircleRadiusProfile_pred_le_of_containsAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i) :
    EdgePrevCircleRadiusProfile v (i - 1) ≤ EdgePrevCircleRadiusProfile v i := by
  have hAB : v (i - 1) ≠ v ((i - 1) + 1) := hsimple.1 (i - 1)
  have hcross :
      0 < Gluck.Discrete.crossR2 (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient (i - 1))
  obtain ⟨O, R, hcircle, hcone⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero (hregular (i - 1)) hcross.ne'
  have hcenter :=
    EdgeNextCircleCenterProfile_eq_edgePrevCircleCenterProfile_succ_of_positiveOrientation
      hsimple horient (i - 1)
  have hradius :=
    EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i - 1)
  have hdist :
      dist (EdgeNextCircleCenterProfile v (i - 1)) (v ((i - 1) - 1)) ≤
        EdgeNextCircleRadiusProfile v (i - 1) := by
    rw [hcenter, hradius]
    simpa [sub_eq_add_neg, add_assoc] using
      Metric.mem_closedBall'.mp (hcontains ((i - 1) - 1))
  have hmem :
      v ((i - 1) - 1) ∈
        edgeClosedDisk (v (i - 1)) (v ((i - 1) + 1))
          (edgeCircumcenterParameter (v (i - 1)) (v ((i - 1) + 1))
            (v ((i - 1) + 1 + 1))) := by
    refine (mem_edgeClosedDisk_iff_dist_le hAB
      (edgeCircumcenterParameter (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) + 1 + 1)))).mpr ?_
    simpa [EdgeNextCircleCenterProfile, EdgeNextCircleRadiusProfile,
      sub_eq_add_neg, add_assoc] using hdist
  have hlePrev :
      EdgePrevCircleRadiusProfile v (i - 1) ≤ EdgeNextCircleRadiusProfile v (i - 1) := by
    simpa [EdgePrevCircleRadiusProfile, EdgeNextCircleRadiusProfile,
      sub_eq_add_neg, add_assoc] using
      (edgeRegularCircleRadius_le_of_mem_edgeClosedDisk
        (A := v (i - 1)) (B := v ((i - 1) + 1)) (C := v ((i - 1) - 1))
        (O := O) (R := R)
        hAB hcross hcircle hcone hmem)
  calc
    EdgePrevCircleRadiusProfile v (i - 1) ≤ EdgeNextCircleRadiusProfile v (i - 1) :=
      hlePrev
    _ = EdgePrevCircleRadiusProfile v i := by
      simpa [sub_eq_add_neg, add_assoc] using
        EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
          hsimple horient (i - 1)

/-- A containing previous-curvature disk gives both neighboring radius
inequalities required for a local maximum candidate. -/
theorem edgePrevCircleRadiusProfile_neighbors_le_of_containsAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hcontains : EdgePrevCurvatureDiskContainsAll v i) :
    EdgePrevCircleRadiusProfile v (i - 1) ≤ EdgePrevCircleRadiusProfile v i ∧
      EdgePrevCircleRadiusProfile v (i + 1) ≤ EdgePrevCircleRadiusProfile v i := by
  exact ⟨
    edgePrevCircleRadiusProfile_pred_le_of_containsAll_of_positiveOrientation
      hsimple hregular horient hcontains,
    edgePrevCircleRadiusProfile_succ_le_of_containsAll_of_positiveOrientation
      hsimple hregular horient hcontains⟩

/-- If the previous curvature disk at `i` has no vertices in its interior,
then the radius at `i` is no larger than the next previous-radius. -/
theorem edgePrevCircleRadiusProfile_le_succ_of_interiorMissesAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hmiss : EdgePrevCurvatureDiskInteriorMissesAll v i) :
    EdgePrevCircleRadiusProfile v i ≤ EdgePrevCircleRadiusProfile v (i + 1) := by
  have hAB : v i ≠ v (i + 1) := hsimple.1 i
  have hcrossPrev : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient i)
  obtain ⟨OΔ, RΔ, hcircleΔ, hconeΔ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero (hregular i) hcrossPrev.ne'
  have hyΔ : 0 ≤ edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)) :=
    edgeCircumcenterParameter_nonneg_of_regular hAB hcrossPrev hcircleΔ hconeΔ
  have hcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i + 1 + 1)) := by
    simpa [sub_eq_add_neg, add_assoc] using horient (i + 1)
  have hmem :
      v (i + 1 + 1) ∈
        edgeClosedExterior (v i) (v (i + 1))
          (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) := by
    refine (mem_edgeClosedExterior_iff_radius_le_dist hAB
      (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1)))).mpr ?_
    simpa [InClosedDiskR2, EdgePrevCircleCenterProfile, EdgePrevCircleRadiusProfile] using
      hmiss (i + 1 + 1)
  have hleNext :
      EdgePrevCircleRadiusProfile v i ≤ EdgeNextCircleRadiusProfile v i := by
    simpa [EdgePrevCircleRadiusProfile, EdgeNextCircleRadiusProfile] using
      (edgeCircleRadius_le_of_mem_edgeClosedExterior
        (A := v i) (B := v (i + 1)) (C := v (i + 1 + 1))
        hAB hcross hyΔ hmem)
  calc
    EdgePrevCircleRadiusProfile v i ≤ EdgeNextCircleRadiusProfile v i := hleNext
    _ = EdgePrevCircleRadiusProfile v (i + 1) :=
      EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient i

/-- If the previous curvature disk at `i` has no vertices in its interior,
then the radius at `i` is no larger than the previous previous-radius. -/
theorem edgePrevCircleRadiusProfile_le_pred_of_interiorMissesAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hmiss : EdgePrevCurvatureDiskInteriorMissesAll v i) :
    EdgePrevCircleRadiusProfile v i ≤ EdgePrevCircleRadiusProfile v (i - 1) := by
  have hAB : v (i - 1) ≠ v ((i - 1) + 1) := hsimple.1 (i - 1)
  have hcrossΔ :
      0 < Gluck.Discrete.crossR2 (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) + 1 + 1)) := by
    simpa [sub_eq_add_neg, add_assoc] using horient i
  obtain ⟨OΔ, RΔ, hcircleΔ, hconeΔ⟩ :=
    dahlbergRegularAt_circle_of_cross_ne_zero_right
      (by simpa [sub_eq_add_neg, add_assoc] using hregular i) hcrossΔ.ne'
  have hyΔ :
      0 ≤ edgeCircumcenterParameter (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) + 1 + 1)) :=
    edgeCircumcenterParameter_nonneg_of_regular_right hAB hcrossΔ hcircleΔ hconeΔ
  have hcross :
      0 < Gluck.Discrete.crossR2 (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient (i - 1))
  have hcenter :=
    EdgeNextCircleCenterProfile_eq_edgePrevCircleCenterProfile_succ_of_positiveOrientation
      hsimple horient (i - 1)
  have hradius :=
    EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i - 1)
  have hdist :
      EdgeNextCircleRadiusProfile v (i - 1) ≤
        dist (EdgeNextCircleCenterProfile v (i - 1)) (v ((i - 1) - 1)) := by
    rw [hcenter, hradius]
    simpa [InClosedDiskR2, sub_eq_add_neg, add_assoc] using hmiss ((i - 1) - 1)
  have hmem :
      v ((i - 1) - 1) ∈
        edgeClosedExterior (v (i - 1)) (v ((i - 1) + 1))
          (edgeCircumcenterParameter (v (i - 1)) (v ((i - 1) + 1))
            (v ((i - 1) + 1 + 1))) := by
    refine (mem_edgeClosedExterior_iff_radius_le_dist hAB
      (edgeCircumcenterParameter (v (i - 1)) (v ((i - 1) + 1))
        (v ((i - 1) + 1 + 1)))).mpr ?_
    simpa [EdgeNextCircleCenterProfile, EdgeNextCircleRadiusProfile,
      sub_eq_add_neg, add_assoc] using hdist
  have hlePrev :
      EdgeNextCircleRadiusProfile v (i - 1) ≤ EdgePrevCircleRadiusProfile v (i - 1) := by
    simpa [EdgeNextCircleRadiusProfile, EdgePrevCircleRadiusProfile,
      sub_eq_add_neg, add_assoc] using
      (edgeCircleRadius_le_of_mem_edgeClosedExterior
        (A := v (i - 1)) (B := v ((i - 1) + 1)) (C := v ((i - 1) - 1))
        hAB hcross hyΔ hmem)
  calc
    EdgePrevCircleRadiusProfile v i = EdgeNextCircleRadiusProfile v (i - 1) := by
      simpa [sub_eq_add_neg, add_assoc] using
        (EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
          hsimple horient (i - 1)).symm
    _ ≤ EdgePrevCircleRadiusProfile v (i - 1) := hlePrev

/-- An interior-missing previous-curvature disk gives both neighboring radius
inequalities required for a local minimum candidate. -/
theorem edgePrevCircleRadiusProfile_le_neighbors_of_interiorMissesAll_of_positiveOrientation
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hmiss : EdgePrevCurvatureDiskInteriorMissesAll v i) :
    EdgePrevCircleRadiusProfile v i ≤ EdgePrevCircleRadiusProfile v (i - 1) ∧
      EdgePrevCircleRadiusProfile v i ≤ EdgePrevCircleRadiusProfile v (i + 1) := by
  exact ⟨
    edgePrevCircleRadiusProfile_le_pred_of_interiorMissesAll_of_positiveOrientation
      hsimple hregular horient hmiss,
    edgePrevCircleRadiusProfile_le_succ_of_interiorMissesAll_of_positiveOrientation
      hsimple hregular horient hmiss⟩

/-- Ordered CDFV disk data formally supplies the weak one-step radius
inequalities around the four ordered disks. -/
theorem dahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate_of_orderedDiskCertificate
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    DahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate disk := by
  have hmax₁ :=
    edgePrevCircleRadiusProfile_neighbors_le_of_containsAll_of_positiveOrientation
      hsimple hregular horient disk.contains₁
  have hmin₂ :=
    edgePrevCircleRadiusProfile_le_neighbors_of_interiorMissesAll_of_positiveOrientation
      hsimple hregular horient disk.misses₂
  have hmax₃ :=
    edgePrevCircleRadiusProfile_neighbors_le_of_containsAll_of_positiveOrientation
      hsimple hregular horient disk.contains₃
  have hmin₄ :=
    edgePrevCircleRadiusProfile_le_neighbors_of_interiorMissesAll_of_positiveOrientation
      hsimple hregular horient disk.misses₄
  exact
    { weakMax₁_left := hmax₁.1
      weakMax₁_right := hmax₁.2
      weakMin₂_left := hmin₂.1
      weakMin₂_right := hmin₂.2
      weakMax₃_left := hmax₃.1
      weakMax₃_right := hmax₃.2
      weakMin₄_left := hmin₄.1
      weakMin₄_right := hmin₄.2 }

/-- A geometric assembly certificate carries the formally proved weak
one-step radius inequalities for its ordered disk data. -/
theorem dahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate_of_geometricAssemblyCertificate
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (cert : DahlbergE2Theorem6GeometricAssemblyCertificate v) :
    DahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate cert.disk :=
  dahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate_of_orderedDiskCertificate
    hsimple hregular horient cert.disk

/-- Ordered disk data automatically form the weak geometric assembly
certificate once positive orientation and regularity supply incidence and
one-step radius comparisons. -/
def dahlbergE2Theorem6WeakGeometricAssemblyCertificate_of_orderedDiskCertificate
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (disk : DahlbergE2Theorem6OrderedDiskCertificate v) :
    DahlbergE2Theorem6WeakGeometricAssemblyCertificate v :=
  { disk := disk
    incidence :=
      dahlbergE2Theorem6OrderedDiskBoundaryIncidence_of_positiveOrientation
        hsimple horient disk
    weakExtrema :=
      dahlbergE2Theorem6WeakRadiusExtremaForOrderedDiskCertificate_of_orderedDiskCertificate
        hsimple hregular horient disk }

/-- A full geometric assembly certificate can be weakened to the formally
proved one-step radius package. -/
def dahlbergE2Theorem6WeakGeometricAssemblyCertificate_of_geometricAssemblyCertificate
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (cert : DahlbergE2Theorem6GeometricAssemblyCertificate v) :
    DahlbergE2Theorem6WeakGeometricAssemblyCertificate v :=
  dahlbergE2Theorem6WeakGeometricAssemblyCertificate_of_orderedDiskCertificate
    hsimple hregular horient cert.disk

/-- In the positive-orientation branch, signed Menger curvature is the
reciprocal of the previous-vertex circle-radius profile. -/
theorem signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) (i : ZMod n) :
    SignedMengerProfile v i = (EdgePrevCircleRadiusProfile v i)⁻¹ := by
  have hcross : 0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v (i - 1)) :=
    polygonEdgePrev_cross_pos_of_vertex_cross_pos (horient i)
  calc
    SignedMengerProfile v i
        = Gluck.Discrete.signedMengerR2 (v i) (v (i + 1)) (v (i - 1)) := by
          exact (signedMengerR2_cycle (v (i - 1)) (v i) (v (i + 1))).symm
    _ = normalizedCircleCurvature (chordHalfLength (v i) (v (i + 1)))
        (edgeCircumcenterParameter (v i) (v (i + 1)) (v (i - 1))) :=
          signedMengerR2_edge_parameter_of_pos (hsimple.1 i) hcross
    _ = (EdgePrevCircleRadiusProfile v i)⁻¹ := by
      simp [normalizedCircleCurvature, EdgePrevCircleRadiusProfile, one_div]

/-! ### Equal-radius propagation along the curvature-circle profile -/

/-- Equal adjacent signed-Menger values in the positive regular branch define
the same previous-vertex curvature circle. -/
theorem edgePrevCurvatureCircleData_succ_eq_of_signedMengerProfile_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1)) :
    EdgePrevCurvatureCircleData v i =
      EdgePrevCurvatureCircleData v (i + 1) := by
  have hy :=
    signedMengerProfile_edgeCircumcenterParameter_eq_of_endpoint_pos_eq
      hsimple hregular i (signedMengerProfile_pos_of_positiveOrientation hsimple horient i) hκ
  have hcenterNext :
      EdgePrevCircleCenterProfile v i = EdgeNextCircleCenterProfile v i := by
    simpa [EdgePrevCircleCenterProfile, EdgeNextCircleCenterProfile] using
      congrArg (edgeCircleCenter (v i) (v (i + 1))) hy
  have hradiusNext :
      EdgePrevCircleRadiusProfile v i = EdgeNextCircleRadiusProfile v i := by
    simpa [EdgePrevCircleRadiusProfile, EdgeNextCircleRadiusProfile] using
      congrArg (normalizedCircleRadius (chordHalfLength (v i) (v (i + 1)))) hy
  have hcenter :
      EdgePrevCircleCenterProfile v i = EdgePrevCircleCenterProfile v (i + 1) :=
    hcenterNext.trans
      (EdgeNextCircleCenterProfile_eq_edgePrevCircleCenterProfile_succ_of_positiveOrientation
        hsimple horient i)
  have hradius :
      EdgePrevCircleRadiusProfile v i = EdgePrevCircleRadiusProfile v (i + 1) :=
    hradiusNext.trans
      (EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient i)
  exact Prod.ext hcenter hradius

/-- Equal adjacent previous-circle radii in the positive regular branch define
the same previous-vertex curvature circle. -/
theorem edgePrevCurvatureCircleData_succ_eq_of_radius_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hρ : EdgePrevCircleRadiusProfile v i =
      EdgePrevCircleRadiusProfile v (i + 1)) :
    EdgePrevCurvatureCircleData v i =
      EdgePrevCurvatureCircleData v (i + 1) := by
  have hκ : SignedMengerProfile v i = SignedMengerProfile v (i + 1) := by
    calc
      SignedMengerProfile v i = (EdgePrevCircleRadiusProfile v i)⁻¹ :=
        signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
          hsimple horient i
      _ = (EdgePrevCircleRadiusProfile v (i + 1))⁻¹ :=
        congrArg (fun r : ℝ => r⁻¹) hρ
      _ = SignedMengerProfile v (i + 1) :=
        (signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
          hsimple horient (i + 1)).symm
  exact edgePrevCurvatureCircleData_succ_eq_of_signedMengerProfile_eq
    hsimple hregular horient i hκ

/-- Interior-missing is a property of the curvature circle itself, so it is
preserved when the centre/radius data agree. -/
theorem edgePrevCurvatureDiskInteriorMissesAll_congr_circleData
    {n : ℕ} {v : ZMod n → ℂ} {i j : ZMod n}
    (hdata : EdgePrevCurvatureCircleData v i =
      EdgePrevCurvatureCircleData v j) :
    EdgePrevCurvatureDiskInteriorMissesAll v i ↔
      EdgePrevCurvatureDiskInteriorMissesAll v j := by
  have hcenter :
      EdgePrevCircleCenterProfile v i = EdgePrevCircleCenterProfile v j :=
    congrArg Prod.fst hdata
  have hradius :
      EdgePrevCircleRadiusProfile v i = EdgePrevCircleRadiusProfile v j :=
    congrArg Prod.snd hdata
  simp [EdgePrevCurvatureDiskInteriorMissesAll, hcenter, hradius]

/-- The predecessor form of equal-radius curvature-circle rigidity. -/
theorem edgePrevCurvatureCircleData_pred_eq_of_radius_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hρ : EdgePrevCircleRadiusProfile v i =
      EdgePrevCircleRadiusProfile v (i - 1)) :
    EdgePrevCurvatureCircleData v i =
      EdgePrevCurvatureCircleData v (i - 1) := by
  have hρ' :
      EdgePrevCircleRadiusProfile v (i - 1) =
        EdgePrevCircleRadiusProfile v ((i - 1) + 1) := by
    simpa using hρ.symm
  have hdata := edgePrevCurvatureCircleData_succ_eq_of_radius_eq
    hsimple hregular horient (i - 1) hρ'
  simpa using hdata.symm

/-- Across an equal-radius successor step, the two curvature disks have the
same interior-missing property. -/
theorem edgePrevCurvatureDiskInteriorMissesAll_succ_iff_of_radius_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hρ : EdgePrevCircleRadiusProfile v i =
      EdgePrevCircleRadiusProfile v (i + 1)) :
    EdgePrevCurvatureDiskInteriorMissesAll v i ↔
      EdgePrevCurvatureDiskInteriorMissesAll v (i + 1) :=
  edgePrevCurvatureDiskInteriorMissesAll_congr_circleData
    (edgePrevCurvatureCircleData_succ_eq_of_radius_eq
      hsimple hregular horient i hρ)

/-- Across an equal-radius predecessor step, the two curvature disks have the
same interior-missing property. -/
theorem edgePrevCurvatureDiskInteriorMissesAll_pred_iff_of_radius_eq
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) (i : ZMod n)
    (hρ : EdgePrevCircleRadiusProfile v i =
      EdgePrevCircleRadiusProfile v (i - 1)) :
    EdgePrevCurvatureDiskInteriorMissesAll v i ↔
      EdgePrevCurvatureDiskInteriorMissesAll v (i - 1) :=
  edgePrevCurvatureDiskInteriorMissesAll_congr_circleData
    (edgePrevCurvatureCircleData_pred_eq_of_radius_eq
      hsimple hregular horient i hρ)

/-- An interior-missing curvature disk is a weak local maximum of positive
signed Menger curvature. -/
theorem signedMengerProfile_neighbors_le_of_interiorMissesAll
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v) {i : ZMod n}
    (hmiss : EdgePrevCurvatureDiskInteriorMissesAll v i) :
    SignedMengerProfile v (i - 1) ≤ SignedMengerProfile v i ∧
      SignedMengerProfile v (i + 1) ≤ SignedMengerProfile v i := by
  have hρ :=
    edgePrevCircleRadiusProfile_le_neighbors_of_interiorMissesAll_of_positiveOrientation
      hsimple hregular horient hmiss
  have hρpos := EdgePrevCircleRadiusProfile_pos hsimple
  constructor
  · rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient (i - 1),
      signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient i]
    exact (inv_le_inv₀ (hρpos (i - 1)) (hρpos i)).2 hρ.1
  · rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient (i + 1),
      signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient i]
    exact (inv_le_inv₀ (hρpos (i + 1)) (hρpos i)).2 hρ.2

/-- Two distinct curvature disks whose interiors miss all vertices force the
plateau-aware four-vertex conclusion in the positive regular branch. -/
theorem signedMengerProfile_dahlbergFourVertex_of_two_distinct_interiorMissing
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) {i j : ZMod n}
    (hmissi : EdgePrevCurvatureDiskInteriorMissesAll v i)
    (hmissj : EdgePrevCurvatureDiskInteriorMissesAll v j)
    (hdistinct : EdgePrevCurvatureCirclesDistinct v i j) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  let P : ZMod n → Prop := fun z =>
    EdgePrevCurvatureCircleData v z = EdgePrevCurvatureCircleData v i
  let Q : ZMod n → Prop := fun z =>
    EdgePrevCurvatureCircleData v z = EdgePrevCurvatureCircleData v j
  have hij : i ≠ j := by
    intro hij
    apply hdistinct
    rw [hij]
  have hPi : P i := rfl
  have hQj : Q j := rfl
  have hdisjoint : ∀ z, ¬ (P z ∧ Q z) := by
    rintro z ⟨hPz, hQz⟩
    exact hdistinct (hPz.symm.trans hQz)
  have hweakP : ∀ z, P z →
      SignedMengerProfile v (z - 1) ≤ SignedMengerProfile v z ∧
        SignedMengerProfile v (z + 1) ≤ SignedMengerProfile v z := by
    intro z hPz
    apply signedMengerProfile_neighbors_le_of_interiorMissesAll
      hsimple hregular horient
    exact (edgePrevCurvatureDiskInteriorMissesAll_congr_circleData hPz).2 hmissi
  have hweakQ : ∀ z, Q z →
      SignedMengerProfile v (z - 1) ≤ SignedMengerProfile v z ∧
        SignedMengerProfile v (z + 1) ≤ SignedMengerProfile v z := by
    intro z hQz
    apply signedMengerProfile_neighbors_le_of_interiorMissesAll
      hsimple hregular horient
    exact (edgePrevCurvatureDiskInteriorMissesAll_congr_circleData hQz).2 hmissj
  have hpropRight : ∀ {a : ZMod n},
      SignedMengerProfile v a = SignedMengerProfile v (a + 1) →
      EdgePrevCurvatureCircleData v a = EdgePrevCurvatureCircleData v (a + 1) := by
    intro a ha
    exact edgePrevCurvatureCircleData_succ_eq_of_signedMengerProfile_eq
      hsimple hregular horient a ha
  have hpropLeft : ∀ {a : ZMod n},
      SignedMengerProfile v a = SignedMengerProfile v (a - 1) →
      EdgePrevCurvatureCircleData v a = EdgePrevCurvatureCircleData v (a - 1) := by
    intro a ha
    have ha' :
        SignedMengerProfile v (a - 1) =
          SignedMengerProfile v ((a - 1) + 1) := by
      simpa using ha.symm
    have hdata := edgePrevCurvatureCircleData_succ_eq_of_signedMengerProfile_eq
      hsimple hregular horient (a - 1) ha'
    simpa using hdata.symm
  apply dahlbergFourVertex_of_two_disjoint_marked_weakMaxima
    hij hPi hQj hdisjoint hweakP
  · intro z hPz hκ
    exact (hpropRight hκ).symm.trans hPz
  · intro z hPz hκ
    exact (hpropLeft hκ).symm.trans hPz
  · exact hweakQ
  · intro z hQz hκ
    exact (hpropRight hκ).symm.trans hQz
  · intro z hQz hκ
    exact (hpropLeft hκ).symm.trans hQz
  · exact not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle

/-- A Dahlberg four-vertex theorem for the positive radius profile transfers
to signed Menger curvature by reciprocal monotonicity. -/
theorem signedMengerProfile_dahlbergFourVertex_of_positiveRadiusProfile
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hfv : DahlbergFourVertex (EdgePrevCircleRadiusProfile v)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_congr
    (fun i => signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
      hsimple horient i)
    (dahlbergFourVertex_inv_of_pos (EdgePrevCircleRadiusProfile_pos hsimple) hfv)

/-- Radius-level ordered adjacent turns in the positive-orientation branch.
Because positive signed Menger curvature is reciprocal radius, the inequalities
are opposite to the corresponding signed-Menger turns. -/
def PositiveRadiusOrderedAdjacentTurns {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ,
    i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      EdgeNextCircleRadiusProfile v (i₁ : ZMod n) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgeNextCircleRadiusProfile v (((i₁ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgeNextCircleRadiusProfile v (i₂ : ZMod n) ∧
      EdgeNextCircleRadiusProfile v (((i₂ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgeNextCircleRadiusProfile v (i₃ : ZMod n) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgeNextCircleRadiusProfile v (((i₃ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgeNextCircleRadiusProfile v (i₄ : ZMod n) ∧
      EdgeNextCircleRadiusProfile v (((i₄ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1))

/-- One-step strict extrema of the previous-radius profile give Dahlberg's
positive-radius ordered-turn package.

This is the formal non-plateau endpoint of Lemma 8: after the geometric disk
inclusion argument has produced strict adjacent previous-radius extrema, the
translation to `PositiveRadiusOrderedAdjacentTurns` is just the identity
`EdgeNext i = EdgePrev (i + 1)` in the positive-orientation branch. -/
theorem positiveRadiusOrderedAdjacentTurns_of_edgePrev_strict_turns {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    {i₁ i₂ i₃ i₄ : ℕ}
    (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃) (hi₃₄ : i₃ < i₄)
    (hi₄₁ : i₄ < i₁ + n)
    (hmin₁_left :
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n))
    (hmin₁_right :
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₁ : ZMod n) + 1) + 1)))
    (hmax₂_left :
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)))
    (hmax₂_right :
      EdgePrevCircleRadiusProfile v ((((i₂ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)))
    (hmin₃_left :
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n))
    (hmin₃_right :
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₃ : ZMod n) + 1) + 1)))
    (hmax₄_left :
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1)))
    (hmax₄_right :
      EdgePrevCircleRadiusProfile v ((((i₄ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1))) :
    PositiveRadiusOrderedAdjacentTurns v := by
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₁ : ZMod n)] using hmin₁_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₁ : ZMod n) + 1)), add_assoc] using hmin₁_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₂ : ZMod n)] using hmax₂_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₂ : ZMod n) + 1)), add_assoc] using hmax₂_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₃ : ZMod n)] using hmin₃_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₃ : ZMod n) + 1)), add_assoc] using hmin₃_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₄ : ZMod n)] using hmax₄_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₄ : ZMod n) + 1)), add_assoc] using hmax₄_right

/-- Dahlberg's positive-radius ordered-turn package is equivalent to the
same eight inequalities stated only with the previous-radius profile.

This is the reverse of
`positiveRadiusOrderedAdjacentTurns_of_edgePrev_strict_turns`; it uses only
the formal identity `EdgeNext i = EdgePrev (i + 1)` in the positive-orientation
branch. -/
theorem edgePrev_strict_turns_of_positiveRadiusOrderedAdjacentTurns {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    ∃ i₁ i₂ i₃ i₄ : ℕ,
      i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₁ : ZMod n) + 1) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v ((((i₂ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₃ : ZMod n) + 1) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v ((((i₄ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1)) := by
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hmin₁_left, hmin₁_right, hmax₂_left, hmax₂_right,
      hmin₃_left, hmin₃_right, hmax₄_left, hmax₄_right⟩
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₁ : ZMod n)] using hmin₁_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₁ : ZMod n) + 1)), add_assoc] using hmin₁_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₂ : ZMod n)] using hmax₂_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₂ : ZMod n) + 1)), add_assoc] using hmax₂_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₃ : ZMod n)] using hmin₃_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₃ : ZMod n) + 1)), add_assoc] using hmin₃_right
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₄ : ZMod n)] using hmax₄_left
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₄ : ZMod n) + 1)), add_assoc] using hmax₄_right

/-- Radius-profile form of the convex disk witnesses supplied by Dahlberg's
convex discrete four-vertex theorem (Theorem 6/CDFV).

The theorem is stated geometrically in terms of two curvature disks whose
interiors miss the polygon and two curvature disks which contain the polygon,
with the four circles pairwise distinct.  In the current formal interface, this
is recorded as the corresponding plateau-aware Dahlberg four-vertex statement
for the previous-vertex curvature-radius profile. -/
def DahlbergE2ConvexDfvRadiusWitnesses {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  DahlbergFourVertex (EdgePrevCircleRadiusProfile v)

/-- Exact source form of Dahlberg's Theorem 6.

It records the paper's unordered pair of containing curvature disks and
unordered pair of interior-missing curvature disks, with all four curvature
circles pairwise distinct. -/
def DahlbergE2Theorem6ExactPaperSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6PaperCertificate v)

/-- Legacy strengthened CDFV source used by the earlier reduction.

Unlike Dahlberg's Theorem 6 itself, this source additionally requires the
four disk witnesses to occur in alternating cyclic order and carries
plateau-aware extrema at those same indices.  The exact paper statement is
`DahlbergE2Theorem6ExactPaperSource`; the extra bridge must be proved
separately. -/
def DahlbergE2Theorem6GeometricCdfvSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6CdfvCertificate v)

/-- Dahlberg §3 Lemma 5 source: in the strictly convex nonconcyclic branch,
there are two distinct curvature disks containing all vertices. -/
def DahlbergE2Theorem6Lemma5ContainingDisksSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v)

/-- Dahlberg §3 Lemma 7 source: in the strictly convex nonconcyclic branch,
there are two distinct curvature disks whose interiors contain no vertices. -/
def DahlbergE2Theorem6Lemma7InteriorMissingDisksSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v)

/-- The final §3 assembly step in Dahlberg's proof of Theorem 6: the two
Lemma 5 disks and two Lemma 7 disks are arranged into the ordered CDFV
certificate used by the Lean reduction. -/
def DahlbergE2Theorem6AssemblySource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6CdfvCertificate v)

/-- Dahlberg's Lemmas 5 and 7 imply the exact statement of Theorem 6.

The only fields not already present in the two lemma certificates are the
four cross-type circle inequalities, which follow from nonconcyclicity. -/
theorem dahlbergE2Theorem6ExactPaperSource_of_lemma5_lemma7
    (hlemma5 : DahlbergE2Theorem6Lemma5ContainingDisksSource)
    (hlemma7 : DahlbergE2Theorem6Lemma7InteriorMissingDisksSource) :
    DahlbergE2Theorem6ExactPaperSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  rcases hlemma5 hn hsimple hregular horient hnoncircle with ⟨containing⟩
  rcases hlemma7 hn hsimple hregular horient hnoncircle with ⟨interiorMissing⟩
  exact ⟨dahlbergE2Theorem6PaperCertificate_of_splitCertificates
    hsimple hnoncircle containing interiorMissing⟩

/-- Source-free paper source for Dahlberg §3 Lemma 5. -/
theorem dahlbergE2_theorem6_lemma5_containing_disks_source :
    DahlbergE2Theorem6Lemma5ContainingDisksSource := by
  intro n hne hn v hsimple _hregular horient hnoncircle
  letI : NeZero n := hne
  have hsupport : StrictConvexEdgeSupport v :=
    Gluck.Discrete.strictConvexEdgeSupport_of_simple_positiveOrientation
      hsimple horient
  have hgeom : StrictConvexCyclicChordGeometry v :=
    strictConvexCyclicChordGeometry_of_edgeSupport hsupport
  exact dahlbergE2Theorem6Lemma5ContainingDisks
    hn hsimple horient hsupport hgeom hnoncircle

/-- Source-free paper source for Dahlberg §3 Lemma 7. -/
theorem dahlbergE2_theorem6_lemma7_interior_missing_disks_source :
    DahlbergE2Theorem6Lemma7InteriorMissingDisksSource := by
  intro n hne hn v hsimple _hregular horient hnoncircle
  letI : NeZero n := hne
  have hsupport : StrictConvexEdgeSupport v :=
    Gluck.Discrete.strictConvexEdgeSupport_of_simple_positiveOrientation
      hsimple horient
  have hgeom : StrictConvexCyclicChordGeometry v :=
    strictConvexCyclicChordGeometry_of_edgeSupport hsupport
  exact dahlbergE2Theorem6Lemma7InteriorMissingDisks
    hn hsimple horient hsupport hgeom hnoncircle

/-- Source-free exact form of Dahlberg's §3 Theorem 6. -/
theorem dahlbergE2_theorem6_exact_paper_source :
    DahlbergE2Theorem6ExactPaperSource := by
  exact dahlbergE2Theorem6ExactPaperSource_of_lemma5_lemma7
    dahlbergE2_theorem6_lemma5_containing_disks_source
    dahlbergE2_theorem6_lemma7_interior_missing_disks_source

/-- The exact Theorem 6 source projects back to Dahlberg's Lemmas 5 and 7. -/
theorem dahlbergE2Theorem6_lemma5_lemma7_of_exactPaperSource
    (hsrc : DahlbergE2Theorem6ExactPaperSource) :
    DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
      DahlbergE2Theorem6Lemma7InteriorMissingDisksSource := by
  constructor
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨cert.containing⟩
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨cert.interiorMissing⟩

/-- The exact Theorem 6 source is precisely the conjunction of the paper's
Lemmas 5 and 7 on the current certificate interfaces. -/
theorem dahlbergE2Theorem6ExactPaperSource_iff_lemma5_lemma7 :
    DahlbergE2Theorem6ExactPaperSource ↔
      DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
        DahlbergE2Theorem6Lemma7InteriorMissingDisksSource := by
  constructor
  · exact dahlbergE2Theorem6_lemma5_lemma7_of_exactPaperSource
  · rintro ⟨hlemma5, hlemma7⟩
    exact dahlbergE2Theorem6ExactPaperSource_of_lemma5_lemma7 hlemma5 hlemma7

/-- Sharper assembly interface for Dahlberg §3 Theorem 6: construct ordered
disk data and prove the matching radius-profile extrema separately. -/
def DahlbergE2Theorem6OrderedAssemblySource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty
      { disk : DahlbergE2Theorem6OrderedDiskCertificate v //
        DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate disk }

/-- Geometric assembly interface for Dahlberg §3 Theorem 6: the final
assembly step returns ordered disk data, the formal boundary-incidence facts
for the defining triples, and the matching radius extrema. -/
def DahlbergE2Theorem6GeometricAssemblySource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6GeometricAssemblyCertificate v)

/-- Weak geometric assembly interface for Dahlberg §3 Theorem 6: the final
ordering step returns ordered disk data plus the weak radius inequalities that
are already formally forced by those disk hypotheses. -/
def DahlbergE2Theorem6WeakGeometricAssemblySource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6WeakGeometricAssemblyCertificate v)

/-- Minimal ordered-disk selection interface for Dahlberg §3 Theorem 6:
after Lemma 5 and Lemma 7 supply two containing and two interior-missing
curvature disks, the remaining ordering step chooses the four disks in cyclic
order and proves their pairwise circle distinctness.  Boundary incidence and
weak one-step radius inequalities are then formal consequences of this data. -/
def DahlbergE2Theorem6OrderedDiskSelectionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6OrderedDiskCertificate v)

/-- Certificate-level alternating arrangement interface for Dahlberg §3
Theorem 6.

After Lemma 5 and Lemma 7 have supplied the actual two containing disks and
the actual two interior-missing disks, the remaining ordering step chooses
them in alternating cyclic order.  The same-type distinctness fields are
already part of those two certificates. -/
def DahlbergE2Theorem6AlternatingDiskArrangementSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    DahlbergE2Theorem6ContainingDisksCertificate v →
    DahlbergE2Theorem6InteriorMissingDisksCertificate v →
    Nonempty (DahlbergE2Theorem6AlternatingDiskCertificate v)

/-- Sharper ordered-disk selection interface for Dahlberg §3 Theorem 6:
the paper-level ordering step only has to choose the two containing and two
interior-missing disks in alternating cyclic order and carry the same-type
distinctness supplied by Lemmas 5 and 7.

All cross distinctness between a containing disk and an interior-missing disk
is now formal from nonconcyclicity. -/
def DahlbergE2Theorem6AlternatingDiskSelectionSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6AlternatingDiskCertificate v)

/-- A certificate-level arrangement source implies the older selection source
by unpacking the Lemma 5 and Lemma 7 existence packages. -/
theorem dahlbergE2Theorem6AlternatingDiskSelectionSource_of_arrangementSource
    (hsrc : DahlbergE2Theorem6AlternatingDiskArrangementSource) :
    DahlbergE2Theorem6AlternatingDiskSelectionSource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hcontains with ⟨contains⟩
  rcases hmisses with ⟨misses⟩
  exact hsrc hn hsimple hregular horient hnoncircle contains misses

/-- Alternating disk selection implies the older ordered-disk selection source
by formally filling the cross-distinctness fields. -/
theorem dahlbergE2Theorem6OrderedDiskSelectionSource_of_alternatingDiskSelectionSource
    (hsrc : DahlbergE2Theorem6AlternatingDiskSelectionSource) :
    DahlbergE2Theorem6OrderedDiskSelectionSource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨cert⟩
  exact ⟨
    dahlbergE2Theorem6OrderedDiskCertificate_of_alternatingDiskCertificate
      hsimple hnoncircle cert⟩

/-- Ordered-disk selection implies alternating-disk selection by forgetting
the cross-distinctness fields. -/
theorem dahlbergE2Theorem6AlternatingDiskSelectionSource_of_orderedDiskSelectionSource
    (hsrc : DahlbergE2Theorem6OrderedDiskSelectionSource) :
    DahlbergE2Theorem6AlternatingDiskSelectionSource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨cert⟩
  exact ⟨dahlbergE2Theorem6AlternatingDiskCertificate_of_orderedDiskCertificate cert⟩

/-- At the selection-source level, alternating and ordered disk certificates
are formally equivalent; the only nontrivial added fields in the ordered
certificate are cross distinctness, already proved from nonconcyclicity. -/
theorem dahlbergE2Theorem6AlternatingDiskSelectionSource_iff_orderedDiskSelectionSource :
    DahlbergE2Theorem6AlternatingDiskSelectionSource ↔
      DahlbergE2Theorem6OrderedDiskSelectionSource := by
  constructor
  · exact dahlbergE2Theorem6OrderedDiskSelectionSource_of_alternatingDiskSelectionSource
  · exact dahlbergE2Theorem6AlternatingDiskSelectionSource_of_orderedDiskSelectionSource

/-- Ordered disk selection is enough for the weak geometric assembly source,
because boundary incidence and the weak radius inequalities have already been
proved from positive orientation, regularity, and the disk hypotheses. -/
theorem dahlbergE2Theorem6WeakGeometricAssemblySource_of_orderedDiskSelectionSource
    (hsrc : DahlbergE2Theorem6OrderedDiskSelectionSource) :
    DahlbergE2Theorem6WeakGeometricAssemblySource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨disk⟩
  exact ⟨
    dahlbergE2Theorem6WeakGeometricAssemblyCertificate_of_orderedDiskCertificate
      hsimple hregular horient disk⟩

/-- Remaining §3 plateau upgrade: the global cyclic/plateau argument upgrades
weak one-step radius inequalities around the ordered curvature disks to the
plateau-aware local extrema certificate used by the Lean CDFV reduction. -/
def DahlbergE2Theorem6PlateauUpgradeSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    Nonempty (DahlbergE2Theorem6ContainingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6InteriorMissingDisksCertificate v) →
    Nonempty (DahlbergE2Theorem6WeakGeometricAssemblyCertificate v) →
    Nonempty (DahlbergE2Theorem6GeometricAssemblyCertificate v)

/-- Sharper plateau upgrade for Dahlberg §3 Theorem 6: once ordered disk
selection and the formal weak assembly construction have fixed a weak
certificate, the remaining global cyclic/plateau argument only has to upgrade
that same ordered disk's weak one-step inequalities to the plateau-aware
radius-extrema certificate. -/
def DahlbergE2Theorem6PlateauExtremaUpgradeSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    ∀ weak : DahlbergE2Theorem6WeakGeometricAssemblyCertificate v,
      Nonempty (DahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate weak.disk)

/-- Finer plateau upgrade for Dahlberg §3 Theorem 6: for the fixed weak
ordered-disk certificate, the remaining argument produces explicit
left/right plateau exits at the four ordered disks.

This source is closer to the paper proof than
`DahlbergE2Theorem6PlateauExtremaUpgradeSource`: it does not directly assert
local extrema, but asserts the finite plateau-resolution data from which the
local-extremum package is formally reconstructed. -/
def DahlbergE2Theorem6PlateauResolutionUpgradeSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    ∀ weak : DahlbergE2Theorem6WeakGeometricAssemblyCertificate v,
      Nonempty
        (DahlbergE2Theorem6PlateauResolutionForOrderedDiskCertificate weak.disk)

/-- Explicit plateau exits imply the sharper local-extrema upgrade source. -/
theorem dahlbergE2Theorem6PlateauExtremaUpgradeSource_of_plateauResolutionUpgradeSource
    (hsrc : DahlbergE2Theorem6PlateauResolutionUpgradeSource) :
    DahlbergE2Theorem6PlateauExtremaUpgradeSource := by
  intro n hne hn v hsimple hregular horient hnoncircle weak
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle weak with ⟨hres⟩
  exact ⟨
    dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_plateauResolution
      hres⟩

/-- The plateau-extrema upgrade source also supplies explicit plateau
resolution, because `DiscreteLocalMax` and `DiscreteLocalMin` are exactly the
left/right plateau-exit witness packages. -/
theorem dahlbergE2Theorem6PlateauResolutionUpgradeSource_of_plateauExtremaUpgradeSource
    (hsrc : DahlbergE2Theorem6PlateauExtremaUpgradeSource) :
    DahlbergE2Theorem6PlateauResolutionUpgradeSource := by
  intro n hne hn v hsimple hregular horient hnoncircle weak
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle weak with ⟨hext⟩
  exact ⟨
    dahlbergE2Theorem6PlateauResolution_of_radiusExtremaForOrderedDiskCertificate
      hext⟩

/-- The explicit plateau-resolution and local-extrema upgrade interfaces are
formally equivalent. -/
theorem dahlbergE2Theorem6PlateauResolutionUpgradeSource_iff_plateauExtremaUpgradeSource :
    DahlbergE2Theorem6PlateauResolutionUpgradeSource ↔
      DahlbergE2Theorem6PlateauExtremaUpgradeSource := by
  constructor
  · exact dahlbergE2Theorem6PlateauExtremaUpgradeSource_of_plateauResolutionUpgradeSource
  · exact dahlbergE2Theorem6PlateauResolutionUpgradeSource_of_plateauExtremaUpgradeSource

/-- The sharper plateau-extrema source implies the older plateau-upgrade
source by rebuilding a geometric assembly certificate from the upgraded
extrema for the weak certificate's own ordered disk. -/
theorem dahlbergE2Theorem6PlateauUpgradeSource_of_plateauExtremaUpgradeSource
    (hsrc : DahlbergE2Theorem6PlateauExtremaUpgradeSource) :
    DahlbergE2Theorem6PlateauUpgradeSource := by
  intro n hne hn v hsimple hregular horient hnoncircle _hcontains _hmisses hweak
  letI : NeZero n := hne
  rcases hweak with ⟨weak⟩
  rcases hsrc hn hsimple hregular horient hnoncircle weak with ⟨hext⟩
  exact ⟨
    dahlbergE2Theorem6GeometricAssemblyCertificate_of_orderedDiskCertificate
      hsimple horient weak.disk hext⟩

/-- The sharper ordered assembly source implies the older full-CDFV assembly
source. -/
theorem dahlbergE2Theorem6AssemblySource_of_orderedAssemblySource
    (hsrc : DahlbergE2Theorem6OrderedAssemblySource) :
    DahlbergE2Theorem6AssemblySource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨⟨disk, hext⟩⟩
  exact ⟨dahlbergE2Theorem6CdfvCertificate_of_orderedDiskCertificate disk hext⟩

/-- The older full-CDFV assembly source implies the sharper ordered assembly
source by projecting the ordered disk data and local-extrema proof from the
full certificate. -/
theorem dahlbergE2Theorem6OrderedAssemblySource_of_assemblySource
    (hsrc : DahlbergE2Theorem6AssemblySource) :
    DahlbergE2Theorem6OrderedAssemblySource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with ⟨cert⟩
  exact ⟨⟨dahlbergE2Theorem6OrderedDiskCertificate_of_cdfvCertificate cert,
    dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_cdfvCertificate cert⟩⟩

/-- The geometric assembly source implies the ordered assembly source by
forgetting the boundary-incidence proof. -/
theorem dahlbergE2Theorem6OrderedAssemblySource_of_geometricAssemblySource
    (hsrc : DahlbergE2Theorem6GeometricAssemblySource) :
    DahlbergE2Theorem6OrderedAssemblySource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨cert⟩
  exact ⟨⟨cert.disk, cert.extrema⟩⟩

/-- The ordered assembly source implies the geometric assembly source because
boundary incidence of the four defining triples is already formal in the
positive-orientation branch. -/
theorem dahlbergE2Theorem6GeometricAssemblySource_of_orderedAssemblySource
    (hsrc : DahlbergE2Theorem6OrderedAssemblySource) :
    DahlbergE2Theorem6GeometricAssemblySource := by
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle hcontains hmisses with
    ⟨⟨disk, hext⟩⟩
  exact ⟨
    dahlbergE2Theorem6GeometricAssemblyCertificate_of_orderedDiskCertificate
      hsimple horient disk hext⟩

/-- The ordered and geometric §3 assembly interfaces are formally equivalent:
the geometric interface only adds boundary-incidence data that is now proved
from the local circumcircle construction. -/
theorem dahlbergE2Theorem6OrderedAssemblySource_iff_geometricAssemblySource :
    DahlbergE2Theorem6OrderedAssemblySource ↔
      DahlbergE2Theorem6GeometricAssemblySource := by
  constructor
  · exact dahlbergE2Theorem6GeometricAssemblySource_of_orderedAssemblySource
  · exact dahlbergE2Theorem6OrderedAssemblySource_of_geometricAssemblySource

/-- The older and sharper §3 assembly interfaces are formally equivalent. -/
theorem dahlbergE2Theorem6AssemblySource_iff_orderedAssemblySource :
    DahlbergE2Theorem6AssemblySource ↔ DahlbergE2Theorem6OrderedAssemblySource := by
  constructor
  · exact dahlbergE2Theorem6OrderedAssemblySource_of_assemblySource
  · exact dahlbergE2Theorem6AssemblySource_of_orderedAssemblySource

/-- Paper-facing sources for Dahlberg's §3 Theorem 6 / CDFV: Lemma 5,
Lemma 7, and their final assembly. -/
def DahlbergE2Theorem6PaperSources : Prop :=
  DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
  DahlbergE2Theorem6Lemma7InteriorMissingDisksSource ∧
  DahlbergE2Theorem6GeometricAssemblySource

/-- Sharper paper-facing sources for Dahlberg's §3 Theorem 6 / CDFV: Lemma 5,
Lemma 7, weak geometric assembly, and the remaining global plateau upgrade. -/
def DahlbergE2Theorem6WeakPaperSources : Prop :=
  DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
  DahlbergE2Theorem6Lemma7InteriorMissingDisksSource ∧
  DahlbergE2Theorem6WeakGeometricAssemblySource ∧
  DahlbergE2Theorem6PlateauUpgradeSource

/-- Sharper §3 paper-facing source package: Lemma 5, Lemma 7, the purely
geometric ordered-disk selection, and the remaining plateau upgrade.  Compared
with `DahlbergE2Theorem6WeakPaperSources`, the weak boundary/incidence and
one-step radius facts are no longer imported from the paper. -/
def DahlbergE2Theorem6OrderedDiskPaperSources : Prop :=
  DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
  DahlbergE2Theorem6Lemma7InteriorMissingDisksSource ∧
  DahlbergE2Theorem6OrderedDiskSelectionSource ∧
  DahlbergE2Theorem6PlateauUpgradeSource

/-- Sharpest current §3 paper-facing source package: Lemma 5, Lemma 7,
certificate-level alternating disk arrangement, and explicit
plateau-resolution data for the selected weak certificate.

Cross distinctness between containing and interior-missing disks, weak
geometric assembly, and local-extremum reconstruction are formal. -/
def DahlbergE2Theorem6SharpOrderedDiskPaperSources : Prop :=
  DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
  DahlbergE2Theorem6Lemma7InteriorMissingDisksSource ∧
  DahlbergE2Theorem6AlternatingDiskArrangementSource ∧
  DahlbergE2Theorem6PlateauResolutionUpgradeSource

/-- The sharpest current §3 package implies the ordered-disk package by
turning certificate-level alternating arrangement into ordered selection,
explicit plateau exits into local extrema, and then wrapping that as the older
plateau-upgrade source. -/
theorem dahlbergE2Theorem6OrderedDiskPaperSources_of_sharpOrderedDiskPaperSources
    (hsrc : DahlbergE2Theorem6SharpOrderedDiskPaperSources) :
    DahlbergE2Theorem6OrderedDiskPaperSources := by
  exact ⟨hsrc.1, hsrc.2.1,
    dahlbergE2Theorem6OrderedDiskSelectionSource_of_alternatingDiskSelectionSource
      (dahlbergE2Theorem6AlternatingDiskSelectionSource_of_arrangementSource
        hsrc.2.2.1),
    dahlbergE2Theorem6PlateauUpgradeSource_of_plateauExtremaUpgradeSource
      (dahlbergE2Theorem6PlateauExtremaUpgradeSource_of_plateauResolutionUpgradeSource
        hsrc.2.2.2)⟩

/-- The ordered-disk §3 source package implies the older weak package by
constructing the weak geometric assembly certificate formally. -/
theorem dahlbergE2Theorem6WeakPaperSources_of_orderedDiskPaperSources
    (hsrc : DahlbergE2Theorem6OrderedDiskPaperSources) :
    DahlbergE2Theorem6WeakPaperSources := by
  exact ⟨hsrc.1, hsrc.2.1,
    dahlbergE2Theorem6WeakGeometricAssemblySource_of_orderedDiskSelectionSource
      hsrc.2.2.1,
    hsrc.2.2.2⟩

/-- The weak §3 paper-source package implies the older full paper-source
package by applying the plateau upgrade to the weak assembly certificate. -/
theorem dahlbergE2Theorem6PaperSources_of_weakPaperSources
    (hsrc : DahlbergE2Theorem6WeakPaperSources) :
    DahlbergE2Theorem6PaperSources := by
  refine ⟨hsrc.1, hsrc.2.1, ?_⟩
  intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
  letI : NeZero n := hne
  exact hsrc.2.2.2 hn hsimple hregular horient hnoncircle hcontains hmisses
    (hsrc.2.2.1 hn hsimple hregular horient hnoncircle hcontains hmisses)

/-- The older full §3 paper-source package implies the sharper weak package by
forgetting the plateau-aware extrema to the formally proved weak inequalities;
the plateau upgrade is then recovered by reusing the full assembly source. -/
theorem dahlbergE2Theorem6WeakPaperSources_of_paperSources
    (hsrc : DahlbergE2Theorem6PaperSources) :
    DahlbergE2Theorem6WeakPaperSources := by
  refine ⟨hsrc.1, hsrc.2.1, ?_, ?_⟩
  · intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
    letI : NeZero n := hne
    rcases hsrc.2.2 hn hsimple hregular horient hnoncircle hcontains hmisses with
      ⟨cert⟩
    exact ⟨
      dahlbergE2Theorem6WeakGeometricAssemblyCertificate_of_geometricAssemblyCertificate
        hsimple hregular horient cert⟩
  · intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses _hweak
    letI : NeZero n := hne
    exact hsrc.2.2 hn hsimple hregular horient hnoncircle hcontains hmisses

/-- The full §3 paper-source package implies the sharper ordered-disk package
by projecting the ordered disk data from the geometric assembly certificate. -/
theorem dahlbergE2Theorem6OrderedDiskPaperSources_of_paperSources
    (hsrc : DahlbergE2Theorem6PaperSources) :
    DahlbergE2Theorem6OrderedDiskPaperSources := by
  refine ⟨hsrc.1, hsrc.2.1, ?_, ?_⟩
  · intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses
    letI : NeZero n := hne
    rcases hsrc.2.2 hn hsimple hregular horient hnoncircle hcontains hmisses with
      ⟨cert⟩
    exact ⟨cert.disk⟩
  · intro n hne hn v hsimple hregular horient hnoncircle hcontains hmisses _hweak
    letI : NeZero n := hne
    exact hsrc.2.2 hn hsimple hregular horient hnoncircle hcontains hmisses

/-- The sharper ordered-disk package implies the full §3 paper-source package. -/
theorem dahlbergE2Theorem6PaperSources_of_orderedDiskPaperSources
    (hsrc : DahlbergE2Theorem6OrderedDiskPaperSources) :
    DahlbergE2Theorem6PaperSources :=
  dahlbergE2Theorem6PaperSources_of_weakPaperSources
    (dahlbergE2Theorem6WeakPaperSources_of_orderedDiskPaperSources hsrc)

/-- The sharper ordered-disk and full §3 paper-source packages are equivalent. -/
theorem dahlbergE2Theorem6OrderedDiskPaperSources_iff_paperSources :
    DahlbergE2Theorem6OrderedDiskPaperSources ↔ DahlbergE2Theorem6PaperSources := by
  constructor
  · exact dahlbergE2Theorem6PaperSources_of_orderedDiskPaperSources
  · exact dahlbergE2Theorem6OrderedDiskPaperSources_of_paperSources

/-- The older and sharper §3 paper-source packages are equivalent. -/
theorem dahlbergE2Theorem6WeakPaperSources_iff_paperSources :
    DahlbergE2Theorem6WeakPaperSources ↔ DahlbergE2Theorem6PaperSources := by
  constructor
  · exact dahlbergE2Theorem6PaperSources_of_weakPaperSources
  · exact dahlbergE2Theorem6WeakPaperSources_of_paperSources

/-- The split §3 paper sources imply the current geometric CDFV source. -/
theorem dahlbergE2Theorem6GeometricCdfvSource_of_paperSources
    (hsrc : DahlbergE2Theorem6PaperSources) :
    DahlbergE2Theorem6GeometricCdfvSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact dahlbergE2Theorem6AssemblySource_of_orderedAssemblySource
    (dahlbergE2Theorem6OrderedAssemblySource_of_geometricAssemblySource hsrc.2.2)
    hn hsimple hregular horient hnoncircle
    (hsrc.1 hn hsimple hregular horient hnoncircle)
    (hsrc.2.1 hn hsimple hregular horient hnoncircle)

/-- A full CDFV certificate contains Dahlberg §3 Lemma 5's two containing
curvature disks. -/
def dahlbergE2Theorem6ContainingDisksCertificate_of_cdfvCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6ContainingDisksCertificate v := by
  exact
    { i := cert.i₁
      j := cert.i₃
      contains_i := cert.contains₁
      contains_j := cert.contains₃
      distinct := cert.circle₁_ne₃ }

/-- A full CDFV certificate contains Dahlberg §3 Lemma 7's two
interior-missing curvature disks. -/
def dahlbergE2Theorem6InteriorMissingDisksCertificate_of_cdfvCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6InteriorMissingDisksCertificate v := by
  exact
    { i := cert.i₂
      j := cert.i₄
      misses_i := cert.misses₂
      misses_j := cert.misses₄
      distinct := cert.circle₂_ne₄ }

/-- Forget the additional cyclic-order and local-extremum data from the
legacy strengthened CDFV certificate, retaining exactly Dahlberg's four-disk
Theorem 6 conclusion. -/
def dahlbergE2Theorem6PaperCertificate_of_cdfvCertificate
    {n : ℕ} {v : ZMod n → ℂ}
    (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2Theorem6PaperCertificate v :=
  { containing :=
      dahlbergE2Theorem6ContainingDisksCertificate_of_cdfvCertificate cert
    interiorMissing :=
      dahlbergE2Theorem6InteriorMissingDisksCertificate_of_cdfvCertificate cert
    containing_i_ne_missing_i := cert.circle₁_ne₂
    containing_i_ne_missing_j := cert.circle₁_ne₄
    containing_j_ne_missing_i := cert.circle₂_ne₃.symm
    containing_j_ne_missing_j := cert.circle₃_ne₄ }

/-- The legacy strengthened CDFV source implies the exact statement of
Dahlberg's Theorem 6 by forgetting its uncited extra data. -/
theorem dahlbergE2Theorem6ExactPaperSource_of_geometricCdfvSource
    (hsrc : DahlbergE2Theorem6GeometricCdfvSource) :
    DahlbergE2Theorem6ExactPaperSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
  exact ⟨dahlbergE2Theorem6PaperCertificate_of_cdfvCertificate cert⟩

/-- The geometric CDFV source implies the split §3 paper sources.  The assembly
component is immediate because the full CDFV certificate is already supplied. -/
theorem dahlbergE2Theorem6PaperSources_of_geometricCdfvSource
    (hsrc : DahlbergE2Theorem6GeometricCdfvSource) :
    DahlbergE2Theorem6PaperSources := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨dahlbergE2Theorem6ContainingDisksCertificate_of_cdfvCertificate cert⟩
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨dahlbergE2Theorem6InteriorMissingDisksCertificate_of_cdfvCertificate cert⟩
  · intro n hne hn v hsimple hregular horient hnoncircle _hcontains _hmisses
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨dahlbergE2Theorem6GeometricAssemblyCertificate_of_cdfvCertificate
      hsimple horient cert⟩

/-- The split §3 paper-source package is formally equivalent to the geometric
CDFV source used by the reduction. -/
theorem dahlbergE2Theorem6PaperSources_iff_geometricCdfvSource :
    DahlbergE2Theorem6PaperSources ↔ DahlbergE2Theorem6GeometricCdfvSource := by
  constructor
  · exact dahlbergE2Theorem6GeometricCdfvSource_of_paperSources
  · exact dahlbergE2Theorem6PaperSources_of_geometricCdfvSource

/-- Direct §3 assembly source for Dahlberg's Theorem 6 / CDFV.

After Lemma 5 and Lemma 7 have supplied the actual containing and
interior-missing disk certificates, the remaining §3 argument only has to
choose an ordered disk certificate and attach the matching plateau-resolution
data for that chosen certificate.  This avoids the stronger interface which
upgrades every possible weak certificate. -/
def DahlbergE2Theorem6OrderedDiskPlateauAssemblySource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    DahlbergE2Theorem6ContainingDisksCertificate v →
    DahlbergE2Theorem6InteriorMissingDisksCertificate v →
    Nonempty
      (Σ disk : DahlbergE2Theorem6OrderedDiskCertificate v,
        DahlbergE2Theorem6PlateauResolutionForOrderedDiskCertificate disk)

/-- Paper-facing §3 Theorem 6 sources with the final assembly stated directly
as one ordered-disk-plus-plateau certificate. -/
def DahlbergE2Theorem6OrderedDiskPlateauPaperSources : Prop :=
  DahlbergE2Theorem6Lemma5ContainingDisksSource ∧
  DahlbergE2Theorem6Lemma7InteriorMissingDisksSource ∧
  DahlbergE2Theorem6OrderedDiskPlateauAssemblySource

/-- The direct ordered-disk-plus-plateau §3 package implies Dahlberg's
geometric CDFV source. -/
theorem dahlbergE2Theorem6GeometricCdfvSource_of_orderedDiskPlateauPaperSources
    (hsrc : DahlbergE2Theorem6OrderedDiskPlateauPaperSources) :
    DahlbergE2Theorem6GeometricCdfvSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  rcases hsrc.1 hn hsimple hregular horient hnoncircle with ⟨contains⟩
  rcases hsrc.2.1 hn hsimple hregular horient hnoncircle with ⟨misses⟩
  rcases hsrc.2.2 hn hsimple hregular horient hnoncircle contains misses with
    ⟨⟨disk, hres⟩⟩
  exact ⟨
    dahlbergE2Theorem6CdfvCertificate_of_orderedDiskCertificate disk
      (dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_plateauResolution
        hres)⟩

/-- The direct ordered-disk-plus-plateau §3 package implies the older full
Theorem 6 paper-source package. -/
theorem dahlbergE2Theorem6PaperSources_of_orderedDiskPlateauPaperSources
    (hsrc : DahlbergE2Theorem6OrderedDiskPlateauPaperSources) :
    DahlbergE2Theorem6PaperSources := by
  exact dahlbergE2Theorem6PaperSources_of_geometricCdfvSource
    (dahlbergE2Theorem6GeometricCdfvSource_of_orderedDiskPlateauPaperSources
      hsrc)

/-- The geometric CDFV source also implies the direct
ordered-disk-plus-plateau §3 package: Lemma 5 and Lemma 7 are projected from
the full CDFV certificate, while the assembly component keeps the ordered disk
and extracts explicit plateau-resolution data from the certificate's local
extrema. -/
theorem dahlbergE2Theorem6OrderedDiskPlateauPaperSources_of_geometricCdfvSource
    (hsrc : DahlbergE2Theorem6GeometricCdfvSource) :
    DahlbergE2Theorem6OrderedDiskPlateauPaperSources := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨dahlbergE2Theorem6ContainingDisksCertificate_of_cdfvCertificate cert⟩
  · intro n hne hn v hsimple hregular horient hnoncircle
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    exact ⟨dahlbergE2Theorem6InteriorMissingDisksCertificate_of_cdfvCertificate cert⟩
  · intro n hne hn v hsimple hregular horient hnoncircle _contains _misses
    letI : NeZero n := hne
    rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
    let disk := dahlbergE2Theorem6OrderedDiskCertificate_of_cdfvCertificate cert
    let hext :=
      dahlbergE2Theorem6RadiusExtremaForOrderedDiskCertificate_of_cdfvCertificate
        cert
    exact ⟨⟨disk,
      dahlbergE2Theorem6PlateauResolution_of_radiusExtremaForOrderedDiskCertificate
        hext⟩⟩

/-- The direct ordered-disk-plus-plateau §3 package is formally equivalent to
the geometric CDFV source. -/
theorem dahlbergE2Theorem6OrderedDiskPlateauPaperSources_iff_geometricCdfvSource :
    DahlbergE2Theorem6OrderedDiskPlateauPaperSources ↔
      DahlbergE2Theorem6GeometricCdfvSource := by
  constructor
  · exact dahlbergE2Theorem6GeometricCdfvSource_of_orderedDiskPlateauPaperSources
  · exact dahlbergE2Theorem6OrderedDiskPlateauPaperSources_of_geometricCdfvSource

/-- A CDFV certificate projects to the radius-profile four-vertex witness
used by the formal reduction. -/
theorem dahlbergE2ConvexDfvRadiusWitnesses_of_theorem6Certificate {n : ℕ}
    {v : ZMod n → ℂ} (cert : DahlbergE2Theorem6CdfvCertificate v) :
    DahlbergE2ConvexDfvRadiusWitnesses v := by
  exact ⟨cert.i₁, cert.i₂, cert.i₃, cert.i₄,
    cert.i₁_lt_i₂, cert.i₂_lt_i₃, cert.i₃_lt_i₄, cert.i₄_lt_wrap,
    cert.localMax₁, cert.localMin₂, cert.localMax₃, cert.localMin₄⟩

/-- Dahlberg's radius-witness package already contains strict adjacent
boundary turns around the extremal radius plateaux.

This is the purely cyclic part of the Lemma 8/Lemma 9 bridge: it extracts
actual strict one-edge turns from the plateau-aware CDFV radius witnesses, but
does not yet assert Dahlberg's stronger ordered-adjacent-turn conclusion. -/
theorem dahlbergE2ConvexDfvRadiusWitnesses_exists_boundary_turns {n : ℕ}
    {v : ZMod n → ℂ} (hwitness : DahlbergE2ConvexDfvRadiusWitnesses v) :
    (∃ i : ZMod n,
        EdgePrevCircleRadiusProfile v i < EdgePrevCircleRadiusProfile v (i + 1)) ∧
      (∃ i : ZMod n,
        EdgePrevCircleRadiusProfile v (i + 1) < EdgePrevCircleRadiusProfile v i) ∧
      (∃ i : ZMod n,
        EdgePrevCircleRadiusProfile v i < EdgePrevCircleRadiusProfile v (i + 1)) ∧
      (∃ i : ZMod n,
        EdgePrevCircleRadiusProfile v (i + 1) < EdgePrevCircleRadiusProfile v i) := by
  exact hwitness.exists_boundary_turns

/-- In the positive-orientation branch, the radius-profile CDFV witness form is
equivalent to Dahlberg's conclusion for signed Menger curvature.

The forward implication is reciprocal-radius monotonicity.  The reverse
implication applies the same monotonicity to the positive signed-Menger profile
and uses `(ρ⁻¹)⁻¹ = ρ`. -/
theorem dahlbergE2ConvexDfvRadiusWitnesses_iff_signedMengerProfile_dahlbergFourVertex
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) :
    DahlbergE2ConvexDfvRadiusWitnesses v ↔
      DahlbergFourVertex (SignedMengerProfile v) := by
  constructor
  · intro hfv
    exact signedMengerProfile_dahlbergFourVertex_of_positiveRadiusProfile
      hsimple horient hfv
  · intro hfv
    have hρpos : ∀ i : ZMod n, 0 < EdgePrevCircleRadiusProfile v i :=
      EdgePrevCircleRadiusProfile_pos hsimple
    have hκpos : ∀ i : ZMod n, 0 < SignedMengerProfile v i := by
      intro i
      rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient i]
      exact inv_pos.mpr (hρpos i)
    have hinv : DahlbergFourVertex (fun i => (SignedMengerProfile v i)⁻¹) :=
      dahlbergFourVertex_inv_of_pos hκpos hfv
    exact dahlbergFourVertex_congr (κ := fun i => (SignedMengerProfile v i)⁻¹)
      (μ := EdgePrevCircleRadiusProfile v)
      (by
        intro i
        rw [signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
          hsimple horient i]
        exact (inv_inv (EdgePrevCircleRadiusProfile v i)).symm)
      hinv

/-- Dahlberg's radius-witness form gives the signed-Menger D4VT conclusion in
the positive-orientation branch. -/
theorem signedMengerProfile_dahlbergFourVertex_of_convexDfvRadiusWitnesses
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hfv : DahlbergE2ConvexDfvRadiusWitnesses v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact (dahlbergE2ConvexDfvRadiusWitnesses_iff_signedMengerProfile_dahlbergFourVertex
    hsimple horient).mp hfv

/-- A CDFV radius-witness package already forces the signed-Menger profile to
be nonconstant in the positive-orientation branch. -/
theorem not_constant_signedMengerProfile_of_convexDfvRadiusWitnesses
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hfv : DahlbergE2ConvexDfvRadiusWitnesses v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_of_dahlbergFourVertex
    (signedMengerProfile_dahlbergFourVertex_of_convexDfvRadiusWitnesses
      hsimple horient hfv)

/-- The signed-Menger D4VT conclusion gives Dahlberg's radius-witness form in
the positive-orientation branch. -/
theorem convexDfvRadiusWitnesses_of_signedMengerProfile_dahlbergFourVertex
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hfv : DahlbergFourVertex (SignedMengerProfile v)) :
    DahlbergE2ConvexDfvRadiusWitnesses v := by
  exact (dahlbergE2ConvexDfvRadiusWitnesses_iff_signedMengerProfile_dahlbergFourVertex
    hsimple horient).mpr hfv

/-- Adjacent positive radius turns imply the radius-profile witness form of
Dahlberg's convex discrete four-vertex theorem.

This is a formal compatibility lemma between the source interface used for
Lemma 9 and the CDFV witness interface above: the radius turns occur in
`min-max-min-max` order, so the cyclic conclusion is obtained with the
corresponding rotated constructor. -/
theorem dahlbergE2ConvexDfvRadiusWitnesses_of_positiveRadiusOrderedAdjacentTurns
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    DahlbergE2ConvexDfvRadiusWitnesses v := by
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hmin₁_left, hmin₁_right, hmax₂_left, hmax₂_right,
      hmin₃_left, hmin₃_right, hmax₄_left, hmax₄_right⟩
  have hi₁₂' : i₁ + 1 < i₂ + 1 := Nat.succ_lt_succ hi₁₂
  have hi₂₃' : i₂ + 1 < i₃ + 1 := Nat.succ_lt_succ hi₂₃
  have hi₃₄' : i₃ + 1 < i₄ + 1 := Nat.succ_lt_succ hi₃₄
  have hi₄₁' : i₄ + 1 < (i₁ + 1) + n := by
    omega
  have hmin₁_left' :
      EdgePrevCircleRadiusProfile v ((i₁ + 1 : ℕ) : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₁ + 1 : ℕ) : ZMod n) - 1) := by
    have h :
        EdgePrevCircleRadiusProfile v ((i₁ : ZMod n) + 1) <
          EdgePrevCircleRadiusProfile v (i₁ : ZMod n) := by
      simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient (i₁ : ZMod n)] using hmin₁_left
    simpa [sub_eq_add_neg, add_assoc] using h
  have hmin₁_right' :
      EdgePrevCircleRadiusProfile v ((i₁ + 1 : ℕ) : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₁ + 1 : ℕ) : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₁ : ZMod n) + 1)), add_assoc] using hmin₁_right
  have hmax₂_left' :
      EdgePrevCircleRadiusProfile v (((i₂ + 1 : ℕ) : ZMod n) - 1) <
        EdgePrevCircleRadiusProfile v ((i₂ + 1 : ℕ) : ZMod n) := by
    have h :
        EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
          EdgePrevCircleRadiusProfile v ((i₂ : ZMod n) + 1) := by
      simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient (i₂ : ZMod n)] using hmax₂_left
    simpa [sub_eq_add_neg, add_assoc] using h
  have hmax₂_right' :
      EdgePrevCircleRadiusProfile v (((i₂ + 1 : ℕ) : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v ((i₂ + 1 : ℕ) : ZMod n) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₂ : ZMod n) + 1)), add_assoc] using hmax₂_right
  have hmin₃_left' :
      EdgePrevCircleRadiusProfile v ((i₃ + 1 : ℕ) : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₃ + 1 : ℕ) : ZMod n) - 1) := by
    have h :
        EdgePrevCircleRadiusProfile v ((i₃ : ZMod n) + 1) <
          EdgePrevCircleRadiusProfile v (i₃ : ZMod n) := by
      simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient (i₃ : ZMod n)] using hmin₃_left
    simpa [sub_eq_add_neg, add_assoc] using h
  have hmin₃_right' :
      EdgePrevCircleRadiusProfile v ((i₃ + 1 : ℕ) : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₃ + 1 : ℕ) : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₃ : ZMod n) + 1)), add_assoc] using hmin₃_right
  have hmax₄_left' :
      EdgePrevCircleRadiusProfile v (((i₄ + 1 : ℕ) : ZMod n) - 1) <
        EdgePrevCircleRadiusProfile v ((i₄ + 1 : ℕ) : ZMod n) := by
    have h :
        EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
          EdgePrevCircleRadiusProfile v ((i₄ : ZMod n) + 1) := by
      simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
        hsimple horient (i₄ : ZMod n)] using hmax₄_left
    simpa [sub_eq_add_neg, add_assoc] using h
  have hmax₄_right' :
      EdgePrevCircleRadiusProfile v (((i₄ + 1 : ℕ) : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v ((i₄ + 1 : ℕ) : ZMod n) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (((i₄ : ZMod n) + 1)), add_assoc] using hmax₄_right
  exact dahlbergFourVertex_of_strict_neighbors_min_max (two_le_of_four_le hn)
    hi₁₂' hi₂₃' hi₃₄' hi₄₁'
    hmin₁_left' hmin₁_right'
    hmax₂_left' hmax₂_right'
    hmin₃_left' hmin₃_right'
    hmax₄_left' hmax₄_right'

/-- Positive radius ordered turns are ordered turns of the reciprocal previous
radius profile. -/
theorem orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile_of_positiveRadiusOrderedAdjacentTurns
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    OrderedAdjacentTurns (fun i => (EdgePrevCircleRadiusProfile v i)⁻¹) := by
  have hpos : ∀ i : ZMod n, 0 < EdgePrevCircleRadiusProfile v i :=
    EdgePrevCircleRadiusProfile_pos hsimple
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hinc₁, hdec₁, hdec₂, hinc₂, hinc₃, hdec₃, hdec₄, hinc₄⟩
  have hinc₁' :
      EdgePrevCircleRadiusProfile v ((i₁ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₁ : ZMod n)] using hinc₁
  have hdec₁' :
      EdgePrevCircleRadiusProfile v ((i₁ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₁ : ZMod n) + 1), add_assoc] using hdec₁
  have hdec₂' :
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile v ((i₂ : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₂ : ZMod n)] using hdec₂
  have hinc₂' :
      EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1) + 1) <
        EdgePrevCircleRadiusProfile v ((i₂ : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₂ : ZMod n) + 1), add_assoc] using hinc₂
  have hinc₃' :
      EdgePrevCircleRadiusProfile v ((i₃ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₃ : ZMod n)] using hinc₃
  have hdec₃' :
      EdgePrevCircleRadiusProfile v ((i₃ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₃ : ZMod n) + 1), add_assoc] using hdec₃
  have hdec₄' :
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile v ((i₄ : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₄ : ZMod n)] using hdec₄
  have hinc₄' :
      EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1) + 1) <
        EdgePrevCircleRadiusProfile v ((i₄ : ZMod n) + 1) := by
    simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₄ : ZMod n) + 1), add_assoc] using hinc₄
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (inv_lt_inv₀ (hpos (i₁ : ZMod n)) (hpos ((i₁ : ZMod n) + 1))).mpr
      hinc₁'
  · exact (inv_lt_inv₀ (hpos (((i₁ : ZMod n) + 1) + 1))
        (hpos ((i₁ : ZMod n) + 1))).mpr hdec₁'
  · exact (inv_lt_inv₀ (hpos ((i₂ : ZMod n) + 1)) (hpos (i₂ : ZMod n))).mpr
      hdec₂'
  · exact (inv_lt_inv₀ (hpos ((i₂ : ZMod n) + 1))
        (hpos (((i₂ : ZMod n) + 1) + 1))).mpr hinc₂'
  · exact (inv_lt_inv₀ (hpos (i₃ : ZMod n)) (hpos ((i₃ : ZMod n) + 1))).mpr
      hinc₃'
  · exact (inv_lt_inv₀ (hpos (((i₃ : ZMod n) + 1) + 1))
        (hpos ((i₃ : ZMod n) + 1))).mpr hdec₃'
  · exact (inv_lt_inv₀ (hpos ((i₄ : ZMod n) + 1)) (hpos (i₄ : ZMod n))).mpr
      hdec₄'
  · exact (inv_lt_inv₀ (hpos ((i₄ : ZMod n) + 1))
        (hpos (((i₄ : ZMod n) + 1) + 1))).mpr hinc₄'

/-- Ordered turns of the reciprocal previous-radius profile are positive
radius ordered turns. -/
theorem positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : OrderedAdjacentTurns (fun i => (EdgePrevCircleRadiusProfile v i)⁻¹)) :
    PositiveRadiusOrderedAdjacentTurns v := by
  have hpos : ∀ i : ZMod n, 0 < EdgePrevCircleRadiusProfile v i :=
    EdgePrevCircleRadiusProfile_pos hsimple
  rcases hturns with
    ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁,
      hinc₁, hdec₁, hdec₂, hinc₂, hinc₃, hdec₃, hdec₄, hinc₄⟩
  have hinc₁' :
      EdgePrevCircleRadiusProfile v ((i₁ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) :=
    (inv_lt_inv₀ (hpos (i₁ : ZMod n)) (hpos ((i₁ : ZMod n) + 1))).mp hinc₁
  have hdec₁' :
      EdgePrevCircleRadiusProfile v ((i₁ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1) + 1) :=
    (inv_lt_inv₀ (hpos (((i₁ : ZMod n) + 1) + 1))
      (hpos ((i₁ : ZMod n) + 1))).mp hdec₁
  have hdec₂' :
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile v ((i₂ : ZMod n) + 1) :=
    (inv_lt_inv₀ (hpos ((i₂ : ZMod n) + 1)) (hpos (i₂ : ZMod n))).mp hdec₂
  have hinc₂' :
      EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1) + 1) <
        EdgePrevCircleRadiusProfile v ((i₂ : ZMod n) + 1) :=
    (inv_lt_inv₀ (hpos ((i₂ : ZMod n) + 1))
      (hpos (((i₂ : ZMod n) + 1) + 1))).mp hinc₂
  have hinc₃' :
      EdgePrevCircleRadiusProfile v ((i₃ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) :=
    (inv_lt_inv₀ (hpos (i₃ : ZMod n)) (hpos ((i₃ : ZMod n) + 1))).mp hinc₃
  have hdec₃' :
      EdgePrevCircleRadiusProfile v ((i₃ : ZMod n) + 1) <
        EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1) + 1) :=
    (inv_lt_inv₀ (hpos (((i₃ : ZMod n) + 1) + 1))
      (hpos ((i₃ : ZMod n) + 1))).mp hdec₃
  have hdec₄' :
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile v ((i₄ : ZMod n) + 1) :=
    (inv_lt_inv₀ (hpos ((i₄ : ZMod n) + 1)) (hpos (i₄ : ZMod n))).mp hdec₄
  have hinc₄' :
      EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1) + 1) <
        EdgePrevCircleRadiusProfile v ((i₄ : ZMod n) + 1) :=
    (inv_lt_inv₀ (hpos ((i₄ : ZMod n) + 1))
      (hpos (((i₄ : ZMod n) + 1) + 1))).mp hinc₄
  refine ⟨i₁, i₂, i₃, i₄, hi₁₂, hi₂₃, hi₃₄, hi₄₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₁ : ZMod n)] using hinc₁'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₁ : ZMod n) + 1), add_assoc] using hdec₁'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₂ : ZMod n)] using hdec₂'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₂ : ZMod n) + 1), add_assoc] using hinc₂'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₃ : ZMod n)] using hinc₃'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₃ : ZMod n) + 1), add_assoc] using hdec₃'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient (i₄ : ZMod n)] using hdec₄'
  · simpa [EdgeNextCircleRadiusProfile_eq_edgePrevCircleRadiusProfile_succ_of_positiveOrientation
      hsimple horient ((i₄ : ZMod n) + 1), add_assoc] using hinc₄'

/-- Positive radius ordered turns are equivalent to ordered turns of the
reciprocal previous-radius profile. -/
theorem positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile
    {n : ℕ} {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) :
    PositiveRadiusOrderedAdjacentTurns v ↔
      OrderedAdjacentTurns (fun i => (EdgePrevCircleRadiusProfile v i)⁻¹) := by
  constructor
  · exact orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient
  · exact positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile
      hsimple horient

/-- Positive radius ordered turns imply the corresponding signed-Menger
ordered turns. -/
theorem orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    OrderedAdjacentTurns (SignedMengerProfile v) := by
  exact orderedAdjacentTurns_congr
    (fun i => signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
      hsimple horient i)
    (orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient hturns)

/-- Signed-Menger ordered turns imply positive radius ordered turns in the
positive-orientation branch. -/
theorem positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_signedMengerProfile
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : OrderedAdjacentTurns (SignedMengerProfile v)) :
    PositiveRadiusOrderedAdjacentTurns v := by
  exact positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_inv_edgePrevCircleRadiusProfile
    hsimple horient
    (orderedAdjacentTurns_congr
      (fun i => (signedMengerProfile_eq_inv_edgePrevCircleRadiusProfile_of_positiveOrientation
        hsimple horient i).symm)
      hturns)

/-- In the positive-orientation branch, positive radius ordered turns are
equivalent to signed-Menger ordered turns. -/
theorem positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v) :
    PositiveRadiusOrderedAdjacentTurns v ↔ OrderedAdjacentTurns (SignedMengerProfile v) := by
  constructor
  · exact orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient
  · exact positiveRadiusOrderedAdjacentTurns_of_orderedAdjacentTurns_signedMengerProfile
      hsimple horient

/-- Direct Euclidean isometries preserve positive radius ordered turns in the
positive-orientation branch. -/
theorem positiveRadiusOrderedAdjacentTurns_directIsometry_iff {n : ℕ} [NeZero n]
    {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i))) :
    PositiveRadiusOrderedAdjacentTurns (fun i => directIsometryR2 u a (v i)) ↔
      PositiveRadiusOrderedAdjacentTurns v := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  constructor
  · intro hturns
    have hsigned :
        OrderedAdjacentTurns
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) :=
      (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
        hsimple horient).mp hturns
    have hsigned₀ : OrderedAdjacentTurns (SignedMengerProfile v) :=
      orderedAdjacentTurns_congr
        (fun i => (congrFun (SignedMengerProfile_directIsometry hu a v) i).symm)
        hsigned
    exact (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
      hsimple₀ horient₀).mpr hsigned₀
  · intro hturns
    have hsigned₀ : OrderedAdjacentTurns (SignedMengerProfile v) :=
      (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
        hsimple₀ horient₀).mp hturns
    have hsigned :
        OrderedAdjacentTurns
          (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) :=
      orderedAdjacentTurns_congr
        (fun i => congrFun (SignedMengerProfile_directIsometry hu a v) i)
        hsigned₀
    exact (positiveRadiusOrderedAdjacentTurns_iff_orderedAdjacentTurns_signedMengerProfile
      hsimple horient).mpr hsigned

/-- Positive radius ordered turns force nonconstancy of the signed-Menger
profile. -/
theorem not_constant_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c := by
  exact not_constant_of_orderedAdjacentTurns
    (orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient hturns)

/-- Positive radius ordered turns imply Dahlberg's plateau-aware four-vertex
conclusion for the signed-Menger profile. -/
theorem signedMengerProfile_dahlbergFourVertex_of_positiveRadiusOrderedAdjacentTurns
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (horient : PositivePolygonOrientation v)
    (hturns : PositiveRadiusOrderedAdjacentTurns v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_orderedAdjacentTurns_four_le hn
    (orderedAdjacentTurns_signedMengerProfile_of_positiveRadiusOrderedAdjacentTurns
      hsimple horient hturns)

/-- Auxiliary-polygon package produced by Dahlberg's non-strict disk
reduction.  The auxiliary polygon is in the already-proved strict-orientation
case, and its Dahlberg conclusion transfers back to the original polygon. -/
def DahlbergDiskAuxiliaryReduction {n : ℕ} [NeZero n] (v : ZMod n → ℂ) : Prop :=
  ∃ m : ℕ, ∃ _hne : NeZero m, ∃ w : ZMod m → ℂ,
    4 ≤ m ∧
    Gluck.Discrete.IsSimplePolygon w ∧
    DahlbergRegular w ∧
    (PositivePolygonOrientation w ∨ NegativePolygonOrientation w) ∧
    ¬ Concyclic w ∧
    (DahlbergFourVertex (SignedMengerProfile w) →
      DahlbergFourVertex (SignedMengerProfile v))

/-- Typed version of the auxiliary-polygon package in Dahlberg's non-strict
disk reduction.

This is definitionally the same data as `DahlbergDiskAuxiliaryReduction`, but
with named fields.  It is the target shape for formalizing the final §4
construction: construct a strict-orientation auxiliary polygon `w`, prove it is
nonconcyclic, and prove that its D4VT conclusion transfers back to the original
polygon. -/
structure DahlbergAuxiliaryPolygon {n : ℕ} [NeZero n] (v : ZMod n → ℂ) where
  m : ℕ
  hne : NeZero m
  w : ZMod m → ℂ
  four_le : 4 ≤ m
  simple : Gluck.Discrete.IsSimplePolygon w
  regular : DahlbergRegular w
  strictOrientation : PositivePolygonOrientation w ∨ NegativePolygonOrientation w
  nonconcyclic : ¬ Concyclic w
  transfer :
    DahlbergFourVertex (SignedMengerProfile w) →
      DahlbergFourVertex (SignedMengerProfile v)

/-- Certificate form of the final normalized §4 auxiliary-polygon
construction.

The surrounding source includes the normalized hypotheses
`MinimalEnclosingDiskR2 v 0 1`, `v 0 = 1`, and `dist 0 (v 1) < 1`.
This certificate is the output: a strict-orientation auxiliary polygon whose
Dahlberg conclusion transfers back to the original polygon. -/
structure DahlbergE2Section4AuxiliaryPolygonCertificate {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) where
  aux : DahlbergAuxiliaryPolygon v

/-- The typed auxiliary-polygon package implies the old existential package. -/
theorem dahlbergDiskAuxiliaryReduction_of_auxiliaryPolygon {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (aux : DahlbergAuxiliaryPolygon v) :
    DahlbergDiskAuxiliaryReduction v := by
  exact ⟨aux.m, aux.hne, aux.w, aux.four_le, aux.simple, aux.regular,
    aux.strictOrientation, aux.nonconcyclic, aux.transfer⟩

/-- The old existential auxiliary-reduction package can be repackaged as a
typed auxiliary polygon. -/
theorem exists_dahlbergAuxiliaryPolygon_of_diskAuxiliaryReduction {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ} (haux : DahlbergDiskAuxiliaryReduction v) :
    Nonempty (DahlbergAuxiliaryPolygon v) := by
  rcases haux with
    ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
  exact ⟨({
    m := m
    hne := hne
    w := w
    four_le := hm
    simple := hsimple
    regular := hregular
    strictOrientation := horient
    nonconcyclic := hnoncircle
    transfer := htransfer } : DahlbergAuxiliaryPolygon v)⟩

/-- Typed and existential forms of Dahlberg's auxiliary-reduction package are
equivalent. -/
theorem dahlbergDiskAuxiliaryReduction_iff_exists_auxiliaryPolygon {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ} :
    DahlbergDiskAuxiliaryReduction v ↔
      Nonempty (DahlbergAuxiliaryPolygon v) := by
  constructor
  · exact exists_dahlbergAuxiliaryPolygon_of_diskAuxiliaryReduction
  · rintro ⟨aux⟩
    exact dahlbergDiskAuxiliaryReduction_of_auxiliaryPolygon aux

/-- Direct Euclidean isometries preserve Dahlberg's auxiliary-reduction
package.  The auxiliary polygon itself is unchanged; only the final transfer
to the original polygon is transported through the signed-Menger profile
invariance. -/
theorem dahlbergDiskAuxiliaryReduction_directIsometry {n : ℕ} [NeZero n]
    {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ) {v : ZMod n → ℂ}
    (haux : DahlbergDiskAuxiliaryReduction v) :
    DahlbergDiskAuxiliaryReduction (fun i => directIsometryR2 u a (v i)) := by
  rcases haux with
    ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
  exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle,
    fun hfv => (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mpr
      (htransfer hfv)⟩

/-- Direct Euclidean isometries preserve Dahlberg's auxiliary-reduction
package exactly. -/
theorem dahlbergDiskAuxiliaryReduction_directIsometry_iff {n : ℕ} [NeZero n]
    {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ) (v : ZMod n → ℂ) :
    DahlbergDiskAuxiliaryReduction (fun i => directIsometryR2 u a (v i)) ↔
      DahlbergDiskAuxiliaryReduction v := by
  constructor
  · intro haux
    rcases haux with
      ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
    exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle,
      fun hfv => (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mp
        (htransfer hfv)⟩
  · exact dahlbergDiskAuxiliaryReduction_directIsometry hu a

/-- Positive real homotheties preserve Dahlberg's auxiliary-reduction package
exactly.  The final transfer is adjusted by positive-affine invariance of the
signed-Menger profile, since signed Menger curvature scales by `r⁻¹`. -/
theorem dahlbergDiskAuxiliaryReduction_posRealHomothety_iff {n : ℕ} [NeZero n]
    {r : ℝ} (hr : 0 < r) (v : ZMod n → ℂ) :
    DahlbergDiskAuxiliaryReduction (fun i => (r : ℂ) * v i) ↔
      DahlbergDiskAuxiliaryReduction v := by
  constructor
  · intro haux
    rcases haux with
      ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
    exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, fun hfv => by
      have hscaled : DahlbergFourVertex
          (SignedMengerProfile (fun i => (r : ℂ) * v i)) :=
        htransfer hfv
      have hscaled' : DahlbergFourVertex
          (fun i => r⁻¹ * SignedMengerProfile v i + 0) := by
        simpa [SignedMengerProfile_posRealHomothety hr v] using hscaled
      exact (dahlbergFourVertex_posAffine_iff (κ := SignedMengerProfile v)
        (a := r⁻¹) (b := 0) (inv_pos.mpr hr)).mp hscaled'⟩
  · intro haux
    rcases haux with
      ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
    exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, fun hfv => by
      have hbase : DahlbergFourVertex (SignedMengerProfile v) :=
        htransfer hfv
      have hscaled' : DahlbergFourVertex
          (fun i => r⁻¹ * SignedMengerProfile v i + 0) :=
        (dahlbergFourVertex_posAffine_iff (κ := SignedMengerProfile v)
          (a := r⁻¹) (b := 0) (inv_pos.mpr hr)).mpr hbase
      simpa [SignedMengerProfile_posRealHomothety hr v] using hscaled'⟩

/-- If the reversed cyclic polygon has Dahlberg's auxiliary-reduction package,
then so does the original polygon. -/
theorem dahlbergDiskAuxiliaryReduction_of_reverseCyclicPolygon {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ}
    (haux : DahlbergDiskAuxiliaryReduction (ReverseCyclicPolygon v)) :
    DahlbergDiskAuxiliaryReduction v := by
  rcases haux with
    ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
  exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, fun hfv => by
    have hrev : DahlbergFourVertex (SignedMengerProfile (ReverseCyclicPolygon v)) :=
      htransfer hfv
    exact dahlbergFourVertex_of_neg_reflectIndex (κ := SignedMengerProfile v) (by
      convert hrev using 1
      ext i
      exact (SignedMengerProfile_reverseCyclicPolygon v i).symm)⟩

/-- If a cyclic translate of a polygon has Dahlberg's auxiliary-reduction
package, then so does the original polygon. -/
theorem dahlbergDiskAuxiliaryReduction_of_translateCyclicPolygon {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ} {a : ZMod n}
    (haux : DahlbergDiskAuxiliaryReduction (TranslateCyclicPolygon v a)) :
    DahlbergDiskAuxiliaryReduction v := by
  rcases haux with
    ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
  exact ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, fun hfv => by
    have htrans : DahlbergFourVertex
        (SignedMengerProfile (TranslateCyclicPolygon v a)) :=
      htransfer hfv
    have hshift : DahlbergFourVertex (fun i => SignedMengerProfile v (i + a)) := by
      convert htrans using 1
      ext i
      exact (SignedMengerProfile_translateCyclicPolygon v a i).symm
    exact (dahlbergFourVertex_translateIndex_iff (κ := SignedMengerProfile v)
      (a := a)).mp hshift⟩

/-- Eliminate Dahlberg's auxiliary-reduction package using any strict
oriented nonconcyclic auxiliary-polygon D4VT source. -/
theorem dahlbergFourVertex_of_dahlbergDiskAuxiliaryReduction {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ}
    (haux : DahlbergDiskAuxiliaryReduction v)
    (hstrict :
      ∀ {m : ℕ} [NeZero m] {w : ZMod m → ℂ},
        4 ≤ m →
        Gluck.Discrete.IsSimplePolygon w →
        DahlbergRegular w →
        (PositivePolygonOrientation w ∨ NegativePolygonOrientation w) →
        ¬ Concyclic w →
        DahlbergFourVertex (SignedMengerProfile w)) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  rcases haux with
    ⟨m, hne, w, hm, hsimple, hregular, horient, hnoncircle, htransfer⟩
  letI : NeZero m := hne
  exact htransfer (hstrict hm hsimple hregular horient hnoncircle)

/-- Minimal-disk setup used in Dahlberg's §4 non-strict reduction.

Dahlberg starts the final proof by choosing the smallest closed disk `Δ`
containing the polygon and its boundary vertex set `E = V(Γ) ∩ ∂Δ`.  This
predicate records the part of that setup currently represented in the formal
API: a minimal enclosing disk together with at least one vertex on its
boundary. -/
def DahlbergDiskReductionSetup {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∃ O R, MinimalEnclosingDiskR2 v O R ∧
    ∃ i : ZMod n, OnDiskBoundaryR2 v O R i

/-- The index set of vertices lying on the boundary of a chosen Euclidean
disk.  This is Dahlberg's set `E = V(Γ) ∩ ∂Δ`, recorded at the cyclic-index
level. -/
def DiskBoundaryIndices {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) :
    Set (ZMod n) :=
  {i | OnDiskBoundaryR2 v O R i}

theorem mem_diskBoundaryIndices {n : ℕ} {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    {i : ZMod n} :
    i ∈ DiskBoundaryIndices v O R ↔ OnDiskBoundaryR2 v O R i := by
  rfl

/-- Direct Euclidean isometries preserve Dahlberg's boundary index set. -/
theorem diskBoundaryIndices_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w O : ℂ) (R : ℝ) (v : ZMod n → ℂ) :
    DiskBoundaryIndices (fun i => directIsometryR2 u w (v i))
        (directIsometryR2 u w O) R =
      DiskBoundaryIndices v O R := by
  ext i
  exact onDiskBoundaryR2_directIsometry hu w O R v i

/-- A nonempty proper cyclic index set has an adjacent transition across its
boundary.

This is the finite cyclic selection used at the start of Dahlberg's §4
complementary-interval step: the boundary vertex set `E` cannot be constant as
a cyclic `0/1` profile, so some adjacent pair crosses from `E` to its
complement or from the complement back into `E`. -/
theorem exists_mem_succ_not_mem_or_not_mem_succ_mem_of_nonempty_ne_univ
    {n : ℕ} [NeZero n] (E : Set (ZMod n))
    (hE : E.Nonempty) (hproper : E ≠ Set.univ) :
    ∃ i : ZMod n, (i ∈ E ∧ i + 1 ∉ E) ∨ (i ∉ E ∧ i + 1 ∈ E) := by
  classical
  let χ : ZMod n → ℝ := fun i => if i ∈ E then 1 else 0
  have hcompl : ∃ i : ZMod n, i ∉ E := by
    by_contra hnone
    apply hproper
    ext i
    constructor
    · intro _hi
      trivial
    · intro _hi
      by_contra hiE
      exact hnone ⟨i, hiE⟩
  have hnc : ¬ ∃ c, ∀ i : ZMod n, χ i = c := by
    rintro ⟨c, hc⟩
    rcases hE with ⟨i, hi⟩
    rcases hcompl with ⟨j, hj⟩
    have hiχ : χ i = 1 := by simp [χ, hi]
    have hjχ : χ j = 0 := by simp [χ, hj]
    have h10 : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = χ i := hiχ.symm
        _ = c := hc i
        _ = χ j := (hc j).symm
        _ = 0 := hjχ
    norm_num at h10
  rcases exists_ne_succ_of_not_constant (κ := χ) hnc with ⟨i, hneq⟩
  by_cases hi : i ∈ E
  · by_cases hsucc : i + 1 ∈ E
    · exfalso
      exact hneq (by simp [χ, hi, hsucc])
    · exact ⟨i, Or.inl ⟨hi, hsucc⟩⟩
  · by_cases hsucc : i + 1 ∈ E
    · exact ⟨i, Or.inr ⟨hi, hsucc⟩⟩
    · exfalso
      exact hneq (by simp [χ, hi, hsucc])

/-- Dahlberg's minimal-disk boundary set has an adjacent cyclic transition
whenever it is nonempty and proper. -/
theorem diskBoundaryIndices_exists_adjacent_transition {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hEnonempty : (DiskBoundaryIndices v O R).Nonempty)
    (hEproper : DiskBoundaryIndices v O R ≠ Set.univ) :
    ∃ i : ZMod n,
      (i ∈ DiskBoundaryIndices v O R ∧ i + 1 ∉ DiskBoundaryIndices v O R) ∨
        (i ∉ DiskBoundaryIndices v O R ∧ i + 1 ∈ DiskBoundaryIndices v O R) := by
  exact exists_mem_succ_not_mem_or_not_mem_succ_mem_of_nonempty_ne_univ
    (DiskBoundaryIndices v O R) hEnonempty hEproper

/-- A nonempty proper boundary index set for an enclosing disk has a boundary
vertex with a strictly interior cyclic neighbor.

This is the metric form of the finite cyclic transition: nonmembership in
`E = V(Γ) ∩ ∂Δ` is strict interiority because every vertex is contained in the
chosen enclosing disk. -/
theorem diskBoundaryIndices_exists_boundary_adjacent_interior {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hEnonempty : (DiskBoundaryIndices v O R).Nonempty)
    (hEproper : DiskBoundaryIndices v O R ≠ Set.univ) :
    ∃ i : ZMod n,
      OnDiskBoundaryR2 v O R i ∧
        (dist O (v (i + 1)) < R ∨ dist O (v (i - 1)) < R) := by
  rcases diskBoundaryIndices_exists_adjacent_transition hEnonempty hEproper with
    ⟨i, htransition⟩
  rcases htransition with hforward | hbackward
  · refine ⟨i, (mem_diskBoundaryIndices).mp hforward.1, Or.inl ?_⟩
    exact lt_of_le_of_ne (Metric.mem_closedBall'.mp (hΔ.2.1 (i + 1)))
      (fun hdist ↦ hforward.2 ((mem_diskBoundaryIndices).mpr (Metric.mem_sphere'.mpr hdist)))
  · refine ⟨i + 1, (mem_diskBoundaryIndices).mp hbackward.2, Or.inr ?_⟩
    have hinterior : dist O (v i) < R := by
      exact lt_of_le_of_ne (Metric.mem_closedBall'.mp (hΔ.2.1 i))
        (fun hdist ↦ hbackward.1 ((mem_diskBoundaryIndices).mpr (Metric.mem_sphere'.mpr hdist)))
    simpa [sub_eq_add_neg, add_assoc] using hinterior

/-- Direct Euclidean isometries preserve Dahlberg's minimal-disk setup. -/
theorem dahlbergDiskReductionSetup_directIsometry {n : ℕ} {u : ℂ} (hu : ‖u‖ = 1)
    (w : ℂ) (v : ZMod n → ℂ) :
    DahlbergDiskReductionSetup (fun i => directIsometryR2 u w (v i)) ↔
      DahlbergDiskReductionSetup v := by
  constructor
  · intro hsetup
    rcases hsetup with ⟨O', R, hΔ, i, hi⟩
    let O : ℂ := u⁻¹ * (O' - w)
    have hcenter : directIsometryR2 u w O = O' := by
      exact directIsometryR2_inverse_center hu w O'
    have hΔ' : MinimalEnclosingDiskR2 (fun i => directIsometryR2 u w (v i))
        (directIsometryR2 u w O) R := by
      simpa [hcenter] using hΔ
    have hi' : OnDiskBoundaryR2 (fun j => directIsometryR2 u w (v j))
        (directIsometryR2 u w O) R i := by
      simpa [hcenter] using hi
    exact ⟨O, R, (minimalEnclosingDiskR2_directIsometry hu w O R v).mp hΔ',
      i, (onDiskBoundaryR2_directIsometry hu w O R v i).mp hi'⟩
  · intro hsetup
    rcases hsetup with ⟨O, R, hΔ, i, hi⟩
    exact ⟨directIsometryR2 u w O, R,
      (minimalEnclosingDiskR2_directIsometry hu w O R v).mpr hΔ,
      i, (onDiskBoundaryR2_directIsometry hu w O R v i).mpr hi⟩

/-- Positive real homotheties preserve Dahlberg's minimal-disk setup. -/
theorem dahlbergDiskReductionSetup_posRealHomothety {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v : ZMod n → ℂ) :
    DahlbergDiskReductionSetup v →
      DahlbergDiskReductionSetup (fun i => (r : ℂ) * v i) := by
  rintro ⟨O, R, hΔ, i, hi⟩
  exact ⟨(r : ℂ) * O, r * R,
    minimalEnclosingDiskR2_posRealHomothety hr O R v hΔ,
    i, (onDiskBoundaryR2_posRealHomothety hr O R v i).mpr hi⟩

/-- In the §4 minimal-disk setup for a simple polygon, the smallest disk has
positive radius. -/
theorem dahlbergDiskReductionSetup_exists_radius_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      ∃ i : ZMod n, OnDiskBoundaryR2 v O R i := by
  rcases hsetup with ⟨O, R, hΔ, hboundary⟩
  exact ⟨O, R, hΔ, radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple,
    hboundary⟩

/-- In Dahlberg's §4 minimal-disk setup, any selected boundary vertex realizes
the maximal distance from the disk centre among all polygon vertices. -/
theorem dahlbergDiskReductionSetup_exists_boundary_max {n : ℕ}
    {v : ZMod n → ℂ}
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R i, MinimalEnclosingDiskR2 v O R ∧
      OnDiskBoundaryR2 v O R i ∧
      ∀ j : ZMod n, dist O (v j) ≤ dist O (v i) := by
  rcases hsetup with ⟨O, R, hΔ, i, hboundary⟩
  exact ⟨O, R, i, hΔ, hboundary,
    fun j => dist_le_boundary_dist_of_minimalEnclosingDiskR2 hΔ hboundary⟩

/-- The boundary index set `E` in Dahlberg's §4 setup is nonempty. -/
theorem dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty {n : ℕ}
    {v : ZMod n → ℂ}
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R, MinimalEnclosingDiskR2 v O R ∧
      (DiskBoundaryIndices v O R).Nonempty := by
  rcases hsetup with ⟨O, R, hΔ, i, hi⟩
  exact ⟨O, R, hΔ, i, hi⟩

/-- In the nonconcyclic §4 branch, not every vertex can lie on the boundary
of the minimal enclosing disk; otherwise the polygon would be concyclic. -/
theorem dahlbergDiskReductionSetup_exists_interior_vertex_of_nonconcyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      (∃ i : ZMod n, OnDiskBoundaryR2 v O R i) ∧
      ∃ j : ZMod n, dist O (v j) < R := by
  rcases dahlbergDiskReductionSetup_exists_radius_pos hsimple hsetup with
    ⟨O, R, hΔ, hRpos, hboundary⟩
  refine ⟨O, R, hΔ, hRpos, hboundary, ?_⟩
  by_contra hnoInterior
  have hall : ∀ j : ZMod n, dist O (v j) = R := by
    intro j
    exact le_antisymm (Metric.mem_closedBall'.mp (hΔ.2.1 j))
      (not_lt.mp (fun hj => hnoInterior ⟨j, hj⟩))
  exact hnoncircle ⟨O, R, hRpos, hall⟩

/-- In the nonconcyclic §4 branch, Dahlberg's boundary index set `E` is a
nonempty proper subset of the cyclic vertex indices. -/
theorem dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty_proper_of_nonconcyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      (DiskBoundaryIndices v O R).Nonempty ∧
      ∃ j : ZMod n, j ∉ DiskBoundaryIndices v O R := by
  rcases dahlbergDiskReductionSetup_exists_interior_vertex_of_nonconcyclic
      hsimple hnoncircle hsetup with
    ⟨O, R, hΔ, hRpos, hboundary, hinterior⟩
  rcases hboundary with ⟨i, hi⟩
  rcases hinterior with ⟨j, hj⟩
  exact ⟨O, R, hΔ, hRpos, ⟨i, hi⟩, j,
    not_onDiskBoundaryR2_of_dist_lt hj⟩

/-- If every vertex lies on a positive-radius disk boundary, the polygon is
concyclic with that disk as witness. -/
theorem concyclic_of_forall_onDiskBoundaryR2 {n : ℕ} {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} (hRpos : 0 < R)
    (hall : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i) :
    Concyclic v := by
  exact ⟨O, R, hRpos, fun i ↦ Metric.mem_sphere'.mp (hall i)⟩

/-- For a nonconcyclic polygon, no positive-radius disk can have every vertex
on its boundary. -/
theorem exists_not_onDiskBoundaryR2_of_not_concyclic {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hRpos : 0 < R) (hnoncircle : ¬ Concyclic v) :
    ∃ j : ZMod n, ¬ OnDiskBoundaryR2 v O R j := by
  by_contra hnone
  have hall : ∀ j : ZMod n, OnDiskBoundaryR2 v O R j := by
    intro j
    by_contra hj
    exact hnone ⟨j, hj⟩
  exact hnoncircle (concyclic_of_forall_onDiskBoundaryR2 hRpos hall)

/-- The boundary index set of any positive-radius disk witnessing a
nonconcyclic polygon is not the full cyclic index set. -/
theorem diskBoundaryIndices_ne_univ_of_not_concyclic {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hRpos : 0 < R) (hnoncircle : ¬ Concyclic v) :
    DiskBoundaryIndices v O R ≠ Set.univ := by
  rcases exists_not_onDiskBoundaryR2_of_not_concyclic hRpos hnoncircle with
    ⟨j, hj⟩
  intro hE
  have hjE : j ∈ DiskBoundaryIndices v O R := by
    simp [hE]
  exact hj ((mem_diskBoundaryIndices).mp hjE)

/-- In Dahlberg's nonconcyclic §4 branch, the chosen boundary index set `E`
is nonempty and not all of `ZMod n`. -/
theorem dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty_ne_univ_of_nonconcyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      (DiskBoundaryIndices v O R).Nonempty ∧
      DiskBoundaryIndices v O R ≠ Set.univ := by
  rcases dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty_proper_of_nonconcyclic
      hsimple hnoncircle hsetup with
    ⟨O, R, hΔ, hRpos, hE, j, hj⟩
  refine ⟨O, R, hΔ, hRpos, hE, ?_⟩
  intro htop
  have hjE : j ∈ DiskBoundaryIndices v O R := by
    simp [htop]
  exact hj hjE

/-- In Dahlberg's nonconcyclic §4 branch, the chosen minimal disk has a
boundary vertex with a strictly interior cyclic neighbor. -/
theorem dahlbergDiskReductionSetup_exists_boundary_adjacent_interior_of_nonconcyclic
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R i, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      OnDiskBoundaryR2 v O R i ∧
      (dist O (v (i + 1)) < R ∨ dist O (v (i - 1)) < R) := by
  rcases dahlbergDiskReductionSetup_diskBoundaryIndices_nonempty_ne_univ_of_nonconcyclic
      hsimple hnoncircle hsetup with
    ⟨O, R, hΔ, hRpos, hEnonempty, hEproper⟩
  rcases diskBoundaryIndices_exists_boundary_adjacent_interior
      hΔ hEnonempty hEproper with
    ⟨i, hboundary, hadjacentInterior⟩
  exact ⟨O, R, i, hΔ, hRpos, hboundary, hadjacentInterior⟩

/-- Combined finite-disk data for Dahlberg's §4 nonconcyclic branch: a
positive minimal disk, a boundary vertex realizing the maximal radius, and a
strictly interior vertex. -/
theorem dahlbergDiskReductionSetup_exists_boundary_max_and_interior
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R i j, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      OnDiskBoundaryR2 v O R i ∧ dist O (v j) < R ∧ i ≠ j ∧
      ∀ k : ZMod n, dist O (v k) ≤ dist O (v i) := by
  rcases dahlbergDiskReductionSetup_exists_radius_pos hsimple hsetup with
    ⟨O, R, hΔ, hRpos, i, hi⟩
  have hinterior : ∃ j : ZMod n, dist O (v j) < R := by
    by_contra hnoInterior
    have hall : ∀ j : ZMod n, dist O (v j) = R := by
      intro j
      exact le_antisymm (Metric.mem_closedBall'.mp (hΔ.2.1 j))
        (not_lt.mp (fun hj => hnoInterior ⟨j, hj⟩))
    exact hnoncircle ⟨O, R, hRpos, hall⟩
  rcases hinterior with ⟨j, hj⟩
  exact ⟨O, R, i, j, hΔ, hRpos, hi, hj,
    ne_of_onDiskBoundaryR2_of_dist_lt hi hj,
    fun k => dist_le_boundary_dist_of_minimalEnclosingDiskR2 hΔ hi⟩

/-- Dahlberg's §4 nonconcyclic branch can choose a maximal boundary index and
a complementary interior index. -/
theorem dahlbergDiskReductionSetup_diskBoundaryIndices_boundary_max_and_complement
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hnoncircle : ¬ Concyclic v)
    (hsetup : DahlbergDiskReductionSetup v) :
    ∃ O R i j, MinimalEnclosingDiskR2 v O R ∧ 0 < R ∧
      i ∈ DiskBoundaryIndices v O R ∧
      j ∉ DiskBoundaryIndices v O R ∧
      i ≠ j ∧
      ∀ k : ZMod n, dist O (v k) ≤ dist O (v i) := by
  rcases dahlbergDiskReductionSetup_exists_boundary_max_and_interior
      hsimple hnoncircle hsetup with
    ⟨O, R, i, j, hΔ, hRpos, hi, hj, hij, hmax⟩
  exact ⟨O, R, i, j, hΔ, hRpos, hi,
    not_onDiskBoundaryR2_of_dist_lt hj, hij, hmax⟩

/-- Radius of the smallest closed disk with fixed centre `O` containing the
finite cyclic vertex set `v`. -/
noncomputable def finiteEnclosingRadius {n : ℕ} [NeZero n] (v : ZMod n → ℂ)
    (O : ℂ) : ℝ :=
  (Finset.univ : Finset (ZMod n)).sup' Finset.univ_nonempty (fun i => dist O (v i))

/-- The fixed-centre enclosing radius varies continuously with the centre. -/
theorem continuous_finiteEnclosingRadius {n : ℕ} [NeZero n] (v : ZMod n → ℂ) :
    Continuous (finiteEnclosingRadius v) := by
  unfold finiteEnclosingRadius
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun i _ => continuous_id.dist (continuous_const : Continuous fun _ : ℂ => v i))

/-- The fixed-centre enclosing radius tends to infinity as the centre leaves
every compact set. -/
theorem tendsto_finiteEnclosingRadius_cocompact_atTop {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) :
    Filter.Tendsto (finiteEnclosingRadius v) (Filter.cocompact ℂ) Filter.atTop := by
  have hdist : Filter.Tendsto (fun O : ℂ => dist O (v 0))
      (Filter.cocompact ℂ) Filter.atTop :=
    tendsto_dist_right_cocompact_atTop (v 0)
  refine Filter.tendsto_atTop_mono ?_ hdist
  intro O
  unfold finiteEnclosingRadius
  exact Finset.le_sup' (fun i : ZMod n => dist O (v i)) (Finset.mem_univ 0)

/-- Every vertex lies in the disk of radius `finiteEnclosingRadius v O`
centred at `O`. -/
theorem polygonInClosedDiskR2_finiteEnclosingRadius {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) (O : ℂ) :
    PolygonInClosedDiskR2 v O (finiteEnclosingRadius v O) := by
  intro i
  unfold finiteEnclosingRadius
  exact Metric.mem_closedBall'.mpr
    (Finset.le_sup' (fun j : ZMod n => dist O (v j)) (Finset.mem_univ i))

/-- Every finite cyclic Euclidean vertex set has a least enclosing disk. -/
theorem exists_minimalEnclosingDiskR2 {n : ℕ} [NeZero n] (v : ZMod n → ℂ) :
    ∃ O R, MinimalEnclosingDiskR2 v O R := by
  obtain ⟨O, hmin⟩ :=
    (continuous_finiteEnclosingRadius v).exists_forall_le
      (tendsto_finiteEnclosingRadius_cocompact_atTop v)
  refine ⟨O, finiteEnclosingRadius v O, ?_, ?_, ?_⟩
  · exact dist_nonneg.trans
      (Finset.le_sup' (fun i : ZMod n => dist O (v i)) (Finset.mem_univ 0))
  · exact polygonInClosedDiskR2_finiteEnclosingRadius v O
  · intro O' R' _hR' hpoly
    exact (hmin O').trans
      (Finset.sup'_le Finset.univ_nonempty (fun i : ZMod n => dist O' (v i))
        (fun i _hi => Metric.mem_closedBall'.mp (hpoly i)))

/-- Dahlberg's convex-radius input for the positive-orientation branch.

This is the radius-level extraction from Lemma 8 plus the convex discrete
four-vertex theorem (Theorem 6) in Dahlberg's paper.  It says that the
nonconstant strictly convex branch supplies four cyclically ordered adjacent
radius turns.  The conversion from these radius turns to signed-Menger turns is
formalized below, so this is the smaller Euclidean geometric source gate for
Lemma 9. -/
def DahlbergE2ConvexRadiusSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) →
    PositiveRadiusOrderedAdjacentTurns v

/-- Dahlberg's convex/CDFV radius-witness source.

This is the part of Lemma 9 that uses Theorem 6: a strictly convex,
nonconcyclic polygon supplies the four extremal curvature-disk witnesses,
recorded here on the circle-radius profile. -/
def DahlbergE2ConvexDfvRadiusSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) →
    DahlbergE2ConvexDfvRadiusWitnesses v

/-- Nonconcyclic spelling of Dahlberg's convex/CDFV radius-witness source.

This is the closest current Lean interface to Dahlberg's Theorem 6/CDFV:
a strictly convex, nonconcyclic polygon supplies the four extremal
curvature-disk witnesses, recorded on the circle-radius profile. -/
def DahlbergE2ConvexDfvRadiusNonconcyclicSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    DahlbergE2ConvexDfvRadiusWitnesses v

/-- The geometric CDFV source implies the radius-witness source used by the
rest of the file. -/
theorem dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_theorem6GeometricSource
    (hsrc : DahlbergE2Theorem6GeometricCdfvSource) :
    DahlbergE2ConvexDfvRadiusNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  rcases hsrc hn hsimple hregular horient hnoncircle with ⟨cert⟩
  exact dahlbergE2ConvexDfvRadiusWitnesses_of_theorem6Certificate cert

/-- Signed-Menger spelling of Dahlberg's convex/CDFV source.

This is the theorem-level content of Dahlberg's strictly convex positive branch:
the CDFV disk witnesses give the plateau-aware Dahlberg conclusion for signed
Menger curvature.  It is equivalent to the radius-witness source by reciprocal
radius monotonicity in the positive-orientation branch. -/
def DahlbergE2ConvexDfvSignedSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) →
    DahlbergFourVertex (SignedMengerProfile v)

/-- Nonconcyclic spelling of Dahlberg's convex/CDFV source.

In the positive locally regular branch, nonconcyclicity is formally equivalent
to nonconstancy of the signed-Menger profile, so this is only a geometric
restatement of `DahlbergE2ConvexDfvSignedSource`. -/
def DahlbergE2ConvexDfvSignedNonconcyclicSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    DahlbergFourVertex (SignedMengerProfile v)

/-- Constant-or-Dahlberg spelling of the convex/CDFV signed-Menger source.

This is closer to the theorem-level positive strictly-convex branch: without a
separate nonconcyclic/nonconstant hypothesis, the conclusion is either constant
signed-Menger curvature or the plateau-aware Dahlberg four-vertex conclusion. -/
def DahlbergE2ConvexDfvSignedConstantOrSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) ∨
      DahlbergFourVertex (SignedMengerProfile v)

/-- The constant-or signed-CDFV source implies the nonconstant spelling. -/
theorem dahlbergE2ConvexDfvSignedSource_of_constantOrSource
    (hsrc : DahlbergE2ConvexDfvSignedConstantOrSource) :
    DahlbergE2ConvexDfvSignedSource := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (hsrc hn hsimple hregular horient) hnc

/-- The nonconstant signed-CDFV source implies the constant-or spelling. -/
theorem dahlbergE2ConvexDfvSignedConstantOrSource_of_signedSource
    (hsrc : DahlbergE2ConvexDfvSignedSource) :
    DahlbergE2ConvexDfvSignedConstantOrSource := by
  intro n hne hn v hsimple hregular horient
  letI : NeZero n := hne
  by_cases hconst : ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c
  · exact Or.inl hconst
  · exact Or.inr (hsrc hn hsimple hregular horient hconst)

/-- The nonconstant and constant-or signed-CDFV source spellings are formally
equivalent. -/
theorem dahlbergE2ConvexDfvSignedConstantOrSource_iff_signedSource :
    DahlbergE2ConvexDfvSignedConstantOrSource ↔ DahlbergE2ConvexDfvSignedSource := by
  constructor
  · exact dahlbergE2ConvexDfvSignedSource_of_constantOrSource
  · exact dahlbergE2ConvexDfvSignedConstantOrSource_of_signedSource

/-- The constant-or signed-CDFV source implies the nonconcyclic spelling. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_of_constantOrSource
    (hsrc : DahlbergE2ConvexDfvSignedConstantOrSource) :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact dahlbergFourVertex_of_constant_or_of_not_constant
    (hsrc hn hsimple hregular horient)
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- The nonconstant signed-CDFV source implies the nonconcyclic spelling. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_of_signedSource
    (hsrc : DahlbergE2ConvexDfvSignedSource) :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- The nonconcyclic signed-CDFV source implies the nonconstant spelling. -/
theorem dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource
    (hsrc : DahlbergE2ConvexDfvSignedNonconcyclicSource) :
    DahlbergE2ConvexDfvSignedSource := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_concyclic_of_not_constant_signedMengerProfile_positiveOrientation
      hsimple hnc horient)

/-- The nonconstant radius-CDFV source implies the nonconcyclic spelling. -/
theorem dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_radiusSource
    (hsrc : DahlbergE2ConvexDfvRadiusSource) :
    DahlbergE2ConvexDfvRadiusNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- The nonconcyclic radius-CDFV source implies the nonconstant spelling. -/
theorem dahlbergE2ConvexDfvRadiusSource_of_nonconcyclicSource
    (hsrc : DahlbergE2ConvexDfvRadiusNonconcyclicSource) :
    DahlbergE2ConvexDfvRadiusSource := by
  intro n hne hn v hsimple hregular horient hnc
  letI : NeZero n := hne
  exact hsrc hn hsimple hregular horient
    (not_concyclic_of_not_constant_signedMengerProfile_positiveOrientation
      hsimple hnc horient)

/-- The nonconstant and nonconcyclic radius-CDFV source spellings are formally
equivalent in the positive locally regular branch. -/
theorem dahlbergE2ConvexDfvRadiusSource_iff_nonconcyclicSource :
    DahlbergE2ConvexDfvRadiusSource ↔
      DahlbergE2ConvexDfvRadiusNonconcyclicSource := by
  constructor
  · exact dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_radiusSource
  · exact dahlbergE2ConvexDfvRadiusSource_of_nonconcyclicSource

/-- The nonconcyclic radius-witness CDFV source implies the nonconcyclic
signed-Menger spelling. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_of_radiusNonconcyclicSource
    (hsrc : DahlbergE2ConvexDfvRadiusNonconcyclicSource) :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact signedMengerProfile_dahlbergFourVertex_of_convexDfvRadiusWitnesses
    hsimple horient (hsrc hn hsimple hregular horient hnoncircle)

/-- The nonconcyclic signed-Menger CDFV source implies the nonconcyclic
radius-witness spelling. -/
theorem dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_signedNonconcyclicSource
    (hsrc : DahlbergE2ConvexDfvSignedNonconcyclicSource) :
    DahlbergE2ConvexDfvRadiusNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  exact convexDfvRadiusWitnesses_of_signedMengerProfile_dahlbergFourVertex
    hsimple horient (hsrc hn hsimple hregular horient hnoncircle)

/-- The nonconcyclic radius-witness and signed-Menger CDFV sources are formally
equivalent in the positive-orientation branch. -/
theorem dahlbergE2ConvexDfvRadiusNonconcyclicSource_iff_signedNonconcyclicSource :
    DahlbergE2ConvexDfvRadiusNonconcyclicSource ↔
      DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  constructor
  · exact dahlbergE2ConvexDfvSignedNonconcyclicSource_of_radiusNonconcyclicSource
  · exact dahlbergE2ConvexDfvRadiusNonconcyclicSource_of_signedNonconcyclicSource

/-- The nonconstant and nonconcyclic signed-CDFV source spellings are formally
equivalent in the positive locally regular branch. -/
theorem dahlbergE2ConvexDfvSignedSource_iff_nonconcyclicSource :
    DahlbergE2ConvexDfvSignedSource ↔
      DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  constructor
  · exact dahlbergE2ConvexDfvSignedNonconcyclicSource_of_signedSource
  · exact dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource

/-- The constant-or signed CDFV source can be applied after direct Euclidean
normalization. -/
theorem dahlbergE2ConvexDfvSignedConstantOrSource_directIsometry
    (hsrc : DahlbergE2ConvexDfvSignedConstantOrSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i))) :
    (∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c) ∨
      DahlbergFourVertex
        (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  exact constant_or_dahlbergFourVertex_congr
    (fun i => congrFun (SignedMengerProfile_directIsometry hu a v) i)
    (hsrc hn hsimple₀ hregular₀ horient₀)

/-- The signed CDFV source can be applied after direct Euclidean
normalization. -/
theorem dahlbergE2ConvexDfvSignedSource_directIsometry
    (hsrc : DahlbergE2ConvexDfvSignedSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hnc :
      ¬ ∃ c, ∀ i : ZMod n,
        SignedMengerProfile (fun j => directIsometryR2 u a (v j)) i = c) :
    DahlbergFourVertex (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  have hnc₀ : ¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c :=
    (not_constant_signedMengerProfile_directIsometry_iff hu a v).mp hnc
  exact (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mpr
    (hsrc hn hsimple₀ hregular₀ horient₀ hnc₀)

/-- The nonconcyclic signed CDFV source can be applied after direct Euclidean
normalization. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_directIsometry
    (hsrc : DahlbergE2ConvexDfvSignedNonconcyclicSource)
    {n : ℕ} [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ)
    (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (hregular : DahlbergRegular (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i)))
    (hnoncircle : ¬ Concyclic (fun i => directIsometryR2 u a (v i))) :
    DahlbergFourVertex
      (SignedMengerProfile (fun i => directIsometryR2 u a (v i))) := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have hregular₀ : DahlbergRegular v :=
    (dahlbergRegular_directIsometry_iff hu a v).mp hregular
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  have hnoncircle₀ : ¬ Concyclic v :=
    (not_concyclic_directIsometry hu a v).mp hnoncircle
  exact (dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v).mpr
    (hsrc hn hsimple₀ hregular₀ horient₀ hnoncircle₀)

/-- The radius-profile and signed-Menger forms of the convex/CDFV source are
equivalent in the positive-orientation branch. -/
theorem dahlbergE2_convexDfvRadiusSource_iff_signedSource :
    DahlbergE2ConvexDfvRadiusSource ↔ DahlbergE2ConvexDfvSignedSource := by
  constructor
  · intro hsrc n hne hn v hsimple hregular horient hnc
    exact signedMengerProfile_dahlbergFourVertex_of_convexDfvRadiusWitnesses
      hsimple horient (hsrc hn hsimple hregular horient hnc)
  · intro hsrc n hne hn v hsimple hregular horient hnc
    exact convexDfvRadiusWitnesses_of_signedMengerProfile_dahlbergFourVertex
      hsimple horient (hsrc hn hsimple hregular horient hnc)

/-- Source-level conversion from Dahlberg's CDFV radius-witness source to the
signed-Menger source used by the final E² D4VT route. -/
theorem dahlbergE2ConvexDfvSignedSource_of_radiusSource
    (hsrc : DahlbergE2ConvexDfvRadiusSource) :
    DahlbergE2ConvexDfvSignedSource := by
  exact dahlbergE2_convexDfvRadiusSource_iff_signedSource.mp hsrc

/-- Direct Euclidean isometries preserve Dahlberg's convex radius-witness
package in the positive-orientation branch. -/
theorem dahlbergE2ConvexDfvRadiusWitnesses_directIsometry_iff {n : ℕ}
    [NeZero n] {u : ℂ} (hu : ‖u‖ = 1) (a : ℂ) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon
      (fun i => directIsometryR2 u a (v i)))
    (horient : PositivePolygonOrientation (fun i => directIsometryR2 u a (v i))) :
    DahlbergE2ConvexDfvRadiusWitnesses (fun i => directIsometryR2 u a (v i)) ↔
      DahlbergE2ConvexDfvRadiusWitnesses v := by
  have hsimple₀ : Gluck.Discrete.IsSimplePolygon v :=
    (isSimplePolygon_directIsometry_iff hu a v).mp hsimple
  have horient₀ : PositivePolygonOrientation v :=
    (positivePolygonOrientation_directIsometry hu a v).mp horient
  rw [dahlbergE2ConvexDfvRadiusWitnesses_iff_signedMengerProfile_dahlbergFourVertex
      hsimple horient,
    dahlbergE2ConvexDfvRadiusWitnesses_iff_signedMengerProfile_dahlbergFourVertex
      hsimple₀ horient₀,
    dahlbergFourVertex_signedMengerProfile_directIsometry_iff hu a v]

/-- Source-level conversion from Dahlberg's signed-Menger CDFV source back to
the radius-witness source used by ordered-turn refinements. -/
theorem dahlbergE2ConvexDfvRadiusSource_of_signedSource
    (hsrc : DahlbergE2ConvexDfvSignedSource) :
    DahlbergE2ConvexDfvRadiusSource := by
  exact dahlbergE2_convexDfvRadiusSource_iff_signedSource.mpr hsrc

/-- Dahlberg's Lemma 8 monotonicity bridge in the convex positive-orientation
branch.

Given the CDFV radius witnesses, Lemma 8 propagates disk nesting along the two
monotone arcs between a global radius minimum and maximum.  The resulting
contradiction to the failure of four extrema gives the adjacent radius turns
used by the signed-Menger reduction below. -/
def DahlbergE2Lemma8RadiusTurnBridgeSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ ∃ c, ∀ i : ZMod n, SignedMengerProfile v i = c) →
    DahlbergE2ConvexDfvRadiusWitnesses v →
    PositiveRadiusOrderedAdjacentTurns v

/-- Variant of Dahlberg's Lemma 8 bridge with the redundant nonconstancy
hypothesis removed: nonconstancy follows from the supplied CDFV radius
witnesses. -/
def DahlbergE2Lemma8RadiusTurnBridgeFromWitnessSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    DahlbergE2ConvexDfvRadiusWitnesses v →
    PositiveRadiusOrderedAdjacentTurns v

/-- Certificate extracted from Dahlberg's Lemma 8 disk-nesting propagation:
four ordered one-step extrema of the previous-radius profile.

The global proof still needs the monotone-arc extraction from CDFV witnesses
to this certificate.  Once the eight inequalities below are available, the
conversion to `PositiveRadiusOrderedAdjacentTurns` is purely algebraic. -/
def DahlbergE2Lemma8DiskNestingCertificate {n : ℕ} (v : ZMod n → ℂ) : Prop :=
    ∃ i₁ i₂ i₃ i₄ : ℕ,
      i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₁ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₁ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₁ : ZMod n) + 1) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₂ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v ((((i₂ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₂ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v (i₃ : ZMod n) ∧
      EdgePrevCircleRadiusProfile v (((i₃ : ZMod n) + 1)) <
        EdgePrevCircleRadiusProfile v ((((i₃ : ZMod n) + 1) + 1)) ∧
      EdgePrevCircleRadiusProfile v (i₄ : ZMod n) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1)) ∧
      EdgePrevCircleRadiusProfile v ((((i₄ : ZMod n) + 1) + 1)) <
        EdgePrevCircleRadiusProfile v (((i₄ : ZMod n) + 1))

/-- Sharper Lemma 8 source: the disk-inclusion geometry produces the
disk-nesting certificate from the CDFV radius witnesses. -/
def DahlbergE2Lemma8StrictPreviousRadiusTurnsSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    DahlbergE2ConvexDfvRadiusWitnesses v →
    DahlbergE2Lemma8DiskNestingCertificate v

/-- Paper-faithful global bridge from Theorem 6 to Dahlberg's Lemma 9.

This asks for the plateau-aware four-vertex conclusion stated in the paper
from the exact unordered four-disk certificate supplied by Theorem 6. -/
def DahlbergE2Lemma9PaperBridgeSource : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    PositivePolygonOrientation v →
    (¬ Concyclic v) →
    DahlbergE2Theorem6PaperCertificate v →
    DahlbergFourVertex (SignedMengerProfile v)

/-- Source-free paper-faithful form of Dahlberg's Lemma 9.

The two distinct interior-missing circles from Theorem 6 determine disjoint
weak-maximum plateaux of signed Menger curvature.  Circle rigidity propagates
each plateau across adjacent equal values, and the finite cyclic alternation
lemma supplies a local minimum on each complementary arc. -/
theorem dahlbergE2_lemma9_paper_bridge_source :
    DahlbergE2Lemma9PaperBridgeSource := by
  intro n hne _hn v hsimple hregular horient hnoncircle cert
  letI : NeZero n := hne
  exact signedMengerProfile_dahlbergFourVertex_of_two_distinct_interiorMissing
    hsimple hregular horient hnoncircle
    cert.interiorMissing.misses_i cert.interiorMissing.misses_j
    cert.interiorMissing.distinct

/-- The exact Theorem 6 source and the paper-faithful Lemma 9 bridge give the
strict positive-orientation D4VT source used by the final theorem. -/
theorem dahlbergE2ConvexDfvSignedNonconcyclicSource_of_exactTheorem6_and_lemma9Bridge
    (htheorem6 : DahlbergE2Theorem6ExactPaperSource)
    (hlemma9 : DahlbergE2Lemma9PaperBridgeSource) :
    DahlbergE2ConvexDfvSignedNonconcyclicSource := by
  intro n hne hn v hsimple hregular horient hnoncircle
  letI : NeZero n := hne
  rcases htheorem6 hn hsimple hregular horient hnoncircle with ⟨cert⟩
  exact hlemma9 hn hsimple hregular horient hnoncircle cert

/-- Direct paper-faithful §4 source for Dahlberg's Euclidean D4VT.

The non-strict branch assumes failure of strict orientation and concludes the
D4VT directly from the finite Section 4 contradiction. -/
def DahlbergE2Section4Source : Prop :=
  ∀ {n : ℕ} [NeZero n], ∀ (_hn : 4 ≤ n) {v : ZMod n → ℂ},
    Gluck.Discrete.IsSimplePolygon v →
    DahlbergRegular v →
    (¬ Concyclic v) →
    (¬ (PositivePolygonOrientation v ∨ NegativePolygonOrientation v)) →
    DahlbergFourVertex (SignedMengerProfile v)

/-- The theorem-facing paper sources for Dahlberg's Euclidean D4VT. -/
structure DahlbergE2PaperSources : Prop where
  theorem6 : DahlbergE2Theorem6ExactPaperSource
  lemma9 : DahlbergE2Lemma9PaperBridgeSource
  section4 : DahlbergE2Section4Source

/-- The positively oriented strict branch of Dahlberg's E² D4VT from just the
strict convex signed-Menger CDFV source. -/
theorem dahlbergFourVertex_of_posOrientation_convexDfvSource
    (hsrc : DahlbergE2ConvexDfvSignedSource)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact hsrc hn hsimple hregular horient
    (not_constant_signedMengerProfile_of_not_concyclic_positiveOrientation
      hsimple hregular horient hnoncircle)

/-- The negatively oriented strict branch of Dahlberg's E² D4VT from just the
strict convex signed-Menger CDFV source, after reversal to the positive branch. -/
theorem neg_dahlbergFourVertex_of_negOrientation_convexDfvSource
    (hsrc : DahlbergE2ConvexDfvSignedSource)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (fun i => -SignedMengerProfile v i) := by
  have hpos : PositivePolygonOrientation (ReverseCyclicPolygon v) :=
    positiveOrientation_reverseCyclicPolygon_of_negativeOrientation horient
  have hsimple' : Gluck.Discrete.IsSimplePolygon (ReverseCyclicPolygon v) :=
    isSimplePolygon_reverseCyclicPolygon hsimple
  have hregular' : DahlbergRegular (ReverseCyclicPolygon v) :=
    dahlbergRegular_reverseCyclicPolygon hregular
  have hnoncircle' : ¬ Concyclic (ReverseCyclicPolygon v) := by
    intro hcyc
    exact hnoncircle (concyclic_reverseCyclicPolygon_iff.mp hcyc)
  have hfv_rev : DahlbergFourVertex (SignedMengerProfile (ReverseCyclicPolygon v)) :=
    dahlbergFourVertex_of_posOrientation_convexDfvSource
      hsrc hn hsimple' hregular' hpos hnoncircle'
  have hfv_reflected : DahlbergFourVertex (fun i => -SignedMengerProfile v (-i)) := by
    convert hfv_rev using 1
    ext i
    exact (SignedMengerProfile_reverseCyclicPolygon v i).symm
  exact (dahlbergFourVertex_reflectIndex_iff
    (κ := fun i : ZMod n => -SignedMengerProfile v i) (a := 0)).mp (by
      convert hfv_reflected using 1
      ext i
      congr 1
      abel_nf)

/-- The negatively oriented strict branch of Dahlberg's E² D4VT from just the
strict convex signed-Menger CDFV source. -/
theorem dahlbergFourVertex_of_negOrientation_convexDfvSource
    (hsrc : DahlbergE2ConvexDfvSignedSource)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  exact dahlbergFourVertex_of_neg
    (neg_dahlbergFourVertex_of_negOrientation_convexDfvSource
      hsrc hn hsimple hregular horient hnoncircle)

/-- The strict-orientation branch of Dahlberg's E² D4VT from just the strict
convex signed-Menger CDFV source. -/
theorem dahlbergFourVertex_of_strictOrientation_convexDfvSource
    (hsrc : DahlbergE2ConvexDfvSignedSource)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  rcases horient with hpos | hneg
  · exact dahlbergFourVertex_of_posOrientation_convexDfvSource
      hsrc hn hsimple hregular hpos hnoncircle
  · exact dahlbergFourVertex_of_negOrientation_convexDfvSource
      hsrc hn hsimple hregular hneg hnoncircle

/-- Dahlberg's Euclidean D4VT from the theorem-facing paper sources. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_paperSources
    (hsrc : DahlbergE2PaperSources)
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) := by
  have hstrict : DahlbergE2ConvexDfvSignedSource :=
    dahlbergE2ConvexDfvSignedSource_of_nonconcyclicSource
      (dahlbergE2ConvexDfvSignedNonconcyclicSource_of_exactTheorem6_and_lemma9Bridge
        hsrc.theorem6 hsrc.lemma9)
  by_cases horient : PositivePolygonOrientation v ∨ NegativePolygonOrientation v
  · exact dahlbergFourVertex_of_strictOrientation_convexDfvSource
      hstrict hn hsimple hregular horient hnoncircle
  · exact hsrc.section4 hn hsimple hregular hnoncircle horient

end Gluck.Forward
