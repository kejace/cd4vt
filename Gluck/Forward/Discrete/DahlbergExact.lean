/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4CircleArcSource

/-!
# Dahlberg's Euclidean theorem from the exact paper sources

This module exposes the source-free Euclidean D4VT endpoint obtained from the
proved exact Theorem 6, plateau-aware Lemma 9 bridge, and direct Section 4
contradiction.
-/

namespace Gluck.Forward

/-- Dahlberg's Euclidean discrete four-vertex theorem in the nonconcyclic
case, with no external paper-source argument. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_exactPaper
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) :=
  signedMengerProfile_dahlbergFourVertex_E2_of_paperSources
    dahlbergE2_paperSources hn hsimple hregular hnoncircle

end Gluck.Forward
