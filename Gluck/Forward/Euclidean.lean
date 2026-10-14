import Gluck.Forward.Discrete.DahlbergExact

/-! Euclidean discrete reductions for Dahlberg's four-vertex theorem. -/

namespace Gluck.Forward

/-! ## Same-sign Euclidean discrete reductions -/

/-- E² source-form Dahlberg reduction: a nonconcyclic locally regular simple
polygon has two local maxima and two local minima of signed Menger curvature,
alternating in Dahlberg's plateau-aware sense. -/
theorem signedMengerProfile_dahlbergFourVertex_E2_of_not_concyclic {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex (SignedMengerProfile v) :=
  signedMengerProfile_dahlbergFourVertex_E2_exactPaper hn v hsimple hregular hnoncircle

/-- Dahlberg's Euclidean discrete four-vertex theorem: the signed Menger
curvature of a nonconcyclic locally regular simple closed polygon has two
local maxima and two local minima in cyclic, plateau-aware order. -/
theorem dahlberg_discrete_four_vertex_E2 {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (v : ZMod n → ℂ)
    (hsimple : Gluck.Discrete.IsSimplePolygon v)
    (hregular : DahlbergRegular v) (hnoncircle : ¬ Concyclic v) :
    DahlbergFourVertex
      (fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))) := by
  change DahlbergFourVertex (SignedMengerProfile v)
  exact signedMengerProfile_dahlbergFourVertex_E2_of_not_concyclic
    hn v hsimple hregular hnoncircle

end Gluck.Forward
