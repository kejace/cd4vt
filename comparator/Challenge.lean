/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Challenge.Discrete.Defs
import Challenge.Discrete.Converse
import Challenge.Discrete.TangentChord
import Challenge.Discrete.LocalRegularity
import Challenge.Discrete.TabachnikovReduction
import Challenge.Discrete.TabachnikovConverse
import Challenge.Discrete.PolygonConvexity
import Challenge.Discrete.LocalContinuity
import Challenge.Forward.Kernel
import Challenge.Forward.Discrete.Defs
import Challenge.Discrete.SideTangentDFV
import Challenge.Discrete.SideTangentConverse
import Challenge.Discrete.GlobalContinuity.LevelBands

/-!
# Comparator challenge: the formal statements of the discrete paper

This file states the six theorems displayed in the Lean appendix of
`paper/tabachnikov-converse.tex`, each with the proof `sorry`. It is the trusted
statement, meant to be read by a reviewer, together with the files it imports:

* `Challenge/**` contains every project definition the six statements depend on
  (through types and definition bodies; no lemma is needed), with the code
  copied verbatim from the library (docstrings abridged) and the same names,
  order and `open`/`variable` context.
  There is one file per library module because Lean shares auto-generated
  auxiliary proofs (such as `foo._proof_1`) between declarations of the same
  module, and these names are part of the compared terms.
* Only Mathlib is imported (seven modules, in `Challenge/Discrete/Defs.lean`);
  nothing from the library itself.

Comparator (see `README.md`) checks that the library proves theorems with these
names whose statements, and every definition they depend on, are identical to
the ones here; that the proofs use only `propext`, `Classical.choice` and
`Quot.sound`; and that the Lean kernel accepts them.
-/

/-! ## The six theorems -/

namespace Gluck.Discrete

variable {n : ℕ}

/-- **Theorem 1.1.** Prescribed positive plateau-extremal radii are realized by one
coherent strictly convex polygon. -/
theorem tabachnikov_converse_geometric [NeZero n] (hn : 4 ≤ n) {r : ZMod n → ℝ}
    (hr : ∀ i, 0 < r i) (hext : IsPlateauTwoMaxTwoMin r) :
    ∃ v : ZMod n → ℂ, IsCoherentConvexPolygon v ∧
      ∀ i, vertexCircumradius v i = r i :=
  sorry

/-- **Corollary 1.2.** Positive nonconstant cyclic data are the vertex-circumradius
sequence of a coherent strictly convex polygon exactly when they have two distinct
plateau maxima and two distinct plateau minima. -/
theorem tabachnikov_radius_characterization [NeZero n] (hn : 4 ≤ n) {r : ZMod n → ℝ}
    (hr : ∀ i, 0 < r i) (hnc : ¬ ∃ c, ∀ i, r i = c) :
    (∃ v : ZMod n → ℂ, IsCoherentConvexPolygon v ∧
      ∀ i, vertexCircumradius v i = r i) ↔ IsPlateauTwoMaxTwoMin r :=
  sorry

/-- **Theorem 7.1.** Local continuous (indeed `C¹`) coherent realization for every
positive strict-DFV word, including repeated readings and constant runs. -/
theorem localContinuousRealization_of_dfv [NeZero n]
    {κ₀ : ZMod n → ℝ} {c : ℝ} (hκ₀ : ∀ i, 0 < κ₀ i) (hdfv : DFV κ₀ c) :
    Nonempty (LocalDiscreteRealizationFamily κ₀) :=
  sorry

end Gluck.Discrete

namespace Gluck.Discrete.GlobalContinuity

open Gluck.Forward

/-- **Theorem 7.2.** No continuous path of simple, Dahlberg-regular hexagons
realizes the band profiles `κ^s`, `s ∈ [0, 1]`. -/
theorem no_continuous_regular_hexagon_path :
    ¬ ∃ p : ℝ → (ZMod 6 → ℂ), ContinuousOn p (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsSimplePolygon (p s) ∧ DahlbergRegular (p s) ∧
        SignedMengerProfile (p s) = bandProfile s :=
  sorry

end Gluck.Discrete.GlobalContinuity

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- **Theorem 8.2.** The side-tangent-circle converse for positive cyclic radii:
constants and all DFV difference profiles have an exact realization. -/
theorem sideTangentConverse [NeZero n] (hn : 4 ≤ n) (ρ : ZMod n → ℝ)
    (h : SideTangentAdmissible ρ) : RealizesSideTangent ρ :=
  sorry

/-- **Corollary 8.6.** Positive constant profiles and exactly the four-sign-change
profiles are the radii of inward circles tangent to consecutive supporting lines of a
simple strictly convex polygon, with the central tangency point in its open edge. -/
theorem realizesSideTangent_iff_admissible [NeZero n] (hn : 4 ≤ n) (ρ : ZMod n → ℝ) :
    RealizesSideTangent ρ ↔ SideTangentAdmissible ρ :=
  sorry

end Gluck.Discrete.SideTangent
