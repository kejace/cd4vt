/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Definitions in the main statements

Every definition that the six theorems of the paper's Lean appendix depend on,
through their types and definition bodies: polygons, curvature, coherence,
plateau extrema, the DFV condition, side-tangent circles and the hexagon band
profile. They import only Mathlib.

`Challenge.lean` repeats this file verbatim, followed by the six statements, and
Comparator checks the library against it. Keeping these definitions together in
one module makes the library's auxiliary proof names (such as `foo._proof_1`,
which Lean shares between declarations of one module) coincide with the
challenge's, as Comparator requires.
-/

@[expose] public section

/-! ### Definitions formerly in `Gluck.Discrete.Defs` -/

section

namespace Gluck.Discrete

open scoped Real

/-- Generalized sine over the unit space forms: `sin` at `K = 1`, `sinh` at
`K = -1`, identity otherwise (in particular at the Euclidean `K = 0`). -/
noncomputable def sK (K x : ℝ) : ℝ :=
  if K = 1 then Real.sin x else if K = -1 then Real.sinh x else x

/-- Generalized cosine over the unit space forms: `cos` at `K = 1`, `cosh` at
`K = -1`, constant `1` otherwise. -/
noncomputable def cK (K x : ℝ) : ℝ :=
  if K = 1 then Real.cos x else if K = -1 then Real.cosh x else 1

/-- Generalized tangent `tK K = sK K / cK K`: `tan` at `K = 1`, `tanh` at
`K = -1`, identity at `K = 0`. -/
noncomputable def tK (K x : ℝ) : ℝ :=
  sK K x / cK K x

variable {n : ℕ}

/-- The strict moderate-arc domain for cyclic curvature data `κ` and edge
lengths `ℓ` at ambient curvature `K`: positive edge lengths, positive branch
(`0 < sK`, `0 < cK` at half-lengths — automatic for `K ∈ {0, -1}`, encoding
`ℓ i < π` at `K = 1`), and the strict wall `|κ i| * tK K (ℓ j / 2) < 1` on
both edges adjacent to each vertex. The strict wall is what makes every
turning angle strictly less than `π` (`abs_turningAngle_lt_pi`). -/
def ModerateArc (K : ℝ) (κ ℓ : ZMod n → ℝ) : Prop :=
  ∀ i : ZMod n, 0 < ℓ i ∧ 0 < sK K (ℓ i / 2) ∧ 0 < cK K (ℓ i / 2) ∧
    |κ i| * tK K (ℓ (i - 1) / 2) < 1 ∧ |κ i| * tK K (ℓ i / 2) < 1

/-- The analytic turning-angle law (TA): the turning angle at vertex `i` is
`arcsin (κ i * tK K (ℓ (i-1) / 2)) + arcsin (κ i * tK K (ℓ i / 2))`. Analytic
in `κ i` through `κ i = 0` (a straight vertex), hence the correct gauge for
mixed-sign profiles. -/
noncomputable def turningAngle (K : ℝ) (κ ℓ : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  Real.arcsin (κ i * tK K (ℓ (i - 1) / 2)) + Real.arcsin (κ i * tK K (ℓ i / 2))

/-- Heading of edge `j` in the Euclidean development: the cumulative turning
`ψ j = ∑_{m ≤ j} θ m` over the ordered lift `m ↦ (m : ZMod n)`. Edge `j`
leaves vertex `j` after the turn at vertex `j`. -/
noncomputable def heading (κ ℓ : ZMod n → ℝ) (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (j + 1), turningAngle 0 κ ℓ (m : ZMod n)

/-- Vertex `k` of the Euclidean development in `ℂ`:
`v k = ∑_{j < k} ℓ j · e^{i ψ j}`. -/
noncomputable def vertexR2 (κ ℓ : ZMod n → ℝ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k,
    (ℓ (j : ZMod n) : ℂ) * Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)

/-- The closure gap `E(κ, ℓ) = v n`: the development closes up iff it
vanishes. -/
noncomputable def closureGap (κ ℓ : ZMod n → ℝ) : ℂ :=
  vertexR2 κ ℓ n

/-- The total turning `T(κ, ℓ) = ∑_{i ∈ ZMod n} θ i` of the Euclidean
turning angles. -/
noncomputable def turningSum [NeZero n] (κ ℓ : ZMod n → ℝ) : ℝ :=
  ∑ i : ZMod n, turningAngle 0 κ ℓ i

/-- The polygon of a closed development: `i ↦ v (i.val)`. Well-defined as a
cyclic object by `vertexR2_add_n`. -/
noncomputable def polygonR2 (κ ℓ : ZMod n → ℝ) : ZMod n → ℂ :=
  fun i => vertexR2 κ ℓ i.val

/-- A cyclic vertex tuple `v : ZMod n → ℂ` is a simple polygon when every
closed edge segment `segment ℝ (v i) (v (i + 1))` is nondegenerate,
consecutive edges meet exactly in their shared vertex, and non-adjacent
edges are disjoint. -/
def IsSimplePolygon (v : ZMod n → ℂ) : Prop :=
  (∀ i : ZMod n, v i ≠ v (i + 1)) ∧
    (∀ i : ZMod n,
      segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v (i + 1)) (v (i + 1 + 1))
        = {v (i + 1)}) ∧
    (∀ i j : ZMod n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v j) (v (j + 1)) = ∅)

end Gluck.Discrete

end

/-! ### Definitions formerly in `Gluck.Discrete.Converse` -/

section

namespace Gluck.Discrete

variable {n : ℕ}

/-- **Discrete four-vertex window**: the profile `κ : ZMod n → ℝ` admits four
cyclically ordered indices — represented by `ℕ`-lifts
`i₁ < i₂ < i₃ < i₄ < i₁ + n` — whose values alternate across the level `c`:
`κ i₂, κ i₄ < c < κ i₁, κ i₃`. The hypothesis shape matches
`dfv_plateau_extrema` verbatim. -/
def DFV (κ : ZMod n → ℝ) (c : ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ, i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
    c < κ ((i₁ : ℕ) : ZMod n) ∧ κ ((i₂ : ℕ) : ZMod n) < c ∧
    c < κ ((i₃ : ℕ) : ZMod n) ∧ κ ((i₄ : ℕ) : ZMod n) < c

end Gluck.Discrete

end

/-! ### Definitions formerly in `Gluck.Discrete.TangentChord` -/

section

namespace Gluck.Discrete

open scoped Real

attribute [local instance] Complex.finrank_real_complex_fact

/-- The signed twice-area of a planar triple: the `z`-component of the cross
product `(B - A) × (C - A) = Im(conj(B-A) · (C-A))`. Positive when `A, B, C`
turn left. This is the affine-point form of `Complex.orientation.areaForm`. -/
def crossR2 (A B C : ℂ) : ℝ :=
  (B - A).re * (C - A).im - (B - A).im * (C - A).re

/-- The signed Menger curvature of an ordered planar triple. On a nondegenerate
triple its absolute value is the reciprocal circumradius; the sign records the
triple's orientation. Project-local Euclidean definition. -/
noncomputable def signedMengerR2 (A B C : ℂ) : ℝ :=
  2 * crossR2 A B C / (dist A B * dist B C * dist C A)

end Gluck.Discrete

end

/-! ### Definitions formerly in `Gluck.Discrete.LocalRegularity` -/

section

namespace Gluck.Discrete

open scoped Real
open Complex (normSq)

variable {n : ℕ}

/-- The circumcenter of the plane triple `p, q, r`, in closed form: with
`u = q - p`, `w = r - p`,
`c = p + i (|w|² u - |u|² w) / (2 crossR2 p q r)`. A total function; its
characterizing properties hold under the non-collinearity guard
`crossR2 p q r ≠ 0`. Center of Dahlberg's discrete circle of curvature
through the triple. -/
noncomputable def circumcenterR2 (p q r : ℂ) : ℂ :=
  p + Complex.I * ((normSq (r - p) : ℝ) * (q - p) - (normSq (q - p) : ℝ) * (r - p))
      / (2 * (crossR2 p q r : ℂ))

/-- The open vertex cone at vertex `i`: strictly positive combinations of the
two incident edge vectors. Tabachnikov's *coherence* asks the circumcenter of
each consecutive triple to lie inside this cone. -/
def vertexCone (v : ZMod n → ℂ) (i : ZMod n) : Set ℂ :=
  {z | ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
    z = v i + (s : ℂ) * (v (i - 1) - v i) + (t : ℂ) * (v (i + 1) - v i)}

/-- **Coherent polygon** (Tabachnikov, arXiv:0710.5902, Problem 2): every
consecutive triple is non-collinear and the center of its circumscribed
circle lies inside the open cone of the middle vertex. -/
def CoherentR2 (v : ZMod n → ℂ) : Prop :=
  ∀ i : ZMod n, crossR2 (v i) (v (i - 1)) (v (i + 1)) ≠ 0 ∧
    circumcenterR2 (v i) (v (i - 1)) (v (i + 1)) ∈ vertexCone v i

/-- A plateau local-maximum run for `f`, recorded by an `ℕ`-lift `a` and a
run length `k`: `f` is constant on the lifted run `a, a+1, …, a+k` (as
residues) and drops strictly at both extended ends. Dahlberg's `I(f,P)/Î`
vocabulary in existential form: a constant run with strict drops at both
ends is automatically the maximal plateau through any of its points. -/
def PlateauMaxRun (f : ZMod n → ℝ) (a k : ℕ) : Prop :=
  (∀ m ≤ k, f ((a + m : ℕ) : ZMod n) = f (a : ZMod n)) ∧
    f ((a : ZMod n) - 1) < f (a : ZMod n) ∧
    f ((a + k + 1 : ℕ) : ZMod n) < f (a : ZMod n)

/-- A plateau local-minimum run: as `PlateauMaxRun` with the strict
inequalities reversed. -/
def PlateauMinRun (f : ZMod n → ℝ) (a k : ℕ) : Prop :=
  (∀ m ≤ k, f ((a + m : ℕ) : ZMod n) = f (a : ZMod n)) ∧
    f (a : ZMod n) < f ((a : ZMod n) - 1) ∧
    f (a : ZMod n) < f ((a + k + 1 : ℕ) : ZMod n)

end Gluck.Discrete

end

/-! ### Definitions formerly in `Gluck.Discrete.TabachnikovReduction` -/

section

namespace Gluck.Discrete

variable {n : ℕ}

/-- **Two distinct plateau maxima** — Dahlberg's "`κ` has at least two local
maxima", transcribed: two short plateau maximum runs whose residue supports
are disjoint.  Its shape is verbatim the first conjunct of the conclusion of
`DFV.plateau_extrema`. -/
def HasTwoPlateauMaxRuns (κ : ZMod n → ℝ) : Prop :=
  ∃ a₁ k₁ a₂ k₂ : ℕ, k₁ < n ∧ k₂ < n ∧
    PlateauMaxRun κ a₁ k₁ ∧ PlateauMaxRun κ a₂ k₂ ∧
    ∀ m₁, m₁ ≤ k₁ → ∀ m₂, m₂ ≤ k₂ →
      ((a₁ + m₁ : ℕ) : ZMod n) ≠ ((a₂ + m₂ : ℕ) : ZMod n)

/-- **Two distinct plateau minima** — `HasTwoPlateauMaxRuns` with
`PlateauMinRun` in place of `PlateauMaxRun`.  Verbatim the second conjunct of
the conclusion of `DFV.plateau_extrema`. -/
def HasTwoPlateauMinRuns (κ : ZMod n → ℝ) : Prop :=
  ∃ a₁ k₁ a₂ k₂ : ℕ, k₁ < n ∧ k₂ < n ∧
    PlateauMinRun κ a₁ k₁ ∧ PlateauMinRun κ a₂ k₂ ∧
    ∀ m₁, m₁ ≤ k₁ → ∀ m₂, m₂ ≤ k₂ →
      ((a₁ + m₁ : ℕ) : ZMod n) ≠ ((a₂ + m₂ : ℕ) : ZMod n)

end Gluck.Discrete

end

/-! ### Definitions formerly in `Gluck.Discrete.TabachnikovConverse` -/

section

namespace Gluck.Discrete

open Complex (normSq)

variable {n : ℕ}

/-- **At least two local maxima and two local minima** (Tabachnikov's
hypothesis), with local extrema counted plateau-aware in Dahlberg's sense:
a maximal constant run whose two outside neighbours are both strictly lower
(resp. higher), and two extrema are distinct when their runs are disjoint. -/
def IsPlateauTwoMaxTwoMin (r : ZMod n → ℝ) : Prop :=
  HasTwoPlateauMaxRuns r ∧ HasTwoPlateauMinRuns r

/-- **Coherent convex polygon** (Tabachnikov, Problem 2): a simple polygon,
strictly convex and counterclockwise (every vertex lies strictly to the left
of every edge not incident to it), and coherent. -/
def IsCoherentConvexPolygon (v : ZMod n → ℂ) : Prop :=
  IsSimplePolygon v ∧
    (∀ a c : ZMod n, c ≠ a → c ≠ a + 1 → 0 < crossR2 (v a) (v (a + 1)) (v c)) ∧
    CoherentR2 v

/-- The radius of the circle through the consecutive triple
`v (i - 1), v i, v (i + 1)`. -/
noncomputable def vertexCircumradius (v : ZMod n → ℂ) (i : ZMod n) : ℝ :=
  dist (circumcenterR2 (v i) (v (i - 1)) (v (i + 1))) (v i)

end Gluck.Discrete

end

/-! ### Definitions formerly in `Gluck.Discrete.PolygonConvexity` -/

section

namespace Gluck.Discrete

open scoped Pointwise Real

variable {n : ℕ}

/-- Every vertex other than the endpoints lies in the open left half-plane of
each oriented edge.  This is the strict-convexity interface consumed by the
Dahlberg edge-envelope argument. -/
def StrictConvexEdgeSupport (v : ZMod n → ℂ) : Prop :=
  ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 →
    0 < crossR2 (v i) (v (i + 1)) (v j)

end Gluck.Discrete

end

/-! ### Definitions formerly in `Gluck.Discrete.LocalContinuity` -/

section

namespace Gluck.Discrete

open Filter Set
open scoped Topology

variable {n : ℕ} [NeZero n]

/-- A local family in the literal geometry of `RealizesR2`. The same length
function supplies exact closure, a full turn, and the simple polygon. -/
structure LocalDiscreteRealizationFamily (κ₀ : ZMod n → ℝ) where
  neighborhood : Set (ZMod n → ℝ)
  isOpen_neighborhood : IsOpen neighborhood
  base_mem : κ₀ ∈ neighborhood
  lengths : (ZMod n → ℝ) → (ZMod n → ℝ)
  contDiffOn_lengths : ContDiffOn ℝ 1 lengths neighborhood
  positive : ∀ κ ∈ neighborhood, ∀ i, 0 < κ i
  moderate : ∀ κ ∈ neighborhood, ModerateArc 0 κ (lengths κ)
  closure : ∀ κ ∈ neighborhood, closureGap κ (lengths κ) = 0
  fullTurn : ∀ κ ∈ neighborhood, turningSum κ (lengths κ) = 2 * Real.pi
  simple : ∀ κ ∈ neighborhood, IsSimplePolygon (polygonR2 κ (lengths κ))
  contDiffOn_vertices : ContDiffOn ℝ 1 (fun κ => polygonR2 κ (lengths κ)) neighborhood

end Gluck.Discrete

end

/-! ### Definitions formerly in `Gluck.Forward.Kernel` -/

section

namespace Gluck.Forward

open scoped Real

/-- A Euclidean circle with centre `O` and positive radius `R` through a triple. -/
def CircumcircleR2 (A B C O : ℂ) (R : ℝ) : Prop :=
  0 < R ∧ dist O A = R ∧ dist O B = R ∧ dist O C = R

/-- The closed convex vertex cone at `B`, spanned by the rays toward `A` and
`C`.  Dahlberg's regularity asks that the circumcenter lie in this cone. -/
def InVertexCone (A B C O : ℂ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
    O - B = (a : ℂ) * (A - B) + (b : ℂ) * (C - B)

end Gluck.Forward

end

/-! ### Definitions formerly in `Gluck.Forward.Discrete.Defs` -/

section

namespace Gluck.Forward

def DahlbergRegularAt (A B C : ℂ) : Prop :=
  (Gluck.Discrete.crossR2 A B C = 0 ∧ B ∈ segment ℝ A C) ∨
    ∃ O R, CircumcircleR2 A B C O R ∧ InVertexCone A B C O

/-- Every vertex of a cyclic Euclidean polygon is regular in Dahlberg's sense. -/
def DahlbergRegular {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i, DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1))

/-- The signed-Menger curvature profile of a cyclic Euclidean polygon. -/
noncomputable def SignedMengerProfile {n : ℕ} (v : ZMod n → ℂ) : ZMod n → ℝ :=
  fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))

end Gluck.Forward

end

/-! ### Definitions formerly in `Gluck.Discrete.SideTangentDFV` -/

section

open scoped BigOperators

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- The coefficient that arises by cyclic summation by parts of scaled edges. -/
def radiusDifference (ρ : ZMod n → ℝ) (i : ZMod n) : ℝ := ρ (i - 1) - ρ i

end Gluck.Discrete.SideTangent

end

/-! ### Definitions formerly in `Gluck.Discrete.SideTangentConverse` -/

section

open scoped BigOperators InnerProductSpace

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- The three inward signed-distance equations at a given central edge. -/
def ThreeLineCircle (P N : ZMod n → ℂ) (i : ZMod n) (C : ℂ) (r : ℝ) : Prop :=
  ⟪N (i - 1), P i - C⟫_ℝ = r ∧ ⟪N i, P i - C⟫_ℝ = r ∧
    ⟪N (i + 1), P (i + 1) - C⟫_ℝ = r

/-- Exact supporting-line realization of the prescribed cyclic radii. -/
structure IsSideTangentRealization [NeZero n] (ρ : ZMod n → ℝ)
    (P N C : ZMod n → ℂ) : Prop where
  radius_pos : ∀ i, 0 < ρ i
  simple : IsSimplePolygon P
  strict_convex : StrictConvexEdgeSupport P
  unit_normal : ∀ i, ‖N i‖ = 1
  oriented_edge : ∀ i, ∃ ℓ : ℝ, 0 < ℓ ∧ P (i + 1) - P i = ℓ • (Complex.I * N i)
  supporting : ∀ i j, ⟪N i, P j - P i⟫_ℝ ≤ 0
  circles : ∀ i, ThreeLineCircle P N i (C i) (ρ i)
  unique_circle : ∀ i D r, ThreeLineCircle P N i D r → D = C i ∧ r = ρ i
  central_contact : ∀ i, C i + ρ i • N i ∈ openSegment ℝ (P i) (P (i + 1))

/-- A simple strictly convex polygon with the exact three-line radius at every edge. -/
def RealizesSideTangent [NeZero n] (ρ : ZMod n → ℝ) : Prop :=
  ∃ P N C : ZMod n → ℂ, IsSideTangentRealization ρ P N C

/-- Original constant-or-four-sign-change admissibility, with zero differences retained. -/
def SideTangentAdmissible (ρ : ZMod n → ℝ) : Prop :=
  (∀ i, 0 < ρ i) ∧ ((∃ r, ∀ i, ρ i = r) ∨ DFV (radiusDifference ρ) 0)

end Gluck.Discrete.SideTangent

end

/-! ### Definitions formerly in `Gluck.Discrete.GlobalContinuity.LevelBands` -/

section

namespace Gluck.Discrete.GlobalContinuity

def bandProfile (s : ℝ) : ZMod 6 → ℝ :=
  ![14, 11, 10 + 3 * s, 5, 7 - 3 * s, 3]

end Gluck.Discrete.GlobalContinuity

end
