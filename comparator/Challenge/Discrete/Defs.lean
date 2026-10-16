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
# Challenge: `Gluck/Discrete/Defs.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/Defs.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

@[expose] public section

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
both edges adjacent to each vertex. -/
def ModerateArc (K : ℝ) (κ ℓ : ZMod n → ℝ) : Prop :=
  ∀ i : ZMod n, 0 < ℓ i ∧ 0 < sK K (ℓ i / 2) ∧ 0 < cK K (ℓ i / 2) ∧
    |κ i| * tK K (ℓ (i - 1) / 2) < 1 ∧ |κ i| * tK K (ℓ i / 2) < 1

/-- The analytic turning-angle law (TA): the turning angle at vertex `i` is
`arcsin (κ i * tK K (ℓ (i-1) / 2)) + arcsin (κ i * tK K (ℓ i / 2))`. -/
noncomputable def turningAngle (K : ℝ) (κ ℓ : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  Real.arcsin (κ i * tK K (ℓ (i - 1) / 2)) + Real.arcsin (κ i * tK K (ℓ i / 2))

/-- Heading of edge `j` in the Euclidean development: the cumulative turning
`ψ j = ∑_{m ≤ j} θ m` over the ordered lift `m ↦ (m : ZMod n)`. -/
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

/-- The polygon of a closed development: `i ↦ v (i.val)`. -/
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
