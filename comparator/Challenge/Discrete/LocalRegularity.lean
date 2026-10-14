/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Challenge.Discrete.TangentChord

/-!
# Challenge: `Gluck/Discrete/LocalRegularity.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/LocalRegularity.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

namespace Gluck.Discrete

open scoped Real
open Complex (normSq)

variable {n : ℕ}

/-- The circumcenter of the plane triple `p, q, r`, in closed form: with
`u = q - p`, `w = r - p`,
`c = p + i (|w|² u - |u|² w) / (2 crossR2 p q r)`. A total function; its
characterizing properties hold under the non-collinearity guard
`crossR2 p q r ≠ 0`. -/
noncomputable def circumcenterR2 (p q r : ℂ) : ℂ :=
  p + Complex.I * ((normSq (r - p) : ℝ) * (q - p) - (normSq (q - p) : ℝ) * (r - p))
      / (2 * (crossR2 p q r : ℂ))

/-- The open vertex cone at vertex `i`: strictly positive combinations of the
two incident edge vectors. -/
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
residues) and drops strictly at both extended ends. -/
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
