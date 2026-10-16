/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Challenge.Discrete.LocalRegularity

/-!
# Challenge: `Gluck/Discrete/TabachnikovReduction.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/TabachnikovReduction.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

@[expose] public section

namespace Gluck.Discrete

variable {n : ℕ}

/-- **Two distinct plateau maxima**: two short plateau maximum runs whose
residue supports are disjoint. -/
def HasTwoPlateauMaxRuns (κ : ZMod n → ℝ) : Prop :=
  ∃ a₁ k₁ a₂ k₂ : ℕ, k₁ < n ∧ k₂ < n ∧
    PlateauMaxRun κ a₁ k₁ ∧ PlateauMaxRun κ a₂ k₂ ∧
    ∀ m₁, m₁ ≤ k₁ → ∀ m₂, m₂ ≤ k₂ →
      ((a₁ + m₁ : ℕ) : ZMod n) ≠ ((a₂ + m₂ : ℕ) : ZMod n)

/-- **Two distinct plateau minima**: `HasTwoPlateauMaxRuns` with
`PlateauMinRun` in place of `PlateauMaxRun`. -/
def HasTwoPlateauMinRuns (κ : ZMod n → ℝ) : Prop :=
  ∃ a₁ k₁ a₂ k₂ : ℕ, k₁ < n ∧ k₂ < n ∧
    PlateauMinRun κ a₁ k₁ ∧ PlateauMinRun κ a₂ k₂ ∧
    ∀ m₁, m₁ ≤ k₁ → ∀ m₂, m₂ ≤ k₂ →
      ((a₁ + m₁ : ℕ) : ZMod n) ≠ ((a₂ + m₂ : ℕ) : ZMod n)

end Gluck.Discrete
