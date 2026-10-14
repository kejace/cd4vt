/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Challenge.Discrete.Defs

/-!
# Challenge: `Gluck/Discrete/Converse.lean`

Verbatim copies (docstrings abridged) of the definitions from `Gluck/Discrete/Converse.lean` that the challenge
statements depend on, in the library's order and `open`/`variable` context.
-/

namespace Gluck.Discrete

variable {n : ℕ}

/-- **Discrete four-vertex window**: the profile `κ : ZMod n → ℝ` admits four
cyclically ordered indices — represented by `ℕ`-lifts
`i₁ < i₂ < i₃ < i₄ < i₁ + n` — whose values alternate across the level `c`:
`κ i₂, κ i₄ < c < κ i₁, κ i₃`. -/
def DFV (κ : ZMod n → ℝ) (c : ℝ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ, i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
    c < κ ((i₁ : ℕ) : ZMod n) ∧ κ ((i₂ : ℕ) : ZMod n) < c ∧
    c < κ ((i₃ : ℕ) : ZMod n) ∧ κ ((i₄ : ℕ) : ZMod n) < c

end Gluck.Discrete
