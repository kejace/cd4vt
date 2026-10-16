/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.GraftContraction
public import Mathlib.Topology.Order.IntermediateValue

/-!
# An admissible path without a continuous DFV-level selection

This proves an obstruction to selecting a *level*. It does not identify a
continuous geometric invariant of a polygon and does not claim to refute
global polygon selection. See README.md for the separate smooth argument.
-/

@[expose] public section

namespace Gluck.Discrete.GlobalContinuity

def bandProfile (s : ℝ) : ZMod 6 → ℝ :=
  ![14, 11, 10 + 3 * s, 5, 7 - 3 * s, 3]

theorem continuous_bandProfile : Continuous bandProfile := by
  apply continuous_pi
  intro i
  fin_cases i <;> norm_num [bandProfile] <;> fun_prop

theorem bandProfile_pos {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i, 0 < bandProfile s i := by
  intro i
  fin_cases i <;> norm_num [bandProfile] <;> linarith [hs.1, hs.2]

theorem bandProfile_nonconstant (s : ℝ) :
    ¬ ∃ c, ∀ i, bandProfile s i = c := by
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h5 := hc 5
  norm_num [bandProfile] at h0 h5
  linarith

theorem bandProfile_dfv_iff {s c : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    DFV (bandProfile s) c ↔
      (5 < c ∧ c < 7 - 3 * s) ∨ (11 < c ∧ c < 10 + 3 * s) := by
  constructor
  · intro hd
    obtain ⟨b₁, b₂, b₃, b₄, h₁₂, h₂₃, h₃₄, h₄, ht⟩ := hd.exists_increasing
    have hb₁ : b₁ ≤ 2 := by omega
    have hb₂ : b₂ ≤ 3 := by omega
    have hb₃ : b₃ ≤ 4 := by omega
    rcases ht with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4⟩
    all_goals
      interval_cases b₁ <;> interval_cases b₂ <;> try omega
    all_goals
      interval_cases b₃ <;> interval_cases b₄ <;> try omega
    all_goals
      norm_num [bandProfile] at h1 h2 h3 h4
      first
      | exact Or.inl ⟨by linarith [hs.1, hs.2], by linarith [hs.1, hs.2]⟩
      | exact Or.inr ⟨by linarith [hs.1, hs.2], by linarith [hs.1, hs.2]⟩
  · rintro (⟨hl, hu⟩ | ⟨hl, hu⟩)
    · refine ⟨0, 3, 4, 5, by omega, by omega, by omega, by omega, ?_⟩
      norm_num [bandProfile]
      exact ⟨by linarith [hs.1], hl, hu, by linarith⟩
    · refine ⟨0, 1, 2, 5, by omega, by omega, by omega, by omega, ?_⟩
      norm_num [bandProfile]
      exact ⟨by linarith [hs.2], hl, hu, by linarith⟩

theorem bandProfile_admissible {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    DiscreteFourVertexPos (bandProfile s) := by
  refine ⟨bandProfile_pos hs, Or.inr ?_⟩
  by_cases h : s < 2 / 3
  · refine ⟨(5 + (7 - 3 * s)) / 2, by linarith, ?_⟩
    exact (bandProfile_dfv_iff hs).2 (Or.inl ⟨by linarith, by linarith⟩)
  · refine ⟨(11 + (10 + 3 * s)) / 2, by linarith, ?_⟩
    exact (bandProfile_dfv_iff hs).2 (Or.inr ⟨by linarith, by linarith⟩)

/-- A finite, exact obstruction on a path that stays nonconstant and DFV. -/
theorem no_continuous_band_level :
    ¬ ∃ c : ℝ → ℝ, ContinuousOn c (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, DFV (bandProfile s) (c s) := by
  rintro ⟨c, hc, hdfv⟩
  have h0 := (bandProfile_dfv_iff (s := 0) (by norm_num)).1
    (hdfv 0 (by norm_num))
  have h1 := (bandProfile_dfv_iff (s := 1) (by norm_num)).1
    (hdfv 1 (by norm_num))
  norm_num at h0 h1
  have h9 : (9 : ℝ) ∈ Set.Icc (c 0) (c 1) := by
    constructor <;> rcases h0 with h0 | h0 <;>
      rcases h1 with h1 | h1 <;> linarith
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc h9
  have hh := (bandProfile_dfv_iff hs).1 (hdfv s hs)
  rw [heq] at hh
  rcases hh with hh | hh <;> linarith [hs.1]

theorem closed_band_subset {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    closure {c | DFV (bandProfile s) c} ⊆
      Set.Icc (5 : ℝ) 7 ∪ Set.Icc 11 13 := by
  apply closure_minimal _ (isClosed_Icc.union isClosed_Icc)
  intro c hc
  rcases (bandProfile_dfv_iff hs).1 hc with hc | hc
  · exact Or.inl ⟨hc.1.le, by linarith [hs.1]⟩
  · exact Or.inr ⟨hc.1.le, by linarith [hs.2]⟩

theorem closed_band_zero_subset :
    closure {c | DFV (bandProfile 0) c} ⊆ Set.Icc (5 : ℝ) 7 := by
  apply closure_minimal _ isClosed_Icc
  intro c hc
  have hh := (bandProfile_dfv_iff (s := 0) (by norm_num)).1 hc
  norm_num at hh
  rcases hh with hh | hh <;> constructor <;> linarith

theorem closed_band_one_subset :
    closure {c | DFV (bandProfile 1) c} ⊆ Set.Icc (11 : ℝ) 13 := by
  apply closure_minimal _ isClosed_Icc
  intro c hc
  have hh := (bandProfile_dfv_iff (s := 1) (by norm_num)).1 hc
  norm_num at hh
  rcases hh with hh | hh <;> constructor <;> linarith

/-- The obstruction remains valid for closures of the strict level bands;
this is the version needed by the enclosing-circle argument. -/
theorem no_continuous_closed_band_level :
    ¬ ∃ c : ℝ → ℝ, ContinuousOn c (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        c s ∈ closure {t | DFV (bandProfile s) t} := by
  rintro ⟨c, hc, hband⟩
  have h0 := closed_band_zero_subset (hband 0 (by norm_num))
  have h1 := closed_band_one_subset (hband 1 (by norm_num))
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc
    (by norm_num : (0 : ℝ) ≤ 1) hc
    (show (9 : ℝ) ∈ Set.Icc (c 0) (c 1) from
      ⟨by linarith [h0.2], by linarith [h1.1]⟩)
  have hh := closed_band_subset hs (hband s hs)
  rw [heq] at hh
  norm_num at hh

/-- A reusable logical consumer. The geometric invariant and its level
restriction are explicit hypotheses, not presumed producers. -/
theorem no_continuous_realization_of_closed_band_invariant
    {X : Type*} [TopologicalSpace X]
    (Realizes : (ZMod 6 → ℝ) → X → Prop) (invariant : X → ℝ)
    (hcontinuous : Continuous invariant)
    (hlevel : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      Realizes (bandProfile s) x →
      invariant x ∈ closure {c | DFV (bandProfile s) c}) :
    ¬ ∃ p : ℝ → X, ContinuousOn p (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, Realizes (bandProfile s) (p s) := by
  rintro ⟨p, hp, hr⟩
  exact no_continuous_closed_band_level
    ⟨invariant ∘ p, hcontinuous.comp_continuousOn hp,
      fun s hs => hlevel s hs (p s) (hr s hs)⟩

end Gluck.Discrete.GlobalContinuity
