/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Continuous roots of monotone families

A continuous family of strictly increasing real functions has a continuous root
whenever each function changes sign across a continuously varying bracket.
The parameter space is arbitrary, and continuity in the parameter is only
required at heights strictly inside the bracket.
-/

open Filter Topology

/-- **A parametric strict-mono root selection is continuous.**  If `F x` is strictly
monotone on the moving bracket `[l x, u x]` (endpoints continuous on the parameter set
`S`), `F` is continuous in the parameter slot at every height strictly inside the
bracket, and `ρ` selects for every `x ∈ S` a root of `F x` strictly inside the bracket,
then `ρ` is continuous on `S`.  (Order sandwich: strict monotonicity pins the root
between any two heights at which the signs of `F · y` are locked, and those signs are
open in the parameter.)  Generic input to the nested-IVT anchor existence of ALM-A3;
reused by the A8 turning nest. -/
theorem continuousOn_root_of_strictMonoOn {X : Type*} [TopologicalSpace X]
    {F : X → ℝ → ℝ} {l u ρ : X → ℝ} {S : Set X}
    (hu : ContinuousOn u S) (hl : ContinuousOn l S)
    (hmono : ∀ x ∈ S, StrictMonoOn (F x) (Set.Icc (l x) (u x)))
    (hFc : ∀ x ∈ S, ∀ y ∈ Set.Ioo (l x) (u x), ContinuousWithinAt (fun z ↦ F z y) S x)
    (hmem : ∀ x ∈ S, ρ x ∈ Set.Ioo (l x) (u x))
    (hroot : ∀ x ∈ S, F x (ρ x) = 0) :
    ContinuousOn ρ S := by
  intro x₀ hx₀
  obtain ⟨hl₀, hu₀⟩ := hmem x₀ hx₀
  have key : Filter.Tendsto ρ (nhdsWithin x₀ S) (nhds (ρ x₀)) := by
    rw [tendsto_order]
    constructor
    · intro b hb
      obtain ⟨y₁, hy₁l, hy₁ρ, hy₁b⟩ : ∃ y₁, l x₀ < y₁ ∧ y₁ < ρ x₀ ∧ b ≤ y₁ :=
        ⟨max b ((l x₀ + ρ x₀) / 2), lt_max_iff.mpr (Or.inr (by linarith)),
          max_lt hb (by linarith), le_max_left _ _⟩
      have hy₁u : y₁ < u x₀ := hy₁ρ.trans hu₀
      have hFy₁ : F x₀ y₁ < 0 := by
        have h := hmono x₀ hx₀ ⟨hy₁l.le, hy₁u.le⟩ ⟨hl₀.le, hu₀.le⟩ hy₁ρ
        rwa [hroot x₀ hx₀] at h
      have hev₁ := Filter.Tendsto.eventually_lt_const hFy₁ (hFc x₀ hx₀ y₁ ⟨hy₁l, hy₁u⟩)
      have hev₂ := Filter.Tendsto.eventually_const_lt hy₁u (hu x₀ hx₀)
      filter_upwards [hev₁, hev₂, eventually_mem_nhdsWithin] with x hx₁ hx₂ hxS
      obtain ⟨hρl, hρu⟩ := hmem x hxS
      rcases lt_or_ge y₁ (l x) with hcase | hcase
      · exact hy₁b.trans_lt (hcase.trans hρl)
      · by_contra hcon
        push Not at hcon
        have h := (hmono x hxS).monotoneOn ⟨hρl.le, hρu.le⟩ ⟨hcase, hx₂.le⟩
          (hcon.trans hy₁b)
        rw [hroot x hxS] at h
        exact absurd h (not_le.mpr hx₁)
    · intro b hb
      obtain ⟨y₂, hy₂u, hy₂ρ, hy₂b⟩ : ∃ y₂, y₂ < u x₀ ∧ ρ x₀ < y₂ ∧ y₂ ≤ b :=
        ⟨min b ((ρ x₀ + u x₀) / 2), min_lt_iff.mpr (Or.inr (by linarith)),
          lt_min hb (by linarith), min_le_left _ _⟩
      have hy₂l : l x₀ < y₂ := hl₀.trans hy₂ρ
      have hFy₂ : 0 < F x₀ y₂ := by
        have h := hmono x₀ hx₀ ⟨hl₀.le, hu₀.le⟩ ⟨hy₂l.le, hy₂u.le⟩ hy₂ρ
        rwa [hroot x₀ hx₀] at h
      have hev₁ := Filter.Tendsto.eventually_const_lt hFy₂ (hFc x₀ hx₀ y₂ ⟨hy₂l, hy₂u⟩)
      have hev₂ := Filter.Tendsto.eventually_lt_const hy₂l (hl x₀ hx₀)
      filter_upwards [hev₁, hev₂, eventually_mem_nhdsWithin] with x hx₁ hx₂ hxS
      obtain ⟨hρl, hρu⟩ := hmem x hxS
      rcases lt_or_ge (u x) y₂ with hcase | hcase
      · exact (hρu.trans hcase).trans_le hy₂b
      · by_contra hcon
        push Not at hcon
        have h := (hmono x hxS).monotoneOn ⟨hx₂.le, hcase⟩ ⟨hρl.le, hρu.le⟩
          (hy₂b.trans hcon)
        rw [hroot x hxS] at h
        exact absurd h (not_le.mpr hx₁)
  exact key

/-- **Parametric IVT with continuous root selection** (ticket form
`continuous_root_of_strictMono`).  If on the parameter set `S` the bracket endpoints
`l ≤ u` move continuously, `F x` is continuous and strictly monotone on `[l x, u x]`
with locked endpoint signs `F x (l x) < 0 < F x (u x)`, and `F · y` is continuous on
`S` at each interior height `y`, then some `ρ` continuous on `S` selects the interior
root: `ρ x ∈ (l x, u x)` and `F x (ρ x) = 0`. -/
theorem continuous_root_of_strictMono {X : Type*} [TopologicalSpace X]
    {F : X → ℝ → ℝ} {l u : X → ℝ} {S : Set X}
    (hu : ContinuousOn u S) (hl : ContinuousOn l S) (hle : ∀ x ∈ S, l x ≤ u x)
    (hmono : ∀ x ∈ S, StrictMonoOn (F x) (Set.Icc (l x) (u x)))
    (hFy : ∀ x ∈ S, ContinuousOn (F x) (Set.Icc (l x) (u x)))
    (hFc : ∀ x ∈ S, ∀ y ∈ Set.Ioo (l x) (u x), ContinuousWithinAt (fun z ↦ F z y) S x)
    (hneg : ∀ x ∈ S, F x (l x) < 0) (hpos : ∀ x ∈ S, 0 < F x (u x)) :
    ∃ ρ : X → ℝ, ContinuousOn ρ S ∧
      ∀ x ∈ S, ρ x ∈ Set.Ioo (l x) (u x) ∧ F x (ρ x) = 0 := by
  have hex : ∀ x ∈ S, ∃ y, y ∈ Set.Ioo (l x) (u x) ∧ F x y = 0 := by
    intro x hx
    obtain ⟨y, hy, hy0⟩ :=
      intermediate_value_Ioo (hle x hx) (hFy x hx) ⟨hneg x hx, hpos x hx⟩
    exact ⟨y, hy, hy0⟩
  choose! ρ hρ₁ hρ₂ using hex
  exact ⟨ρ, continuousOn_root_of_strictMonoOn hu hl hmono hFc hρ₁ hρ₂,
    fun x hx ↦ ⟨hρ₁ x hx, hρ₂ x hx⟩⟩

