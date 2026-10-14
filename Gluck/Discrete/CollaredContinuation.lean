/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Abstract collared continuation

This file isolates the topological consequence needed by a wall-crossing
continuation argument.  A compact solution set over a connected parameter
space has closed parameter image.  If every boundary solution can be replaced
by an interior solution in the same fiber (the collar hypothesis), and the
interior parameter image is locally open, then one interior base solution
continues to every parameter.

The theorem deliberately takes the collar and local-openness statements as
hypotheses.  In applications, the former is supplied by an exact level-set
curve entering every active wall.  The latter may be supplied either by a
regular interior point or by a nonzero local degree on a transversal.  The
second option is essential when interior Jacobians can be singular: the collar
hypothesis alone does not imply local openness and does not manufacture the
zero-free moving boundary required by a degree argument.
-/

namespace Gluck.Discrete

open Filter Set
open scoped Topology

/-- A surjective strict derivative makes the image of every open neighborhood
of the base point a neighborhood of the image point. -/
theorem strictFDeriv_image_mem_nhds_of_surjective
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {a : E} {U : Set E}
    (hf : HasStrictFDerivAt f f' a) (hsurj : f'.range = ⊤)
    (hU : IsOpen U) (ha : a ∈ U) :
    f '' U ∈ 𝓝 (f a) := by
  let g : F → E := fun z => hf.implicitFunction f f' hsurj z 0
  have hg : Tendsto g (𝓝 (f a)) (𝓝 a) := by
    simpa [g] using hf.tendsto_implicitFunction hsurj tendsto_id tendsto_const_nhds
  have heq : ∀ᶠ z in 𝓝 (f a), f (g z) = z := by
    have hp : Tendsto (fun z : F ↦ (z, (0 : f'.ker)))
        (𝓝 (f a)) (𝓝 (f a, 0)) := tendsto_id.prodMk_nhds tendsto_const_nhds
    simpa [g] using hp.eventually (hf.map_implicitFunction_eq hsurj)
  filter_upwards [hg.eventually (hU.mem_nhds ha), heq] with z hzU hzeq
  exact ⟨g z, hzU, hzeq⟩

/-- On an open set consisting of regular points, a map to a
finite-dimensional space has open image. -/
theorem isOpen_image_of_hasStrictFDerivAt_surjective
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {U : Set E}
    (hU : IsOpen U)
    (hreg : ∀ a ∈ U, ∃ f' : E →L[ℝ] F,
      HasStrictFDerivAt f f' a ∧ f'.range = ⊤) :
    IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨f', hf, hsurj⟩ := hreg a ha
  exact strictFDeriv_image_mem_nhds_of_surjective hf hsurj hU ha

/-- **Closed-image collared continuation.**  This is the purely topological
core.  The closed solution image is unchanged when boundary solutions are
replaced by strict-interior solutions, and is locally open there; hence it is
a nonempty clopen subset of the connected parameter space. -/
theorem closedImage_collared_continuation
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [PreconnectedSpace K]
    {D U : Set X} {π : X → K}
    (hclosed : IsClosed (π '' D)) (hne : D.Nonempty) (hUD : U ⊆ D)
    (hcollar : ∀ x ∈ D, ∃ y ∈ U, π y = π x)
    (hlocal : ∀ x ∈ U, π '' U ∈ 𝓝 (π x)) :
    π '' U = Set.univ := by
  have himage : π '' D = π '' U := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, heq⟩ := hcollar x hx
      exact ⟨y, hy, heq⟩
    · exact Set.image_mono hUD
  have hopen : IsOpen (π '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    exact hlocal x hx
  have hneU : (π '' U).Nonempty := by
    rw [← himage]
    exact hne.image π
  exact IsClopen.eq_univ ⟨himage ▸ hclosed, hopen⟩ hneU

/-- The pointwise-looking collar hypothesis is exactly inclusion of parameter
images.  In particular, it contains no assertion that the replacement is
nearby or lies in the same connected component of a fiber. -/
theorem fiberPurification_iff_image_subset
    {X K : Type*} {D U : Set X} {pi : X → K} :
    (∀ x ∈ D, ∃ y ∈ U, pi y = pi x) ↔ pi '' D ⊆ pi '' U := by
  constructor
  · rintro h k ⟨x, hx, hxk⟩
    obtain ⟨y, hy, heq⟩ := h x hx
    exact ⟨y, hy, heq.trans hxk⟩
  · intro h x hx
    obtain ⟨y, hy, heq⟩ := h ⟨x, hx, rfl⟩
    exact ⟨y, hy, heq⟩

/-- If the strict carrier is contained in the compactified carrier, fiber
purification is equivalent to equality of their parameter images. -/
theorem fiberPurification_iff_image_eq
    {X K : Type*} {D U : Set X} {pi : X → K} (hUD : U ⊆ D) :
    (∀ x ∈ D, ∃ y ∈ U, pi y = pi x) ↔ pi '' D = pi '' U := by
  rw [fiberPurification_iff_image_subset]
  constructor
  · intro h
    exact Set.Subset.antisymm h (Set.image_mono hUD)
  · exact fun h => h.le

/-- Once the strict parameter image is nonempty and locally open, asking that
its frontier already belong to that image is *equivalent* to the desired
surjectivity.  This records the exact limit of a purely topological repair:
compactness and connectedness reduce the geometry to a frontier certificate,
but cannot manufacture that certificate. -/
theorem frontier_subset_iff_eq_univ
    {K : Type*} [TopologicalSpace K] [PreconnectedSpace K]
    {A : Set K} (hne : A.Nonempty) (hlocal : ∀ k ∈ A, A ∈ 𝓝 k) :
    frontier A ⊆ A ↔ A = Set.univ := by
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    exact hlocal
  constructor
  · intro hfrontier
    have hclosed : IsClosed A := by
      rw [← closure_eq_iff_isClosed, closure_eq_self_union_frontier]
      exact Set.union_eq_left.mpr hfrontier
    exact IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  · rintro rfl
    simp

/-- **Frontier-only continuation.**  Full fiber purification is stronger than
the clopen argument needs.  It is enough to purify a compactified solution
whose parameter lies on the frontier of the strict parameter image.  Thus
locked wall points over parameters already in the strict image, and entire
irrelevant branches away from its frontier, need not be controlled.

The local hypothesis is indexed by the parameter image rather than by every
strict solution.  Consequently one selected regular representative or one
selected nonzero local-degree block in each represented fiber suffices. -/
theorem closedImage_frontier_continuation
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [PreconnectedSpace K]
    {D U : Set X} {pi : X → K}
    (hclosed : IsClosed (pi '' D)) (hneU : U.Nonempty) (hUD : U ⊆ D)
    (hfrontier : ∀ k ∈ frontier (pi '' U), k ∈ pi '' D →
      ∃ y ∈ U, pi y = k)
    (hlocal : ∀ k ∈ pi '' U, pi '' U ∈ 𝓝 k) :
    pi '' U = Set.univ := by
  have hopen : IsOpen (pi '' U) := by
    rw [isOpen_iff_mem_nhds]
    exact hlocal
  have hfrontier_subset : frontier (pi '' U) ⊆ pi '' U := by
    intro k hk
    have hkD : k ∈ pi '' D := by
      apply closure_minimal (Set.image_mono hUD) hclosed
      exact frontier_subset_closure hk
    obtain ⟨y, hy, heq⟩ := hfrontier k hk hkD
    exact ⟨y, hy, heq⟩
  have hclosedU : IsClosed (pi '' U) := by
    rw [← closure_eq_iff_isClosed, closure_eq_self_union_frontier]
    exact Set.union_eq_left.mpr hfrontier_subset
  exact IsClopen.eq_univ ⟨hclosedU, hopen⟩ (hneU.image pi)

/-- Compact form of `closedImage_frontier_continuation`. -/
theorem compact_frontier_continuation
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [T2Space K] [PreconnectedSpace K]
    {D U : Set X} {pi : X → K}
    (hD : IsCompact D) (hneU : U.Nonempty) (hUD : U ⊆ D)
    (hpi : ContinuousOn pi D)
    (hfrontier : ∀ k ∈ frontier (pi '' U), k ∈ pi '' D →
      ∃ y ∈ U, pi y = k)
    (hlocal : ∀ k ∈ pi '' U, pi '' U ∈ 𝓝 k) :
    pi '' U = Set.univ := by
  exact closedImage_frontier_continuation
    (hD.image_of_continuousOn hpi).isClosed hneU hUD hfrontier hlocal

/-- Selected-witness form of `compact_frontier_continuation`.  The witness can
carry a regularity or local-degree certificate; no condition is imposed on
the other strict solutions in its fiber. -/
theorem compact_frontier_continuation_of_selected
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [T2Space K] [PreconnectedSpace K]
    {D U : Set X} {pi : X → K}
    (hD : IsCompact D) (hneU : U.Nonempty) (hUD : U ⊆ D)
    (hpi : ContinuousOn pi D)
    (hfrontier : ∀ k ∈ frontier (pi '' U), k ∈ pi '' D →
      ∃ y ∈ U, pi y = k)
    (hselected : ∀ k ∈ pi '' U, ∃ x ∈ U,
      pi x = k ∧ pi '' U ∈ 𝓝 (pi x)) :
    pi '' U = Set.univ := by
  apply compact_frontier_continuation hD hneU hUD hpi hfrontier
  intro k hk
  obtain ⟨x, hx, heq, hlocal⟩ := hselected k hk
  simpa only [heq] using hlocal

/-- Frontier-only continuation from one selected strict submersion in each
represented fiber. -/
theorem compact_frontier_continuation_of_selected_surjective
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {D U : Set E} {f : E → F}
    (hD : IsCompact D) (hneU : U.Nonempty) (hUD : U ⊆ D)
    (hfD : ContinuousOn f D) (hU : IsOpen U)
    (hfrontier : ∀ k ∈ frontier (f '' U), k ∈ f '' D →
      ∃ y ∈ U, f y = k)
    (hselected : ∀ k ∈ f '' U, ∃ x ∈ U, f x = k ∧
      ∃ f' : E →L[ℝ] F, HasStrictFDerivAt f f' x ∧ f'.range = ⊤) :
    f '' U = Set.univ := by
  apply compact_frontier_continuation hD hneU hUD hfD hfrontier
  intro k hk
  obtain ⟨x, hx, hfx, f', hf, hsurj⟩ := hselected k hk
  rw [← hfx]
  exact strictFDeriv_image_mem_nhds_of_surjective hf hsurj hU hx

/-- **Proper selected-branch continuation.**  If the projection of a nonempty
strict selected solution space is proper and its image is locally open, then
it is onto every connected parameter space.  This is the branch-specific
alternative to compactifying by wall solutions: properness is exactly the
assertion that the selected strict branch cannot escape through a wall or at
infinity. -/
theorem proper_selectedBranch_surjective
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [PreconnectedSpace K]
    {pi : X → K}
    (hproper : IsProperMap pi) (hne : Nonempty X)
    (hlocal : ∀ k ∈ Set.range pi, Set.range pi ∈ 𝓝 k) :
    Function.Surjective pi := by
  have hopen : IsOpen (Set.range pi) := by
    rw [isOpen_iff_mem_nhds]
    exact hlocal
  have hneRange : (Set.range pi).Nonempty := by
    exact hne.elim fun x ↦ ⟨pi x, x, rfl⟩
  have hrange : Set.range pi = Set.univ :=
    IsClopen.eq_univ ⟨hproper.isClosed_range, hopen⟩ hneRange
  exact Set.range_eq_univ.mp hrange

/-- Proper selected-branch continuation with local openness supplied by one
strict submersion representative in each represented parameter fiber. -/
theorem proper_selectedBranch_surjective_of_selected_submersion
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F}
    (hproper : IsProperMap f) (hne : Nonempty E)
    (hselected : ∀ k ∈ Set.range f, ∃ x, f x = k ∧
      ∃ f' : E →L[ℝ] F, HasStrictFDerivAt f f' x ∧ f'.range = ⊤) :
    Function.Surjective f := by
  apply proper_selectedBranch_surjective hproper hne
  intro k hk
  obtain ⟨x, hfx, f', hf, hsurj⟩ := hselected k hk
  have himage := strictFDeriv_image_mem_nhds_of_surjective
    hf hsurj isOpen_univ (Set.mem_univ x)
  simpa only [Set.image_univ, hfx] using himage

/-- **Compact collared continuation.**  Let `D` be a compact set of closed
solutions and `U ⊆ D` its strict interior.  If every point of `D` has a
same-parameter representative in `U`, and the parameter image of `U` is
locally open, then one base solution forces an interior solution over every
point of a connected parameter space.

The `hlocal` hypothesis is the exact topological output needed from an
interior submersion theorem: `π '' U` is a neighborhood of `π x` for every
`x ∈ U`.  More generally it can be discharged by a nonzero local
winding/degree certificate, without assuming that every interior zero is
regular. -/
theorem compact_collared_continuation
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [T2Space K] [PreconnectedSpace K]
    {D U : Set X} {π : X → K}
    (hD : IsCompact D) (hne : D.Nonempty) (hUD : U ⊆ D)
    (hπ : ContinuousOn π D)
    (hcollar : ∀ x ∈ D, ∃ y ∈ U, π y = π x)
    (hlocal : ∀ x ∈ U, π '' U ∈ 𝓝 (π x)) :
    π '' U = Set.univ := by
  exact closedImage_collared_continuation
    (hD.image_of_continuousOn hπ).isClosed hne hUD hcollar hlocal

/-- Pointwise form of `compact_collared_continuation`. -/
theorem compact_collared_continuation_surjOn
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [T2Space K] [PreconnectedSpace K]
    {D U : Set X} {π : X → K}
    (hD : IsCompact D) (hne : D.Nonempty) (hUD : U ⊆ D)
    (hπ : ContinuousOn π D)
    (hcollar : ∀ x ∈ D, ∃ y ∈ U, π y = π x)
    (hlocal : ∀ x ∈ U, π '' U ∈ 𝓝 (π x)) :
    Set.SurjOn π U Set.univ := by
  have himage := compact_collared_continuation hD hne hUD hπ hcollar hlocal
  intro k _
  have hk : k ∈ π '' U := by rw [himage]; exact Set.mem_univ k
  exact hk

end Gluck.Discrete
