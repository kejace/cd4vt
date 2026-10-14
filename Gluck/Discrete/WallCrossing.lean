/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Regular level sets cross transverse walls

This file records the local analytic fact needed at a regular moderate-wall
solution.  If the derivative of a constraint map is surjective and a tangent
vector in its kernel points strictly through a scalar wall, the exact level set
contains a differentiable curve entering the positive side of that wall.

The result uses Mathlib's finite-dimensional implicit-function theorem.  It is
independent of the particular closing coordinates and can therefore be reused
for both the angle--length and split-angle charts.
-/

namespace Gluck.Discrete

open Filter Set
open scoped Topology

/-- The active-wall cone condition on one fixed profile fiber.

`Z` is the closed solution fiber for a single prescribed profile, `f' x` is
the derivative of its equality constraints, `w' x i` is the derivative of
wall slack `i`, and `active x` records the walls vanishing at `x`.  The margin
`μ` is chosen only after `Z` has been fixed; this definition deliberately does
not assert a margin uniform over a family of profiles. -/
def HasFixedProfileActiveWallCone
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : Set E) (f' : E → E →L[ℝ] F)
    (w' : E → ι → E →L[ℝ] ℝ) (active : E → Set ι) : Prop :=
  ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ Z, (active x).Nonempty →
    (f' x).range = ⊤ ∧ ∃ v : E,
      ‖v‖ = 1 ∧ v ∈ (f' x).ker ∧ ∀ i ∈ active x, μ ≤ w' x i v

/-- The active-wall cone condition over a family of profiles, with the
quantifiers in the required order `∀ κ, ∃ μκ > 0`.  In particular this
does **not** assert one positive margin uniform over the whole profile set;
the margins may tend to zero as profiles approach a constant one. -/
def HasPerProfileActiveWallCone
    {ι P E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set P) (Z : P → Set E) (f' : P → E → E →L[ℝ] F)
    (w' : P → E → ι → E →L[ℝ] ℝ)
    (active : P → E → Set ι) : Prop :=
  ∀ κ ∈ K, HasFixedProfileActiveWallCone (Z κ) (f' κ) (w' κ) (active κ)

/-- Fully expanded per-profile quantifier order.  The margin is selected after
`κ`; this is intentionally `∀ κ, ∃ μκ`, not `∃ μ, ∀ κ`. -/
theorem hasPerProfileActiveWallCone_iff
    {ι P E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set P) (Z : P → Set E) (f' : P → E → E →L[ℝ] F)
    (w' : P → E → ι → E →L[ℝ] ℝ)
    (active : P → E → Set ι) :
    HasPerProfileActiveWallCone K Z f' w' active ↔
      ∀ κ ∈ K, ∃ μ : ℝ, 0 < μ ∧
        ∀ x ∈ Z κ, (active κ x).Nonempty →
          (f' κ x).range = ⊤ ∧ ∃ v : E,
            ‖v‖ = 1 ∧ v ∈ (f' κ x).ker ∧
              ∀ i ∈ active κ x, μ ≤ w' κ x i v :=
  Iff.rfl

/-- Pointwise cone margins on a finite fixed-profile wall fiber have one
positive common lower bound.  This is the finite-fiber packaging used by the
four-point wall calculation: algebraic transversality supplies the pointwise
data, while finiteness of the wall fiber supplies the per-profile margin. -/
theorem hasFixedProfileActiveWallCone_of_finite
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Finite ι]
    (Z : Set E) (f' : E → E →L[ℝ] F)
    (w' : E → ι → E →L[ℝ] ℝ) (active : E → Set ι)
    (hZ : Z.Finite)
    (hpoint : ∀ x ∈ Z, (active x).Nonempty →
      ∃ μ : ℝ, 0 < μ ∧ (f' x).range = ⊤ ∧ ∃ v : E,
        ‖v‖ = 1 ∧ v ∈ (f' x).ker ∧ ∀ i ∈ active x, μ ≤ w' x i v) :
    HasFixedProfileActiveWallCone Z f' w' active := by
  classical
  let S : Set E := {x | x ∈ Z ∧ (active x).Nonempty}
  have hSfinite : S.Finite := hZ.subset fun x hx ↦ hx.1
  by_cases hS : S.Nonempty
  · haveI : Finite S := hSfinite.to_subtype
    haveI : Nonempty S := hS.to_subtype
    have hdata : ∀ x : S, ∃ μ : ℝ,
        0 < μ ∧ (f' x).range = ⊤ ∧ ∃ v : E,
          ‖v‖ = 1 ∧ v ∈ (f' x).ker ∧ ∀ i ∈ active x, μ ≤ w' x i v :=
      fun x ↦ hpoint x x.property.1 x.property.2
    choose margin hmargin using hdata
    obtain ⟨x₀, hx₀⟩ := Finite.exists_min margin
    refine ⟨margin x₀, (hmargin x₀).1, ?_⟩
    intro x hx hactive
    let xs : S := ⟨x, hx, hactive⟩
    obtain ⟨_, hrange, v, hvnorm, hvker, hvwall⟩ := hmargin xs
    refine ⟨hrange, v, hvnorm, hvker, fun i hi ↦ ?_⟩
    exact (hx₀ xs).trans (hvwall i hi)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx hactive
    exact (hS ⟨x, hx, hactive⟩).elim

/-- On a finite fixed-profile wall fiber with finitely many wall labels,
pointwise strict inward vectors imply the quantitative active-wall cone. -/
theorem hasFixedProfileActiveWallCone_of_finite_of_pointwise
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Finite ι]
    (Z : Set E) (f' : E → E →L[ℝ] F)
    (w' : E → ι → E →L[ℝ] ℝ) (active : E → Set ι)
    (hZ : Z.Finite)
    (hpoint : ∀ x ∈ Z, (active x).Nonempty →
      (f' x).range = ⊤ ∧ ∃ v : E,
        ‖v‖ = 1 ∧ v ∈ (f' x).ker ∧ ∀ i ∈ active x, 0 < w' x i v) :
    HasFixedProfileActiveWallCone Z f' w' active := by
  apply hasFixedProfileActiveWallCone_of_finite Z f' w' active hZ
  intro x hx hactive
  obtain ⟨hrange, v, hvnorm, hvker, hvwall⟩ := hpoint x hx hactive
  have hAfin : Set.Finite (active x) := Set.toFinite _
  obtain ⟨i₀, hi₀, hmin⟩ :=
    Set.exists_min_image (active x) (fun i ↦ w' x i v) hAfin hactive
  exact ⟨w' x i₀ v, hvwall i₀ hi₀, hrange, v, hvnorm, hvker, hmin⟩

/-! ## The finite wall-count reduction -/

/-- If more than four positive split-angle coordinates have total `2π`, then
fewer than four of them can be at least `π / 2`.  Applied to the `2n` split
angles of a positive moderate development (`n ≥ 4`), this says that a boundary
zero has at most three active wall incidences.

The strict positivity of every split is important: four half-right incidences
already contribute `2π`, while any remaining split contributes strictly more. -/
theorem activeWall_card_lt_four_of_positive_total_two_pi
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (active : Finset ι)
    (hι : 4 < Fintype.card ι)
    (hx : ∀ i, 0 < x i)
    (hsum : ∑ i, x i = 2 * Real.pi)
    (hactive : ∀ i ∈ active, Real.pi / 2 ≤ x i) :
    active.card < 4 := by
  classical
  by_contra hcard
  have hfour : 4 ≤ active.card := Nat.le_of_not_gt hcard
  obtain ⟨walls, hwalls, hwalls_card⟩ := active.exists_subset_card_eq hfour
  have hwalls_ne : walls ≠ Finset.univ := by
    intro heq
    have := congrArg Finset.card heq
    simp only [Finset.card_univ, hwalls_card] at this
    omega
  have houtside : ∃ i : ι, i ∉ walls := by
    by_contra h
    apply hwalls_ne
    ext i
    have hi : i ∈ walls := by
      by_contra hi
      exact h ⟨i, hi⟩
    simp [hi]
  obtain ⟨i, hi⟩ := houtside
  have hwalls_lt : (∑ j ∈ walls, x j) < ∑ j, x j := by
    exact Finset.sum_lt_sum_of_subset (Finset.subset_univ walls)
      (Finset.mem_univ i) hi (hx i) (fun j _ _ => (hx j).le)
  have hwalls_lower : 2 * Real.pi ≤ ∑ j ∈ walls, x j := by
    calc
      2 * Real.pi = ∑ _j ∈ walls, Real.pi / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, hwalls_card]
        ring
      _ ≤ ∑ j ∈ walls, x j := by
        gcongr with j hj
        exact hactive j (hwalls hj)
  rw [hsum] at hwalls_lt
  exact (not_lt_of_ge hwalls_lower) hwalls_lt

/-- A regular zero of `f` enters the positive side of every wall whose
derivative is positive on some tangent vector to the level set.

The returned curve remains on the exact level `f = f a`, has initial velocity
`v`, and lies strictly beyond the wall for every sufficiently small positive
parameter. -/
theorem regularWallZero_entersInterior
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {a v : E}
    {w : E → ℝ} {w' : E →L[ℝ] ℝ}
    (hf : HasStrictFDerivAt f f' a)
    (hsurj : f'.range = ⊤)
    (hv : v ∈ f'.ker)
    (hw : HasFDerivAt w w' a)
    (hpos : 0 < w' v) :
    ∃ (γ : ℝ → E) (ε : ℝ),
      0 < ε ∧
      γ 0 = a ∧
      HasDerivAt γ v 0 ∧
      Tendsto γ (𝓝 0) (𝓝 a) ∧
      ∀ t, 0 < t → t < ε →
        f (γ t) = f a ∧ w a < w (γ t) := by
  let q : f'.ker := ⟨v, hv⟩
  let γ : ℝ → E := fun t =>
    hf.implicitFunction f f' hsurj (f a) (t • q)
  have hγ0 : γ 0 = a := by
    simp [γ, hf.implicitFunction_apply_image hsurj]
  have hq_deriv : HasStrictDerivAt (fun t : ℝ => t • q) q 0 := by
    simpa using ((hasStrictDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const q)
  have hq_tendsto : Tendsto (fun t : ℝ => t • q) (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, zero_smul] using hq_deriv.hasDerivAt.continuousAt
  have hγ_tendsto : Tendsto γ (𝓝 0) (𝓝 a) := by
    simpa [γ] using
      (hf.tendsto_implicitFunction hsurj
        (g₁ := fun _ : ℝ => f a) (g₂ := fun t : ℝ => t • q)
        tendsto_const_nhds hq_tendsto)
  have hγ_deriv : HasDerivAt γ v 0 := by
    simpa [γ, q, Function.comp_def] using
      ((hf.to_implicitFunction hsurj).comp_hasStrictDerivAt_of_eq 0 hq_deriv (by simp)).hasDerivAt
  have hlevel : ∀ᶠ t : ℝ in 𝓝 0, f (γ t) = f a := by
    have hp : Tendsto (fun t : ℝ => (f a, t • q)) (𝓝 0) (𝓝 (f a, 0)) :=
      tendsto_const_nhds.prodMk_nhds hq_tendsto
    simpa [γ] using hp.eventually (hf.map_implicitFunction_eq hsurj)
  have hwall : HasDerivAt (fun t : ℝ => w (γ t)) (w' v) 0 := by
    simpa [Function.comp_def] using
      hw.comp_hasDerivAt_of_eq 0 hγ_deriv hγ0.symm
  have hslope :
      Tendsto (fun t : ℝ => t⁻¹ * (w (γ t) - w (γ 0)))
        (𝓝[>] (0 : ℝ)) (𝓝 (w' v)) := by
    simpa [smul_eq_mul] using hwall.tendsto_slope_zero_right
  have hgood :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), f (γ t) = f a ∧ w a < w (γ t) := by
    filter_upwards [hlevel.filter_mono nhdsWithin_le_nhds,
      hslope.eventually_const_lt hpos, self_mem_nhdsWithin] with t hft hs ht
    refine ⟨hft, ?_⟩
    have hinv : 0 < t⁻¹ := inv_pos.mpr ht
    have hdiff : 0 < w (γ t) - w (γ 0) :=
      pos_of_mul_pos_right hs hinv.le
    rw [hγ0] at hdiff
    exact sub_pos.mp hdiff
  obtain ⟨ε, hε, hεsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  refine ⟨γ, ε, hε, hγ0, hγ_deriv, hγ_tendsto, ?_⟩
  intro t ht0 htε
  exact hεsub ⟨ht0, htε⟩

/-- Simultaneous version of `regularWallZero_entersInterior` for a finite active
set of walls. A single tangent vector which is strictly inward for every active
wall integrates to one exact level-set curve entering all of them at once. -/
theorem regularWallZero_entersAllInteriors
    {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {a v : E}
    {w : ι → E → ℝ} {w' : ι → E →L[ℝ] ℝ}
    (hf : HasStrictFDerivAt f f' a)
    (hsurj : f'.range = ⊤)
    (hv : v ∈ f'.ker)
    (hw : ∀ i, HasFDerivAt (w i) (w' i) a)
    (hpos : ∀ i, 0 < w' i v) :
    ∃ (γ : ℝ → E) (ε : ℝ),
      0 < ε ∧
      γ 0 = a ∧
      HasDerivAt γ v 0 ∧
      Tendsto γ (𝓝 0) (𝓝 a) ∧
      ∀ t, 0 < t → t < ε →
        f (γ t) = f a ∧ ∀ i, w i a < w i (γ t) := by
  let q : f'.ker := ⟨v, hv⟩
  let γ : ℝ → E := fun t =>
    hf.implicitFunction f f' hsurj (f a) (t • q)
  have hγ0 : γ 0 = a := by
    simp [γ, hf.implicitFunction_apply_image hsurj]
  have hq_deriv : HasStrictDerivAt (fun t : ℝ => t • q) q 0 := by
    simpa using ((hasStrictDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const q)
  have hq_tendsto : Tendsto (fun t : ℝ => t • q) (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, zero_smul] using hq_deriv.hasDerivAt.continuousAt
  have hγ_tendsto : Tendsto γ (𝓝 0) (𝓝 a) := by
    simpa [γ] using
      (hf.tendsto_implicitFunction hsurj
        (g₁ := fun _ : ℝ => f a) (g₂ := fun t : ℝ => t • q)
        tendsto_const_nhds hq_tendsto)
  have hγ_deriv : HasDerivAt γ v 0 := by
    simpa [γ, q, Function.comp_def] using
      ((hf.to_implicitFunction hsurj).comp_hasStrictDerivAt_of_eq 0 hq_deriv (by simp)).hasDerivAt
  have hlevel : ∀ᶠ t : ℝ in 𝓝 0, f (γ t) = f a := by
    have hp : Tendsto (fun t : ℝ => (f a, t • q)) (𝓝 0) (𝓝 (f a, 0)) :=
      tendsto_const_nhds.prodMk_nhds hq_tendsto
    simpa [γ] using hp.eventually (hf.map_implicitFunction_eq hsurj)
  have hwall : ∀ i, HasDerivAt (fun t : ℝ => w i (γ t)) (w' i v) 0 := by
    intro i
    simpa [Function.comp_def] using
      (hw i).comp_hasDerivAt_of_eq 0 hγ_deriv hγ0.symm
  have hwall_good : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), w i a < w i (γ t) := by
    intro i
    have hslope :
        Tendsto (fun t : ℝ => t⁻¹ * (w i (γ t) - w i (γ 0)))
          (𝓝[>] (0 : ℝ)) (𝓝 (w' i v)) := by
      simpa [smul_eq_mul] using (hwall i).tendsto_slope_zero_right
    filter_upwards [hslope.eventually_const_lt (hpos i), self_mem_nhdsWithin]
      with t hs ht
    have hinv : 0 < t⁻¹ := inv_pos.mpr ht
    have hdiff : 0 < w i (γ t) - w i (γ 0) :=
      pos_of_mul_pos_right hs hinv.le
    rw [hγ0] at hdiff
    exact sub_pos.mp hdiff
  have hgood :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), f (γ t) = f a ∧ ∀ i, w i a < w i (γ t) := by
    filter_upwards [hlevel.filter_mono nhdsWithin_le_nhds,
      Filter.eventually_all.2 hwall_good] with t hft hwt
    exact ⟨hft, hwt⟩
  obtain ⟨ε, hε, hεsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  refine ⟨γ, ε, hε, hγ0, hγ_deriv, hγ_tendsto, ?_⟩
  intro t ht0 htε
  exact hεsub ⟨ht0, htε⟩

/-- **Active-wall purification.**  At a point of a closed inequality domain,
the common inward-vector hypothesis is needed only for the walls which are
actually active.  Along the exact level-set curve supplied by the implicit
function theorem, active slacks become positive by their derivative signs;
the finitely many inactive slacks remain positive by continuity.

This is the local consumer of `HasFixedProfileActiveWallCone`.  In a geometric
application the index type should contain every boundary inequality (moderate
walls, edge-collapse faces, and angle faces), while the margin in the cone
hypothesis is chosen after fixing the profile fiber. -/
theorem regularActiveWallZero_entersStrictDomain
    {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {a v : E}
    {w : ι → E → ℝ} {w' : ι → E →L[ℝ] ℝ}
    (hf : HasStrictFDerivAt f f' a)
    (hsurj : f'.range = ⊤)
    (hv : v ∈ f'.ker)
    (hw : ∀ i, HasFDerivAt (w i) (w' i) a)
    (hclosed : ∀ i, 0 ≤ w i a)
    (hinward : ∀ i, w i a = 0 → 0 < w' i v) :
    ∃ (γ : ℝ → E) (ε : ℝ),
      0 < ε ∧
      γ 0 = a ∧
      HasDerivAt γ v 0 ∧
      Tendsto γ (𝓝 0) (𝓝 a) ∧
      ∀ t, 0 < t → t < ε →
        f (γ t) = f a ∧ ∀ i, 0 < w i (γ t) := by
  let q : f'.ker := ⟨v, hv⟩
  let γ : ℝ → E := fun t =>
    hf.implicitFunction f f' hsurj (f a) (t • q)
  have hγ0 : γ 0 = a := by
    simp [γ, hf.implicitFunction_apply_image hsurj]
  have hq_deriv : HasStrictDerivAt (fun t : ℝ => t • q) q 0 := by
    simpa using ((hasStrictDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const q)
  have hq_tendsto : Tendsto (fun t : ℝ => t • q) (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, zero_smul] using hq_deriv.hasDerivAt.continuousAt
  have hγ_tendsto : Tendsto γ (𝓝 0) (𝓝 a) := by
    simpa [γ] using
      (hf.tendsto_implicitFunction hsurj
        (g₁ := fun _ : ℝ => f a) (g₂ := fun t : ℝ => t • q)
        tendsto_const_nhds hq_tendsto)
  have hγ_deriv : HasDerivAt γ v 0 := by
    simpa [γ, q, Function.comp_def] using
      ((hf.to_implicitFunction hsurj).comp_hasStrictDerivAt_of_eq 0 hq_deriv (by simp)).hasDerivAt
  have hlevel : ∀ᶠ t : ℝ in 𝓝 0, f (γ t) = f a := by
    have hp : Tendsto (fun t : ℝ => (f a, t • q)) (𝓝 0) (𝓝 (f a, 0)) :=
      tendsto_const_nhds.prodMk_nhds hq_tendsto
    simpa [γ] using hp.eventually (hf.map_implicitFunction_eq hsurj)
  have hstrict : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < w i (γ t) := by
    intro i
    rcases eq_or_ne (w i a) 0 with hactive | hinactive
    · have hwall : HasDerivAt (fun t : ℝ => w i (γ t)) (w' i v) 0 := by
        simpa [Function.comp_def] using
          (hw i).comp_hasDerivAt_of_eq 0 hγ_deriv hγ0.symm
      have hslope :
          Tendsto (fun t : ℝ => t⁻¹ * (w i (γ t) - w i (γ 0)))
            (𝓝[>] (0 : ℝ)) (𝓝 (w' i v)) := by
        simpa [smul_eq_mul] using hwall.tendsto_slope_zero_right
      filter_upwards [hslope.eventually_const_lt (hinward i hactive),
        self_mem_nhdsWithin] with t hs ht
      have hinv : 0 < t⁻¹ := inv_pos.mpr ht
      have hdiff : 0 < w i (γ t) - w i (γ 0) :=
        pos_of_mul_pos_right hs hinv.le
      rw [hγ0, hactive] at hdiff
      simpa using hdiff
    · have hbase : 0 < w i a := lt_of_le_of_ne (hclosed i) (Ne.symm hinactive)
      have hcont : Tendsto (fun t : ℝ => w i (γ t)) (𝓝 0) (𝓝 (w i a)) := by
        have hwcont : ContinuousAt (w i) a := (hw i).continuousAt
        simpa [Function.comp_def] using hwcont.tendsto.comp hγ_tendsto
      exact (hcont.eventually_const_lt hbase).filter_mono nhdsWithin_le_nhds
  have hgood :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), f (γ t) = f a ∧ ∀ i, 0 < w i (γ t) := by
    filter_upwards [hlevel.filter_mono nhdsWithin_le_nhds,
      Filter.eventually_all.2 hstrict] with t hft hwt
    exact ⟨hft, hwt⟩
  obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  refine ⟨γ, ε, hε, hγ0, hγ_deriv, hγ_tendsto, ?_⟩
  intro t ht0 htε
  exact hεsub ⟨ht0, htε⟩

/-- Pointwise collar form of `regularActiveWallZero_entersStrictDomain`: the
closed-domain point has a strict-domain representative on the same equality
fiber. -/
theorem regularActiveWallZero_hasStrictRepresentative
    {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {a v : E}
    {w : ι → E → ℝ} {w' : ι → E →L[ℝ] ℝ}
    (hf : HasStrictFDerivAt f f' a)
    (hsurj : f'.range = ⊤)
    (hv : v ∈ f'.ker)
    (hw : ∀ i, HasFDerivAt (w i) (w' i) a)
    (hclosed : ∀ i, 0 ≤ w i a)
    (hinward : ∀ i, w i a = 0 → 0 < w' i v) :
    ∃ y : E, f y = f a ∧ ∀ i, 0 < w i y := by
  obtain ⟨γ, ε, hε, -, -, -, hγ⟩ :=
    regularActiveWallZero_entersStrictDomain
      hf hsurj hv hw hclosed hinward
  have hhalf_pos : 0 < ε / 2 := by positivity
  have hhalf_lt : ε / 2 < ε := by linarith
  exact ⟨γ (ε / 2), hγ (ε / 2) hhalf_pos hhalf_lt⟩

/-- A pointwise active-wall cone certificate supplies exactly the collar
conclusion used by global continuation.  If no wall is active, the original
point is already strict; otherwise the certificate is integrated by
`regularActiveWallZero_hasStrictRepresentative`. -/
theorem activeWallRegularity_hasStrictRepresentative
    {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {w : ι → E → ℝ} {a : E}
    (hclosed : ∀ i, 0 ≤ w i a)
    (hregular : (∃ i, w i a = 0) →
      ∃ (f' : E →L[ℝ] F) (v : E) (w' : ι → E →L[ℝ] ℝ),
        HasStrictFDerivAt f f' a ∧
        f'.range = ⊤ ∧
        v ∈ f'.ker ∧
        (∀ i, HasFDerivAt (w i) (w' i) a) ∧
        ∀ i, w i a = 0 → 0 < w' i v) :
    ∃ y : E, f y = f a ∧ ∀ i, 0 < w i y := by
  by_cases hactive : ∃ i, w i a = 0
  · obtain ⟨f', v, w', hf, hsurj, hv, hw, hinward⟩ := hregular hactive
    exact regularActiveWallZero_hasStrictRepresentative
      hf hsurj hv hw hclosed hinward
  · refine ⟨a, rfl, fun i => ?_⟩
    exact lt_of_le_of_ne (hclosed i) (Ne.symm (not_exists.mp hactive i))

/-! ## Mixed double-wall cofactors

For a four-gap carrier whose ordered endpoint pairs are independent, the
ordinary quadrilateral assertion that every genuine two-wall corner points
inward is false.  In local coordinates `(t,s,u)`, where `s,u` are the two
inward wall slacks, write the complex derivative columns as `A,B,C`.  The
two wall-face Jacobians are

`Jₛ = [A,C]` and `Jᵤ = [A,B]`.

The cofactor kernel has slack components `(-Jₛ,Jᵤ)`.  Thus opposite signs of
the face Jacobians give an inward zero curve, equal signs give an
index-transfer corner, and a zero product is the singular/tangency residue.
The results below formalize both regular alternatives independently of the
particular closure chart.
-/

noncomputable section

/-- Oriented area of two complex columns. -/
def mixedWallBracket (z w : ℂ) : ℝ :=
  z.re * w.im - z.im * w.re

/-- The cofactor relation for a real `2 × 3` matrix written as three
complex columns. -/
theorem mixedWall_cofactor_identity (A B C : ℂ) :
    (mixedWallBracket B C) • A +
        (mixedWallBracket C A) • B +
      (mixedWallBracket A B) • C = 0 := by
  apply Complex.ext <;>
    simp [mixedWallBracket] <;>
    ring

/-- A three-coordinate vector in the local double-wall chart. -/
def mixedWallVector (t s u : ℝ) : Fin 3 → ℝ := ![t, s, u]

/-- The first wall face `s = 0`, as a continuous linear embedding of its
oriented `(t,u)` coordinates into the three-coordinate wall chart. -/
noncomputable def mixedWallFirstFaceEmbedding :
    (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (mixedWallVector 1 0 0) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (mixedWallVector 0 0 1)

@[simp] theorem mixedWallFirstFaceEmbedding_apply (w : ℝ × ℝ) :
    mixedWallFirstFaceEmbedding w = mixedWallVector w.1 0 w.2 := by
  funext i
  fin_cases i <;> simp [mixedWallFirstFaceEmbedding, mixedWallVector]

@[simp] theorem mixedWallVector_zero (t s u : ℝ) :
    mixedWallVector t s u 0 = t := rfl

@[simp] theorem mixedWallVector_one (t s u : ℝ) :
    mixedWallVector t s u 1 = s := rfl

@[simp] theorem mixedWallVector_two (t s u : ℝ) :
    mixedWallVector t s u 2 = u := rfl

/-- The three complex columns of a linearized closure map. -/
def mixedWallColumn (D : (Fin 3 → ℝ) →L[ℝ] ℂ) (j : Fin 3) : ℂ :=
  D (mixedWallVector (if j = 0 then 1 else 0)
    (if j = 1 then 1 else 0) (if j = 2 then 1 else 0))

@[simp] theorem mixedWallColumn_zero (D : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    mixedWallColumn D 0 = D (mixedWallVector 1 0 0) := by
  simp [mixedWallColumn]

@[simp] theorem mixedWallColumn_one (D : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    mixedWallColumn D 1 = D (mixedWallVector 0 1 0) := by
  simp [mixedWallColumn]

@[simp] theorem mixedWallColumn_two (D : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    mixedWallColumn D 2 = D (mixedWallVector 0 0 1) := by
  simp [mixedWallColumn]

theorem mixedWallVector_decompose (t s u : ℝ) :
    mixedWallVector t s u =
      t • mixedWallVector 1 0 0 +
        s • mixedWallVector 0 1 0 +
          u • mixedWallVector 0 0 1 := by
  funext i
  fin_cases i <;> simp

theorem map_mixedWallVector
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) (t s u : ℝ) :
    D (mixedWallVector t s u) =
      t • mixedWallColumn D 0 + s • mixedWallColumn D 1 +
        u • mixedWallColumn D 2 := by
  rw [mixedWallVector_decompose, map_add, map_add, map_smul, map_smul,
    map_smul, mixedWallColumn_zero, mixedWallColumn_one, mixedWallColumn_two]

/-- The kernel cofactor of a three-column closure derivative. -/
def mixedWallCofactorVector
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) : Fin 3 → ℝ :=
  mixedWallVector
    (mixedWallBracket (mixedWallColumn D 1) (mixedWallColumn D 2))
    (mixedWallBracket (mixedWallColumn D 2) (mixedWallColumn D 0))
    (mixedWallBracket (mixedWallColumn D 0) (mixedWallColumn D 1))

theorem mixedWallCofactorVector_mem_ker
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    mixedWallCofactorVector D ∈ D.ker := by
  rw [LinearMap.mem_ker]
  change D (mixedWallVector
    (mixedWallBracket (mixedWallColumn D 1) (mixedWallColumn D 2))
    (mixedWallBracket (mixedWallColumn D 2) (mixedWallColumn D 0))
    (mixedWallBracket (mixedWallColumn D 0) (mixedWallColumn D 1))) = 0
  rw [map_mixedWallVector]
  exact mixedWall_cofactor_identity _ _ _

/-- Jacobian on the first wall face (`s = 0`), in coordinates `(t,u)`. -/
def mixedWallFirstFaceJacobian
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) : ℝ :=
  mixedWallBracket (mixedWallColumn D 0) (mixedWallColumn D 2)

/-- Jacobian on the second wall face (`u = 0`), in coordinates `(t,s)`. -/
def mixedWallSecondFaceJacobian
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) : ℝ :=
  mixedWallBracket (mixedWallColumn D 0) (mixedWallColumn D 1)

/-- A kernel vector which crosses the first wall coordinate while remaining
tangent to the second forces the second restricted face Jacobian to vanish.
This is the coordinate-free algebra used when a physical zero curve is
known before its mixed-wall cofactor is identified. -/
theorem mixedWallSecondFaceJacobian_eq_zero_of_kernel
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) (v : Fin 3 → ℝ)
    (hker : D v = 0) (hone : v 1 ≠ 0) (htwo : v 2 = 0) :
    mixedWallSecondFaceJacobian D = 0 := by
  have hv : v = mixedWallVector (v 0) (v 1) (v 2) := by
    funext i
    fin_cases i <;> rfl
  rw [hv, map_mixedWallVector, htwo] at hker
  simp only [zero_smul, add_zero] at hker
  have hre := congrArg Complex.re hker
  have him := congrArg Complex.im hker
  simp only [Complex.add_re, Complex.smul_re, Complex.zero_re,
    smul_eq_mul] at hre
  simp only [Complex.add_im, Complex.smul_im, Complex.zero_im,
    smul_eq_mul] at him
  have hproduct : v 1 * mixedWallSecondFaceJacobian D = 0 := by
    unfold mixedWallSecondFaceJacobian mixedWallBracket
    linear_combination (mixedWallColumn D 0).re * him -
      (mixedWallColumn D 0).im * hre
  exact (mul_eq_zero.mp hproduct).resolve_left hone

/-- Evaluation of the first two-column face determinant is continuous in the
ambient derivative.  This is the small openness fact used to retain regularity
after an inward wall-opening curve leaves a multiple corner. -/
theorem continuous_mixedWallFirstFaceJacobian :
    Continuous (mixedWallFirstFaceJacobian :
      ((Fin 3 → ℝ) →L[ℝ] ℂ) → ℝ) := by
  unfold mixedWallFirstFaceJacobian mixedWallBracket mixedWallColumn
  fun_prop

theorem mixedWallCofactorVector_firstSlack
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    mixedWallCofactorVector D 1 = -mixedWallFirstFaceJacobian D := by
  simp [mixedWallCofactorVector, mixedWallFirstFaceJacobian,
    mixedWallBracket]
  ring

theorem mixedWallCofactorVector_secondSlack
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    mixedWallCofactorVector D 2 = mixedWallSecondFaceJacobian D := by
  rfl

private theorem exists_sign_mul_pos_of_mul_pos
    {x y : ℝ} (hxy : 0 < x * y) :
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      0 < sigma * x ∧ 0 < sigma * y := by
  rcases (mul_pos_iff.mp hxy) with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨1, Or.inl rfl, by simpa, by simpa⟩
  · exact ⟨-1, Or.inr rfl, by simpa, by simpa⟩

/-- At an inward regular double wall, one orientation of the cofactor kernel
has both wall-slack coordinates positive. -/
theorem exists_oriented_mixedWallCofactorVector
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (hinward : mixedWallFirstFaceJacobian D *
      mixedWallSecondFaceJacobian D < 0) :
    ∃ v : Fin 3 → ℝ, v ∈ D.ker ∧ 0 < v 1 ∧ 0 < v 2 := by
  let c := mixedWallCofactorVector D
  have hprod : 0 < c 1 * c 2 := by
    change 0 < mixedWallCofactorVector D 1 *
      mixedWallCofactorVector D 2
    rw [mixedWallCofactorVector_firstSlack,
      mixedWallCofactorVector_secondSlack]
    nlinarith
  obtain ⟨sigma, _hsigma, hs, hu⟩ :=
    exists_sign_mul_pos_of_mul_pos hprod
  refine ⟨sigma • c, ?_, ?_, ?_⟩
  · exact D.ker.smul_mem sigma (mixedWallCofactorVector_mem_ker D)
  · simpa [Pi.smul_apply, smul_eq_mul] using hs
  · simpa [Pi.smul_apply, smul_eq_mul] using hu

/-- A nonzero Jacobian on the first wall face already makes the full
three-coordinate closure derivative surjective. -/
theorem mixedWallDerivative_range_eq_top_of_firstFaceJacobian_ne
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (hJ : mixedWallFirstFaceJacobian D ≠ 0) : D.range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro z
  let A := mixedWallColumn D 0
  let C := mixedWallColumn D 2
  let J := mixedWallFirstFaceJacobian D
  let t := (z.re * C.im - z.im * C.re) / J
  let u := (A.re * z.im - A.im * z.re) / J
  refine ⟨mixedWallVector t 0 u, ?_⟩
  change D (mixedWallVector t 0 u) = z
  rw [map_mixedWallVector]
  simp only [zero_smul, add_zero]
  have hJ' : J ≠ 0 := by simpa [J] using hJ
  have hJdef : J = A.re * C.im - A.im * C.re := by
    rfl
  apply Complex.ext
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    change t * A.re + u * C.re = z.re
    dsimp only [t, u]
    field_simp [hJ']
    rw [hJdef]
    ring
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    change t * A.im + u * C.im = z.im
    dsimp only [t, u]
    field_simp [hJ']
    rw [hJdef]
    ring

/-- At a transfer corner the cofactor line has opposite wall-slack signs in
both orientations, so this local zero curve cannot purify the corner. -/
theorem no_oriented_mixedWallCofactorVector_of_transfer
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (htransfer : 0 < mixedWallFirstFaceJacobian D *
      mixedWallSecondFaceJacobian D) (sigma : ℝ) :
    ¬(0 < (sigma • mixedWallCofactorVector D) 1 ∧
      0 < (sigma • mixedWallCofactorVector D) 2) := by
  intro hpos
  have hcofactor : mixedWallCofactorVector D 1 *
      mixedWallCofactorVector D 2 < 0 := by
    rw [mixedWallCofactorVector_firstSlack,
      mixedWallCofactorVector_secondSlack]
    nlinarith
  have hscaled : 0 <
      (sigma * mixedWallCofactorVector D 1) *
        (sigma * mixedWallCofactorVector D 2) :=
    mul_pos hpos.1 hpos.2
  have hsquare := sq_nonneg sigma
  nlinarith

/-- The two boundary-oriented face Jacobians have the same sign at an inward
corner.  The second face carries the opposite boundary orientation, hence its
raw Jacobian appears with a minus sign. -/
theorem mixedWall_boundaryJacobian_product_pos_of_inward
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (hinward : mixedWallFirstFaceJacobian D *
      mixedWallSecondFaceJacobian D < 0) :
    0 < mixedWallFirstFaceJacobian D *
      (-mixedWallSecondFaceJacobian D) := by
  nlinarith

/-- At a transfer corner the two boundary-oriented face Jacobians have
opposite signs.  This is the local index cancellation used by the global
oriented wall chain. -/
theorem mixedWall_boundaryJacobian_product_neg_of_transfer
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (htransfer : 0 < mixedWallFirstFaceJacobian D *
      mixedWallSecondFaceJacobian D) :
    mixedWallFirstFaceJacobian D *
      (-mixedWallSecondFaceJacobian D) < 0 := by
  nlinarith

/-- The singular double-wall residue is exactly the vanishing of at least
one restricted wall-face Jacobian. -/
theorem mixedWall_jacobian_product_eq_zero_iff
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    mixedWallFirstFaceJacobian D * mixedWallSecondFaceJacobian D = 0 ↔
      mixedWallFirstFaceJacobian D = 0 ∨
        mixedWallSecondFaceJacobian D = 0 := by
  exact mul_eq_zero

/-- Exhaustive sign trichotomy for a mixed regular double-wall jet. -/
theorem mixedWall_jacobian_trichotomy
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    mixedWallFirstFaceJacobian D * mixedWallSecondFaceJacobian D < 0 ∨
      0 < mixedWallFirstFaceJacobian D * mixedWallSecondFaceJacobian D ∨
      mixedWallFirstFaceJacobian D * mixedWallSecondFaceJacobian D = 0 := by
  rcases lt_trichotomy
      (mixedWallFirstFaceJacobian D * mixedWallSecondFaceJacobian D) 0 with
    hneg | hzero | hpos
  · exact Or.inl hneg
  · exact Or.inr (Or.inr hzero)
  · exact Or.inr (Or.inl hpos)

/-! ### Integer local indices at mixed walls -/

/-- The local Brouwer index carried by a nonzero oriented real Jacobian.
Keeping the zero value makes the same definition record the singular
residue without a separate partial function. -/
def orientedJacobianIndex (J : ℝ) : ℤ :=
  if 0 < J then 1 else if J < 0 then -1 else 0

@[simp] theorem orientedJacobianIndex_of_pos {J : ℝ} (hJ : 0 < J) :
    orientedJacobianIndex J = 1 := by
  simp [orientedJacobianIndex, hJ]

@[simp] theorem orientedJacobianIndex_of_neg {J : ℝ} (hJ : J < 0) :
    orientedJacobianIndex J = -1 := by
  simp [orientedJacobianIndex, hJ, hJ.not_gt]

@[simp] theorem orientedJacobianIndex_zero :
    orientedJacobianIndex 0 = 0 := by
  simp [orientedJacobianIndex]

theorem orientedJacobianIndex_eq_zero_iff {J : ℝ} :
    orientedJacobianIndex J = 0 ↔ J = 0 := by
  rcases lt_trichotomy J 0 with hneg | rfl | hpos
  · simp [orientedJacobianIndex_of_neg hneg, hneg.ne]
  · simp
  · simp [orientedJacobianIndex_of_pos hpos, hpos.ne']

@[simp] theorem orientedJacobianIndex_neg (J : ℝ) :
    orientedJacobianIndex (-J) = -orientedJacobianIndex J := by
  rcases lt_trichotomy J 0 with hneg | rfl | hpos
  · rw [orientedJacobianIndex_of_neg hneg,
      orientedJacobianIndex_of_pos (neg_pos.mpr hneg)]
    norm_num
  · simp
  · rw [orientedJacobianIndex_of_pos hpos,
      orientedJacobianIndex_of_neg (neg_lt_zero.mpr hpos)]

/-- If a nonzero oriented Jacobian is split as `a + b`, then either the sum
keeps the orientation of `a`, or the correction term `b` has the opposite
orientation.  This elementary dichotomy chooses a compatible face in a
two-chart fan without comparing determinant magnitudes. -/
theorem orientedJacobianIndex_add_eq_self_or_right_eq_neg_self
    {a b : ℝ} (ha : a ≠ 0) :
    orientedJacobianIndex (a + b) = orientedJacobianIndex a ∨
      orientedJacobianIndex b = -orientedJacobianIndex a := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · rcases lt_trichotomy b 0 with hbNeg | hbZero | hbPos
    · left
      rw [orientedJacobianIndex_of_neg haNeg,
        orientedJacobianIndex_of_neg (by linarith)]
    · left
      subst b
      simp
    · right
      rw [orientedJacobianIndex_of_pos hbPos,
        orientedJacobianIndex_of_neg haNeg]
      norm_num
  · rcases lt_trichotomy b 0 with hbNeg | hbZero | hbPos
    · right
      rw [orientedJacobianIndex_of_neg hbNeg,
        orientedJacobianIndex_of_pos haPos]
    · left
      subst b
      simp
    · left
      rw [orientedJacobianIndex_of_pos haPos,
        orientedJacobianIndex_of_pos (by linarith)]

/-- Opposite-sign Jacobians carry cancelling integer local indices. -/
theorem orientedJacobianIndex_add_eq_zero_of_mul_neg
    {J K : ℝ} (hJK : J * K < 0) :
    orientedJacobianIndex J + orientedJacobianIndex K = 0 := by
  rcases mul_neg_iff.mp hJK with ⟨hJ, hK⟩ | ⟨hJ, hK⟩
  · rw [orientedJacobianIndex_of_pos hJ,
      orientedJacobianIndex_of_neg hK]
    norm_num
  · rw [orientedJacobianIndex_of_neg hJ,
      orientedJacobianIndex_of_pos hK]
    norm_num

/-- Same-sign Jacobians carry the same integer local index. -/
theorem orientedJacobianIndex_sub_eq_zero_of_mul_pos
    {J K : ℝ} (hJK : 0 < J * K) :
    orientedJacobianIndex J - orientedJacobianIndex K = 0 := by
  rcases mul_pos_iff.mp hJK with ⟨hJ, hK⟩ | ⟨hJ, hK⟩
  · rw [orientedJacobianIndex_of_pos hJ,
      orientedJacobianIndex_of_pos hK]
    norm_num
  · rw [orientedJacobianIndex_of_neg hJ,
      orientedJacobianIndex_of_neg hK]
    norm_num

/-- The first wall face uses its raw `(t,u)` Jacobian orientation. -/
def mixedWallFirstBoundaryLocalIndex
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) : ℤ :=
  orientedJacobianIndex (mixedWallFirstFaceJacobian D)

/-- The second wall face has the opposite boundary orientation, so its local
index is the negative of the raw `(t,s)` Jacobian sign. -/
def mixedWallSecondBoundaryLocalIndex
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) : ℤ :=
  -orientedJacobianIndex (mixedWallSecondFaceJacobian D)

/-- A regular transfer corner contributes opposite local degrees on its two
incident boundary-oriented wall faces.  This is the exact integer
cancellation, rather than only the preceding determinant-sign statement. -/
theorem mixedWall_boundaryLocalIndices_cancel_of_transfer
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (htransfer : 0 < mixedWallFirstFaceJacobian D *
      mixedWallSecondFaceJacobian D) :
    mixedWallFirstBoundaryLocalIndex D +
      mixedWallSecondBoundaryLocalIndex D = 0 := by
  simpa [mixedWallFirstBoundaryLocalIndex,
    mixedWallSecondBoundaryLocalIndex, sub_eq_add_neg] using
    orientedJacobianIndex_sub_eq_zero_of_mul_pos htransfer

/-- At an inward regular corner the two boundary-oriented local degrees are
equal and therefore reinforce rather than cancel. -/
theorem mixedWall_boundaryLocalIndices_eq_of_inward
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (hinward : mixedWallFirstFaceJacobian D *
      mixedWallSecondFaceJacobian D < 0) :
    mixedWallFirstBoundaryLocalIndex D =
      mixedWallSecondBoundaryLocalIndex D := by
  have hcancel := orientedJacobianIndex_add_eq_zero_of_mul_neg hinward
  unfold mixedWallFirstBoundaryLocalIndex mixedWallSecondBoundaryLocalIndex
  omega

/-- A singular double-wall jet has zero local index on at least one of its
two incident wall faces. -/
theorem mixedWall_boundaryLocalIndex_eq_zero_of_singular
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (hsingular : mixedWallFirstFaceJacobian D *
      mixedWallSecondFaceJacobian D = 0) :
    mixedWallFirstBoundaryLocalIndex D = 0 ∨
      mixedWallSecondBoundaryLocalIndex D = 0 := by
  rcases mul_eq_zero.mp hsingular with hfirst | hsecond
  · left
    simp [mixedWallFirstBoundaryLocalIndex, hfirst]
  · right
    simp [mixedWallSecondBoundaryLocalIndex, hsecond]

/-- The complete signed local outcome of a two-wall jet, parameterized by
the geometric opening proposition supplied by its concrete chart. -/
inductive MixedWallSignedOutcome
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) (InwardOpening : Prop) : Prop where
  | inward
      (sign : mixedWallFirstFaceJacobian D *
        mixedWallSecondFaceJacobian D < 0)
      (opening : InwardOpening)
      (reinforce : mixedWallFirstBoundaryLocalIndex D =
        mixedWallSecondBoundaryLocalIndex D)
  | transfer
      (sign : 0 < mixedWallFirstFaceJacobian D *
        mixedWallSecondFaceJacobian D)
      (cancel : mixedWallFirstBoundaryLocalIndex D +
        mixedWallSecondBoundaryLocalIndex D = 0)
  | singular
      (zero : mixedWallFirstFaceJacobian D *
        mixedWallSecondFaceJacobian D = 0)
      (zeroIndex : mixedWallFirstBoundaryLocalIndex D = 0 ∨
        mixedWallSecondBoundaryLocalIndex D = 0)

/-- Any concrete construction of the inward branch upgrades the determinant
trichotomy to the complete signed local outcome. -/
theorem mixedWall_signedOutcome
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) (InwardOpening : Prop)
    (openInward : mixedWallFirstFaceJacobian D *
      mixedWallSecondFaceJacobian D < 0 → InwardOpening) :
    MixedWallSignedOutcome D InwardOpening := by
  rcases mixedWall_jacobian_trichotomy D with
      hinward | htransfer | hsingular
  · exact .inward hinward (openInward hinward)
      (mixedWall_boundaryLocalIndices_eq_of_inward D hinward)
  · exact .transfer htransfer
      (mixedWall_boundaryLocalIndices_cancel_of_transfer D htransfer)
  · exact .singular hsingular
      (mixedWall_boundaryLocalIndex_eq_zero_of_singular D hsingular)

/-- The two non-purifying branches of a signed mixed-wall trichotomy.  This
is the packet transported by the selected-lineage argument after the inward
branch has already emitted its target certificate. -/
inductive MixedWallSignedResidue
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) : Prop where
  | transfer
      (sign : 0 < mixedWallFirstFaceJacobian D *
        mixedWallSecondFaceJacobian D)
      (cancel : mixedWallFirstBoundaryLocalIndex D +
        mixedWallSecondBoundaryLocalIndex D = 0)
  | singular
      (zero : mixedWallFirstFaceJacobian D *
        mixedWallSecondFaceJacobian D = 0)
      (zeroIndex : mixedWallFirstBoundaryLocalIndex D = 0 ∨
        mixedWallSecondBoundaryLocalIndex D = 0)

/-- Once the inward payload is regarded as success, a signed mixed-wall
outcome is exactly either that success or one residual transfer/singular
packet. -/
theorem MixedWallSignedOutcome.opening_or_residue
    {D : (Fin 3 → ℝ) →L[ℝ] ℂ} {InwardOpening : Prop}
    (outcome : MixedWallSignedOutcome D InwardOpening) :
    InwardOpening ∨ MixedWallSignedResidue D := by
  rcases outcome with
      ⟨_sign, opening, _reinforce⟩ | ⟨sign, cancel⟩ |
        ⟨zero, zeroIndex⟩
  · exact Or.inl opening
  · exact Or.inr (.transfer sign cancel)
  · exact Or.inr (.singular zero zeroIndex)

/-! ## Triple-wall cofactors

At a point where three upper walls meet, use the three inward wall slacks as
coordinates.  The same cofactor vector as above spans the regular kernel.
There are now three possibilities: all three cofactor entries have a common
orientation, some pair has opposite signs, or one entry vanishes.  These are
respectively the inward, transfer, and face-tangent alternatives. -/

/-- All three entries of the cofactor kernel have a common nonzero sign.
It is enough to compare entries `1` and `2` with entry `0`. -/
def tripleWallCofactorInward
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) : Prop :=
  0 < mixedWallCofactorVector D 0 * mixedWallCofactorVector D 1 ∧
    0 < mixedWallCofactorVector D 0 * mixedWallCofactorVector D 2

/-- Some pair of triple-wall cofactor entries has opposite signs. -/
def tripleWallCofactorTransfer
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) : Prop :=
  mixedWallCofactorVector D 0 * mixedWallCofactorVector D 1 < 0 ∨
    mixedWallCofactorVector D 0 * mixedWallCofactorVector D 2 < 0 ∨
      mixedWallCofactorVector D 1 * mixedWallCofactorVector D 2 < 0

/-- A triple-wall cofactor is tangent to at least one incident wall face. -/
def tripleWallCofactorSingular
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) : Prop :=
  ∃ i, mixedWallCofactorVector D i = 0

/-- If one triple-wall derivative column vanishes, the cofactor is tangent to
at least two incident faces and is therefore singular. -/
theorem tripleWallCofactorSingular_of_column_eq_zero
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) (i : Fin 3)
    (hcolumn : mixedWallColumn D i = 0) :
    tripleWallCofactorSingular D := by
  fin_cases i
  · refine ⟨1, ?_⟩
    change D (mixedWallVector 1 0 0) = 0 at hcolumn
    simp [mixedWallCofactorVector, hcolumn, mixedWallBracket]
  · refine ⟨0, ?_⟩
    change D (mixedWallVector 0 1 0) = 0 at hcolumn
    simp [mixedWallCofactorVector, hcolumn, mixedWallBracket]
  · refine ⟨0, ?_⟩
    change D (mixedWallVector 0 0 1) = 0 at hcolumn
    simp [mixedWallCofactorVector, hcolumn, mixedWallBracket]

/-- The boundary-oriented local index on one of the three incident faces of
a triple wall.  The cofactor coordinates already include the alternating
face-orientation signs. -/
def tripleWallBoundaryLocalIndex
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) (i : Fin 3) : ℤ :=
  orientedJacobianIndex (mixedWallCofactorVector D i)

/-- In the inward triple-wall branch all three boundary-oriented local
indices agree, so the incident faces reinforce one another. -/
theorem tripleWall_boundaryLocalIndices_eq_of_inward
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (hinward : tripleWallCofactorInward D) :
    tripleWallBoundaryLocalIndex D 0 =
        tripleWallBoundaryLocalIndex D 1 ∧
      tripleWallBoundaryLocalIndex D 0 =
        tripleWallBoundaryLocalIndex D 2 := by
  have h01 := orientedJacobianIndex_sub_eq_zero_of_mul_pos hinward.1
  have h02 := orientedJacobianIndex_sub_eq_zero_of_mul_pos hinward.2
  constructor <;> unfold tripleWallBoundaryLocalIndex <;> omega

/-- Every triple-wall transfer contains a pair of incident faces whose
integer local indices cancel exactly. -/
theorem exists_tripleWall_boundaryLocalIndices_cancel_of_transfer
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (htransfer : tripleWallCofactorTransfer D) :
    ∃ i j : Fin 3, i ≠ j ∧
      tripleWallBoundaryLocalIndex D i +
        tripleWallBoundaryLocalIndex D j = 0 := by
  rcases htransfer with h01 | h02 | h12
  · refine ⟨0, 1, by decide, ?_⟩
    exact orientedJacobianIndex_add_eq_zero_of_mul_neg h01
  · refine ⟨0, 2, by decide, ?_⟩
    exact orientedJacobianIndex_add_eq_zero_of_mul_neg h02
  · refine ⟨1, 2, by decide, ?_⟩
    exact orientedJacobianIndex_add_eq_zero_of_mul_neg h12

/-- If a specified triple-wall face has nonzero local index, every transfer
has an opposite-index partner incident to that very face. -/
private theorem mul_neg_left_or_right_of_ne_of_pairwise
    {a b c : ℝ} (ha : a ≠ 0)
    (hpair : a * b < 0 ∨ a * c < 0 ∨ b * c < 0) :
    a * b < 0 ∨ a * c < 0 := by
  rcases hpair with hab | hac | hbc
  · exact Or.inl hab
  · exact Or.inr hac
  · rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
    · rcases mul_neg_iff.mp hbc with
        ⟨hb_pos, _hc_neg⟩ | ⟨_hb_neg, hc_pos⟩
      · exact Or.inl (mul_neg_of_neg_of_pos ha_neg hb_pos)
      · exact Or.inr (mul_neg_of_neg_of_pos ha_neg hc_pos)
    · rcases mul_neg_iff.mp hbc with
        ⟨_hb_pos, hc_neg⟩ | ⟨hb_neg, _hc_pos⟩
      · exact Or.inr (mul_neg_of_pos_of_neg ha_pos hc_neg)
      · exact Or.inl (mul_neg_of_pos_of_neg ha_pos hb_neg)

theorem exists_tripleWall_boundaryLocalIndex_cancel_at_of_transfer
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (source : Fin 3)
    (hsource : tripleWallBoundaryLocalIndex D source ≠ 0)
    (htransfer : tripleWallCofactorTransfer D) :
    ∃ target : Fin 3, source ≠ target ∧
      tripleWallBoundaryLocalIndex D source +
        tripleWallBoundaryLocalIndex D target = 0 := by
  let c := mixedWallCofactorVector D
  have hcsource : c source ≠ 0 := by
    intro hzero
    apply hsource
    simp [tripleWallBoundaryLocalIndex, c, hzero]
  fin_cases source
  · have hopposite :=
      mul_neg_left_or_right_of_ne_of_pairwise hcsource htransfer
    rcases hopposite with h01 | h02
    · exact ⟨1, by decide,
        orientedJacobianIndex_add_eq_zero_of_mul_neg h01⟩
    · exact ⟨2, by decide,
        orientedJacobianIndex_add_eq_zero_of_mul_neg h02⟩
  · have hpair : c 1 * c 0 < 0 ∨ c 1 * c 2 < 0 ∨
        c 0 * c 2 < 0 := by
      rcases htransfer with h01 | h02 | h12
      · exact Or.inl (by simpa [mul_comm] using h01)
      · exact Or.inr (Or.inr h02)
      · exact Or.inr (Or.inl h12)
    have hopposite :=
      mul_neg_left_or_right_of_ne_of_pairwise hcsource hpair
    rcases hopposite with h10 | h12
    · exact ⟨0, by decide,
        orientedJacobianIndex_add_eq_zero_of_mul_neg h10⟩
    · exact ⟨2, by decide,
        orientedJacobianIndex_add_eq_zero_of_mul_neg h12⟩
  · have hpair : c 2 * c 0 < 0 ∨ c 2 * c 1 < 0 ∨
        c 0 * c 1 < 0 := by
      rcases htransfer with h01 | h02 | h12
      · exact Or.inr (Or.inr h01)
      · exact Or.inl (by simpa [mul_comm] using h02)
      · exact Or.inr (Or.inl (by simpa [mul_comm] using h12))
    have hopposite :=
      mul_neg_left_or_right_of_ne_of_pairwise hcsource hpair
    rcases hopposite with h20 | h21
    · exact ⟨0, by decide,
        orientedJacobianIndex_add_eq_zero_of_mul_neg h20⟩
    · exact ⟨1, by decide,
        orientedJacobianIndex_add_eq_zero_of_mul_neg h21⟩

/-- A singular triple-wall cofactor has zero local index on at least one
incident face. -/
theorem exists_tripleWall_boundaryLocalIndex_eq_zero_of_singular
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (hsingular : tripleWallCofactorSingular D) :
    ∃ i, tripleWallBoundaryLocalIndex D i = 0 := by
  obtain ⟨i, hi⟩ := hsingular
  exact ⟨i, by simp [tripleWallBoundaryLocalIndex, hi]⟩

/-- The triple-wall cofactor alternatives are exhaustive. -/
theorem tripleWallCofactor_trichotomy
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) :
    tripleWallCofactorInward D ∨
      tripleWallCofactorTransfer D ∨
        tripleWallCofactorSingular D := by
  let c := mixedWallCofactorVector D
  by_cases h0 : c 0 = 0
  · exact Or.inr (Or.inr ⟨0, h0⟩)
  by_cases h1 : c 1 = 0
  · exact Or.inr (Or.inr ⟨1, h1⟩)
  by_cases h2 : c 2 = 0
  · exact Or.inr (Or.inr ⟨2, h2⟩)
  rcases lt_or_gt_of_ne h0 with h0neg | h0pos
  · rcases lt_or_gt_of_ne h1 with h1neg | h1pos
    · rcases lt_or_gt_of_ne h2 with h2neg | h2pos
      · left
        exact ⟨mul_pos_of_neg_of_neg h0neg h1neg,
          mul_pos_of_neg_of_neg h0neg h2neg⟩
      · right
        left
        exact Or.inr (Or.inl (mul_neg_of_neg_of_pos h0neg h2pos))
    · right
      left
      exact Or.inl (mul_neg_of_neg_of_pos h0neg h1pos)
  · rcases lt_or_gt_of_ne h1 with h1neg | h1pos
    · right
      left
      exact Or.inl (mul_neg_of_pos_of_neg h0pos h1neg)
    · rcases lt_or_gt_of_ne h2 with h2neg | h2pos
      · right
        left
        exact Or.inr (Or.inl (mul_neg_of_pos_of_neg h0pos h2neg))
      · left
        exact ⟨mul_pos h0pos h1pos, mul_pos h0pos h2pos⟩

/-- The complete signed local outcome of a triple-wall jet, parameterized by
its concrete inward-opening proposition. -/
inductive TripleWallSignedOutcome
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) (InwardOpening : Prop) : Prop where
  | inward
      (sign : tripleWallCofactorInward D)
      (opening : InwardOpening)
      (reinforce :
        tripleWallBoundaryLocalIndex D 0 =
            tripleWallBoundaryLocalIndex D 1 ∧
          tripleWallBoundaryLocalIndex D 0 =
            tripleWallBoundaryLocalIndex D 2)
  | transfer
      (sign : tripleWallCofactorTransfer D)
      (cancel : ∃ i j : Fin 3, i ≠ j ∧
        tripleWallBoundaryLocalIndex D i +
          tripleWallBoundaryLocalIndex D j = 0)
  | singular
      (zero : tripleWallCofactorSingular D)
      (zeroIndex : ∃ i, tripleWallBoundaryLocalIndex D i = 0)

/-- Any concrete construction of the inward triple-wall branch upgrades the
cofactor trichotomy to its complete signed outcome. -/
theorem tripleWall_signedOutcome
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) (InwardOpening : Prop)
    (openInward : tripleWallCofactorInward D → InwardOpening) :
    TripleWallSignedOutcome D InwardOpening := by
  rcases tripleWallCofactor_trichotomy D with
      hinward | htransfer | hsingular
  · exact .inward hinward (openInward hinward)
      (tripleWall_boundaryLocalIndices_eq_of_inward D hinward)
  · exact .transfer htransfer
      (exists_tripleWall_boundaryLocalIndices_cancel_of_transfer D htransfer)
  · exact .singular hsingular
      (exists_tripleWall_boundaryLocalIndex_eq_zero_of_singular D hsingular)

/-- The transfer and singular branches left after a common-inward triple-wall
branch has been converted into its geometric opening payload. -/
inductive TripleWallSignedResidue
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ) : Prop where
  | transfer
      (sign : tripleWallCofactorTransfer D)
      (cancel : ∃ i j : Fin 3, i ≠ j ∧
        tripleWallBoundaryLocalIndex D i +
          tripleWallBoundaryLocalIndex D j = 0)
  | singular
      (zero : tripleWallCofactorSingular D)
      (zeroIndex : ∃ i, tripleWallBoundaryLocalIndex D i = 0)

/-- A signed triple-wall outcome is either its supplied inward success or one
of the two exact residual packets consumed by global lineage transport. -/
theorem TripleWallSignedOutcome.opening_or_residue
    {D : (Fin 3 → ℝ) →L[ℝ] ℂ} {InwardOpening : Prop}
    (outcome : TripleWallSignedOutcome D InwardOpening) :
    InwardOpening ∨ TripleWallSignedResidue D := by
  rcases outcome with
      ⟨_sign, opening, _reinforce⟩ | ⟨sign, cancel⟩ |
        ⟨zero, zeroIndex⟩
  · exact Or.inl opening
  · exact Or.inr (.transfer sign cancel)
  · exact Or.inr (.singular zero zeroIndex)

/-- In the inward triple-wall case, one orientation of the cofactor opens
all three walls simultaneously. -/
theorem exists_oriented_tripleWallCofactorVector
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (hinward : tripleWallCofactorInward D) :
    ∃ v : Fin 3 → ℝ, v ∈ D.ker ∧ ∀ i, 0 < v i := by
  let c := mixedWallCofactorVector D
  have h01 : 0 < c 0 * c 1 := hinward.1
  have h02 : 0 < c 0 * c 2 := hinward.2
  rcases (mul_pos_iff.mp h01) with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have h2 : 0 < c 2 := by
      rcases (mul_pos_iff.mp h02) with hpos | hneg
      · exact hpos.2
      · linarith
    refine ⟨c, mixedWallCofactorVector_mem_ker D, ?_⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · have h2 : c 2 < 0 := by
      rcases (mul_pos_iff.mp h02) with hpos | hneg
      · linarith
      · exact hneg.2
    let v : Fin 3 → ℝ := fun i ↦ -c i
    have hv : v = (-1 : ℝ) • c := by
      funext i
      simp [v]
    refine ⟨v, ?_, ?_⟩
    · rw [hv]
      exact D.ker.smul_mem (-1) (mixedWallCofactorVector_mem_ker D)
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      fin_cases i <;> simp
    rcases hi with rfl | rfl | rfl
    · exact neg_pos.mpr h0
    · exact neg_pos.mpr h1
    · exact neg_pos.mpr h2

/-- In a transfer triple wall, no scalar orientation of the cofactor opens
all three walls. -/
theorem no_oriented_tripleWallCofactorVector_of_transfer
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (htransfer : tripleWallCofactorTransfer D) (sigma : ℝ) :
    ¬(∀ i, 0 < (sigma • mixedWallCofactorVector D) i) := by
  intro hpos
  have h0 := hpos (0 : Fin 3)
  have h1 := hpos (1 : Fin 3)
  have h2 := hpos (2 : Fin 3)
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  have hsquare := sq_nonneg sigma
  rcases htransfer with h01 | h02 | h12
  · have hscaled : 0 <
        (sigma * mixedWallCofactorVector D 0) *
          (sigma * mixedWallCofactorVector D 1) := mul_pos h0 h1
    nlinarith
  · have hscaled : 0 <
        (sigma * mixedWallCofactorVector D 0) *
          (sigma * mixedWallCofactorVector D 2) := mul_pos h0 h2
    nlinarith
  · have hscaled : 0 <
        (sigma * mixedWallCofactorVector D 1) *
          (sigma * mixedWallCofactorVector D 2) := mul_pos h1 h2
    nlinarith

/-- The inward triple-wall alternative forces the closure derivative to be
surjective: one of its two-column brackets is nonzero. -/
theorem mixedWallDerivative_range_eq_top_of_tripleWallCofactorInward
    (D : (Fin 3 → ℝ) →L[ℝ] ℂ)
    (hinward : tripleWallCofactorInward D) :
    D.range = ⊤ := by
  have hc1 : mixedWallCofactorVector D 1 ≠ 0 := by
    intro hzero
    have hprod := hinward.1
    rw [hzero, mul_zero] at hprod
    exact (lt_irrefl 0 hprod)
  apply mixedWallDerivative_range_eq_top_of_firstFaceJacobian_ne
  intro hzero
  apply hc1
  rw [mixedWallCofactorVector_firstSlack, hzero, neg_zero]

/-- A regular triple-wall zero with a common cofactor orientation lies on an
exact level-set curve entering all three wall interiors. -/
theorem regularTripleWallZero_entersInterior
    {f : (Fin 3 → ℝ) → ℂ}
    {D : (Fin 3 → ℝ) →L[ℝ] ℂ}
    (hf : HasStrictFDerivAt f D 0)
    (hinward : tripleWallCofactorInward D) :
    ∃ (gamma : ℝ → (Fin 3 → ℝ)) (epsilon : ℝ),
      0 < epsilon ∧ gamma 0 = 0 ∧
      Filter.Tendsto gamma (nhds 0) (nhds 0) ∧
      ∀ t, 0 < t → t < epsilon →
        f (gamma t) = f 0 ∧ ∀ i, 0 < gamma t i := by
  obtain ⟨v, hvker, hvpos⟩ :=
    exists_oriented_tripleWallCofactorVector D hinward
  have hsurj :=
    mixedWallDerivative_range_eq_top_of_tripleWallCofactorInward D hinward
  let w : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x ↦ x i
  let w' : Fin 3 → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i ↦ ContinuousLinearMap.proj i
  have hw : ∀ i, HasFDerivAt (w i) (w' i) (0 : Fin 3 → ℝ) := by
    intro i
    simpa [w, w'] using
      (hasFDerivAt_apply (𝕜 := ℝ) i (0 : Fin 3 → ℝ))
  have hvpos' : ∀ i, 0 < w' i v := by
    intro i
    simpa [w'] using hvpos i
  obtain ⟨gamma, epsilon, hepsilon, hgammaZero, _hgammaDeriv,
      hgammaTendsto, hgood⟩ :=
    regularWallZero_entersAllInteriors
      (ι := Fin 3) hf hsurj hvker hw hvpos'
  refine ⟨gamma, epsilon, hepsilon, hgammaZero, hgammaTendsto, ?_⟩
  intro t ht he
  obtain ⟨hlevel, hwalls⟩ := hgood t ht he
  exact ⟨hlevel, fun i ↦ by simpa [w] using hwalls i⟩

/-- A regular double-wall closure zero whose two oriented wall-face
Jacobians have opposite signs lies on an exact closure-zero curve entering
both wall interiors.  This is the analytic purification half of the
inward/transfer/singular trichotomy. -/
theorem regularMixedDoubleWallZero_entersInterior
    {f : (Fin 3 → ℝ) → ℂ}
    {D : (Fin 3 → ℝ) →L[ℝ] ℂ}
    (hf : HasStrictFDerivAt f D 0)
    (hinward : mixedWallFirstFaceJacobian D *
      mixedWallSecondFaceJacobian D < 0) :
    ∃ (gamma : ℝ → (Fin 3 → ℝ)) (epsilon : ℝ),
      0 < epsilon ∧ gamma 0 = 0 ∧
      Filter.Tendsto gamma (nhds 0) (nhds 0) ∧
      ∀ t, 0 < t → t < epsilon →
        f (gamma t) = f 0 ∧ 0 < gamma t 1 ∧ 0 < gamma t 2 := by
  obtain ⟨v, hvker, hvone, hvtwo⟩ :=
    exists_oriented_mixedWallCofactorVector D hinward
  have hJ : mixedWallFirstFaceJacobian D ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hinward
    exact (lt_irrefl 0 hinward)
  have hsurj : D.range = ⊤ :=
    mixedWallDerivative_range_eq_top_of_firstFaceJacobian_ne D hJ
  let w : Fin 2 → (Fin 3 → ℝ) → ℝ := fun i x ↦ x i.succ
  let w' : Fin 2 → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i ↦ ContinuousLinearMap.proj i.succ
  have hw : ∀ i, HasFDerivAt (w i) (w' i) (0 : Fin 3 → ℝ) := by
    intro i
    simpa [w, w'] using
      (hasFDerivAt_apply (𝕜 := ℝ) i.succ (0 : Fin 3 → ℝ))
  have hvpos : ∀ i, 0 < w' i v := by
    intro i
    fin_cases i
    · simpa [w'] using hvone
    · simpa [w'] using hvtwo
  obtain ⟨gamma, epsilon, hepsilon, hgammaZero, _hgammaDeriv,
      hgammaTendsto, hgood⟩ :=
    regularWallZero_entersAllInteriors
      (ι := Fin 2) hf hsurj hvker hw hvpos
  refine ⟨gamma, epsilon, hepsilon, hgammaZero, hgammaTendsto, ?_⟩
  intro t ht he
  obtain ⟨hlevel, hwalls⟩ := hgood t ht he
  have hone := hwalls (0 : Fin 2)
  have htwo := hwalls (1 : Fin 2)
  change (0 : ℝ) < gamma t 1 at hone
  change (0 : ℝ) < gamma t 2 at htwo
  exact ⟨hlevel, hone, htwo⟩

/-- The inward double-wall germ contains regular interior zeros arbitrarily
close to the corner.  Besides opening both named slacks, the selected point
retains a nonzero first-face Jacobian, hence a rank-two transverse chart. -/
theorem exists_regularMixedDoubleWallZero_inInterior_near
    {f : (Fin 3 → ℝ) → ℂ}
    (hf : HasStrictFDerivAt f (fderiv ℝ f 0) 0)
    (hfderiv : ContinuousAt (fderiv ℝ f) 0)
    (hinward : mixedWallFirstFaceJacobian (fderiv ℝ f 0) *
      mixedWallSecondFaceJacobian (fderiv ℝ f 0) < 0) :
    ∀ U ∈ nhds (0 : Fin 3 → ℝ),
      ∃ x ∈ U,
        f x = f 0 ∧ 0 < x 1 ∧ 0 < x 2 ∧
          mixedWallFirstFaceJacobian (fderiv ℝ f x) ≠ 0 := by
  obtain ⟨gamma, epsilon, hepsilon, _hgammaZero, hgammaTendsto,
      hgood⟩ := regularMixedDoubleWallZero_entersInterior
    hf hinward
  have hJzero : mixedWallFirstFaceJacobian (fderiv ℝ f 0) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hinward
    exact (lt_irrefl 0 hinward)
  have hJcontinuous : ContinuousAt
      (fun x ↦ mixedWallFirstFaceJacobian (fderiv ℝ f x)) 0 :=
    continuous_mixedWallFirstFaceJacobian.continuousAt.comp
      hfderiv
  have hJevent : ∀ᶠ x in nhds (0 : Fin 3 → ℝ),
      mixedWallFirstFaceJacobian (fderiv ℝ f x) ≠ 0 :=
    hJcontinuous.eventually_ne hJzero
  intro U hU
  have hgammaU : ∀ᶠ t in nhds (0 : ℝ), gamma t ∈ U :=
    hgammaTendsto.eventually hU
  have hgammaJ : ∀ᶠ t in nhds (0 : ℝ),
      mixedWallFirstFaceJacobian (fderiv ℝ f (gamma t)) ≠ 0 :=
    hgammaTendsto.eventually hJevent
  have hnear : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      gamma t ∈ U ∧
        mixedWallFirstFaceJacobian (fderiv ℝ f (gamma t)) ≠ 0 ∧
          t ∈ Set.Ioo (0 : ℝ) epsilon := by
    filter_upwards [hgammaU.filter_mono nhdsWithin_le_nhds,
      hgammaJ.filter_mono nhdsWithin_le_nhds,
      Ioo_mem_nhdsGT hepsilon] with t htU htJ ht
    exact ⟨htU, htJ, ht⟩
  obtain ⟨t, htU, htJ, ht0, htepsilon⟩ := hnear.exists
  obtain ⟨hlevel, hone, htwo⟩ := hgood t ht0 htepsilon
  exact ⟨gamma t, htU, hlevel, hone, htwo, htJ⟩

/-- The inward triple-wall germ likewise contains arbitrarily close regular
zeros with all three wall slacks positive. -/
theorem exists_regularTripleWallZero_inInterior_near
    {f : (Fin 3 → ℝ) → ℂ}
    (hf : HasStrictFDerivAt f (fderiv ℝ f 0) 0)
    (hfderiv : ContinuousAt (fderiv ℝ f) 0)
    (hinward : tripleWallCofactorInward (fderiv ℝ f 0)) :
    ∀ U ∈ nhds (0 : Fin 3 → ℝ),
      ∃ x ∈ U,
        f x = f 0 ∧ (∀ i, 0 < x i) ∧
          mixedWallFirstFaceJacobian (fderiv ℝ f x) ≠ 0 := by
  obtain ⟨gamma, epsilon, hepsilon, _hgammaZero, hgammaTendsto,
      hgood⟩ := regularTripleWallZero_entersInterior
    hf hinward
  have hJzero : mixedWallFirstFaceJacobian (fderiv ℝ f 0) ≠ 0 := by
    intro hzero
    have hone := hinward.1
    rw [mixedWallCofactorVector_firstSlack, hzero, neg_zero,
      mul_zero] at hone
    exact (lt_irrefl 0 hone)
  have hJcontinuous : ContinuousAt
      (fun x ↦ mixedWallFirstFaceJacobian (fderiv ℝ f x)) 0 :=
    continuous_mixedWallFirstFaceJacobian.continuousAt.comp
      hfderiv
  have hJevent : ∀ᶠ x in nhds (0 : Fin 3 → ℝ),
      mixedWallFirstFaceJacobian (fderiv ℝ f x) ≠ 0 :=
    hJcontinuous.eventually_ne hJzero
  intro U hU
  have hgammaU : ∀ᶠ t in nhds (0 : ℝ), gamma t ∈ U :=
    hgammaTendsto.eventually hU
  have hgammaJ : ∀ᶠ t in nhds (0 : ℝ),
      mixedWallFirstFaceJacobian (fderiv ℝ f (gamma t)) ≠ 0 :=
    hgammaTendsto.eventually hJevent
  have hnear : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      gamma t ∈ U ∧
        mixedWallFirstFaceJacobian (fderiv ℝ f (gamma t)) ≠ 0 ∧
          t ∈ Set.Ioo (0 : ℝ) epsilon := by
    filter_upwards [hgammaU.filter_mono nhdsWithin_le_nhds,
      hgammaJ.filter_mono nhdsWithin_le_nhds,
      Ioo_mem_nhdsGT hepsilon] with t htU htJ ht
    exact ⟨htU, htJ, ht⟩
  obtain ⟨t, htU, htJ, ht0, htepsilon⟩ := hnear.exists
  obtain ⟨hlevel, hwalls⟩ := hgood t ht0 htepsilon
  exact ⟨gamma t, htU, hlevel, hwalls, htJ⟩

end

/-! ## Componentwise selected-lineage conservation

Scalar boundary sums can cancel contributions carried by unrelated zero-set
components.  The global wall-chain argument must instead retain one integer
coordinate for each component of the normalized real zero set.  The following
finite conservation package isolates the purely algebraic part of that
argument: internal wall flux may cancel, but a nonzero marked source
coordinate must then occur at some external exit.  Constructing the flux data
from the analytic normalization remains the geometric theorem. -/

/-- Componentwise boundary flux for a finite wall-chain decomposition.
`Lineage` indexes normalized zero-set components, while `Internal` and `Exit`
index the glued internal faces and the external terminal faces. -/
structure SelectedLineageFluxData
    (Lineage Internal Exit : Type*)
    [Fintype Internal] [Fintype Exit] where
  source : Lineage → ℤ
  internalFlux : Internal → Lineage → ℤ
  exitFlux : Exit → Lineage → ℤ
  conservation (lineage : Lineage) :
    source lineage + (∑ node, internalFlux node lineage) +
      ∑ terminal, exitFlux terminal lineage = 0
  internal_cancel (lineage : Lineage) :
    ∑ node, internalFlux node lineage = 0

namespace SelectedLineageFluxData

/-- After gluing the internal transfer faces, the external flux in each
lineage is the negative of its source multiplicity. -/
theorem exit_sum_eq_neg_source
    {Lineage Internal Exit : Type*}
    [Fintype Internal] [Fintype Exit]
    (data : SelectedLineageFluxData Lineage Internal Exit)
    (lineage : Lineage) :
    (∑ terminal, data.exitFlux terminal lineage) =
      -data.source lineage := by
  have hconservation := data.conservation lineage
  rw [data.internal_cancel lineage] at hconservation
  omega

/-- A nonzero marked source coordinate cannot disappear through cancellation
with other lineages: at least one external terminal carries that same marked
coordinate nontrivially. -/
theorem exists_exit_of_source_ne_zero
    {Lineage Internal Exit : Type*}
    [Fintype Internal] [Fintype Exit]
    (data : SelectedLineageFluxData Lineage Internal Exit)
    {lineage : Lineage} (hsource : data.source lineage ≠ 0) :
    ∃ terminal : Exit, data.exitFlux terminal lineage ≠ 0 := by
  by_contra hnone
  have hall : ∀ terminal : Exit,
      data.exitFlux terminal lineage = 0 := by
    intro terminal
    by_contra hterminal
    exact hnone ⟨terminal, hterminal⟩
  have hsum : (∑ terminal, data.exitFlux terminal lineage) = 0 :=
    Finset.sum_eq_zero fun terminal _ ↦ hall terminal
  rw [data.exit_sum_eq_neg_source lineage, neg_eq_zero] at hsum
  exact hsource hsum

end SelectedLineageFluxData

end Gluck.Discrete
