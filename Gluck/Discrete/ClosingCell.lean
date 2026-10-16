/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.Closing
public import Gluck.Discrete.Converse
public import Gluck.Winding
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Order.Hom.Set
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# The closing engine — the turning-angle chart and the antisymmetric 2-cell

This file builds the *turning-angle chart* of the closing engine
(`blueprint/src/chapters/Gluck_Discrete_Closing.tex`, `def:turning_chart`,
`def:closing_2cell`). The key change of coordinates replaces the raw edge-length
packaging by the per-edge turning contribution

  `chartMap p q x = arcsin (p * x / 2) + arcsin (q * x / 2)`,

so that at edge `j` the pair `(p, q) = (κ j, κ (j+1))` gives
`chartMap (κ j) (κ (j+1)) (ℓ j)`, and the total turning is the *linear* sum of
the per-edge contributions:

  `turningSum κ ℓ = ∑ j, chartMap (κ j) (κ (j+1)) (ℓ j)`  (`turningSum_eq_sum_edgeChart`).

In the chart variables `s j = chartMap (κ j) (κ (j+1)) (ℓ j)` the turning
constraint `turningSum = 2π` is the affine condition `∑ j, s j = 2π`, which the
antisymmetric 2-cell keeps for free.

Blueprint: `blueprint/src/chapters/Gluck_Discrete_Closing.tex`, `sec:closure`.
-/

@[expose] public section

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

/-! ## Project-local Mathlib supplement — the per-edge turning-angle chart -/

/-- The per-edge turning-angle contribution of a single edge with adjacent
curvatures `p` (at its tail vertex) and `q` (at its head vertex) and length `x`:
`chartMap p q x = arcsin (p * x / 2) + arcsin (q * x / 2)`. Summing this over all
edges recovers the total turning (`turningSum_eq_sum_edgeChart`), so the turning
constraint becomes affine in the chart variables. -/
noncomputable def chartMap (p q x : ℝ) : ℝ :=
  Real.arcsin (p * x / 2) + Real.arcsin (q * x / 2)

@[simp] lemma chartMap_zero (p q : ℝ) : chartMap p q 0 = 0 := by
  simp [chartMap]

/-- The total turning is the sum of the per-edge chart contributions: edge `j`
(length `ℓ j`, adjacent curvatures `κ j` and `κ (j+1)`) contributes
`chartMap (κ j) (κ (j+1)) (ℓ j)`. This is the linearization underlying the
turning-angle chart (`def:turning_chart`): in the chart variables the constraint
`turningSum = 2π` is the affine `∑ j, s j = 2π`. -/
theorem turningSum_eq_sum_edgeChart [NeZero n] (κ ℓ : ZMod n → ℝ) :
    turningSum κ ℓ = ∑ j : ZMod n, chartMap (κ j) (κ (j + 1)) (ℓ j) := by
  unfold turningSum chartMap
  simp only [turningAngle, tK_zero, mul_div_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_comm]
  congr 1
  -- reindex the `ℓ (i-1)` sum by `i = j + 1`
  rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod n))
    (fun i => Real.arcsin (κ i * (ℓ (i - 1) / 2)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right]

/-! ### Single-edge chart: monotonicity, continuity, and the inverse homeomorphism -/

/-- On the moderate domain `Ioo 0 (2 / max p q)` (for positive `p, q`) each
`arcsin` argument `r * x / 2` (with `0 < r ≤ max p q`) lies in `Ioo (-1) 1`. -/
private lemma chartArg_mem {p q x : ℝ} (hp : 0 < p) (_hq : 0 < q)
    (hx : x ∈ Set.Ioo (0 : ℝ) (2 / max p q)) {r : ℝ} (hr : 0 < r)
    (hrle : r ≤ max p q) : r * x / 2 ∈ Set.Ioo (-1 : ℝ) 1 := by
  obtain ⟨hx0, hxD⟩ := hx
  have hmax : 0 < max p q := lt_of_lt_of_le hp (le_max_left p q)
  refine ⟨by linarith [mul_pos hr hx0], ?_⟩
  have h1 : r * x ≤ max p q * x := mul_le_mul_of_nonneg_right hrle hx0.le
  have h2 : max p q * x < max p q * (2 / max p q) := mul_lt_mul_of_pos_left hxD hmax
  have h3 : max p q * (2 / max p q) = 2 := by field_simp
  linarith

/-- The single-edge turning-angle chart `chartMap p q` is strictly increasing on
the moderate domain `Ioo 0 (2 / max p q)` (for positive `p, q`). Each `arcsin`
summand is strictly increasing there because its argument stays in `(-1, 1)`. -/
theorem chartMap_strictMonoOn {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    StrictMonoOn (chartMap p q) (Set.Ioo (0 : ℝ) (2 / max p q)) := by
  intro x hx y hy hxy
  unfold chartMap
  have hpx := chartArg_mem hp hq hx hp (le_max_left p q)
  have hqx := chartArg_mem hp hq hx hq (le_max_right p q)
  have hpy := chartArg_mem hp hq hy hp (le_max_left p q)
  have hqy := chartArg_mem hp hq hy hq (le_max_right p q)
  have h1 : Real.arcsin (p * x / 2) < Real.arcsin (p * y / 2) :=
    Real.strictMonoOn_arcsin ⟨hpx.1.le, hpx.2.le⟩ ⟨hpy.1.le, hpy.2.le⟩
      (by have := mul_lt_mul_of_pos_left hxy hp; linarith)
  have h2 : Real.arcsin (q * x / 2) < Real.arcsin (q * y / 2) :=
    Real.strictMonoOn_arcsin ⟨hqx.1.le, hqx.2.le⟩ ⟨hqy.1.le, hqy.2.le⟩
      (by have := mul_lt_mul_of_pos_left hxy hq; linarith)
  exact add_lt_add h1 h2

/-- `chartMap p q` is continuous on all of `ℝ` (`arcsin` is continuous
everywhere; the arguments are affine in `x`). -/
theorem chartMap_continuous (p q : ℝ) : Continuous (chartMap p q) := by
  unfold chartMap
  exact (Real.continuous_arcsin.comp (by fun_prop)).add
    (Real.continuous_arcsin.comp (by fun_prop))

/-- The turning-angle chart of a single edge, packaged as a homeomorphism from
the moderate length interval `Ioo 0 (2 / max p q)` onto its image
`chartMap p q '' Ioo 0 (2 / max p q)` (an open interval `(0, β)` of turning
contributions). Its inverse — the continuous, strictly increasing edge-length
recovery `λ` of `def:turning_chart` — is `(chartHomeomorph hp hq).symm`.
Built via `StrictMonoOn.orderIso` (`chartMap_strictMonoOn`) then
`OrderIso.toHomeomorph`; the image is an interval (preconnected image of an
interval), so it carries the order topology. -/
noncomputable def chartHomeomorph {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ↥(Set.Ioo (0 : ℝ) (2 / max p q)) ≃ₜ
      ↥(chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :=
  haveI : (Set.Ioo (0 : ℝ) (2 / max p q)).OrdConnected := Set.ordConnected_Ioo
  haveI : (chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)).OrdConnected :=
    ((isPreconnected_Ioo).image _
      (chartMap_continuous p q).continuousOn).ordConnected
  haveI : OrderTopology ↥(Set.Ioo (0 : ℝ) (2 / max p q)) :=
    orderTopology_of_ordConnected
  haveI : OrderTopology ↥(chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :=
    orderTopology_of_ordConnected
  (StrictMonoOn.orderIso (chartMap p q) _ (chartMap_strictMonoOn hp hq)).toHomeomorph

/-- The edge-length recovery map `λ` of `def:turning_chart`: the inverse of the
single-edge turning chart. On the turning-value interval
`chartMap p q '' Ioo 0 (2 / max p q)` it is the continuous, strictly increasing
inverse `(chartHomeomorph hp hq).symm`; off that interval it is `0` (junk). -/
noncomputable def chartInv {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (s : ℝ) : ℝ := by
  classical
  exact if h : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) then
    ((chartHomeomorph hp hq).symm ⟨s, h⟩ : ℝ) else 0

/-- On the turning-value interval the recovered edge length lies in the moderate
length interval `Ioo 0 (2 / max p q)`. -/
theorem chartInv_mem {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartInv hp hq s ∈ Set.Ioo (0 : ℝ) (2 / max p q) := by
  classical
  rw [chartInv, dif_pos hs]
  exact ((chartHomeomorph hp hq).symm ⟨s, hs⟩).2

/-- Round-trip: recovering the edge length and re-applying the chart returns the
turning value. This is the inverse identity `τ ∘ λ = id` of `def:turning_chart`. -/
theorem chartMap_chartInv {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartMap p q (chartInv hp hq s) = s := by
  classical
  rw [chartInv, dif_pos hs]
  have h := (chartHomeomorph hp hq).apply_symm_apply ⟨s, hs⟩
  have hcoe : ((chartHomeomorph hp hq) ((chartHomeomorph hp hq).symm ⟨s, hs⟩) : ℝ)
      = chartMap p q ((chartHomeomorph hp hq).symm ⟨s, hs⟩ : ℝ) := rfl
  rw [← hcoe, h]

/-- The recovery map `λ` is continuous on the turning-value interval (as the
subtype coercion of the continuous inverse homeomorphism). -/
theorem continuousOn_chartInv {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ContinuousOn (chartInv hp hq) (chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) := by
  classical
  rw [continuousOn_iff_continuous_domRestrict]
  have hrestrict : (chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)).domRestrict
        (chartInv hp hq)
      = fun x => ((chartHomeomorph hp hq).symm x : ℝ) := by
    funext x
    change chartInv hp hq (x : ℝ) = ((chartHomeomorph hp hq).symm x : ℝ)
    simp [chartInv, dif_pos x.2]
  rw [hrestrict]
  exact continuous_subtype_val.comp (chartHomeomorph hp hq).symm.continuous

/-- Left inverse: recovering the length of a charted moderate length returns
the length (`λ ∘ τ = id` on the moderate domain). Together with
`chartMap_chartInv` this makes `chartInv` a two-sided inverse. -/
theorem chartInv_chartMap {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartInv hp hq (chartMap p q x) = x := by
  have hmem : chartMap p q x ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) :=
    ⟨x, hx, rfl⟩
  exact (chartMap_strictMonoOn hp hq).injOn (chartInv_mem hp hq hmem) hx
    (chartMap_chartInv hp hq hmem)

/-- Achieving a turning value inside a compact length subinterval: any `s`
between the chart values at the endpoints is achieved by a length in the
subinterval (intermediate value theorem). This is the `Icc`-refined membership
used by the joint-continuity route. -/
theorem chartMap_mem_image_Icc {p q x₁ x₂ s : ℝ} (hx : x₁ ≤ x₂)
    (h : s ∈ Set.Icc (chartMap p q x₁) (chartMap p q x₂)) :
    s ∈ chartMap p q '' Set.Icc x₁ x₂ :=
  intermediate_value_Icc hx (chartMap_continuous p q).continuousOn h

/-! ### Joint continuity of the inverse of a continuous monotone family

The one nontrivial analytic obligation of `def:turning_chart`: the recovered
edge length depends continuously on *both* the homotopy parameter `t` and the
chart value `s`. We prove it abstractly for any jointly-continuous family
`g : T → ℝ → ℝ` (`T` compact Hausdorff) that is injective on a common compact
length interval `Icc a b`, with a chosen inverse `inv`. The proof is the
compact-to-Hausdorff argument: `F (t, x) = (t, g t x)` is a continuous injection
from the compact `T × Icc a b`, hence a homeomorphism onto its range, so its
inverse — which recovers `inv` in the second coordinate — is continuous. -/

/-- **Joint continuity of the inverse of a continuous strictly-monotone family.**
For a jointly continuous `g : T → ℝ → ℝ` (`T` compact Hausdorff) that is
injective on `Icc a b` for each parameter, any inverse `inv` (a right inverse of
`g t` on the value set `g t '' Icc a b`, landing in `Icc a b`) is jointly
continuous in `(t, s)` on `{(t, s) : s ∈ g t '' Icc a b}`. This is the IFT-free
route to joint continuity of the edge-length recovery `λ` of `def:turning_chart`
(with `g t = chartMap (κ_t j) (κ_t (j+1))`, `κ_t` affine in `t`). -/
theorem continuousOn_inv_family {T : Type*} [TopologicalSpace T] [CompactSpace T]
    [T2Space T] {g : T → ℝ → ℝ} {a b : ℝ}
    (hg : Continuous fun p : T × ℝ => g p.1 p.2)
    (hinj : ∀ t, Set.InjOn (g t) (Set.Icc a b))
    {inv : T → ℝ → ℝ}
    (hinv1 : ∀ t s, s ∈ g t '' Set.Icc a b → g t (inv t s) = s)
    (hinv2 : ∀ t s, s ∈ g t '' Set.Icc a b → inv t s ∈ Set.Icc a b) :
    ContinuousOn (fun p : T × ℝ => inv p.1 p.2)
      {p : T × ℝ | p.2 ∈ g p.1 '' Set.Icc a b} := by
  haveI : CompactSpace ↥(Set.Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  set F : T × ↥(Set.Icc a b) → T × ℝ := fun x => (x.1, g x.1 (x.2 : ℝ)) with hF
  have hFcont : Continuous F :=
    continuous_fst.prodMk
      (hg.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hFinj : Function.Injective F := by
    rintro ⟨t, x⟩ ⟨t', x'⟩ hEq
    simp only [hF, Prod.mk.injEq] at hEq
    obtain ⟨rfl, h2⟩ := hEq
    exact Prod.ext rfl (Subtype.ext (hinj t x.2 x'.2 h2))
  have hrange : Set.range F = {p : T × ℝ | p.2 ∈ g p.1 '' Set.Icc a b} := by
    ext ⟨t, s⟩
    simp only [Set.mem_range, Set.mem_setOf_eq, hF, Prod.mk.injEq, Set.mem_image]
    constructor
    · rintro ⟨⟨t', x⟩, ⟨rfl, rfl⟩⟩
      exact ⟨(x : ℝ), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(t, ⟨x, hx⟩), rfl, rfl⟩
  set e : (T × ↥(Set.Icc a b)) ≃ ↥(Set.range F) := Equiv.ofInjective F hFinj with he
  have hecont : Continuous e := by
    rw [he]
    exact hFcont.subtype_mk _
  have hsymm : Continuous e.symm := hecont.continuous_symm_of_equiv_compact_to_t2
  rw [← hrange, continuousOn_iff_continuous_restrict]
  have hkey : (Set.range F).domRestrict (fun p => inv p.1 p.2)
      = fun y => ((e.symm y).2 : ℝ) := by
    funext y
    have hFy : F (e.symm y) = (y : T × ℝ) := by
      rw [he]; exact Equiv.apply_ofInjective_symm hFinj y
    have h1 : (e.symm y).1 = (y : T × ℝ).1 := by rw [← hFy]
    have h2 : g (e.symm y).1 ((e.symm y).2 : ℝ) = (y : T × ℝ).2 := by
      rw [← hFy]
    set x : ℝ := ((e.symm y).2 : ℝ) with hx
    have hxmem : x ∈ Set.Icc a b := (e.symm y).2.2
    have hgx : g (y : T × ℝ).1 x = (y : T × ℝ).2 := by rw [← h1]; exact h2
    have hmemimg : (y : T × ℝ).2 ∈ g (y : T × ℝ).1 '' Set.Icc a b :=
      ⟨x, hxmem, hgx⟩
    have hinveq : inv (y : T × ℝ).1 (y : T × ℝ).2 = x := by
      apply hinj (y : T × ℝ).1 (hinv2 _ _ hmemimg) hxmem
      rw [hinv1 _ _ hmemimg, hgx]
    change inv (y : T × ℝ).1 (y : T × ℝ).2 = x
    exact hinveq
  rw [hkey]
  exact continuous_subtype_val.comp (continuous_snd.comp hsymm)

/-! ### The central-symmetrization homotopy (`def:central_symmetrization`)

The degree argument of `sec:closure` is anchored at the centrally-symmetric case,
which closes for free (`central_symmetry_closes`). Here we build the homotopy from
the central symmetrization `κ⁰_i = (κ_i + κ_{i+m})/2` (centrally symmetric,
positive) to `κ` itself, `κ_t = κ⁰ + t·(κ - κ⁰)`, `t ∈ [0,1]`. -/

/-- The central symmetrization `κ⁰_i = (κ_i + κ_{i+m})/2` of a profile `κ`
(half-period `m`, so `n = 2m`). It is half-period symmetric (`centralSym_symm`)
and positive when `κ` is. -/
noncomputable def centralSym (m : ℕ) (κ : ZMod n → ℝ) : ZMod n → ℝ :=
  fun i => (κ i + κ (i + (m : ZMod n))) / 2

/-- The central-symmetrization homotopy `κ_t = κ⁰ + t·(κ - κ⁰)` from the central
symmetrization `κ⁰ = centralSym m κ` (`t = 0`) to `κ` itself (`t = 1`). Affine —
hence continuous — in `t`, which drives the joint-continuity route
(`continuousOn_inv_family`). -/
noncomputable def curvHomotopy (m : ℕ) (κ : ZMod n → ℝ) (t : ℝ) : ZMod n → ℝ :=
  fun i => centralSym m κ i + t * (κ i - centralSym m κ i)

@[simp] lemma curvHomotopy_zero (m : ℕ) (κ : ZMod n → ℝ) :
    curvHomotopy m κ 0 = centralSym m κ := by
  funext i; simp [curvHomotopy]

@[simp] lemma curvHomotopy_one (m : ℕ) (κ : ZMod n → ℝ) :
    curvHomotopy m κ 1 = κ := by
  funext i; simp [curvHomotopy]

/-- The central symmetrization is half-period symmetric: `κ⁰_{i+m} = κ⁰_i`
(uses `n = 2m`, so a double shift by `m` is the identity in `ZMod n`). -/
theorem centralSym_symm [NeZero n] {m : ℕ} (hn : n = 2 * m) (κ : ZMod n → ℝ)
    (i : ZMod n) : centralSym m κ (i + (m : ZMod n)) = centralSym m κ i := by
  have hdouble : (i + (m : ZMod n)) + (m : ZMod n) = i := by
    have : ((2 * m : ℕ) : ZMod n) = 0 := by rw [← hn]; exact ZMod.natCast_self n
    have h2 : (m : ZMod n) + (m : ZMod n) = 0 := by
      have := this; push_cast at this; linear_combination this
    rw [add_assoc, h2, add_zero]
  rw [centralSym, centralSym, hdouble, add_comm (κ (i + (m : ZMod n)))]

/-- The central symmetrization of a positive profile is positive. -/
theorem centralSym_pos {m : ℕ} {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) (i : ZMod n) :
    0 < centralSym m κ i := by
  rw [centralSym]; exact div_pos (add_pos (hκ i) (hκ _)) two_pos

/-- Along the homotopy every curvature stays positive for `t ∈ [0,1]`
(`κ_t = (1-t)·κ⁰ + t·κ`, a convex combination of positives). -/
theorem curvHomotopy_pos {m : ℕ} {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : ZMod n) :
    0 < curvHomotopy m κ t i := by
  have hc : 0 < centralSym m κ i := centralSym_pos hκ i
  have hconv : curvHomotopy m κ t i = (1 - t) * centralSym m κ i + t * κ i := by
    rw [curvHomotopy]; ring
  rw [hconv]
  have h1 : 0 ≤ (1 - t) * centralSym m κ i := by
    apply mul_nonneg (by linarith) hc.le
  have h2 : 0 < t * κ i ∨ 0 < (1 - t) * centralSym m κ i := by
    rcases eq_or_lt_of_le ht0 with h | h
    · right; rw [← h]; simp only [sub_zero, one_mul]; exact hc
    · left; exact mul_pos h (hκ i)
  rcases h2 with h | h
  · linarith
  · have : 0 ≤ t * κ i := mul_nonneg ht0 (hκ i).le
    linarith

/-- The homotopy is jointly continuous in `(t, i)`, in particular continuous in
`t` for each fixed vertex (affine in `t`). -/
theorem continuous_curvHomotopy (m : ℕ) (κ : ZMod n → ℝ) (i : ZMod n) :
    Continuous (fun t : ℝ => curvHomotopy m κ t i) := by
  unfold curvHomotopy; fun_prop

/-! ### The generalized anchor path `curvPath` (`def:curv_path`, @080)

The @079 refutation (`closingGap_zero_iff_fails_of_const` below) shows the
hardwired anchor `κ⁰ = centralSym m κ` degenerates on the class
`{κ : κ⁰ constant}` — which contains genuine DFV profiles (constants plus odd
half-period harmonics). The fix is to generalize the homotopy to an *arbitrary*
positive anchor `κˢ`: positivity along the path is free by convexity, and the
half-period symmetry of the anchor is carried as an explicit hypothesis exactly
where it is used (the `t = 0` anchor lemmas), not baked into the path. The
central-symmetrization homotopy is the instance `κˢ = centralSym m κ`
(`curvHomotopy_eq_curvPath`). -/

/-- The generalized anchor path `κ_t = κˢ + t·(κ − κˢ)` from an arbitrary
anchor profile `κˢ` (`t = 0`) to the target `κ` (`t = 1`) (`def:curv_path`).
Affine — hence continuous — in `t` (`continuous_curvPath`); positive for
`t ∈ [0,1]` when both endpoints are (`curvPath_pos`). -/
noncomputable def curvPath (κs κ : ZMod n → ℝ) (t : ℝ) : ZMod n → ℝ :=
  fun i => κs i + t * (κ i - κs i)

@[simp] lemma curvPath_zero (κs κ : ZMod n → ℝ) : curvPath κs κ 0 = κs := by
  funext i; simp [curvPath]

@[simp] lemma curvPath_one (κs κ : ZMod n → ℝ) : curvPath κs κ 1 = κ := by
  funext i; simp [curvPath]

/-- The central-symmetrization homotopy of `def:curv_homotopy` is the
`κˢ = centralSym m κ` instance of the generalized anchor path. -/
theorem curvHomotopy_eq_curvPath (m : ℕ) (κ : ZMod n → ℝ) :
    curvHomotopy m κ = curvPath (centralSym m κ) κ := rfl

/-- Along the generalized anchor path every curvature stays positive for
`t ∈ [0,1]` (`κ_t = (1−t)·κˢ + t·κ`, a convex combination of positives). -/
theorem curvPath_pos {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : ZMod n) :
    0 < curvPath κs κ t i := by
  have hconv : curvPath κs κ t i = (1 - t) * κs i + t * κ i := by
    rw [curvPath]; ring
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [hconv, h]; simpa using hκ i
  · rw [hconv]
    have h1 : 0 < (1 - t) * κs i := mul_pos (by linarith) (hκs i)
    have h2 : 0 ≤ t * κ i := mul_nonneg ht0 (hκ i).le
    linarith

/-- For each fixed vertex the generalized anchor path is continuous (indeed
affine) in `t`. -/
theorem continuous_curvPath (κs κ : ZMod n → ℝ) (i : ZMod n) :
    Continuous (fun t : ℝ => curvPath κs κ t i) := by
  unfold curvPath; fun_prop

/-! ### Reaching the turning value: the chart's wall value and surjectivity

For `def:closing_2cell` the chart base `s⁰_j` (and its antisymmetric
perturbation) must be an achievable turning value, i.e.\ lie in the image
`chartMap p q '' Ioo 0 (2 / max p q)`. The supremum of that image is the *wall
value* `β = chartMap p q (2 / max p q) = π/2 + arcsin(min/max) > π/2`, so any
`s ∈ (0, β)` — in particular any `s ∈ (0, π/2]` — is achieved. -/

/-- The turning contribution at the moderate-arc wall exceeds `π/2`: one of the
two `arcsin` arguments is `1` (contributing `arcsin 1 = π/2`) and the other is
`min/max > 0` (contributing a strictly positive `arcsin`). This is the strict
lower bound on the chart's supremum `β`. -/
theorem pi_div_two_lt_chartMap_wall {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.pi / 2 < chartMap p q (2 / max p q) := by
  rw [chartMap]
  rcases le_total q p with h | h
  · rw [max_eq_left h]
    have e1 : p * (2 / p) / 2 = 1 := by field_simp
    have e3 : 0 < Real.arcsin (q * (2 / p) / 2) := Real.arcsin_pos.2 (by positivity)
    rw [e1, Real.arcsin_one]; linarith
  · rw [max_eq_right h]
    have e1 : q * (2 / q) / 2 = 1 := by field_simp
    have e3 : 0 < Real.arcsin (p * (2 / q) / 2) := Real.arcsin_pos.2 (by positivity)
    rw [e1, Real.arcsin_one]; linarith

/-- **Surjectivity of the single-edge chart.** Every turning value `s` strictly
between `0` and the wall value `chartMap p q (2 / max p q)` is achieved by some
moderate edge length: `s ∈ chartMap p q '' Ioo 0 (2 / max p q)`. By the
intermediate value theorem (`chartMap` is continuous with value `0` at `0`), an
interior length maps to `s`; it is interior since `s ≠ 0` and `s ≠ wall`. This is
the membership criterion that makes `chartInv` a genuine inverse at `s`. -/
theorem chartMap_mem_image {p q : ℝ} (hp : 0 < p) (_hq : 0 < q) {s : ℝ}
    (hs0 : 0 < s) (hs : s < chartMap p q (2 / max p q)) :
    s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) := by
  have hmax : 0 < max p q := lt_of_lt_of_le hp (le_max_left p q)
  have hdle : (0 : ℝ) ≤ 2 / max p q := by positivity
  have hcont : ContinuousOn (chartMap p q) (Set.Icc 0 (2 / max p q)) :=
    (chartMap_continuous p q).continuousOn
  have hsub := intermediate_value_Ioo hdle hcont
  have hmem : s ∈ Set.Ioo (chartMap p q 0) (chartMap p q (2 / max p q)) := by
    rw [chartMap_zero]; exact ⟨hs0, hs⟩
  exact hsub hmem

/-! ### The antisymmetric chart base (`def:closing_2cell`)

The chart base `s(z)` of the closing 2-cell: the constant turning value `2π/n`
perturbed antisymmetrically on two half-period pairs `{a, a+m}` and `{b, b+m}` by
`z = (u, v)`. The antisymmetry (`+u` at `a`, `−u` at `a+m`; likewise `b`) is
exactly what keeps `∑_j s(z)_j = 2π` **identically in `z`** (`sum_chartPerturb`),
so the turning constraint holds for free on the whole 2-cell — the affine
constraint of `def:turning_chart`. -/

/-- The half-period-antisymmetric chart base of `def:closing_2cell`: constant
`2π/n` with `±z.1` on the pair `{a, a+m}` and `±z.2` on the pair `{b, b+m}`. -/
noncomputable def chartPerturb (m : ℕ) (a b : ZMod n) (z : ℝ × ℝ) : ZMod n → ℝ :=
  fun j => 2 * Real.pi / n
    + ((if j = a then z.1 else 0) + (if j = a + (m : ZMod n) then -z.1 else 0))
    + ((if j = b then z.2 else 0) + (if j = b + (m : ZMod n) then -z.2 else 0))

/-- The antisymmetric chart base sums to `2π` identically in `z`: the constant
part gives `n · (2π/n) = 2π` and each antisymmetric pair `±z.i` cancels to `0`
(`Finset.sum_ite_eq'`). This is the "turning is kept for free" property of the
2-cell. -/
theorem sum_chartPerturb [NeZero n] (m : ℕ) (a b : ZMod n) (z : ℝ × ℝ) :
    ∑ j : ZMod n, chartPerturb m a b z j = 2 * Real.pi := by
  unfold chartPerturb
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp
  ring

/-- The antisymmetric perturbation moves each chart coordinate by at most
`|z.1| + |z.2|` away from the base value `2π/n` (each `±z.i` pair contributes
at most `|z.i|`, regardless of coincidences among the four indices). -/
theorem abs_chartPerturb_sub_le (m : ℕ) (a b : ZMod n) (z : ℝ × ℝ) (j : ZMod n) :
    |chartPerturb m a b z j - 2 * Real.pi / n| ≤ |z.1| + |z.2| := by
  have key : ∀ (c : ZMod n) (u : ℝ),
      |(if j = c then u else 0) + (if j = c + (m : ZMod n) then -u else 0)| ≤ |u| := by
    intro c u
    split_ifs <;> simp
  have hEq : chartPerturb m a b z j - 2 * Real.pi / n
      = ((if j = a then z.1 else 0) + (if j = a + (m : ZMod n) then -z.1 else 0))
        + ((if j = b then z.2 else 0) + (if j = b + (m : ZMod n) then -z.2 else 0)) := by
    rw [chartPerturb]; ring
  rw [hEq]
  exact (abs_add_le _ _).trans (add_le_add (key a z.1) (key b z.2))

/-- **Membership of the perturbed chart base among achievable turning values.**
For a positive profile `κ'` and edge `j`, if the perturbation size keeps the
chart value strictly positive (`hlow`) and strictly below the wall of edge `j`
(`hup`), then the value is achieved by a moderate edge length, so `chartInv` is
a genuine inverse there. -/
theorem chartPerturb_mem_image {κ' : ZMod n → ℝ} (hκ' : ∀ i, 0 < κ' i)
    (m : ℕ) (a b : ZMod n) {z : ℝ × ℝ} (j : ZMod n)
    (hlow : |z.1| + |z.2| < 2 * Real.pi / n)
    (hup : 2 * Real.pi / n + (|z.1| + |z.2|)
      < chartMap (κ' j) (κ' (j + 1)) (2 / max (κ' j) (κ' (j + 1)))) :
    chartPerturb m a b z j ∈
      chartMap (κ' j) (κ' (j + 1)) ''
        Set.Ioo (0 : ℝ) (2 / max (κ' j) (κ' (j + 1)))  := by
  have hd := abs_le.mp (abs_chartPerturb_sub_le m a b z j)
  exact chartMap_mem_image (hκ' j) (hκ' (j + 1))
    (by linarith [hd.1]) (by linarith [hd.2])

/-- For a fixed edge `j` the perturbed chart base is a continuous (indeed
affine) function of the perturbation parameter `z`. -/
theorem continuous_chartPerturb (m : ℕ) (a b : ZMod n) (j : ZMod n) :
    Continuous fun z : ℝ × ℝ => chartPerturb m a b z j := by
  unfold chartPerturb
  split_ifs <;> fun_prop

/-! ### The closing 2-cell `Φ` and its gap map `F` (`def:closing_2cell`)

`Φ t z` recovers, edge by edge, the lengths whose per-edge turning
contributions are the antisymmetrically perturbed chart base `chartPerturb`:
`Φ t z j = λ_{t,j}(s(z)_j)`. The turning constraint `turningSum = 2π` then
holds identically on the cell (`turningSum_closingCell`), and the gap map is
`F t z = closureGap κ_t (Φ t z)`. -/

/-- **The closing 2-cell `Φ`** (`def:closing_2cell`): at homotopy time
`t ∈ [0,1]` and perturbation `z`, edge `j` carries the length recovered by the
edge-length recovery map `chartInv` of the pair `(κ_t j, κ_t (j+1))` from the
perturbed chart value `chartPerturb m a b z j`. -/
noncomputable def closingCell (m : ℕ) (a b : ZMod n) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℝ × ℝ) :
    ZMod n → ℝ := fun j =>
  chartInv (curvPath_pos hκs hκ ht0 ht1 j)
    (curvPath_pos hκs hκ ht0 ht1 (j + 1)) (chartPerturb m a b z j)

/-- **The 2-cell keeps the turning constraint identically in `(t, z)`**: as long
as every perturbed chart value is achievable on its edge (`hmem`), the total
turning of `Φ t z` is exactly `2π`. Chain: the affine linearization
`turningSum_eq_sum_edgeChart`, the round-trip `chartMap_chartInv`, and the
antisymmetric cancellation `sum_chartPerturb`. -/
theorem turningSum_closingCell [NeZero n] (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {z : ℝ × ℝ}
    (hmem : ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) :
    turningSum (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z)
      = 2 * Real.pi := by
  rw [turningSum_eq_sum_edgeChart, ← sum_chartPerturb (n := n) m a b z]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [closingCell]
  exact chartMap_chartInv _ _ (hmem j)

/-- **The 2-cell lies in the moderate-arc domain of `κ_t`**: every recovered
length is positive and stays below the joint wall `2 / max` of its edge pair
(`chartInv_mem`), which yields both strict vertex walls of `ModerateArc`. -/
theorem moderateArc_closingCell (m : ℕ) (a b : ZMod n) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℝ × ℝ}
    (hmem : ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) :
    ModerateArc 0 (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z) := by
  have hκ' : ∀ i, 0 < curvPath κs κ t i := curvPath_pos hκs hκ ht0 ht1
  have hL : ∀ j : ZMod n, closingCell m a b hκs hκ ht0 ht1 z j ∈
      Set.Ioo (0 : ℝ)
        (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))) := by
    intro j
    simp only [closingCell]
    exact chartInv_mem _ _ (hmem j)
  have key : ∀ r M x : ℝ, 0 < r → r ≤ M → 0 < x → x < 2 / M → r * (x / 2) < 1 := by
    intro r M x hr hrM hx hxM
    have hM : 0 < M := lt_of_lt_of_le hr hrM
    have h1 : r * x ≤ M * x := mul_le_mul_of_nonneg_right hrM hx.le
    have h2 : M * x < M * (2 / M) := mul_lt_mul_of_pos_left hxM hM
    have h3 : M * (2 / M) = 2 := by field_simp
    linarith
  intro i
  refine ⟨(hL i).1, by simpa using half_pos (hL i).1, by simp, ?_, ?_⟩
  · rw [tK_zero, abs_of_pos (hκ' i)]
    have hprev := hL (i - 1)
    rw [show i - 1 + 1 = i by ring] at hprev
    exact key _ _ _ (hκ' i) (le_max_right _ _) hprev.1 hprev.2
  · rw [tK_zero, abs_of_pos (hκ' i)]
    exact key _ _ _ (hκ' i) (le_max_left _ _) (hL i).1 (hL i).2

/-- **The gap map `F`** of the closing 2-cell (`def:closing_2cell`):
`F t z = closureGap κ_t (Φ t z)`. Zeros of `F` are closed developments; the
degree argument of `sec:closure` tracks its boundary winding along the
homotopy. -/
noncomputable def closingGap (m : ℕ) (a b : ZMod n) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℝ × ℝ) : ℂ :=
  closureGap (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z)

/-! ### Joint continuity of the gap map `F` -/

/-- Project-local supplement: the closure gap is jointly continuous in the
curvature profile and the edge lengths — a finite composition of `arcsin`,
`Complex.exp`, sums, and products. This is the outer layer of the continuity
of `F` on `[0,1] × \overline{D}_ρ` (`def:closing_2cell`). -/
theorem continuous_closureGap :
    Continuous fun x : (ZMod n → ℝ) × (ZMod n → ℝ) => closureGap x.1 x.2 := by
  unfold closureGap vertexR2
  refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ ?_
  · exact Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_snd)
  · refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    refine Complex.continuous_ofReal.comp ?_
    unfold heading
    refine continuous_finsetSum _ fun k _ => ?_
    unfold turningAngle
    simp only [tK_zero]
    exact (Real.continuous_arcsin.comp (by fun_prop)).add
      (Real.continuous_arcsin.comp (by fun_prop))

/-- **Joint continuity of the edge-length recovery over a compact curvature
family.** For continuous positive curvature families `p q : T → ℝ` on a compact
Hausdorff `T`, the recovery `(τ, s) ↦ chartInv (hp τ) (hq τ) s` is jointly
continuous on the pairs whose value is achieved inside the common *normalized*
length window `x ∈ [c·(2/max), d·(2/max)]`, `0 < c ≤ d < 1`. The normalization
`y = x·max/2` makes the domain `Icc c d` parameter-independent, so the landed
`continuousOn_inv_family` applies to `g τ y = chartMap (p τ) (q τ) (y·2/max)`;
the original-scale recovery is the normalized inverse times the continuous
factor `2/max`. -/
theorem continuousOn_chartInv_family {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [T2Space T] {p q : T → ℝ} (hp : ∀ τ, 0 < p τ)
    (hq : ∀ τ, 0 < q τ) (hpc : Continuous p) (hqc : Continuous q)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hd : d < 1) :
    ContinuousOn (fun x : T × ℝ => chartInv (hp x.1) (hq x.1) x.2)
      {x : T × ℝ | x.2 ∈ chartMap (p x.1) (q x.1) ''
        Set.Icc (c * (2 / max (p x.1) (q x.1)))
                (d * (2 / max (p x.1) (q x.1)))} := by
  have hmax : ∀ τ, 0 < max (p τ) (q τ) := fun τ =>
    lt_of_lt_of_le (hp τ) (le_max_left _ _)
  have hone : ∀ τ : T, 2 / max (p τ) (q τ) * (max (p τ) (q τ) / 2) = 1 := by
    intro τ
    rw [div_mul_div_comm, mul_comm (max (p τ) (q τ)) 2,
      div_self (mul_ne_zero two_ne_zero (hmax τ).ne')]
  have hone' : ∀ τ : T, max (p τ) (q τ) / 2 * (2 / max (p τ) (q τ)) = 1 := by
    intro τ
    rw [div_mul_div_comm, mul_comm 2 (max (p τ) (q τ)),
      div_self (mul_ne_zero (hmax τ).ne' two_ne_zero)]
  set g : T → ℝ → ℝ :=
    fun τ y => chartMap (p τ) (q τ) (y * (2 / max (p τ) (q τ))) with hg
  set inv : T → ℝ → ℝ :=
    fun τ s => chartInv (hp τ) (hq τ) s * (max (p τ) (q τ) / 2) with hinv
  -- the normalized window maps into the moderate open length interval
  have hscale : ∀ τ, ∀ y ∈ Set.Icc c d,
      y * (2 / max (p τ) (q τ)) ∈ Set.Ioo (0 : ℝ) (2 / max (p τ) (q τ)) := by
    intro τ y hy
    have h2 : (0 : ℝ) < 2 / max (p τ) (q τ) := div_pos two_pos (hmax τ)
    refine ⟨mul_pos (lt_of_lt_of_le hc hy.1) h2, ?_⟩
    have := mul_lt_mul_of_pos_right (lt_of_le_of_lt hy.2 hd) h2
    simpa using this
  -- joint continuity of the normalized family
  have hgc : Continuous fun x : T × ℝ => g x.1 x.2 := by
    have hinner : Continuous fun x : T × ℝ => x.2 * (2 / max (p x.1) (q x.1)) :=
      continuous_snd.mul (continuous_const.div
        ((hpc.max hqc).comp continuous_fst) fun x => (hmax x.1).ne')
    simp only [hg, chartMap]
    exact (Real.continuous_arcsin.comp
        (((hpc.comp continuous_fst).mul hinner).div_const 2)).add
      (Real.continuous_arcsin.comp
        (((hqc.comp continuous_fst).mul hinner).div_const 2))
  -- injectivity on the common normalized window
  have hinj : ∀ τ, Set.InjOn (g τ) (Set.Icc c d) := by
    intro τ y₁ h₁ y₂ h₂ hEq
    simp only [hg] at hEq
    have := (chartMap_strictMonoOn (hp τ) (hq τ)).injOn
      (hscale τ y₁ h₁) (hscale τ y₂ h₂) hEq
    exact mul_right_cancel₀ (div_pos two_pos (hmax τ)).ne' this
  -- the normalized inverse is a two-sided inverse on the window's values
  have hval : ∀ τ (y : ℝ), y ∈ Set.Icc c d → inv τ (g τ y) = y := by
    intro τ y hy
    have hIx : chartInv (hp τ) (hq τ) (g τ y) = y * (2 / max (p τ) (q τ)) := by
      simp only [hg]
      exact chartInv_chartMap _ _ (hscale τ y hy)
    simp only [hinv, hIx]
    rw [mul_assoc, hone τ, mul_one]
  have hinv1 : ∀ τ s, s ∈ g τ '' Set.Icc c d → g τ (inv τ s) = s := by
    rintro τ s ⟨y, hy, rfl⟩
    rw [hval τ y hy]
  have hinv2 : ∀ τ s, s ∈ g τ '' Set.Icc c d → inv τ s ∈ Set.Icc c d := by
    rintro τ s ⟨y, hy, rfl⟩
    rw [hval τ y hy]; exact hy
  have hmain := continuousOn_inv_family (g := g) (a := c) (b := d)
    hgc hinj hinv1 hinv2
  -- back to the original scale: chartInv = (normalized inverse) · (2/max)
  have hfactor : Continuous fun x : T × ℝ => 2 / max (p x.1) (q x.1) :=
    continuous_const.div ((hpc.max hqc).comp continuous_fst)
      fun x => (hmax x.1).ne'
  have hfinal : ContinuousOn (fun x : T × ℝ => chartInv (hp x.1) (hq x.1) x.2)
      {x : T × ℝ | x.2 ∈ g x.1 '' Set.Icc c d} := by
    refine (hmain.mul hfactor.continuousOn).congr fun x _ => ?_
    simp only [hinv, Pi.mul_apply]
    rw [mul_assoc, hone' x.1, mul_one]
  -- identify the value set with the unnormalized image
  have hset : ∀ τ : T, g τ '' Set.Icc c d
      = chartMap (p τ) (q τ) ''
          Set.Icc (c * (2 / max (p τ) (q τ))) (d * (2 / max (p τ) (q τ))) := by
    intro τ
    have himg : (fun y : ℝ => y * (2 / max (p τ) (q τ))) '' Set.Icc c d
        = Set.Icc (c * (2 / max (p τ) (q τ))) (d * (2 / max (p τ) (q τ))) :=
      Set.image_mul_right_Icc hcd (div_pos two_pos (hmax τ)).le
    calc g τ '' Set.Icc c d
        = chartMap (p τ) (q τ) ''
            ((fun y : ℝ => y * (2 / max (p τ) (q τ))) '' Set.Icc c d) := by
          rw [Set.image_image]
      _ = _ := by rw [himg]
  have hsets : {x : T × ℝ | x.2 ∈ chartMap (p x.1) (q x.1) ''
        Set.Icc (c * (2 / max (p x.1) (q x.1)))
                (d * (2 / max (p x.1) (q x.1)))}
      = {x : T × ℝ | x.2 ∈ g x.1 '' Set.Icc c d} := by
    ext x
    simp only [Set.mem_setOf_eq, hset x.1]
  rw [hsets]
  exact hfinal

/-- **Joint continuity of the closing 2-cell, edge by edge.** On any
perturbation set `Z` whose chart values are achieved inside the common
normalized length window `[c·(2/max), d·(2/max)]` uniformly along the homotopy
(hypothesis `hwin` — the ρ-package of `def:closing_2cell`), the map
`(t, z) ↦ Φ(t,z)_j` is continuous on `[0,1] × Z`. -/
theorem continuousOn_closingCell_apply (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < 1) {Z : Set (ℝ × ℝ)} (j : ZMod n)
    (hwin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z ∈ Z, chartPerturb m a b z j ∈
      chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
        Set.Icc
          (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
          (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))) :
    ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        closingCell m a b hκs hκ x.1.2.1 x.1.2.2 x.2 j)
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z} := by
  have hfam := continuousOn_chartInv_family
    (p := fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvPath κs κ (↑τ) j)
    (q := fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvPath κs κ (↑τ) (j + 1))
    (fun τ => curvPath_pos hκs hκ τ.2.1 τ.2.2 j)
    (fun τ => curvPath_pos hκs hκ τ.2.1 τ.2.2 (j + 1))
    ((continuous_curvPath κs κ j).comp continuous_subtype_val)
    ((continuous_curvPath κs κ (j + 1)).comp continuous_subtype_val)
    hc hcd hd
  have hcomp : Continuous fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
      ((x.1, chartPerturb m a b x.2 j) : ↥(Set.Icc (0 : ℝ) 1) × ℝ) :=
    continuous_fst.prodMk ((continuous_chartPerturb m a b j).comp continuous_snd)
  have hmaps : Set.MapsTo
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        ((x.1, chartPerturb m a b x.2 j) : ↥(Set.Icc (0 : ℝ) 1) × ℝ))
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z}
      {x : ↥(Set.Icc (0 : ℝ) 1) × ℝ | x.2 ∈
        chartMap (curvPath κs κ (↑x.1) j) (curvPath κs κ (↑x.1) (j + 1)) ''
          Set.Icc
            (c * (2 / max (curvPath κs κ (↑x.1) j)
              (curvPath κs κ (↑x.1) (j + 1))))
            (d * (2 / max (curvPath κs κ (↑x.1) j)
              (curvPath κs κ (↑x.1) (j + 1))))} :=
    fun x hx => hwin (↑x.1) x.1.2.1 x.1.2.2 x.2 hx
  exact (hfam.comp hcomp.continuousOn hmaps).congr fun x _ => rfl

/-- **Joint continuity of the gap map `F` of the closing 2-cell**
(`def:closing_2cell`): under the same uniform window hypothesis (now for every
edge), `(t, z) ↦ F(t,z)` is continuous on `[0,1] × Z`. Composition of
`continuous_closureGap` with the per-edge continuity of `Φ` and the continuity
of the homotopy `κ_t`. -/
theorem continuousOn_closingGap (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < 1) {Z : Set (ℝ × ℝ)}
    (hwin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z ∈ Z, ∀ j : ZMod n,
      chartPerturb m a b z j ∈
        chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
          Set.Icc
            (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
            (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))) :
    ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        closingGap m a b hκs hκ x.1.2.1 x.1.2.2 x.2)
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z} := by
  have hpair : ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        ((curvPath κs κ (↑x.1), closingCell m a b hκs hκ x.1.2.1 x.1.2.2 x.2) :
          (ZMod n → ℝ) × (ZMod n → ℝ)))
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | x.2 ∈ Z} := by
    refine ContinuousOn.prodMk ?_ ?_
    · refine Continuous.continuousOn (continuous_pi fun i => ?_)
      exact (continuous_curvPath κs κ i).comp
        (continuous_subtype_val.comp continuous_fst)
    · refine continuousOn_pi.mpr fun j => ?_
      exact continuousOn_closingCell_apply m a b hκs hκ hc hcd hd j
        fun t ht0 ht1 z hz => hwin t ht0 ht1 z hz j
  exact (continuous_closureGap.comp_continuousOn hpair).congr fun x _ => rfl

/-! ### Existence of the uniform window (the ρ-package of `def:closing_2cell`)

By compactness of `[0,1]` the curvature ratios `min/max` of adjacent pairs are
uniformly bounded below along the homotopy, which produces a single normalized
window `[c, d] ⊂ (0,1)` and a radius `ρ > 0` such that every perturbed chart
value `chartPerturb z j` (`|z.1| + |z.2| ≤ ρ`) is achieved inside the window on
every edge, at every time. In normalized coordinates the wall obstruction
disappears: `chartMap p q (e·2/max) ∈ [arcsin e + arcsin(e·min/max), 2·arcsin e]`
uniformly in the pair. -/

/-- Upper bound for the chart at a normalized length: both `arcsin` arguments
are at most `e`, so `chartMap p q (e·(2/max)) ≤ 2·arcsin e`. -/
private lemma chartMap_norm_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {e : ℝ}
    (he : 0 ≤ e) : chartMap p q (e * (2 / max p q)) ≤ 2 * Real.arcsin e := by
  have hmax : 0 < max p q := lt_of_lt_of_le hp (le_max_left _ _)
  have harg : ∀ r : ℝ, 0 < r → r ≤ max p q → r * (e * (2 / max p q)) / 2 ≤ e := by
    intro r hr hrle
    have hEq : r * (e * (2 / max p q)) / 2 = e * (r / max p q) := by
      field_simp
    rw [hEq]
    calc e * (r / max p q) ≤ e * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hmax).mpr hrle) he
      _ = e := mul_one e
  rw [chartMap, two_mul]
  exact add_le_add
    (Real.monotone_arcsin (harg p hp (le_max_left _ _)))
    (Real.monotone_arcsin (harg q hq (le_max_right _ _)))

/-- Lower bound for the chart at a normalized length: one `arcsin` argument is
exactly `e` and the other is `e·(min/max) ≥ e·r`, so
`arcsin e + arcsin (e·r) ≤ chartMap p q (e·(2/max))` for any lower ratio bound
`r ≤ min p q / max p q`. -/
private lemma chartMap_norm_ge {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {e r : ℝ}
    (he : 0 ≤ e) (hr : r ≤ min p q / max p q) :
    Real.arcsin e + Real.arcsin (e * r) ≤ chartMap p q (e * (2 / max p q)) := by
  rcases le_total p q with h | h
  · have hmax : max p q = q := max_eq_right h
    have hmin : min p q = p := min_eq_left h
    rw [chartMap, hmax]
    have hq' : q ≠ 0 := hq.ne'
    have hEq : q * (e * (2 / q)) / 2 = e := by field_simp
    have hEp : p * (e * (2 / q)) / 2 = e * (p / q) := by field_simp
    rw [hEq, hEp]
    rw [hmax, hmin] at hr
    have h1 : Real.arcsin (e * r) ≤ Real.arcsin (e * (p / q)) :=
      Real.monotone_arcsin (mul_le_mul_of_nonneg_left hr he)
    linarith
  · have hmax : max p q = p := max_eq_left h
    have hmin : min p q = q := min_eq_right h
    rw [chartMap, hmax]
    have hp' : p ≠ 0 := hp.ne'
    have hEp : p * (e * (2 / p)) / 2 = e := by field_simp
    have hEq : q * (e * (2 / p)) / 2 = e * (q / p) := by field_simp
    rw [hEp, hEq]
    rw [hmax, hmin] at hr
    have h1 : Real.arcsin (e * r) ≤ Real.arcsin (e * (q / p)) :=
      Real.monotone_arcsin (mul_le_mul_of_nonneg_left hr he)
    linarith

/-- **Uniform lower bound on the adjacent curvature ratios along the
homotopy**: by compactness of `[0,1]` (and finiteness of the edge set) there is
`r > 0` with `r ≤ min(κ_t j, κ_t (j+1)) / max(κ_t j, κ_t (j+1))` for every
`t ∈ [0,1]` and every edge `j`. -/
theorem exists_ratio_bound [NeZero n] {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ j : ZMod n,
      r ≤ min (curvPath κs κ t j) (curvPath κs κ t (j + 1)) /
          max (curvPath κs κ t j) (curvPath κs κ t (j + 1)) := by
  have hA : ∀ j : ZMod n, ∃ rj : ℝ, 0 < rj ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      rj ≤ min (curvPath κs κ t j) (curvPath κs κ t (j + 1)) /
           max (curvPath κs κ t j) (curvPath κs κ t (j + 1)) := by
    intro j
    have hfc : ContinuousOn (fun t : ℝ =>
        min (curvPath κs κ t j) (curvPath κs κ t (j + 1)) /
          max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))
        (Set.Icc (0 : ℝ) 1) := by
      apply ContinuousOn.div
      · exact ((continuous_curvPath κs κ j).min
          (continuous_curvPath κs κ (j + 1))).continuousOn
      · exact ((continuous_curvPath κs κ j).max
          (continuous_curvPath κs κ (j + 1))).continuousOn
      · intro t ht
        exact (lt_of_lt_of_le (curvPath_pos hκs hκ ht.1 ht.2 j)
          (le_max_left _ _)).ne'
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.mpr zero_le_one) hfc
    refine ⟨_, ?_, fun t ht => isMinOn_iff.mp hmin t ht⟩
    exact div_pos
      (lt_min (curvPath_pos hκs hκ ht₀.1 ht₀.2 j)
        (curvPath_pos hκs hκ ht₀.1 ht₀.2 (j + 1)))
      (lt_of_lt_of_le (curvPath_pos hκs hκ ht₀.1 ht₀.2 j) (le_max_left _ _))
  choose r hr0 hrle using hA
  have : Nonempty (ZMod n) := ⟨0⟩
  refine ⟨Finset.univ.inf' Finset.univ_nonempty r, ?_, fun t ht0 ht1 j => ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr fun j _ => hr0 j
  · exact le_trans (Finset.inf'_le r (Finset.mem_univ j)) (hrle j t ⟨ht0, ht1⟩)

/-- **Existence of the uniform window and radius — the ρ-package of
`def:closing_2cell`.** For `n ≥ 4` and a positive profile `κ` there are a
radius `ρ > 0` (with `ρ < 2π/n`) and a normalized window `0 < c ≤ d < 1` such
that every perturbed chart value `chartPerturb m a b z j` with
`|z.1| + |z.2| ≤ ρ` is achieved inside the window
`[c·(2/max), d·(2/max)]` on every edge, at every homotopy time. This
discharges, in one stroke, the window hypotheses of `turningSum_closingCell`
and `moderateArc_closingCell` (via `Icc ⊆ Ioo`) and of
`continuousOn_closingCell_apply` / `continuousOn_closingGap`. The proof
combines the uniform ratio bound (`exists_ratio_bound`), the normalized chart
bounds (`chartMap_norm_le` / `chartMap_norm_ge`), and continuity of
`arcsin` at `1` to place `d` below `1` while clearing `π/2 + ρ` at the wall. -/
theorem exists_closingCell_window [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) :
    ∃ ρ c d : ℝ, 0 < ρ ∧ ρ < 2 * Real.pi / n ∧ 0 < c ∧ c ≤ d ∧ d < 1 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ →
        ∀ a b j : ZMod n, chartPerturb m a b z j ∈
          chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
            Set.Icc
              (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
              (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) := by
  obtain ⟨r, hr0, hrle⟩ := exists_ratio_bound hκs hκ
  have hπ := Real.pi_pos
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn0 : (0 : ℝ) < n := by linarith
  have hX : 0 < Real.pi / n := div_pos hπ hn0
  have hπn4 : Real.pi / n ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left hπ.le four_pos hn4'
  have hasr : 0 < Real.arcsin r := Real.arcsin_pos.2 hr0
  have h2X : 2 * Real.pi / n = 2 * (Real.pi / n) := mul_div_assoc 2 Real.pi n
  -- the radius
  set ρ : ℝ := min (Real.pi / n) (Real.arcsin r) / 2 with hρdef
  have hmin1 : min (Real.pi / n) (Real.arcsin r) ≤ Real.pi / n := min_le_left _ _
  have hmin2 : min (Real.pi / n) (Real.arcsin r) ≤ Real.arcsin r := min_le_right _ _
  have hρ0 : 0 < ρ := div_pos (lt_min hX hasr) two_pos
  have hρ2πn : ρ < 2 * Real.pi / n := by rw [h2X, hρdef]; linarith
  have hρar : ρ < Real.arcsin r := by rw [hρdef]; linarith
  -- the lower window endpoint c = sin θ, θ = π/n − ρ/2
  set θ : ℝ := Real.pi / n - ρ / 2 with hθdef
  have hθ0 : 0 < θ := by rw [hθdef, hρdef]; linarith
  have hθhalf : θ < Real.pi / 2 := by rw [hθdef]; linarith
  set c : ℝ := Real.sin θ with hcdef
  have hc0 : 0 < c := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)
  have hc1 : c < 1 := by
    have := Real.strictMonoOn_sin
      (a := θ) (b := Real.pi / 2)
      ⟨by linarith, hθhalf.le⟩ ⟨by linarith, le_refl _⟩ hθhalf
    simpa [Real.sin_pi_div_two] using this
  have harcc : Real.arcsin c = θ :=
    Real.arcsin_sin (by linarith) hθhalf.le
  -- the upper window endpoint d, via continuity of arcsin at 1
  have hh1 : Real.pi / 2 + ρ <
      Real.arcsin (1 : ℝ) + Real.arcsin ((1 : ℝ) * r) := by
    rw [Real.arcsin_one, one_mul]; linarith
  have hhc : Continuous fun x : ℝ => Real.arcsin x + Real.arcsin (x * r) :=
    Real.continuous_arcsin.add
      (Real.continuous_arcsin.comp (continuous_id.mul continuous_const))
  have hev : ∀ᶠ x in nhdsWithin 1 (Set.Iio (1 : ℝ)),
      Real.pi / 2 + ρ < Real.arcsin x + Real.arcsin (x * r) :=
    (hhc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually_const_lt hh1
  obtain ⟨d₀, hd₀1, hd₀⟩ := (eventually_mem_nhdsWithin.and hev).exists
  set d : ℝ := max d₀ c with hddef
  have hcd : c ≤ d := le_max_right _ _
  have hd1 : d < 1 := max_lt (Set.mem_Iio.mp hd₀1) hc1
  have hd0 : 0 ≤ d := le_trans hc0.le hcd
  have hhd : Real.pi / 2 + ρ < Real.arcsin d + Real.arcsin (d * r) := by
    have h1 : d₀ ≤ d := le_max_left _ _
    have h2 : Real.arcsin d₀ ≤ Real.arcsin d := Real.monotone_arcsin h1
    have h3 : Real.arcsin (d₀ * r) ≤ Real.arcsin (d * r) :=
      Real.monotone_arcsin (mul_le_mul_of_nonneg_right h1 hr0.le)
    linarith [hd₀]
  refine ⟨ρ, c, d, hρ0, hρ2πn, hc0, hcd, hd1, ?_⟩
  intro t ht0 ht1 z hz a b j
  have hp := curvPath_pos hκs hκ ht0 ht1 j
  have hq := curvPath_pos hκs hκ ht0 ht1 (j + 1)
  have hmax : 0 < max (curvPath κs κ t j) (curvPath κs κ t (j + 1)) :=
    lt_of_lt_of_le hp (le_max_left _ _)
  have hA : (0 : ℝ) < 2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)) :=
    div_pos two_pos hmax
  -- the perturbed value lies in [2π/n − ρ, 2π/n + ρ]
  have habs := abs_le.mp (abs_chartPerturb_sub_le m a b z j)
  -- lower endpoint clears the value from below
  have hlow : chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1))
      (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
      ≤ chartPerturb m a b z j := by
    have h1 := chartMap_norm_le hp hq hc0.le
    rw [harcc] at h1
    have h2θ : 2 * θ = 2 * Real.pi / n - ρ := by rw [hθdef, h2X]; ring
    linarith [habs.1]
  -- upper endpoint clears the value from above
  have hup : chartPerturb m a b z j ≤
      chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1))
        (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) := by
    have h1 := chartMap_norm_ge hp hq hd0 (hrle t ht0 ht1 j)
    have h2πn2 : 2 * Real.pi / n ≤ Real.pi / 2 := by rw [h2X]; linarith
    linarith [habs.2]
  exact chartMap_mem_image_Icc
    (mul_le_mul_of_nonneg_right hcd hA.le) ⟨hlow, hup⟩

/-- The compact window sits inside the open moderate length interval: window
membership (as produced by `exists_closingCell_window`) feeds the
`Ioo`-membership hypotheses of `turningSum_closingCell` and
`moderateArc_closingCell`. -/
theorem chartMap_image_window_subset {p q : ℝ} (hp : 0 < p) {c d : ℝ}
    (hc : 0 < c) (hd : d < 1) :
    chartMap p q '' Set.Icc (c * (2 / max p q)) (d * (2 / max p q)) ⊆
      chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) := by
  apply Set.image_mono
  intro x hx
  have hA : (0 : ℝ) < 2 / max p q :=
    div_pos two_pos (lt_of_lt_of_le hp (le_max_left _ _))
  refine ⟨lt_of_lt_of_le (mul_pos hc hA) hx.1, ?_⟩
  calc x ≤ d * (2 / max p q) := hx.2
    _ < 1 * (2 / max p q) := mul_lt_mul_of_pos_right hd hA
    _ = 2 / max p q := one_mul _

/-! ### The center of the 2-cell at `t = 0`: the closing anchor -/

/-- At the center `z = 0` the perturbed chart base is the constant `2π/n`. -/
@[simp] lemma chartPerturb_zero (m : ℕ) (a b : ZMod n) (j : ZMod n) :
    chartPerturb m a b (0, 0) j = 2 * Real.pi / n := by
  simp [chartPerturb]

/-- At `t = 0` (where `κ_0 = κˢ` is half-period symmetric by the anchor
hypothesis `hsym`) the center column `Φ(0, 0)` of the closing 2-cell is a
half-period-symmetric edge-length vector: opposite edges recover equal lengths
from the constant chart value `2π/n` because their curvature pairs coincide. -/
theorem closingCell_zero_symm (m : ℕ)
    (a b : ZMod n) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) (i : ZMod n) :
    closingCell m a b hκs hκ ht0 ht1 (0, 0) (i + (m : ZMod n))
      = closingCell m a b hκs hκ ht0 ht1 (0, 0) i := by
  have hκsym : ∀ i' : ZMod n,
      curvPath κs κ 0 (i' + (m : ZMod n)) = curvPath κs κ 0 i' := by
    intro i'
    simp only [curvPath_zero]
    exact hsym i'
  have hcongr : ∀ {p p' q q' : ℝ} (hp : 0 < p) (hq : 0 < q) (hp' : 0 < p')
      (hq' : 0 < q') (s : ℝ), p = p' → q = q' →
      chartInv hp hq s = chartInv hp' hq' s := by
    intro p p' q q' hp hq hp' hq' s hpe hqe
    subst hpe; subst hqe; rfl
  simp only [closingCell, chartPerturb_zero]
  exact hcongr _ _ _ _ _ (hκsym i)
    (by rw [show i + (m : ZMod n) + 1 = (i + 1) + (m : ZMod n) by ring]
        exact hκsym (i + 1))

/-- **The closing anchor `F(0, 0) = 0`** — the center of the 2-cell closes at
`t = 0` (`lem:central_symmetry_closes` applied to the half-period-symmetric
center column). This is the base point of the degree argument of
`sec:closure` and the (⇐) direction of `lem:closure_boundary_rigidity`. -/
theorem closingGap_center_eq_zero [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (a b : ZMod n) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1)
    (hmem : ∀ j : ZMod n, chartPerturb m a b ((0 : ℝ), (0 : ℝ)) j ∈
      chartMap (curvPath κs κ 0 j) (curvPath κs κ 0 (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvPath κs κ 0 j) (curvPath κs κ 0 (j + 1)))) :
    closingGap m a b hκs hκ ht0 ht1 (0, 0) = 0 := by
  have hκsym : ∀ i : ZMod n,
      curvPath κs κ 0 (i + (m : ZMod n)) = curvPath κs κ 0 i := by
    intro i
    simp only [curvPath_zero]
    exact hsym i
  exact central_symmetry_closes hn hκsym
    (closingCell_zero_symm m a b hκs hκ hsym ht0 ht1)
    (turningSum_closingCell m a b hκs hκ ht0 ht1 hmem)

/-- **The assembled closing 2-cell** (`def:closing_2cell`, complete package):
for `n = 2m ≥ 4` and a positive profile `κ` there is a radius `ρ > 0` such
that on `[0,1] × {|z.1| + |z.2| ≤ ρ}` the 2-cell `Φ = closingCell` (i) keeps
the turning constraint `turningSum = 2π` identically, (ii) stays in the
moderate-arc domain of `κ_t`, and (iii) has a continuous gap map `F`; moreover
(iv) the center closes at `t = 0`: `F(0,0) = 0`. This is the full analytic
input of the degree argument of `sec:closure` except the two winding leaves
(`lem:closure_boundary_rigidity`, `lem:closure_boundary_exclusion`). -/
theorem closingCell_package [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    (a b : ZMod n) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ t : ℝ, ∀ (ht0 : 0 ≤ t) (ht1 : t ≤ 1), ∀ z : ℝ × ℝ,
        |z.1| + |z.2| ≤ ρ →
        turningSum (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z)
            = 2 * Real.pi ∧
        ModerateArc 0 (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z)) ∧
      ContinuousOn
        (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
          closingGap m a b hκs hκ x.1.2.1 x.1.2.2 x.2)
        {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | |x.2.1| + |x.2.2| ≤ ρ} ∧
      ∀ (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1),
        closingGap m a b hκs hκ ht0 ht1 (0, 0) = 0 := by
  obtain ⟨ρ, c, d, hρ0, _hρ2πn, hc0, hcd, hd1, hwin⟩ :=
    exists_closingCell_window hn4 m hκs hκ
  have hmem : ∀ t : ℝ, ∀ (ht0 : 0 ≤ t) (ht1 : t ≤ 1), ∀ z : ℝ × ℝ,
      |z.1| + |z.2| ≤ ρ → ∀ j : ZMod n, chartPerturb m a b z j ∈
        chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
          Set.Ioo (0 : ℝ)
            (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))) :=
    fun t ht0 ht1 z hz j =>
      chartMap_image_window_subset (curvPath_pos hκs hκ ht0 ht1 j) hc0 hd1
        (hwin t ht0 ht1 z hz a b j)
  refine ⟨ρ, hρ0, ?_, ?_, ?_⟩
  · intro t ht0 ht1 z hz
    exact ⟨turningSum_closingCell m a b hκs hκ ht0 ht1 (hmem t ht0 ht1 z hz),
      moderateArc_closingCell m a b hκs hκ ht0 ht1 (hmem t ht0 ht1 z hz)⟩
  · exact continuousOn_closingGap m a b hκs hκ hc0 hcd hd1
      (Z := {z : ℝ × ℝ | |z.1| + |z.2| ≤ ρ})
      fun t ht0 ht1 z hz j => hwin t ht0 ht1 z hz a b j
  · intro ht0 ht1
    exact closingGap_center_eq_zero hn a b hκs hκ hsym ht0 ht1
      (hmem 0 ht0 ht1 (0, 0) (by simp [hρ0.le]))

/-! ### Constant curvature closes identically — the `t = 0` degeneracy of the
dispatched rigidity target

**Counterexample structure for `lem:closure_boundary_rigidity` as dispatched
@079.** For a CONSTANT positive profile `κ ≡ c` the development inscribes in a
circle of radius `1/c`: edge `j` is a chord subtending the central angle
`φ_j = 2·arcsin(c·ℓ_j/2)`, and the heading of edge `j` is — up to the constant
`arcsin(c·ℓ_{-1}/2)` — the accumulated central angle plus half the current one.
The edge vector therefore telescopes,
`ℓ_j·e^{iψ_j} = e^{iA₋₁}/(ic)·(e^{iΣ_{j+1}} − e^{iΣ_j})`, and whenever the
turning sum — which equals the total central angle — is `2π`, the development
closes REGARDLESS of the individual edge lengths
(`closureGap_eq_zero_of_const`). Consequently the gap map of the closing 2-cell
vanishes identically in `z` whenever the central symmetrization `κ⁰` is
constant (`closingGap_eq_zero_of_centralSym_const`), so the `t = 0` rigidity
statement `F(0,z) = 0 ↔ z = 0` is FALSE without a nondegeneracy hypothesis on
`κ⁰ = centralSym m κ` (`closingGap_zero_iff_fails_of_const`). This degeneracy
is not vacuous downstream: profiles `κ_i = c + (odd half-period harmonics)`
have `centralSym m κ ≡ c` and can satisfy the DFV pattern. -/

/-- The half-angle telescoping identity `e^{2xi} − 1 = 2i·(sin x)·e^{xi}` in
`ℂ` for a real angle `x`, in the exact `Complex.exp ((· : ℝ) * I)` packaging of
the development's edge vectors. -/
private lemma exp_ofReal_two_mul_I_sub_one (x : ℝ) :
    Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) - 1
      = 2 * Complex.I * (Real.sin x : ℂ) * Complex.exp ((x : ℝ) * Complex.I) := by
  have hpyth : (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (Real.sin_sq_add_cos_sq x)
  have h2 : ((2 * x : ℝ) : ℂ) * Complex.I
      = (x : ℝ) * Complex.I + (x : ℝ) * Complex.I := by push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  linear_combination hpyth - (Real.sin x : ℂ) ^ 2 * Complex.I_sq

/-- **Constant curvature closes identically** (the inscribed-polygon
telescope): for a constant profile `κ ≡ c ≠ 0`, any edge-length vector inside
the arcsin wall (`|c·(ℓ_i/2)| ≤ 1`) whose turning sum is `2π` develops to a
CLOSED polygon. This is the discrete "circles close for free" degeneracy: at
constant curvature the closure gap imposes no constraint beyond the turning
constraint, which the antisymmetric 2-cell keeps identically — so `t = 0`
rigidity FAILS whenever `centralSym m κ` is constant. -/
theorem closureGap_eq_zero_of_const [NeZero n] {c : ℝ} (hc : c ≠ 0)
    {ℓ : ZMod n → ℝ} (hwall : ∀ i : ZMod n, |c * (ℓ i / 2)| ≤ 1)
    (hT : turningSum (fun _ => c) ℓ = 2 * Real.pi) :
    closureGap (fun _ => c) ℓ = 0 := by
  classical
  set A : ZMod n → ℝ := fun i => Real.arcsin (c * (ℓ i / 2)) with hA
  have hθ : ∀ i : ZMod n, turningAngle 0 (fun _ => c) ℓ i = A (i - 1) + A i := by
    intro i
    simp only [turningAngle, tK_zero, hA]
  have hstep : ∀ j : ℕ, heading (fun _ => c) ℓ (j + 1)
      = heading (fun _ => c) ℓ j
        + turningAngle 0 (fun _ => c) ℓ ((j + 1 : ℕ) : ZMod n) := by
    intro j
    unfold heading
    exact Finset.sum_range_succ _ (j + 1)
  -- the heading partial-sum formula `ψ_j = A₋₁ + 2·Σ_{i<j} A_i + A_j`
  have hhead : ∀ j : ℕ, heading (fun _ => c) ℓ j
      = A (-1) + 2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n)
        + A ((j : ℕ) : ZMod n) := by
    intro j
    induction j with
    | zero =>
      unfold heading
      simp [hθ, zero_sub]
    | succ j ih =>
      rw [hstep j, ih, hθ]
      have hcast : ((j + 1 : ℕ) : ZMod n) - 1 = ((j : ℕ) : ZMod n) := by
        push_cast; ring
      rw [hcast, Finset.sum_range_succ]
      ring
  -- per-edge telescoping against the central-angle partial sums
  set g : ℕ → ℂ := fun j =>
    Complex.exp (((2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n) : ℝ) : ℂ)
      * Complex.I) with hg
  set C : ℂ := Complex.exp ((A (-1) : ℂ) * Complex.I) / ((c : ℂ) * Complex.I)
    with hC
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hcI : (c : ℂ) * Complex.I ≠ 0 := mul_ne_zero hc' Complex.I_ne_zero
  have hterm : ∀ j : ℕ, (ℓ ((j : ℕ) : ZMod n) : ℂ)
      * Complex.exp ((heading (fun _ => c) ℓ j : ℂ) * Complex.I)
      = C * (g (j + 1) - g j) := by
    intro j
    have hsin : Real.sin (A ((j : ℕ) : ZMod n))
        = c * (ℓ ((j : ℕ) : ZMod n) / 2) := by
      have h := abs_le.mp (hwall ((j : ℕ) : ZMod n))
      rw [hA]
      exact Real.sin_arcsin h.1 h.2
    have hgdiff : g (j + 1) - g j
        = Complex.exp (((2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n) : ℝ) : ℂ)
            * Complex.I)
          * (Complex.exp (((2 * A ((j : ℕ) : ZMod n) : ℝ) : ℂ) * Complex.I) - 1) := by
      simp only [hg, Finset.sum_range_succ]
      rw [show (2 * (∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n)
            + A ((j : ℕ) : ZMod n)) : ℝ)
          = 2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n)
            + 2 * A ((j : ℕ) : ZMod n) from by ring]
      push_cast
      rw [add_mul, Complex.exp_add]
      ring
    rw [hgdiff, exp_ofReal_two_mul_I_sub_one, hsin, hhead j]
    have hexp : ((A (-1) + 2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n)
          + A ((j : ℕ) : ZMod n) : ℝ) : ℂ) * Complex.I
        = (A (-1) : ℂ) * Complex.I
          + ((2 * ∑ i ∈ Finset.range j, A ((i : ℕ) : ZMod n) : ℝ) : ℂ) * Complex.I
          + (A ((j : ℕ) : ZMod n) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hexp, Complex.exp_add, Complex.exp_add, hC]
    push_cast
    field_simp
  -- the total central angle is the turning sum
  have hSigma : (2 * ∑ i ∈ Finset.range n, A ((i : ℕ) : ZMod n) : ℝ)
      = 2 * Real.pi := by
    have h1 := turningSum_eq_sum_edgeChart (n := n) (fun _ => c) ℓ
    rw [hT] at h1
    have h2 : ∀ j : ZMod n, chartMap c c (ℓ j) = 2 * A j := by
      intro j
      simp only [chartMap, hA, mul_div_assoc]
      ring
    rw [Finset.sum_congr (rfl : (Finset.univ : Finset (ZMod n)) = Finset.univ)
      fun j _ => h2 j, ← Finset.mul_sum] at h1
    have h3 := sum_range_natCast_add A 0
    simp only [zero_add] at h3
    rw [h3]
    linarith
  -- assemble and telescope
  unfold closureGap vertexR2
  rw [Finset.sum_congr (rfl : Finset.range n = Finset.range n)
    fun j _ => hterm j, ← Finset.mul_sum, Finset.sum_range_sub g n]
  have hgn : g n = 1 := by
    simp only [hg, hSigma]
    push_cast
    exact Complex.exp_two_pi_mul_I
  have hg0 : g 0 = 1 := by
    simp [hg]
  rw [hgn, hg0, sub_self, mul_zero]

/- USER (2026-07-14): the "handle the constant-κ⁰ class by a direct base-case,
   closure is free" route is NOT the free win it looks like — read before
   attempting it.
   • The class here is `centralSym m κ ≡ c`, i.e. `κ_{i+m} = 2c − κ_i`: the
     TARGET κ is half-period-ODD about c. The free-closure lemma
     `central_symmetry_closes` (Closing.lean) requires half-period-EVEN
     curvature `κ(i+m) = κ(i)`. It applies to the ANCHOR κ⁰ (a circle), NOT to
     the target κ. So "trivially closes to a circle" is about the t=0 anchor
     only; it does NOT hand you a `RealizesR2 κ` witness for the non-constant
     target.
   • Here `F(0,·) ≡ 0` on the whole window (this lemma), so the z-Jacobian
     columns `C_a = C_b = 0` and `Im(conj C_a · C_b) ≠ 0` fails by
     construction — neither the winding argument nor a plain IFT-in-z continues
     the branch. A direct base-case must instead go through the HOMOTOPY
     direction: `F(t,z) = t·G(z) + O(t²)` with `G := ∂_t F(0,·)` (a NEW object,
     not the landed z-derivative `anchorGapDeriv`), solve `G(z*) = 0` in the
     2-DOF fiber, check `∂_z G(z*)` nonsingular, IFT on `F(t,z)/t`, then redo
     ModerateArc + IsSimplePolygon along the branch. Real second-order work; it
     reuses NONE of the landed C_a/C_b machinery.
   • The @080 bump-anchor selector (κˢ = c + δw non-constant) is the cheaper
     finish: it restores C_a,C_b ≠ 0 and reuses all landed z-Jacobian lemmas,
     paying only the two-level-witness combinatorics. Prefer it unless the
     explicit goal is to eliminate that combinatorics. -/
/-- At `t = 0` with CONSTANT central symmetrization the gap map vanishes at
EVERY point of the 2-cell, not only at the center: the inscribed-polygon
degeneracy transported to the closing 2-cell. (Compare
`closingGap_center_eq_zero`, which needs no constancy but only covers
`z = 0`.) No `n = 2m` hypothesis is needed — constancy alone degenerates the
gap. -/
theorem closingGap_eq_zero_of_centralSym_const [NeZero n] (m : ℕ)
    (a b : ZMod n) {κ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) {c : ℝ}
    (hconst : ∀ i, centralSym m κ i = c)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) {z : ℝ × ℝ}
    (hmem : ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (curvHomotopy m κ 0 j) (curvHomotopy m κ 0 (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvHomotopy m κ 0 j) (curvHomotopy m κ 0 (j + 1)))) :
    closingGap m a b (centralSym_pos (m := m) hκ) hκ ht0 ht1 z = 0 := by
  have hc0 : 0 < c := by
    have := centralSym_pos (m := m) hκ 0
    rwa [hconst 0] at this
  have hfun : curvPath (centralSym m κ) κ 0 = fun _ => c := by
    funext i
    rw [curvPath_zero]
    exact hconst i
  have hMA := moderateArc_closingCell m a b (centralSym_pos (m := m) hκ) hκ
    ht0 ht1 hmem
  have hT := turningSum_closingCell m a b (centralSym_pos (m := m) hκ) hκ
    ht0 ht1 hmem
  rw [hfun] at hMA hT
  have hwall : ∀ i : ZMod n,
      |c * (closingCell m a b (centralSym_pos (m := m) hκ) hκ ht0 ht1 z i / 2)|
        ≤ 1 := by
    intro i
    have h1 := (hMA i).2.2.2.2
    simp only [tK_zero] at h1
    have hpos : 0 < closingCell m a b (centralSym_pos (m := m) hκ) hκ
        ht0 ht1 z i := (hMA i).1
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ)
      < closingCell m a b (centralSym_pos (m := m) hκ) hκ ht0 ht1 z i / 2)]
    exact le_of_lt h1
  unfold closingGap
  rw [hfun]
  exact closureGap_eq_zero_of_const hc0.ne' hwall hT

/-- **The `t = 0` rigidity target is degenerate for constant profiles**: for
`κ ≡ c > 0` (whose central symmetrization is again `≡ c`) there is a positive
radius on which the gap map `F(0,·)` of the closing 2-cell vanishes
IDENTICALLY in `z`. -/
theorem closingGap_const_profile_eq_zero [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {c : ℝ} (hc : 0 < c)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ →
      closingGap (κ := fun _ => c) m a b
        (centralSym_pos (m := m) fun _ => hc) (fun _ => hc) ht0 ht1 z = 0 := by
  obtain ⟨ρ, c₁, d₁, hρ0, _hρπ, hc₁, hcd₁, hd₁, hwin⟩ :=
    exists_closingCell_window hn4 m (κ := fun _ => c)
      (centralSym_pos (m := m) fun _ => hc) (fun _ => hc)
  refine ⟨ρ, hρ0, fun z hz => ?_⟩
  have hconst : ∀ i : ZMod n, centralSym m (fun _ => c) i = c := by
    intro i
    simp [centralSym]
  refine closingGap_eq_zero_of_centralSym_const m a b _ hconst ht0 ht1 ?_
  intro j
  exact chartMap_image_window_subset (curvHomotopy_pos (fun _ => hc) ht0 ht1 j)
    hc₁ hd₁ (hwin 0 ht0 ht1 z hz a b j)

/-- **Refutation of the dispatched `t = 0` rigidity iff** (`closingGap_zero_iff`
as specified @079, `lem:closure_boundary_rigidity`): for a constant positive
profile — with the perturbed half-pairs `a, b` arbitrary, in particular as
distinct as desired — EVERY radius contains a NONZERO `z` with `F(0,z) = 0`.
Positivity and pair-distinctness therefore do not suffice; a correct rigidity
statement must carry a nondegeneracy hypothesis on `κ⁰ = centralSym m κ`
(non-constancy at the very least). -/
theorem closingGap_zero_iff_fails_of_const [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {c : ℝ} (hc : 0 < c)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) :
    ∀ ρ' : ℝ, 0 < ρ' → ∃ z : ℝ × ℝ, z ≠ 0 ∧ |z.1| + |z.2| ≤ ρ' ∧
      closingGap (κ := fun _ => c) m a b
        (centralSym_pos (m := m) fun _ => hc) (fun _ => hc) ht0 ht1 z = 0 := by
  obtain ⟨ρ, hρ0, hall⟩ := closingGap_const_profile_eq_zero hn4 m a b hc ht0 ht1
  intro ρ' hρ'
  have hmin : 0 < min ρ ρ' := lt_min hρ0 hρ'
  have habs : |min ρ ρ' / 2| + |(0 : ℝ)| = min ρ ρ' / 2 := by
    rw [abs_zero, add_zero, abs_of_pos (by linarith : (0 : ℝ) < min ρ ρ' / 2)]
  refine ⟨(min ρ ρ' / 2, 0), ?_, ?_, hall _ ?_⟩
  · intro hEq
    have h1 : min ρ ρ' / 2 = 0 := by
      simpa using congrArg Prod.fst hEq
    linarith
  · change |min ρ ρ' / 2| + |(0 : ℝ)| ≤ ρ'
    rw [habs]
    have := min_le_right ρ ρ'
    linarith
  · change |min ρ ρ' / 2| + |(0 : ℝ)| ≤ ρ
    rw [habs]
    have := min_le_left ρ ρ'
    linarith

/-- Monotonicity of the uniform window in the radius: the window package of
`exists_closingCell_window` restricts to any smaller radius `ρ' ≤ ρ` — the
sanctioned shrinking of `ρ` in `def:closing_2cell`
(`lem:closure_boundary_rigidity` licenses proving rigidity on a possibly
smaller ball). -/
theorem closingCell_window_mono (m : ℕ) {κs κ : ZMod n → ℝ}
    {c d ρ ρ' : ℝ} (hρ' : ρ' ≤ ρ)
    (hwin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ →
      ∀ a b j : ZMod n, chartPerturb m a b z j ∈
        chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
          Set.Icc
            (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
            (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ' →
      ∀ a b j : ZMod n, chartPerturb m a b z j ∈
        chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
          Set.Icc
            (c * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1))))
            (d * (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) :=
  fun t ht0 ht1 z hz => hwin t ht0 ht1 z (hz.trans hρ')

/-- **The heading advance over an index block, in chart form** — exact and
hypothesis-free: `ψ_{j+k} − ψ_j` equals the sum of the per-edge chart values
over the block's `k` edges plus the boundary half-turn correction
`P_{j+k} − P_j`, where `P_e = arcsin(κ_e·(ℓ_e/2))` is the tail half-turn of
edge `e`. (Telescoping of `θ_i = Q_{i-1} + P_i` against
`s_e = P_e + Q_e = chartMap`.) With `k = m` on the closing 2-cell this
expresses the opposite-heading defect `ψ_{j+m} − ψ_j − π` through the
antisymmetric chart perturbation and the two boundary half-turns alone — the
exact paired-edge splitting that any corrected `t = 0` rigidity analysis
(nondegenerate `κ⁰`) starts from. -/
theorem heading_add_eq_chartBlock (κ ℓ : ZMod n → ℝ) (j k : ℕ) :
    heading κ ℓ (j + k) = heading κ ℓ j
      + ∑ e ∈ Finset.range k, chartMap (κ ((j + e : ℕ) : ZMod n))
          (κ (((j + e : ℕ) : ZMod n) + 1)) (ℓ ((j + e : ℕ) : ZMod n))
      + Real.arcsin (κ ((j + k : ℕ) : ZMod n) * (ℓ ((j + k : ℕ) : ZMod n) / 2))
      - Real.arcsin (κ ((j : ℕ) : ZMod n) * (ℓ ((j : ℕ) : ZMod n) / 2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show j + (k + 1) = j + k + 1 from by ring]
    have hstep : heading κ ℓ (j + k + 1)
        = heading κ ℓ (j + k)
          + turningAngle 0 κ ℓ ((j + k + 1 : ℕ) : ZMod n) := by
      unfold heading
      exact Finset.sum_range_succ _ (j + k + 1)
    have hθ : turningAngle 0 κ ℓ ((j + k + 1 : ℕ) : ZMod n)
        = Real.arcsin (κ ((j + k + 1 : ℕ) : ZMod n)
            * (ℓ ((j + k : ℕ) : ZMod n) / 2))
          + Real.arcsin (κ ((j + k + 1 : ℕ) : ZMod n)
            * (ℓ ((j + k + 1 : ℕ) : ZMod n) / 2)) := by
      have hcast : ((j + k + 1 : ℕ) : ZMod n) - 1 = ((j + k : ℕ) : ZMod n) := by
        push_cast; ring
      simp only [turningAngle, tK_zero, hcast]
    have hchart : chartMap (κ ((j + k : ℕ) : ZMod n))
        (κ (((j + k : ℕ) : ZMod n) + 1)) (ℓ ((j + k : ℕ) : ZMod n))
        = Real.arcsin (κ ((j + k : ℕ) : ZMod n)
            * (ℓ ((j + k : ℕ) : ZMod n) / 2))
          + Real.arcsin (κ ((j + k + 1 : ℕ) : ZMod n)
            * (ℓ ((j + k : ℕ) : ZMod n) / 2)) := by
      have hcast : ((j + k : ℕ) : ZMod n) + 1 = ((j + k + 1 : ℕ) : ZMod n) := by
        push_cast; ring
      rw [chartMap, hcast]
      simp only [mul_div_assoc]
    rw [hstep, ih, Finset.sum_range_succ, hθ, hchart]
    ring

/-- Any block of `m` consecutive lifted indices (`n = 2m`) hits the antipodal
pair `{x, x + m}` exactly once, counting both members: the two half-blocks of a
full period partition it, and shifting a block by `m` swaps the two members of
the pair. -/
lemma sum_ite_pair_half [NeZero n] {m : ℕ} (hn : n = 2 * m) (x : ZMod n)
    (j : ℕ) :
    ((∑ e ∈ Finset.range m, if ((j + e : ℕ) : ZMod n) = x then (1 : ℕ) else 0)
      + ∑ e ∈ Finset.range m,
          if ((j + e : ℕ) : ZMod n) = x + (m : ZMod n) then (1 : ℕ) else 0)
      = 1 := by
  classical
  have hmm : (m : ZMod n) + (m : ZMod n) = 0 := by
    have h : ((2 * m : ℕ) : ZMod n) = 0 := by rw [← hn]; exact ZMod.natCast_self n
    push_cast at h
    linear_combination h
  have hfull : (∑ e ∈ Finset.range (m + m),
      if ((j + e : ℕ) : ZMod n) = x then (1 : ℕ) else 0) = 1 := by
    rw [show m + m = n from by rw [hn]; ring,
      sum_range_natCast_add (fun i => if i = x then (1 : ℕ) else 0) j]
    simp
  rw [Finset.sum_range_add] at hfull
  have hsecond : ∀ e : ℕ,
      (if ((j + (m + e) : ℕ) : ZMod n) = x then (1 : ℕ) else 0)
      = if ((j + e : ℕ) : ZMod n) = x + (m : ZMod n) then (1 : ℕ) else 0 := by
    intro e
    have hcast : ((j + (m + e) : ℕ) : ZMod n)
        = ((j + e : ℕ) : ZMod n) + (m : ZMod n) := by
      push_cast; ring
    rw [hcast]
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · rw [← h, add_assoc, hmm, add_zero]
    · rw [h, add_assoc, hmm, add_zero]
  rw [Finset.sum_congr (rfl : Finset.range m = Finset.range m)
    fun e _ => hsecond e] at hfull
  exact hfull

/-- **The chart-perturbation sum over a half-period block is explicitly
affine**: on the closing 2-cell the perturbed chart values of any `m`
consecutive edges (`n = 2m`) sum to `π + ε_a·u + ε_b·v` with signs
`ε_a, ε_b ∈ {±1}` recording which member of each antipodal pair the block
contains. Combined with `heading_add_eq_chartBlock` at `k = m` and the chart
round-trip `chartMap_chartInv`, this makes the opposite-heading defect
`ψ_{j+m} − ψ_j − π` of the 2-cell an explicit affine function of `z` plus two
boundary half-turn corrections — the exact splitting behind any corrected
(nondegenerate-`κ⁰`) `t = 0` rigidity analysis. -/
theorem sum_chartPerturb_block [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (a b : ZMod n) (z : ℝ × ℝ) (j : ℕ) :
    ∃ εa εb : ℝ, (εa = 1 ∨ εa = -1) ∧ (εb = 1 ∨ εb = -1) ∧
      ∑ e ∈ Finset.range m, chartPerturb m a b z ((j + e : ℕ) : ZMod n)
        = Real.pi + εa * z.1 + εb * z.2 := by
  classical
  have hm : m ≠ 0 := fun h => NeZero.ne n (by rw [hn, h, mul_zero])
  have hcastS : ∀ y : ZMod n,
      (∑ e ∈ Finset.range m, if ((j + e : ℕ) : ZMod n) = y then (1 : ℝ) else 0)
      = ((∑ e ∈ Finset.range m,
          if ((j + e : ℕ) : ZMod n) = y then (1 : ℕ) else 0 : ℕ) : ℝ) := by
    intro y
    push_cast
    rfl
  have hsign : ∀ x : ZMod n, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ((∑ e ∈ Finset.range m, if ((j + e : ℕ) : ZMod n) = x then (1 : ℝ) else 0)
        - ∑ e ∈ Finset.range m,
            if ((j + e : ℕ) : ZMod n) = x + (m : ZMod n) then (1 : ℝ) else 0)
        = ε := by
    intro x
    have hp := sum_ite_pair_half hn x j
    rcases Nat.add_eq_one_iff.mp hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨-1, Or.inr rfl, by rw [hcastS, hcastS, h1, h2]; norm_num⟩
    · exact ⟨1, Or.inl rfl, by rw [hcastS, hcastS, h1, h2]; norm_num⟩
  obtain ⟨εa, hεa, hSa⟩ := hsign a
  obtain ⟨εb, hεb, hSb⟩ := hsign b
  refine ⟨εa, εb, hεa, hεb, ?_⟩
  have hfac : ∀ (w : ℝ) (y : ZMod n),
      (∑ e ∈ Finset.range m, if ((j + e : ℕ) : ZMod n) = y then w else 0)
      = w * ∑ e ∈ Finset.range m,
          if ((j + e : ℕ) : ZMod n) = y then (1 : ℝ) else 0 := by
    intro w y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  have hconst : ∑ _e ∈ Finset.range m, (2 * Real.pi / n : ℝ) = Real.pi := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hn]
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    push_cast
    field_simp
  simp only [chartPerturb, Finset.sum_add_distrib]
  rw [hconst, hfac z.1 a, hfac (-z.1) (a + (m : ZMod n)), hfac z.2 b,
    hfac (-z.2) (b + (m : ZMod n))]
  linear_combination z.1 * hSa + z.2 * hSb

/-- **The exact opposite-heading defect of the closing 2-cell** (all homotopy
times `t`, all `z` in the window): the heading advance over a half-period is
`π + ε_a·u + ε_b·v` (signs `±1` from `sum_chartPerturb_block`) plus the two
boundary half-turn corrections. At `z = 0` and `t = 0` the correction terms
cancel by half-period symmetry and this recovers `heading_add_half`; in
general it is the exact (non-linearized) formula for the defect `γ_j` in the
paired-edge splitting
`F = ∑_{j<m} e^{iψ_j}(ℓ_j − ℓ_{j+m}·e^{iγ_j})` of the corrected `t = 0`
rigidity analysis and of any boundary-exclusion estimate. -/
theorem heading_closingCell_add_half [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (a b : ZMod n) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℝ × ℝ}
    (hmem : ∀ i : ZMod n, chartPerturb m a b z i ∈
      chartMap (curvPath κs κ t i) (curvPath κs κ t (i + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvPath κs κ t i) (curvPath κs κ t (i + 1))))
    (j : ℕ) :
    ∃ εa εb : ℝ, (εa = 1 ∨ εa = -1) ∧ (εb = 1 ∨ εb = -1) ∧
      heading (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z) (j + m)
        = heading (curvPath κs κ t) (closingCell m a b hκs hκ ht0 ht1 z) j
          + Real.pi + εa * z.1 + εb * z.2
          + Real.arcsin (curvPath κs κ t ((j + m : ℕ) : ZMod n)
              * (closingCell m a b hκs hκ ht0 ht1 z ((j + m : ℕ) : ZMod n) / 2))
          - Real.arcsin (curvPath κs κ t ((j : ℕ) : ZMod n)
              * (closingCell m a b hκs hκ ht0 ht1 z ((j : ℕ) : ZMod n) / 2)) := by
  obtain ⟨εa, εb, hεa, hεb, hsum⟩ := sum_chartPerturb_block hn a b z j
  refine ⟨εa, εb, hεa, hεb, ?_⟩
  have hround : ∀ i : ZMod n,
      chartMap (curvPath κs κ t i) (curvPath κs κ t (i + 1))
        (closingCell m a b hκs hκ ht0 ht1 z i) = chartPerturb m a b z i := by
    intro i
    simp only [closingCell]
    exact chartMap_chartInv _ _ (hmem i)
  rw [heading_add_eq_chartBlock, Finset.sum_congr
    (rfl : Finset.range m = Finset.range m)
    (fun e _ => hround ((j + e : ℕ) : ZMod n)), hsum]
  ring

/-! ## The closure Jacobian at a symmetric anchor (`def:closing_jacobian_col`, @080)

The corrected `t = 0` rigidity (`lem:closure_boundary_rigidity`) is anchored at
an explicit *closure Jacobian*: at a positive half-period-symmetric anchor `κˢ`
with constant chart base `2π/n`, the linear part of `F(0,·)` at `z = 0` is
`L(u,v) = u·C_a + v·C_b` with columns `C_q` in closed form (validated against
finite differences of `F` to relative error `4·10⁻⁹`,
`references/verify_jacobian_formula.py`). The nondegeneracy criterion is
`Im(conj C_a · C_b) ≠ 0`, and it yields an explicit `σ_min`-style lower bound
`‖u·C_a + v·C_b‖ ≥ σ·(|u| + |v|)` (`norm_smul_add_smul_ge`) — the direct
estimate that replaces the inverse function theorem in the rigidity proof. -/

/-- The derivative of the arcsin slot `x ↦ arcsin (p·x/2)` of the single-edge
chart: `p / (2·√(1 − (p·x/2)²))` — the `A_j`/`B_j` ingredients of
`def:closing_jacobian_col` (`A_j = chartSlotDeriv κˢ_j ℓ_j`,
`B_j = chartSlotDeriv κˢ_{j+1} ℓ_j`). -/
noncomputable def chartSlotDeriv (p x : ℝ) : ℝ :=
  p / (2 * Real.sqrt (1 - (p * x / 2) ^ 2))

/-- The arcsin slot of the chart has strict derivative `chartSlotDeriv p x`
at any point strictly inside the wall `|p·x/2| < 1`. -/
theorem hasStrictDerivAt_arcsinSlot {p x : ℝ} (h : |p * x / 2| < 1) :
    HasStrictDerivAt (fun y : ℝ => Real.arcsin (p * y / 2))
      (chartSlotDeriv p x) x := by
  have hlt := abs_lt.mp h
  have harc := Real.hasStrictDerivAt_arcsin
    (ne_of_gt hlt.1) (ne_of_lt hlt.2)
  have hlin : HasStrictDerivAt (fun y : ℝ => p * y / 2) (p / 2) x := by
    simpa using ((hasStrictDerivAt_id x).const_mul p).div_const 2
  have hcomp := harc.comp x hlin
  have hEq : 1 / Real.sqrt (1 - (p * x / 2) ^ 2) * (p / 2)
      = chartSlotDeriv p x := by
    rw [chartSlotDeriv]; ring
  rw [hEq] at hcomp
  exact hcomp

/-- The slot derivative is positive strictly inside the wall (for `p > 0`). -/
theorem chartSlotDeriv_pos {p x : ℝ} (hp : 0 < p) (h : |p * x / 2| < 1) :
    0 < chartSlotDeriv p x := by
  have h1 : (p * x / 2) ^ 2 < 1 := by
    have := abs_lt.mp h
    nlinarith [abs_nonneg (p * x / 2)]
  exact div_pos hp (by positivity)

/-- The single-edge chart has strict derivative `A + B` — the sum of its two
slot derivatives — at any point strictly inside both walls. This is the
`τ'_j = A_j + B_j > 0` input of the chart-inverse differentiation
(`lem:closure_boundary_rigidity`). -/
theorem hasStrictDerivAt_chartMap {p q x : ℝ} (hp : |p * x / 2| < 1)
    (hq : |q * x / 2| < 1) :
    HasStrictDerivAt (chartMap p q)
      (chartSlotDeriv p x + chartSlotDeriv q x) x :=
  (hasStrictDerivAt_arcsinSlot hp).add (hasStrictDerivAt_arcsinSlot hq)

/-- The constant chart value `2π/n` is an achievable turning value on every
edge of a positive profile when `n ≥ 4`: it is positive and clears the wall
value through `2π/n ≤ π/2 < wall`. -/
theorem base_chart_mem_image [NeZero n] (hn4 : 4 ≤ n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (j : ZMod n) :
    2 * Real.pi / n ∈ chartMap (κs j) (κs (j + 1)) ''
      Set.Ioo (0 : ℝ) (2 / max (κs j) (κs (j + 1))) := by
  have hn0 : (0 : ℝ) < n := by
    have := NeZero.pos n
    exact_mod_cast this
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  refine chartMap_mem_image (hκs j) (hκs (j + 1)) (by positivity) ?_
  have h1 : 2 * Real.pi / n ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hn0 two_pos]
    nlinarith
  exact lt_of_le_of_lt h1 (pi_div_two_lt_chartMap_wall (hκs j) (hκs (j + 1)))

/-- **The Jacobian base point** (`def:closing_jacobian_col`): edge `j` recovers
its base length from the constant chart value `2π/n` via the chart inverse of
its curvature pair `(κˢ_j, κˢ_{j+1})`. This is the center column `Φ(0,0)` of
the closing 2-cell at the anchor. -/
noncomputable def jacobianBaseLen {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) :
    ZMod n → ℝ :=
  fun j => chartInv (hκs j) (hκs (j + 1)) (2 * Real.pi / n)

/-- The Jacobian base length is a moderate length of its edge pair. -/
theorem jacobianBaseLen_mem [NeZero n] (hn4 : 4 ≤ n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (j : ZMod n) :
    jacobianBaseLen hκs j ∈
      Set.Ioo (0 : ℝ) (2 / max (κs j) (κs (j + 1))) :=
  chartInv_mem _ _ (base_chart_mem_image hn4 hκs j)

/-- `λ'_j = 1/(A_j + B_j)` — the derivative of the edge-length recovery at the
Jacobian base point (`def:closing_jacobian_col`). -/
noncomputable def jacobianLambda' {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (j : ZMod n) : ℝ :=
  1 / (chartSlotDeriv (κs j) (jacobianBaseLen hκs j)
    + chartSlotDeriv (κs (j + 1)) (jacobianBaseLen hκs j))

/-- `p_j = A_j/(A_j + B_j)` — the tail-slot share of the chart derivative at
the Jacobian base point (`def:closing_jacobian_col`). -/
noncomputable def jacobianShare {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (j : ZMod n) : ℝ :=
  chartSlotDeriv (κs j) (jacobianBaseLen hκs j)
    / (chartSlotDeriv (κs j) (jacobianBaseLen hκs j)
      + chartSlotDeriv (κs (j + 1)) (jacobianBaseLen hκs j))

/-- `E_r = ℓ_r·e^{iψ_r}` — the edge vectors of the base development at the
anchor (`def:closing_jacobian_col`), indexed by the lifted index `r : ℕ`. -/
noncomputable def jacobianEdge {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (r : ℕ) : ℂ :=
  (jacobianBaseLen hκs (r : ZMod n) : ℂ)
    * Complex.exp ((heading κs (jacobianBaseLen hκs) r : ℂ) * Complex.I)

/-- **The closure-Jacobian column `C_q`** (`def:closing_jacobian_col`): the
derivative of `F(0,·)` at `z = 0` in the antisymmetric-pair direction `q`,

  `C_q = 2λ'_q·e^{iψ_q} + i·((2p_q − 1)·E_q + ∑_{r=q+1}^{q+m−1} E_r)`.

Validated against finite differences of `F` to relative error `4·10⁻⁹`
(`references/verify_jacobian_formula.py`); vanishes identically in the
constant-anchor case, matching the @079 degeneracy. -/
noncomputable def closingJacobianCol (m : ℕ) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (q : ℕ) : ℂ :=
  (2 * jacobianLambda' hκs (q : ZMod n) : ℝ)
      * Complex.exp ((heading κs (jacobianBaseLen hκs) q : ℂ) * Complex.I)
    + Complex.I * (((2 * jacobianShare hκs (q : ZMod n) - 1 : ℝ))
        * jacobianEdge hκs q
      + ∑ r ∈ Finset.Ico (q + 1) (q + m), jacobianEdge hκs r)

/-- **The linear part `L` of `F(0,·)` at `z = 0`**: `L z = z.1·C_a + z.2·C_b`
(`def:closing_jacobian_col`). -/
noncomputable def closingJacobianL (m : ℕ) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (a b : ℕ) (z : ℝ × ℝ) : ℂ :=
  z.1 • closingJacobianCol m hκs a + z.2 • closingJacobianCol m hκs b

/-- `simp`-friendly form of the linear part: real scalars become complex
multiplications. -/
@[simp] lemma closingJacobianL_apply (m : ℕ) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (a b : ℕ) (z : ℝ × ℝ) :
    closingJacobianL m hκs a b z
      = (z.1 : ℂ) * closingJacobianCol m hκs a
        + (z.2 : ℂ) * closingJacobianCol m hκs b := by
  simp [closingJacobianL, Complex.real_smul]

/-! ### The determinant criterion: an explicit `σ_min` lower bound

Project-local Mathlib supplement. A real `2×2` system presented by two complex
columns `C_a, C_b` is nonsingular iff `Im(conj C_a · C_b) ≠ 0`, and in that
case `‖u·C_a + v·C_b‖` is bounded below by an explicit positive multiple of
`|u| + |v|` — the elementary substitute for `σ_min` that drives the direct
rigidity estimate of `lem:closure_boundary_rigidity` (no inverse function
theorem). -/

/-- The `ℓ¹`-`σ_min` lower bound: if `D = Im(conj C_a · C_b) ≠ 0` then
`‖u·C_a + v·C_b‖ ≥ σ·(|u| + |v|)` with `σ = |D|/(‖C_a‖ + ‖C_b‖) > 0`.
(Pairing `w = u·C_a + v·C_b` against `conj C_a` isolates `v·D`; against
`conj C_b` isolates `−u·D`; `|Im| ≤ ‖·‖` finishes.) -/
theorem norm_smul_add_smul_ge {Ca Cb : ℂ}
    (hD : ((starRingEnd ℂ) Ca * Cb).im ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ u v : ℝ,
      σ * (|u| + |v|) ≤ ‖u • Ca + v • Cb‖ := by
  set D : ℝ := ((starRingEnd ℂ) Ca * Cb).im with hDdef
  have hCa : Ca ≠ 0 := by
    rintro rfl
    simp [hDdef] at hD
  have hCb : Cb ≠ 0 := by
    rintro rfl
    simp [hDdef] at hD
  have hnCa : 0 < ‖Ca‖ := norm_pos_iff.mpr hCa
  have hnCb : 0 < ‖Cb‖ := norm_pos_iff.mpr hCb
  have hsum : 0 < ‖Ca‖ + ‖Cb‖ := by linarith
  refine ⟨|D| / (‖Ca‖ + ‖Cb‖), div_pos (abs_pos.mpr hD) hsum, fun u v => ?_⟩
  set w : ℂ := u • Ca + v • Cb with hw
  -- pairing against `conj Ca` isolates `v·D`
  have hpair1 : ((starRingEnd ℂ) Ca * w).im = v * D := by
    have hself : ((starRingEnd ℂ) Ca * Ca).im = 0 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
    rw [hw, mul_add, Complex.add_im]
    rw [mul_comm ((starRingEnd ℂ) Ca) (u • Ca), smul_mul_assoc,
      mul_comm Ca ((starRingEnd ℂ) Ca), Complex.smul_im, hself,
      mul_comm ((starRingEnd ℂ) Ca) (v • Cb), smul_mul_assoc,
      mul_comm Cb ((starRingEnd ℂ) Ca), Complex.smul_im]
    ring
  -- pairing against `conj Cb` isolates `−u·D`
  have hpair2 : ((starRingEnd ℂ) Cb * w).im = -(u * D) := by
    have hswap : ((starRingEnd ℂ) Cb * Ca).im = -D := by
      have : (starRingEnd ℂ) Cb * Ca
          = (starRingEnd ℂ) ((starRingEnd ℂ) Ca * Cb) := by
        rw [map_mul, Complex.conj_conj, mul_comm]
      rw [this, Complex.conj_im]
    have hself : ((starRingEnd ℂ) Cb * Cb).im = 0 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
    rw [hw, mul_add, Complex.add_im]
    rw [mul_comm ((starRingEnd ℂ) Cb) (u • Ca), smul_mul_assoc,
      mul_comm Ca ((starRingEnd ℂ) Cb), Complex.smul_im, hswap,
      mul_comm ((starRingEnd ℂ) Cb) (v • Cb), smul_mul_assoc,
      mul_comm Cb ((starRingEnd ℂ) Cb), Complex.smul_im, hself]
    ring
  have hbound1 : |v| * |D| ≤ ‖Ca‖ * ‖w‖ := by
    calc |v| * |D| = |((starRingEnd ℂ) Ca * w).im| := by
          rw [hpair1, abs_mul]
      _ ≤ ‖(starRingEnd ℂ) Ca * w‖ := Complex.abs_im_le_norm _
      _ = ‖Ca‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]
  have hbound2 : |u| * |D| ≤ ‖Cb‖ * ‖w‖ := by
    calc |u| * |D| = |((starRingEnd ℂ) Cb * w).im| := by
          rw [hpair2, abs_neg, abs_mul]
      _ ≤ ‖(starRingEnd ℂ) Cb * w‖ := Complex.abs_im_le_norm _
      _ = ‖Cb‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]
  rw [div_mul_eq_mul_div, div_le_iff₀ hsum]
  have hwn : 0 ≤ ‖w‖ := norm_nonneg w
  nlinarith [abs_nonneg u, abs_nonneg v, abs_nonneg D]

/-- Nondegeneracy of the columns makes the linear part injective: the packaged
kernel-triviality form of the determinant criterion. -/
theorem smul_add_smul_eq_zero_iff {Ca Cb : ℂ}
    (hD : ((starRingEnd ℂ) Ca * Cb).im ≠ 0) (u v : ℝ) :
    u • Ca + v • Cb = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h0
    obtain ⟨σ, hσ, hbound⟩ := norm_smul_add_smul_ge hD
    have := hbound u v
    rw [h0, norm_zero] at this
    have habs : |u| + |v| ≤ 0 :=
      le_of_mul_le_mul_left (by linarith : σ * (|u| + |v|) ≤ σ * 0) hσ
    constructor
    · exact abs_eq_zero.mp (le_antisymm (by linarith [abs_nonneg v]) (abs_nonneg u))
    · exact abs_eq_zero.mp (le_antisymm (by linarith [abs_nonneg u]) (abs_nonneg v))
  · rintro ⟨rfl, rfl⟩
    simp

/-! ### Strict differentiability of the edge-length recovery

The analytic backbone of `lem:closure_boundary_rigidity`: the chart inverse is
strictly differentiable at every achieved turning value, with derivative
`λ' = 1/(A + B)` — the inverse-function *rule* for a strictly monotone map
with nonvanishing derivative (`HasStrictDerivAt.of_local_left_inverse`), no
inverse function *theorem*. -/

/-- The moderate turning-value image is a neighborhood of each of its points:
around an achieved value `chartMap p q x`, squeeze `x` into a compact
subinterval of the moderate domain and apply the IVT
(`chartMap_mem_image_Icc`) plus strict monotonicity at its endpoints. -/
theorem chartMap_image_mem_nhds {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) ∈ nhds s := by
  obtain ⟨x, hx, rfl⟩ := hs
  obtain ⟨hx0, hxD⟩ := hx
  have hmax : 0 < max p q := lt_of_lt_of_le hp (le_max_left p q)
  have hD : 0 < 2 / max p q := div_pos two_pos hmax
  set x₁ : ℝ := x / 2 with hx₁def
  set x₂ : ℝ := (x + 2 / max p q) / 2 with hx₂def
  have hx₁mem : x₁ ∈ Set.Ioo (0 : ℝ) (2 / max p q) :=
    ⟨by positivity, by rw [hx₁def]; linarith⟩
  have hx₂mem : x₂ ∈ Set.Ioo (0 : ℝ) (2 / max p q) :=
    ⟨by positivity, by rw [hx₂def]; linarith⟩
  have h₁ : chartMap p q x₁ < chartMap p q x :=
    chartMap_strictMonoOn hp hq hx₁mem ⟨hx0, hxD⟩ (by rw [hx₁def]; linarith)
  have h₂ : chartMap p q x < chartMap p q x₂ :=
    chartMap_strictMonoOn hp hq ⟨hx0, hxD⟩ hx₂mem (by rw [hx₂def]; linarith)
  refine Filter.mem_of_superset (Ioo_mem_nhds h₁ h₂) fun y hy => ?_
  have hyIcc : y ∈ chartMap p q '' Set.Icc x₁ x₂ :=
    chartMap_mem_image_Icc (by rw [hx₁def, hx₂def]; linarith)
      ⟨hy.1.le, hy.2.le⟩
  have hsub : Set.Icc x₁ x₂ ⊆ Set.Ioo (0 : ℝ) (2 / max p q) := fun w hw =>
    ⟨lt_of_lt_of_le hx₁mem.1 hw.1, lt_of_le_of_lt hw.2 hx₂mem.2⟩
  exact Set.image_mono hsub hyIcc

/-- **Strict differentiability of the edge-length recovery** at any achieved
turning value, with the explicit derivative `λ' = 1/(A + B)` in the slot
derivatives at the recovered length. -/
theorem hasStrictDerivAt_chartInv {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    HasStrictDerivAt (chartInv hp hq)
      (1 / (chartSlotDeriv p (chartInv hp hq s)
        + chartSlotDeriv q (chartInv hp hq s))) s := by
  have hmem := chartInv_mem hp hq hs
  have hwallp : |p * chartInv hp hq s / 2| < 1 := by
    have := chartArg_mem hp hq hmem hp (le_max_left p q)
    exact abs_lt.mpr ⟨this.1, this.2⟩
  have hwallq : |q * chartInv hp hq s / 2| < 1 := by
    have := chartArg_mem hp hq hmem hq (le_max_right p q)
    exact abs_lt.mpr ⟨this.1, this.2⟩
  have hf := hasStrictDerivAt_chartMap hwallp hwallq
  have hcont : ContinuousAt (chartInv hp hq) s :=
    (continuousOn_chartInv hp hq).continuousAt (chartMap_image_mem_nhds hp hq hs)
  have hne : chartSlotDeriv p (chartInv hp hq s)
      + chartSlotDeriv q (chartInv hp hq s) ≠ 0 :=
    (add_pos (chartSlotDeriv_pos hp hwallp) (chartSlotDeriv_pos hq hwallq)).ne'
  have hev : ∀ᶠ y in nhds s, chartMap p q (chartInv hp hq y) = y := by
    filter_upwards [chartMap_image_mem_nhds hp hq hs] with y hy
    exact chartMap_chartInv hp hq hy
  have hmain := HasStrictDerivAt.of_local_left_inverse hcont hf hne hev
  simpa [one_div] using hmain

/-! ### The clean `t = 0` cell at the anchor and its edge-length derivatives

`closingGap` at `t = 0` involves the curvatures `curvPath κs κ 0 j`, which are
propositionally (not definitionally) equal to `κs j`. For the rigidity
analysis we work with the *clean* anchor cell (curvatures `κs` directly) and
bridge back at the end. -/

/-- The `t = 0` closing 2-cell at the anchor, in clean form. -/
noncomputable def anchorCell (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (z : ℝ × ℝ) : ZMod n → ℝ :=
  fun j => chartInv (hκs j) (hκs (j + 1)) (chartPerturb m a b z j)

/-- The `t = 0` gap map at the anchor, in clean form. -/
noncomputable def anchorGap (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (z : ℝ × ℝ) : ℂ :=
  closureGap κs (anchorCell m a b hκs z)

/-- The `t = 0` slice of the closing 2-cell is the clean anchor cell. -/
theorem closingCell_zero_eq_anchorCell (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) (z : ℝ × ℝ) :
    closingCell m a b hκs hκ ht0 ht1 z = anchorCell m a b hκs z := by
  funext j
  have hcongr : ∀ {p p' q q' : ℝ} (hp : 0 < p) (hq : 0 < q) (hp' : 0 < p')
      (hq' : 0 < q') (s : ℝ), p = p' → q = q' →
      chartInv hp hq s = chartInv hp' hq' s := by
    intro p p' q q' hp hq hp' hq' s hpe hqe
    subst hpe; subst hqe; rfl
  simp only [closingCell, anchorCell]
  exact hcongr _ _ _ _ _ (congrFun (curvPath_zero κs κ) j)
    (congrFun (curvPath_zero κs κ) (j + 1))

/-- The `t = 0` slice of the gap map is the clean anchor gap. -/
theorem closingGap_zero_eq_anchorGap (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) (z : ℝ × ℝ) :
    closingGap m a b hκs hκ ht0 ht1 z = anchorGap m a b hκs z := by
  simp only [closingGap, anchorGap, curvPath_zero,
    closingCell_zero_eq_anchorCell m a b hκs hκ ht0 ht1 z]

/-- The center of the clean anchor cell is the Jacobian base point. -/
theorem anchorCell_zero (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) :
    anchorCell m a b hκs (0 : ℝ × ℝ) = jacobianBaseLen hκs := by
  funext j
  have h0 : chartPerturb m a b (0 : ℝ × ℝ) j = 2 * Real.pi / n :=
    chartPerturb_zero m a b j
  simp only [anchorCell, jacobianBaseLen, h0]

/-- The pair-direction coefficient of edge `j` for the antisymmetric pair at
`q`: `+1` at `j = q`, `−1` at `j = q + m`, `0` elsewhere (and `0` when the
pair collapses onto one index). -/
def pairSign (m : ℕ) (q j : ZMod n) : ℝ :=
  (if j = q then 1 else 0) - (if j = q + (m : ZMod n) then 1 else 0)

/-- The linear part of the antisymmetric perturbation at edge `j` as a
continuous linear map: `(u, v) ↦ pairSign a j · u + pairSign b j · v`. -/
noncomputable def pairCLM (m : ℕ) (a b j : ZMod n) : ℝ × ℝ →L[ℝ] ℝ :=
  pairSign m a j • ContinuousLinearMap.fst ℝ ℝ ℝ
    + pairSign m b j • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The derivative of a single edge length of the anchor cell at `z = 0`:
`λ'_j` times the pair direction of edge `j`. -/
noncomputable def anchorCellDeriv (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (j : ZMod n) : ℝ × ℝ →L[ℝ] ℝ :=
  jacobianLambda' hκs j • pairCLM m a b j

/-- The perturbed chart base is affine in `z` with the pair-sign coefficients. -/
theorem chartPerturb_eq_affine (m : ℕ) (a b : ZMod n) (z : ℝ × ℝ) (j : ZMod n) :
    chartPerturb m a b z j
      = 2 * Real.pi / n
        + (pairSign m a j * z.1 + pairSign m b j * z.2) := by
  simp only [chartPerturb, pairSign]
  split_ifs <;> ring

/-- The perturbed chart base of edge `j` has (everywhere) the constant strict
derivative `pairSign m a j · du + pairSign m b j · dv`. -/
theorem hasStrictFDerivAt_chartPerturb (m : ℕ) (a b j : ZMod n) (z₀ : ℝ × ℝ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => chartPerturb m a b z j)
      (pairCLM m a b j) z₀ := by
  rw [pairCLM]
  have hfun : (fun z : ℝ × ℝ => chartPerturb m a b z j)
      = fun z : ℝ × ℝ => 2 * Real.pi / n
        + (pairSign m a j * z.1 + pairSign m b j * z.2) := by
    funext z
    exact chartPerturb_eq_affine m a b z j
  rw [hfun]
  have h1 : HasStrictFDerivAt (fun z : ℝ × ℝ => pairSign m a j * z.1)
      (pairSign m a j • ContinuousLinearMap.fst ℝ ℝ ℝ) z₀ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasStrictFDerivAt.const_mul (pairSign m a j)
  have h2 : HasStrictFDerivAt (fun z : ℝ × ℝ => pairSign m b j * z.2)
      (pairSign m b j • ContinuousLinearMap.snd ℝ ℝ ℝ) z₀ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasStrictFDerivAt.const_mul (pairSign m b j)
  exact (h1.add h2).const_add (2 * Real.pi / n)

/-- **Strict differentiability of a single edge length of the anchor cell** at
the center `z = 0` (`lem:closure_boundary_rigidity`, first layer): the
derivative is `λ'_j` times the pair-sign direction of edge `j`. -/
theorem hasStrictFDerivAt_anchorCell [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (j : ZMod n) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => anchorCell m a b hκs z j)
      (anchorCellDeriv m a b hκs j) 0 := by
  rw [anchorCellDeriv]
  have hbase := base_chart_mem_image hn4 hκs j
  have h0 : chartPerturb m a b (0 : ℝ × ℝ) j = 2 * Real.pi / n :=
    chartPerturb_zero m a b j
  have hinv' : HasStrictDerivAt (chartInv (hκs j) (hκs (j + 1)))
      (jacobianLambda' hκs j) (chartPerturb m a b (0 : ℝ × ℝ) j) := by
    rw [h0]
    exact hasStrictDerivAt_chartInv (hκs j) (hκs (j + 1)) hbase
  exact hinv'.comp_hasStrictFDerivAt 0 (hasStrictFDerivAt_chartPerturb m a b j 0)

/-! ### Strict differentiability of the anchor headings

Near the center the heading of the anchor cell takes the *chart form*:
one boundary half-turn slot at edge `−1`, the affine chart sum (whose values
are the perturbed chart base, by the round trip), and one boundary half-turn
slot at edge `k`. This makes the heading derivative two arcsin slots plus an
explicitly affine part. -/

/-- Near the center every perturbed chart value is an achieved turning value
on its edge (continuity of the perturbation + openness of each edge's
turning-value image around the base value `2π/n`). -/
theorem eventually_chartPerturb_mem [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) :
    ∀ᶠ z : ℝ × ℝ in nhds 0, ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (κs j) (κs (j + 1)) ''
        Set.Ioo (0 : ℝ) (2 / max (κs j) (κs (j + 1))) := by
  rw [Filter.eventually_all]
  intro j
  have hcont : ContinuousAt (fun z : ℝ × ℝ => chartPerturb m a b z j) 0 :=
    (continuous_chartPerturb m a b j).continuousAt
  have hmem : chartMap (κs j) (κs (j + 1)) ''
      Set.Ioo (0 : ℝ) (2 / max (κs j) (κs (j + 1))) ∈
      nhds (chartPerturb m a b (0 : ℝ × ℝ) j) := by
    rw [show chartPerturb m a b (0 : ℝ × ℝ) j = 2 * Real.pi / n from
      chartPerturb_zero m a b j]
    exact chartMap_image_mem_nhds (hκs j) (hκs (j + 1))
      (base_chart_mem_image hn4 hκs j)
  exact hcont.eventually_mem hmem

/-- **The chart form of the anchor-cell heading**, eventually near the center:
`ψ_k(z) = arcsin(κˢ_0·(ℓ_{−1}(z)/2)) + ∑_{e<k} s(z)_e
+ arcsin(κˢ_k·(ℓ_k(z)/2))`. -/
theorem heading_anchorCell_eventuallyEq [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (k : ℕ) :
    (fun z : ℝ × ℝ => heading κs (anchorCell m a b hκs z) k)
      =ᶠ[nhds 0] fun z : ℝ × ℝ =>
        Real.arcsin (κs 0 * (anchorCell m a b hκs z (-1) / 2))
          + ∑ e ∈ Finset.range k, chartPerturb m a b z ((e : ℕ) : ZMod n)
          + Real.arcsin (κs (k : ZMod n)
              * (anchorCell m a b hκs z ((k : ℕ) : ZMod n) / 2)) := by
  filter_upwards [eventually_chartPerturb_mem hn4 m a b hκs] with z hz
  have hround : ∀ i : ZMod n,
      chartMap (κs i) (κs (i + 1)) (anchorCell m a b hκs z i)
        = chartPerturb m a b z i := by
    intro i
    simp only [anchorCell]
    exact chartMap_chartInv _ _ (hz i)
  have hblock := heading_add_eq_chartBlock κs (anchorCell m a b hκs z) 0 k
  simp only [Nat.zero_add, Nat.cast_zero] at hblock
  have hhead0 : heading κs (anchorCell m a b hκs z) 0
      = Real.arcsin (κs 0 * (anchorCell m a b hκs z (-1) / 2))
        + Real.arcsin (κs 0 * (anchorCell m a b hκs z 0 / 2)) := by
    simp only [heading, zero_add, Finset.sum_range_one, Nat.cast_zero,
      turningAngle, tK_zero, zero_sub]
  rw [hblock, hhead0, Finset.sum_congr rfl
    (fun e _ => hround ((e : ℕ) : ZMod n))]
  ring

/-- **The heading derivative of the anchor cell at the center**: the two
boundary arcsin slots (edges `−1` and `k`) plus the affine chart-sum part. -/
noncomputable def anchorHeadingDeriv (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (k : ℕ) : ℝ × ℝ →L[ℝ] ℝ :=
  chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
      • anchorCellDeriv m a b hκs (-1)
    + ∑ e ∈ Finset.range k, pairCLM m a b ((e : ℕ) : ZMod n)
    + chartSlotDeriv (κs (k : ZMod n)) (jacobianBaseLen hκs ((k : ℕ) : ZMod n))
      • anchorCellDeriv m a b hκs ((k : ℕ) : ZMod n)

/-- Strict differentiability of one heading slot `z ↦ arcsin(κˢ_i·(ℓ_j(z)/2))`
of the anchor cell at the center, for `i` an endpoint vertex of edge `j`. -/
theorem hasStrictFDerivAt_anchorSlot [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) {i j : ZMod n}
    (hij : i = j ∨ i = j + 1) :
    HasStrictFDerivAt
      (fun z : ℝ × ℝ => Real.arcsin (κs i * (anchorCell m a b hκs z j / 2)))
      (chartSlotDeriv (κs i) (jacobianBaseLen hκs j)
        • anchorCellDeriv m a b hκs j) 0 := by
  have hmem := jacobianBaseLen_mem hn4 hκs j
  have hle : κs i ≤ max (κs j) (κs (j + 1)) := by
    rcases hij with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hwall : |κs i * jacobianBaseLen hκs j / 2| < 1 := by
    have := chartArg_mem (hκs j) (hκs (j + 1)) hmem (hκs i) hle
    exact abs_lt.mpr ⟨this.1, this.2⟩
  have h0 : anchorCell m a b hκs (0 : ℝ × ℝ) j = jacobianBaseLen hκs j :=
    congrFun (anchorCell_zero m a b hκs) j
  have hslot' : HasStrictDerivAt (fun y : ℝ => Real.arcsin (κs i * y / 2))
      (chartSlotDeriv (κs i) (jacobianBaseLen hκs j))
      (anchorCell m a b hκs (0 : ℝ × ℝ) j) := by
    rw [h0]
    exact hasStrictDerivAt_arcsinSlot hwall
  have hcomp := hslot'.comp_hasStrictFDerivAt 0
    (hasStrictFDerivAt_anchorCell hn4 m a b hκs j)
  have hfun : ((fun y : ℝ => Real.arcsin (κs i * y / 2))
        ∘ fun z : ℝ × ℝ => anchorCell m a b hκs z j)
      = fun z : ℝ × ℝ => Real.arcsin (κs i * (anchorCell m a b hκs z j / 2)) := by
    funext z
    simp [Function.comp, mul_div_assoc]
  rw [hfun] at hcomp
  exact hcomp

/-- **Strict differentiability of the anchor-cell headings at the center**
(`lem:closure_boundary_rigidity`, second layer): `ψ_k` has strict derivative
`anchorHeadingDeriv k` at `z = 0`. -/
theorem hasStrictFDerivAt_anchorHeading [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (k : ℕ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => heading κs (anchorCell m a b hκs z) k)
      (anchorHeadingDeriv m a b hκs k) 0 := by
  have h1 := hasStrictFDerivAt_anchorSlot hn4 m a b hκs
    (i := 0) (j := (-1 : ZMod n)) (Or.inr (by ring))
  have h2 : HasStrictFDerivAt
      (fun z : ℝ × ℝ => ∑ e ∈ Finset.range k,
        chartPerturb m a b z ((e : ℕ) : ZMod n))
      (∑ e ∈ Finset.range k, pairCLM m a b ((e : ℕ) : ZMod n)) 0 := by
    have hfun : (∑ e ∈ Finset.range k,
          fun z : ℝ × ℝ => chartPerturb m a b z ((e : ℕ) : ZMod n))
        = fun z : ℝ × ℝ => ∑ e ∈ Finset.range k,
            chartPerturb m a b z ((e : ℕ) : ZMod n) := by
      funext z
      simp
    rw [← hfun]
    exact HasStrictFDerivAt.sum
      (fun e _ => hasStrictFDerivAt_chartPerturb m a b _ 0)
  have h3 := hasStrictFDerivAt_anchorSlot hn4 m a b hκs
    (i := ((k : ℕ) : ZMod n)) (j := ((k : ℕ) : ZMod n)) (Or.inl rfl)
  have hG := (h1.add h2).add h3
  exact hG.congr_of_eventuallyEq
    (heading_anchorCell_eventuallyEq hn4 m a b hκs k).symm

/-! ### Strict differentiability of the anchor gap map -/

/-- The sum-form derivative of the anchor gap at the center:
`dF = Σ_j (e^{iψ_j}·dℓ_j + ℓ_j·e^{iψ_j}·i·dψ_j)`, all data at the Jacobian
base point. -/
noncomputable def anchorGapDeriv (m : ℕ) (a b : ZMod n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) : ℝ × ℝ →L[ℝ] ℂ :=
  ∑ j ∈ Finset.range n,
    (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I) •
        Complex.ofRealCLM.comp (anchorCellDeriv m a b hκs ((j : ℕ) : ZMod n))
      + ((jacobianBaseLen hκs ((j : ℕ) : ZMod n) : ℂ)
          * Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I)
          * Complex.I) •
        Complex.ofRealCLM.comp (anchorHeadingDeriv m a b hκs j))

/-- **Strict differentiability of the anchor gap map at the center**
(`lem:closure_boundary_rigidity`, third layer): `F(0,·)` has strict derivative
`anchorGapDeriv` at `z = 0` — the product/chain rule assembly of the edge and
heading derivatives through `exp(i·ψ)`. -/
theorem hasStrictFDerivAt_anchorGap [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) :
    HasStrictFDerivAt (anchorGap m a b hκs) (anchorGapDeriv m a b hκs) 0 := by
  have hcell0 : anchorCell m a b hκs (0 : ℝ × ℝ) = jacobianBaseLen hκs :=
    anchorCell_zero m a b hκs
  have hterm : ∀ j ∈ Finset.range n, HasStrictFDerivAt
      (fun z : ℝ × ℝ => (anchorCell m a b hκs z ((j : ℕ) : ZMod n) : ℂ)
        * Complex.exp
            ((heading κs (anchorCell m a b hκs z) j : ℂ) * Complex.I))
      (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I) •
          Complex.ofRealCLM.comp (anchorCellDeriv m a b hκs ((j : ℕ) : ZMod n))
        + ((jacobianBaseLen hκs ((j : ℕ) : ZMod n) : ℂ)
            * Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ)
              * Complex.I)
            * Complex.I) •
          Complex.ofRealCLM.comp (anchorHeadingDeriv m a b hκs j)) 0 := by
    intro j _
    have hc : HasStrictFDerivAt
        (fun z : ℝ × ℝ => (anchorCell m a b hκs z ((j : ℕ) : ZMod n) : ℂ))
        (Complex.ofRealCLM.comp
          (anchorCellDeriv m a b hκs ((j : ℕ) : ZMod n))) 0 :=
      Complex.ofRealCLM.hasStrictFDerivAt.comp 0
        (hasStrictFDerivAt_anchorCell hn4 m a b hκs _)
    have hψc : HasStrictFDerivAt
        (fun z : ℝ × ℝ => ((heading κs (anchorCell m a b hκs z) j : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (anchorHeadingDeriv m a b hκs j)) 0 :=
      Complex.ofRealCLM.hasStrictFDerivAt.comp 0
        (hasStrictFDerivAt_anchorHeading hn4 m a b hκs j)
    have hinner := hψc.mul_const Complex.I
    have hexp : HasStrictDerivAt Complex.exp
        (Complex.exp
          ((heading κs (anchorCell m a b hκs (0 : ℝ × ℝ)) j : ℂ) * Complex.I))
        ((heading κs (anchorCell m a b hκs (0 : ℝ × ℝ)) j : ℂ) * Complex.I) :=
      Complex.hasStrictDerivAt_exp _
    have hd := hexp.comp_hasStrictFDerivAt 0 hinner
    have hmul := hc.mul hd
    simp only [Function.comp_apply] at hmul
    rw [hcell0] at hmul
    have hDeq : Complex.exp
          ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I) •
            Complex.ofRealCLM.comp
              (anchorCellDeriv m a b hκs ((j : ℕ) : ZMod n))
          + ((jacobianBaseLen hκs ((j : ℕ) : ZMod n) : ℂ)
              * Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ)
                * Complex.I)
              * Complex.I) •
            Complex.ofRealCLM.comp (anchorHeadingDeriv m a b hκs j)
        = (jacobianBaseLen hκs ((j : ℕ) : ZMod n) : ℂ) •
            (Complex.exp
              ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I) •
              Complex.I •
                Complex.ofRealCLM.comp (anchorHeadingDeriv m a b hκs j))
          + Complex.exp
              ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I) •
            Complex.ofRealCLM.comp
              (anchorCellDeriv m a b hκs ((j : ℕ) : ZMod n)) := by
      rw [smul_smul, smul_smul, add_comm, mul_assoc]
    rw [hDeq]
    exact hmul
  have hsum := HasStrictFDerivAt.sum (x := (0 : ℝ × ℝ)) hterm
  have hfun : (∑ j ∈ Finset.range n,
        fun z : ℝ × ℝ => (anchorCell m a b hκs z ((j : ℕ) : ZMod n) : ℂ)
          * Complex.exp
              ((heading κs (anchorCell m a b hκs z) j : ℂ) * Complex.I))
      = anchorGap m a b hκs := by
    funext z
    simp [anchorGap, closureGap, vertexR2]
  rw [hfun] at hsum
  exact hsum

/-! ### The symmetric base point: cast, counting, and symmetry identities

The ingredients for identifying `anchorGapDeriv` with the closed-form columns
`closingJacobianCol` at a half-period-symmetric anchor. -/

private lemma natCast_zmod_inj [NeZero n] {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : (i : ZMod n) = (j : ZMod n)) : i = j := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this

private lemma neg_one_zmod_eq [NeZero n] :
    (-1 : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
  have h1 : 1 ≤ n := NeZero.one_le
  rw [Nat.cast_sub h1, ZMod.natCast_self, Nat.cast_one, zero_sub]

/-- Evaluation of the pair sign at lifted indices below `n`. -/
theorem pairSign_natCast [NeZero n] {m : ℕ} (hn : n = 2 * m) {q j : ℕ}
    (hq : q < m) (hj : j < n) :
    pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n)
      = (if j = q then (1 : ℝ) else 0) - (if j = q + m then 1 else 0) := by
  have hqn : q < n := by omega
  have hqmn : q + m < n := by omega
  rw [pairSign]
  congr 1
  · refine if_congr ⟨fun h => natCast_zmod_inj hj hqn h, fun h => by rw [h]⟩
      rfl rfl
  · refine if_congr ⟨fun h => ?_, fun h => by rw [h]; push_cast; ring⟩ rfl rfl
    refine natCast_zmod_inj hj hqmn ?_
    rw [h]
    push_cast
    ring

/-- The pair sign at the wrap-around edge `−1`: it fires (negatively) exactly
for the boundary pair `q = m − 1`. -/
theorem pairSign_neg_one [NeZero n] {m : ℕ} (hn : n = 2 * m) (hn4 : 4 ≤ n)
    {q : ℕ} (hq : q < m) :
    pairSign m ((q : ℕ) : ZMod n) (-1)
      = -(if q + 1 = m then (1 : ℝ) else 0) := by
  have hn1 : n - 1 < n := by omega
  rw [neg_one_zmod_eq, pairSign_natCast hn hq hn1]
  have h1 : ¬(n - 1 = q) := by omega
  rw [if_neg h1]
  have h2 : (n - 1 = q + m) ↔ (q + 1 = m) := by omega
  rw [if_congr h2 rfl rfl, zero_sub]

/-- The Jacobian base point is half-period symmetric (the anchor's curvature
pairs coincide on opposite edges). -/
theorem jacobianBaseLen_symm {m : ℕ} {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) (i : ZMod n) :
    jacobianBaseLen hκs (i + (m : ZMod n)) = jacobianBaseLen hκs i := by
  have hcongr : ∀ {p p' q q' : ℝ} (hp : 0 < p) (hq : 0 < q) (hp' : 0 < p')
      (hq' : 0 < q') (s : ℝ), p = p' → q = q' →
      chartInv hp hq s = chartInv hp' hq' s := by
    intro p p' q q' hp hq hp' hq' s hpe hqe
    subst hpe; subst hqe; rfl
  simp only [jacobianBaseLen]
  exact hcongr _ _ _ _ _ (hsym i)
    (by rw [show i + (m : ZMod n) + 1 = (i + 1) + (m : ZMod n) by ring]
        exact hsym (i + 1))

/-- The Jacobian base point satisfies the turning constraint: every edge chart
value is `2π/n`, so the total turning is `2π`. -/
theorem turningSum_jacobianBaseLen [NeZero n] (hn4 : 4 ≤ n)
    {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) :
    turningSum κs (jacobianBaseLen hκs) = 2 * Real.pi := by
  rw [turningSum_eq_sum_edgeChart]
  have hval : ∀ j : ZMod n,
      chartMap (κs j) (κs (j + 1)) (jacobianBaseLen hκs j) = 2 * Real.pi / n := by
    intro j
    simp only [jacobianBaseLen]
    exact chartMap_chartInv _ _ (base_chart_mem_image hn4 hκs j)
  rw [Finset.sum_congr rfl fun j _ => hval j, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by
    have := NeZero.pos n
    positivity
  field_simp

/-- Headings of the Jacobian base point advance by `π` over a half-period. -/
theorem heading_jacobianBaseLen_add_half [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (hn4 : 4 ≤ n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) (j : ℕ) :
    heading κs (jacobianBaseLen hκs) (j + m)
      = heading κs (jacobianBaseLen hκs) j + Real.pi :=
  heading_add_half hn hsym (jacobianBaseLen_symm hκs hsym)
    (turningSum_jacobianBaseLen hn4 hκs) j

/-- The base edge vectors flip sign over a half-period: `E_{j+m} = −E_j`. -/
theorem jacobianEdge_add_half [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (hn4 : 4 ≤ n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) (j : ℕ) :
    jacobianEdge hκs (j + m) = -jacobianEdge hκs j := by
  have hcast : ((j + m : ℕ) : ZMod n) = ((j : ℕ) : ZMod n) + (m : ZMod n) := by
    push_cast; ring
  rw [jacobianEdge, jacobianEdge, hcast, jacobianBaseLen_symm hκs hsym,
    heading_jacobianBaseLen_add_half hn hn4 hκs hsym]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The base edge vectors sum to zero: the symmetric base point closes
(`central_symmetry_closes` at the anchor). -/
theorem sum_jacobianEdge_eq_zero [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (hn4 : 4 ≤ n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) :
    ∑ j ∈ Finset.range n, jacobianEdge hκs j = 0 := by
  have hclose := central_symmetry_closes hn hsym
    (jacobianBaseLen_symm hκs hsym) (turningSum_jacobianBaseLen hn4 hκs)
  simpa [closureGap, vertexR2, jacobianEdge] using hclose

/-- The slot derivatives at the Jacobian base point are positive. -/
theorem jacobianSlot_pos [NeZero n] (hn4 : 4 ≤ n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) {i j : ZMod n} (hij : i = j ∨ i = j + 1) :
    0 < chartSlotDeriv (κs i) (jacobianBaseLen hκs j) := by
  have hmem := jacobianBaseLen_mem hn4 hκs j
  have hle : κs i ≤ max (κs j) (κs (j + 1)) := by
    rcases hij with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hwall : |κs i * jacobianBaseLen hκs j / 2| < 1 := by
    have := chartArg_mem (hκs j) (hκs (j + 1)) hmem (hκs i) hle
    exact abs_lt.mpr ⟨this.1, this.2⟩
  exact chartSlotDeriv_pos (hκs i) hwall

/-- The tail slot times `λ'` is the share `p_j`. -/
theorem tailSlot_mul_lambda' {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (j : ZMod n) :
    chartSlotDeriv (κs j) (jacobianBaseLen hκs j) * jacobianLambda' hκs j
      = jacobianShare hκs j := by
  rw [jacobianLambda', jacobianShare, mul_one_div]

/-- The head slot times `λ'` is `1 − p_j` (the chart derivative splits as
`A + B = 1/λ'`). -/
theorem headSlot_mul_lambda' [NeZero n] (hn4 : 4 ≤ n) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (j : ZMod n) :
    chartSlotDeriv (κs (j + 1)) (jacobianBaseLen hκs j) * jacobianLambda' hκs j
      = 1 - jacobianShare hκs j := by
  have hA := jacobianSlot_pos hn4 hκs (i := j) (j := j) (Or.inl rfl)
  have hB := jacobianSlot_pos hn4 hκs (i := j + 1) (j := j) (Or.inr rfl)
  rw [jacobianLambda', jacobianShare]
  field_simp
  ring

/-- `λ'` is half-period symmetric at a symmetric anchor. -/
theorem jacobianLambda'_add_half {m : ℕ} {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) (i : ZMod n) :
    jacobianLambda' hκs (i + (m : ZMod n)) = jacobianLambda' hκs i := by
  rw [jacobianLambda', jacobianLambda', jacobianBaseLen_symm hκs hsym, hsym,
    show i + (m : ZMod n) + 1 = (i + 1) + (m : ZMod n) by ring, hsym]

/-- The share `p` is half-period symmetric at a symmetric anchor. -/
theorem jacobianShare_add_half {m : ℕ} {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) (i : ZMod n) :
    jacobianShare hκs (i + (m : ZMod n)) = jacobianShare hκs i := by
  rw [jacobianShare, jacobianShare, jacobianBaseLen_symm hκs hsym, hsym,
    show i + (m : ZMod n) + 1 = (i + 1) + (m : ZMod n) by ring, hsym]

/-- Extraction of a pair-signed sum over a full period: only the two members
of the antipodal pair survive. -/
theorem sum_mul_pairSign [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (f : ℕ → ℂ) {q : ℕ} (hq : q < m) :
    ∑ j ∈ Finset.range n,
        f j * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
      = f q - f (q + m) := by
  have hqn : q < n := by omega
  have hqmn : q + m < n := by omega
  have hsummand : ∀ j ∈ Finset.range n,
      f j * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
        = (if j = q then f j else 0) - (if j = q + m then f j else 0) := by
    intro j hj
    rw [pairSign_natCast hn hq (Finset.mem_range.mp hj)]
    push_cast
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hsummand, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.range n) q f,
    Finset.sum_ite_eq' (Finset.range n) (q + m) f,
    if_pos (Finset.mem_range.mpr hqn), if_pos (Finset.mem_range.mpr hqmn)]

/-- The running pair-sign count: over the first `j` edges the antisymmetric
pair contributes `[q < j] − [q + m < j]`. -/
theorem sum_pairSign_range [NeZero n] {m : ℕ} (hn : n = 2 * m) {q j : ℕ}
    (hq : q < m) (hj : j ≤ n) :
    ∑ e ∈ Finset.range j, pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n)
      = (if q < j then (1 : ℝ) else 0) - (if q + m < j then 1 else 0) := by
  have hsummand : ∀ e ∈ Finset.range j,
      pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n)
        = (if e = q then (1 : ℝ) else 0) - (if e = q + m then 1 else 0) :=
    fun e he =>
      pairSign_natCast hn hq (lt_of_lt_of_le (Finset.mem_range.mp he) hj)
  rw [Finset.sum_congr rfl hsummand, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.range j) q (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' (Finset.range j) (q + m) (fun _ => (1 : ℝ))]
  simp only [Finset.mem_range]

/-- **The master column identification**: the sum-form derivative of the
anchor gap, evaluated in the direction of the antisymmetric pair `q`, equals
the closed-form Jacobian column `C_q` of `def:closing_jacobian_col`. The
computation: the `dℓ` part extracts `2λ'_q e^{iψ_q}` (pair extraction +
half-period symmetry); the constant heading gauge multiplies `ΣE = 0`; the
running count contributes `∑_{Ioc q (q+m)} E`; the boundary slots contribute
`2p_q E_q`; assembling gives `C_q`. -/
theorem sum_col_eval [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    {q : ℕ} (hq : q < m) :
    ∑ j ∈ Finset.range n,
      (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I)
          * ((jacobianLambda' hκs ((j : ℕ) : ZMod n)
              * pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
        + jacobianEdge hκs j * Complex.I
          * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
                * (jacobianLambda' hκs (-1)
                  * pairSign m ((q : ℕ) : ZMod n) (-1))
              + (∑ e ∈ Finset.range j,
                  pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n))
              + chartSlotDeriv (κs ((j : ℕ) : ZMod n))
                  (jacobianBaseLen hκs ((j : ℕ) : ZMod n))
                * (jacobianLambda' hκs ((j : ℕ) : ZMod n)
                  * pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n)) : ℝ) : ℂ))
      = closingJacobianCol m hκs q := by
  have hcastqm : ((q + m : ℕ) : ZMod n)
      = ((q : ℕ) : ZMod n) + (m : ZMod n) := by
    push_cast; ring
  have hexpqm : Complex.exp
        ((heading κs (jacobianBaseLen hκs) (q + m) : ℂ) * Complex.I)
      = -Complex.exp
          ((heading κs (jacobianBaseLen hκs) q : ℂ) * Complex.I) := by
    rw [heading_jacobianBaseLen_add_half hn hn4 hκs hsym]
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  -- split every summand into the four pieces
  have hsplit : ∀ j ∈ Finset.range n,
      (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I)
          * ((jacobianLambda' hκs ((j : ℕ) : ZMod n)
              * pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
        + jacobianEdge hκs j * Complex.I
          * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
                * (jacobianLambda' hκs (-1)
                  * pairSign m ((q : ℕ) : ZMod n) (-1))
              + (∑ e ∈ Finset.range j,
                  pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n))
              + chartSlotDeriv (κs ((j : ℕ) : ZMod n))
                  (jacobianBaseLen hκs ((j : ℕ) : ZMod n))
                * (jacobianLambda' hκs ((j : ℕ) : ZMod n)
                  * pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n)) : ℝ) : ℂ))
      = (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I)
            * ((jacobianLambda' hκs ((j : ℕ) : ZMod n) : ℝ) : ℂ))
          * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
        + ((jacobianEdge hκs j * Complex.I)
            * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
                * (jacobianLambda' hκs (-1)
                  * pairSign m ((q : ℕ) : ZMod n) (-1)) : ℝ) : ℂ)
          + (jacobianEdge hκs j * Complex.I
              * ((∑ e ∈ Finset.range j,
                  pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n) : ℝ) : ℂ)
            + (jacobianEdge hκs j * Complex.I
                * ((chartSlotDeriv (κs ((j : ℕ) : ZMod n))
                      (jacobianBaseLen hκs ((j : ℕ) : ZMod n))
                    * jacobianLambda' hκs ((j : ℕ) : ZMod n) : ℝ) : ℂ))
              * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ))) := by
    intro j _
    push_cast
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Part 1: the `dℓ` sum extracts `2λ'_q·e^{iψ_q}`
  have hP : ∑ j ∈ Finset.range n,
      (Complex.exp ((heading κs (jacobianBaseLen hκs) j : ℂ) * Complex.I)
          * ((jacobianLambda' hκs ((j : ℕ) : ZMod n) : ℝ) : ℂ))
        * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
      = ((2 * jacobianLambda' hκs ((q : ℕ) : ZMod n) : ℝ) : ℂ)
        * Complex.exp
            ((heading κs (jacobianBaseLen hκs) q : ℂ) * Complex.I) := by
    rw [sum_mul_pairSign hn _ hq]
    rw [hexpqm, hcastqm, jacobianLambda'_add_half hκs hsym]
    push_cast
    ring
  -- Part 2a: the constant heading gauge multiplies `ΣE = 0`
  have hQ1 : ∑ j ∈ Finset.range n,
      (jacobianEdge hκs j * Complex.I)
        * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
            * (jacobianLambda' hκs (-1)
              * pairSign m ((q : ℕ) : ZMod n) (-1)) : ℝ) : ℂ)
      = 0 := by
    have : ∀ j ∈ Finset.range n,
        (jacobianEdge hκs j * Complex.I)
          * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
              * (jacobianLambda' hκs (-1)
                * pairSign m ((q : ℕ) : ZMod n) (-1)) : ℝ) : ℂ)
        = jacobianEdge hκs j
          * (Complex.I * ((chartSlotDeriv (κs 0) (jacobianBaseLen hκs (-1))
              * (jacobianLambda' hκs (-1)
                * pairSign m ((q : ℕ) : ZMod n) (-1)) : ℝ) : ℂ)) :=
      fun j _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul,
      sum_jacobianEdge_eq_zero hn hn4 hκs hsym, zero_mul]
  -- Part 2b: the running count contributes the half-block of edges
  have hQ2 : ∑ j ∈ Finset.range n,
      jacobianEdge hκs j * Complex.I
        * ((∑ e ∈ Finset.range j,
            pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n) : ℝ) : ℂ)
      = (∑ r ∈ Finset.Ico (q + 1) (q + m), jacobianEdge hκs r) * Complex.I
        - jacobianEdge hκs q * Complex.I := by
    have hqmn : q + m < n := by omega
    have hstep : ∀ j ∈ Finset.range n,
        jacobianEdge hκs j * Complex.I
          * ((∑ e ∈ Finset.range j,
              pairSign m ((q : ℕ) : ZMod n) ((e : ℕ) : ZMod n) : ℝ) : ℂ)
        = if j ∈ Finset.Ico (q + 1) (q + m + 1)
            then jacobianEdge hκs j * Complex.I else 0 := by
      intro j hj
      rw [sum_pairSign_range hn hq (le_of_lt (Finset.mem_range.mp hj))]
      rcases lt_or_ge q j with h1 | h1
      · rcases lt_or_ge (q + m) j with h2 | h2
        · rw [if_pos h1, if_pos h2,
            if_neg (fun hmem => by
              have := Finset.mem_Ico.mp hmem; omega)]
          push_cast
          ring
        · rw [if_pos h1, if_neg (show ¬(q + m < j) by omega),
            if_pos (Finset.mem_Ico.mpr (by omega))]
          push_cast
          ring
      · rw [if_neg (show ¬(q < j) by omega),
          if_neg (show ¬(q + m < j) by omega),
          if_neg (fun hmem => by
            have := Finset.mem_Ico.mp hmem; omega)]
        push_cast
        ring
    have hsub : Finset.Ico (q + 1) (q + m + 1) ⊆ Finset.range n := fun x hx =>
      Finset.mem_range.mpr (by have := Finset.mem_Ico.mp hx; omega)
    rw [Finset.sum_congr rfl hstep, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr hsub,
      Finset.sum_Ico_succ_top (by omega : q + 1 ≤ q + m),
      jacobianEdge_add_half hn hn4 hκs hsym, Finset.sum_mul]
    ring
  -- Part 2c: the boundary slots contribute `2p_q·E_q·i`
  have hQ3 : ∑ j ∈ Finset.range n,
      (jacobianEdge hκs j * Complex.I
          * ((chartSlotDeriv (κs ((j : ℕ) : ZMod n))
                (jacobianBaseLen hκs ((j : ℕ) : ZMod n))
              * jacobianLambda' hκs ((j : ℕ) : ZMod n) : ℝ) : ℂ))
        * ((pairSign m ((q : ℕ) : ZMod n) ((j : ℕ) : ZMod n) : ℝ) : ℂ)
      = 2 * ((jacobianShare hκs ((q : ℕ) : ZMod n) : ℝ) : ℂ)
        * jacobianEdge hκs q * Complex.I := by
    rw [sum_mul_pairSign hn _ hq]
    rw [jacobianEdge_add_half hn hn4 hκs hsym, hcastqm]
    simp only [tailSlot_mul_lambda' hκs]
    rw [jacobianShare_add_half hκs hsym]
    ring
  rw [hP, hQ1, hQ2, hQ3, closingJacobianCol]
  push_cast
  ring

/-- **The derivative of the anchor gap is the closed-form Jacobian**: at a
half-period-symmetric anchor, `anchorGapDeriv` is exactly the linear map
`(u, v) ↦ u·C_a + v·C_b` with the columns of `def:closing_jacobian_col`. -/
theorem anchorGapDeriv_eq [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {a b : ℕ} (ha : a < m) (hb : b < m) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) :
    anchorGapDeriv m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs
      = (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (closingJacobianCol m hκs a)
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
            (closingJacobianCol m hκs b) := by
  refine ContinuousLinearMap.ext fun w => ?_
  have hEvalA := sum_col_eval hn4 hn hκs hsym ha
  have hEvalB := sum_col_eval hn4 hn hκs hsym hb
  simp only [anchorGapDeriv, sum_apply, add_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Complex.ofRealCLM_apply, anchorCellDeriv, anchorHeadingDeriv, pairCLM,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, Complex.real_smul]
  rw [← hEvalA, ← hEvalB, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  push_cast
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  simp only [jacobianEdge]
  ring

/-! ### The `t = 0` closing rigidity at a nondegenerate symmetric anchor
(`lem:closure_boundary_rigidity`, L3g)

The final assembly: strict differentiability of the anchor gap
(`hasStrictFDerivAt_anchorGap`) with the closed-form derivative
(`anchorGapDeriv_eq`), the `σ_min` lower bound (`norm_smul_add_smul_ge`), and
the vanishing at the center give the direct estimate
`‖F(0,z)‖ ≥ (σ/2)·‖z‖` on a small `ℓ¹`-window — no inverse function
theorem. -/

/-- The clean anchor gap vanishes at the center: the Jacobian base point is
half-period symmetric and keeps the turning constraint, so it closes by
`central_symmetry_closes`. This is the (⇐) direction of
`lem:closure_boundary_rigidity` in clean anchor form. -/
theorem anchorGap_center_eq_zero [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i) :
    anchorGap m a b hκs 0 = 0 := by
  simp only [anchorGap, anchorCell_zero]
  exact central_symmetry_closes hn hsym (jacobianBaseLen_symm hκs hsym)
    (turningSum_jacobianBaseLen hn4 hκs)

/-- **`t = 0` rigidity in clean anchor form** (`lem:closure_boundary_rigidity`,
anchor half): at a half-period-symmetric anchor whose Jacobian columns
`C_a, C_b` are nondegenerate (`Im(conj C_a · C_b) ≠ 0` — which already forces
the perturbed half-pairs to be distinct), the anchor gap vanishes on a small
`ℓ¹`-window only at the center. Direct estimate: strict differentiability
supplies `‖F(0,z) − Lz‖ ≤ (σ/2)‖z‖` near `0`, the `σ_min` bound supplies
`‖Lz‖ ≥ σ(|u|+|v|) ≥ σ‖z‖`, so `‖F(0,z)‖ ≥ (σ/2)‖z‖ > 0` off the center. -/
theorem anchorGap_zero_iff [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {a b : ℕ} (ha : a < m) (hb : b < m) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (hL : ((starRingEnd ℂ) (closingJacobianCol m hκs a)
        * closingJacobianCol m hκs b).im ≠ 0) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ' →
      (anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs z = 0 ↔
        z = 0) := by
  obtain ⟨σ, hσ, hbound⟩ := norm_smul_add_smul_ge hL
  have hd := hasStrictFDerivAt_anchorGap hn4 m ((a : ℕ) : ZMod n)
    ((b : ℕ) : ZMod n) hκs
  rw [anchorGapDeriv_eq hn4 hn ha hb hκs hsym] at hd
  set L : ℝ × ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (closingJacobianCol m hκs a)
      + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (closingJacobianCol m hκs b)
    with hLdef
  have h0 : anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs 0 = 0 :=
    anchorGap_center_eq_zero hn4 hn _ _ hκs hsym
  -- the little-o window of the strict derivative at the center
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hd.hasFDerivAt
  have hev : ∀ᶠ z : ℝ × ℝ in nhds 0,
      ‖anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs z - L z‖
        ≤ σ / 2 * ‖z‖ := by
    have hhalf : (0 : ℝ) < σ / 2 := by positivity
    filter_upwards [Asymptotics.isLittleO_iff.mp hlo hhalf] with z hz
    simpa [h0] using hz
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ0, hδ⟩ := hev
  refine ⟨δ / 2, by positivity, fun z hz => ?_⟩
  have hz1 : ‖z‖ ≤ |z.1| + |z.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _))
  constructor
  · intro hFz
    by_contra hzne
    have hsmall := hδ (show dist z 0 < δ by
      rw [dist_zero_right]; linarith [hz1.trans hz])
    rw [hFz, zero_sub, norm_neg] at hsmall
    have hLz : L z = z.1 • closingJacobianCol m hκs a
        + z.2 • closingJacobianCol m hκs b := by
      simp [hLdef]
    have hlow : σ * (|z.1| + |z.2|) ≤ ‖L z‖ := by
      rw [hLz]; exact hbound z.1 z.2
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
    have hz1pos : 0 < |z.1| + |z.2| := lt_of_lt_of_le hzpos hz1
    have hup : ‖L z‖ ≤ σ / 2 * (|z.1| + |z.2|) :=
      hsmall.trans (mul_le_mul_of_nonneg_left hz1 (by positivity))
    nlinarith
  · rintro rfl
    exact h0

/-- **`t = 0` closing rigidity at a nondegenerate symmetric anchor**
(`lem:closure_boundary_rigidity`, corrected @080): let `n = 2m ≥ 4`, `κˢ` a
positive half-period-symmetric anchor with nondegenerate Jacobian columns
`Im(conj C_a · C_b) ≠ 0` (which already forces the perturbed half-pairs to be
distinct). Then for every radius `ρ > 0` — in particular the window radius of
`exists_closingCell_window`, shrinkable per `closingCell_window_mono` — there
is `0 < ρ' ≤ ρ` such that on the `ℓ¹`-ball of radius `ρ'` the `t = 0` gap map
of the closing 2-cell vanishes only at the center: `F(0,z) = 0 ↔ z = 0`. -/
theorem closingGap_zero_iff [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {a b : ℕ} (ha : a < m) (hb : b < m) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (hL : ((starRingEnd ℂ) (closingJacobianCol m hκs a)
        * closingJacobianCol m hκs b).im ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ z : ℝ × ℝ, |z.1| + |z.2| ≤ ρ' →
      (closingGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs hκ ht0 ht1 z = 0
        ↔ z = 0) := by
  obtain ⟨ρ'', hρ''0, hiff⟩ := anchorGap_zero_iff hn4 hn ha hb hκs hsym hL
  refine ⟨min ρ'' ρ, lt_min hρ''0 hρ, min_le_right _ _, fun z hz => ?_⟩
  rw [closingGap_zero_eq_anchorGap]
  exact hiff z (hz.trans (min_le_left _ _))

/-! ### The two-level witness profile (`lem:anchor_witness_two_level`, @080)

For the constant-κ⁰ class the anchor selector needs an explicit non-constant
positive half-period-symmetric anchor with nondegenerate Jacobian columns
(`Im(conj C_0 · C_1) ≠ 0`). The witness is the *two-level profile*
`κ^(ε) = K + ε·1_{{0,m}}`. This section lands the compositional layer: the
profile and its structural properties, the `(p,q)`-symmetry of the chart
(only three distinct edge charts occur at the two-level profile), and the
exact vanishing of ALL Jacobian columns at the constant base point `ε = 0` —
the ground of the perturbative expansion. -/

/-- The two-level witness profile `κ^(ε)_j = K + ε·[j ∈ {0, m}]`
(`lem:anchor_witness_two_level`). -/
noncomputable def twoLevelProfile (m : ℕ) (K ε : ℝ) : ZMod n → ℝ :=
  fun j => K + (if j = 0 ∨ j = (m : ZMod n) then ε else 0)

/-- The two-level profile at `ε = 0` is the constant profile `K`. -/
theorem twoLevelProfile_zero (m : ℕ) (K : ℝ) :
    twoLevelProfile (n := n) m K 0 = fun _ => K := by
  funext j
  unfold twoLevelProfile
  split_ifs <;> ring

/-- Positivity of the two-level profile for `|ε| < K`. -/
theorem twoLevelProfile_pos {m : ℕ} {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K)
    (j : ZMod n) : 0 < twoLevelProfile m K ε j := by
  have h := abs_lt.mp hε
  unfold twoLevelProfile
  split_ifs <;> linarith [h.1]

/-- Half-period symmetry of the two-level profile: the bump set `{0, m}` is
invariant under the half-period shift (`m + m = 0` in `ZMod (2m)`). -/
theorem twoLevelProfile_symm [NeZero n] {m : ℕ} (hn : n = 2 * m) (K ε : ℝ)
    (i : ZMod n) :
    twoLevelProfile m K ε (i + (m : ZMod n)) = twoLevelProfile m K ε i := by
  have h2m : (m : ZMod n) + (m : ZMod n) = 0 := by
    have h : ((2 * m : ℕ) : ZMod n) = 0 := by
      rw [← hn]; exact ZMod.natCast_self n
    push_cast at h
    linear_combination h
  have hcond : (i + (m : ZMod n) = 0 ∨ i + (m : ZMod n) = (m : ZMod n))
      ↔ (i = 0 ∨ i = (m : ZMod n)) := by
    constructor
    · rintro (h | h)
      · right
        have h' := congrArg (· + (m : ZMod n)) h
        simpa [add_assoc, h2m] using h'
      · left
        have h' := congrArg (· - (m : ZMod n)) h
        simpa using h'
    · rintro (h | h)
      · right; rw [h, zero_add]
      · left; rw [h, h2m]
  unfold twoLevelProfile
  simp only [hcond]

/-- Non-constancy of the two-level profile for `ε ≠ 0`: the bump index `0`
carries `K + ε`, its neighbor `1 ∉ {0, m}` carries `K`. -/
theorem twoLevelProfile_ne_of_ne [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K ε : ℝ} (hε : ε ≠ 0) :
    twoLevelProfile (n := n) m K ε 1 ≠ twoLevelProfile (n := n) m K ε 0 := by
  have hm2 : 2 ≤ m := by omega
  have h10 : (1 : ZMod n) ≠ 0 := by
    intro h
    have h' : ((1 : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) := by simpa using h
    have := natCast_zmod_inj (by omega) (by omega) h'
    omega
  have h1m : (1 : ZMod n) ≠ (m : ZMod n) := by
    intro h
    have h' : ((1 : ℕ) : ZMod n) = ((m : ℕ) : ZMod n) := by simpa using h
    have := natCast_zmod_inj (by omega) (by omega) h'
    omega
  unfold twoLevelProfile
  rw [if_pos (Or.inl rfl), if_neg (by tauto)]
  simpa using hε

/-- The turning chart is symmetric in the two adjacent curvatures. -/
theorem chartMap_comm (p q x : ℝ) : chartMap p q x = chartMap q p x := by
  unfold chartMap
  ring

/-- The edge-length recovery is symmetric in the two adjacent curvatures: at
the two-level profile the four special edges `{n−1, 0, m−1, m}` therefore all
recover the SAME length from the constant chart value. -/
theorem chartInv_comm {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartInv hp hq s = chartInv hq hp s := by
  have hmapeq : chartMap q p = chartMap p q := funext fun x => chartMap_comm q p x
  have hs' : s ∈ chartMap q p '' Set.Ioo (0 : ℝ) (2 / max q p) := by
    rw [hmapeq, max_comm q p]; exact hs
  have h1 := chartInv_mem hp hq hs
  have h2 := chartInv_mem hq hp hs'
  rw [max_comm q p] at h2
  refine (chartMap_strictMonoOn hp hq).injOn h1 h2 ?_
  rw [chartMap_chartInv hp hq hs, chartMap_comm p q, chartMap_chartInv hq hp hs']

/-- **All Jacobian columns vanish at a constant anchor** — the exact
base-point identity grounding the two-level perturbation
(`lem:anchor_witness_two_level`): at `κˢ ≡ K` the anchor gap vanishes
identically near the center (the inscribed-polygon degeneracy
`closureGap_eq_zero_of_const`), so its strict derivative — which
`anchorGapDeriv_eq` evaluates to the columns — is the zero map. -/
theorem closingJacobianCol_const_eq_zero [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) {q : ℕ} (hq : q < m) :
    closingJacobianCol m (fun _ : ZMod n => hK) q = 0 := by
  have hκs : ∀ i : ZMod n, 0 < (fun _ : ZMod n => K) i := fun _ => hK
  have hsym : ∀ i : ZMod n,
      (fun _ : ZMod n => K) (i + (m : ZMod n)) = (fun _ : ZMod n => K) i :=
    fun _ => rfl
  -- the anchor gap vanishes identically near the center
  have hev : (fun _ : ℝ × ℝ => (0 : ℂ)) =ᶠ[nhds 0]
      anchorGap m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs := by
    filter_upwards [eventually_chartPerturb_mem hn4 m ((q : ℕ) : ZMod n)
      ((q : ℕ) : ZMod n) hκs] with z hz
    have hwall : ∀ i : ZMod n,
        |K * (anchorCell m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs z i / 2)|
          ≤ 1 := by
      intro i
      have hmem : anchorCell m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs z i
          ∈ Set.Ioo (0 : ℝ) (2 / K) := by
        simpa [anchorCell, max_self] using chartInv_mem (hκs i) (hκs (i + 1)) (hz i)
      have hKx : anchorCell m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs z i * K
          < 2 := (lt_div_iff₀ hK).mp hmem.2
      rw [abs_of_nonneg (mul_nonneg hK.le
        (div_nonneg hmem.1.le (by norm_num : (0 : ℝ) ≤ 2)))]
      linarith
    have hT : turningSum (fun _ : ZMod n => K)
        (anchorCell m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs z)
          = 2 * Real.pi := by
      rw [turningSum_eq_sum_edgeChart,
        ← sum_chartPerturb (n := n) m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) z]
      exact Finset.sum_congr rfl fun j _ => chartMap_chartInv _ _ (hz j)
    exact (closureGap_eq_zero_of_const hK.ne' hwall hT).symm
  -- hence the strict derivative of the anchor gap at the center is zero
  have hd := hasStrictFDerivAt_anchorGap hn4 m ((q : ℕ) : ZMod n)
    ((q : ℕ) : ZMod n) hκs
  have hzero : HasStrictFDerivAt
      (anchorGap m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs)
      (0 : ℝ × ℝ →L[ℝ] ℂ) 0 :=
    (hasStrictFDerivAt_const (0 : ℂ) (0 : ℝ × ℝ)).congr_of_eventuallyEq hev
  have hD0 : anchorGapDeriv m ((q : ℕ) : ZMod n) ((q : ℕ) : ZMod n) hκs = 0 :=
    hd.hasFDerivAt.unique hzero.hasFDerivAt
  rw [anchorGapDeriv_eq hn4 hn hq hq hκs hsym] at hD0
  simpa using ContinuousLinearMap.ext_iff.mp hD0 (1, 0)

/-! ### The curvature-slot derivative of the edge-length recovery

The two-level witness moves ONE curvature value; the induced motion of the
special-edge base lengths is the scalar function `p ↦ λ_{p,q}(s)` of the first
adjacent curvature. We totalize it (`chartInvCurv`), prove an eventual
membership/round-trip package by squeezing through the strict monotonicity of
the chart in the length slot and continuity in the curvature slot, and get the
strict derivative from the EXPLICIT local left inverse
`Θ(x) = (2/x)·sin(s − arcsin(q·x/2))` — implicit differentiation with no
inverse function theorem, exactly as in the length slot. -/

/-- The edge-length recovery as a (totalized) function of the FIRST adjacent
curvature: `chartInvCurv hq s p = λ_{p,q}(s)` for `p > 0` (junk `0`
otherwise). At the two-level profile the four special edges carry
`chartInvCurv hK (2π/n) (K + ε)` (up to `chartInv_comm`). -/
noncomputable def chartInvCurv {q : ℝ} (hq : 0 < q) (s : ℝ) (p : ℝ) : ℝ :=
  if h : 0 < p then chartInv h hq s else 0

/-- On positive curvature the totalization is the chart inverse. -/
theorem chartInvCurv_of_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (s : ℝ) :
    chartInvCurv hq s p = chartInv hp hq s := dif_pos hp

/-- **The eventual membership/round-trip package in the curvature slot**: if
`s` is achieved at the pair `(p₀, q)` then, for every sandwich
`x₁ < λ_{p₀,q}(s) < x₂` inside the moderate window, all curvatures `p` near
`p₀` are positive, achieve `s`, recover it (round trip), stay moderate, and
keep the recovered length inside `(x₁, x₂)`. This single filter statement
drives both the continuity and the differentiability of `chartInvCurv`. -/
theorem eventually_chartInvCurv_mem {p₀ q : ℝ} (hp₀ : 0 < p₀) (hq : 0 < q)
    {s x₁ x₂ : ℝ} (hs : s ∈ chartMap p₀ q '' Set.Ioo (0 : ℝ) (2 / max p₀ q))
    (h₁ : 0 < x₁) (h₁lt : x₁ < chartInv hp₀ hq s)
    (h₂gt : chartInv hp₀ hq s < x₂) (h₂ : x₂ < 2 / max p₀ q) :
    ∀ᶠ p in nhds p₀, 0 < p ∧
      s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) ∧
      chartMap p q (chartInvCurv hq s p) = s ∧
      chartInvCurv hq s p ∈ Set.Ioo (0 : ℝ) (2 / max p q) ∧
      chartInvCurv hq s p ∈ Set.Ioo x₁ x₂ := by
  have hx₀ := chartInv_mem hp₀ hq hs
  have hround₀ : chartMap p₀ q (chartInv hp₀ hq s) = s := chartMap_chartInv hp₀ hq hs
  -- the chart at a FIXED length is continuous in the curvature slot
  have hc : ∀ x : ℝ, ContinuousAt (fun p : ℝ => chartMap p q x) p₀ := by
    intro x
    unfold chartMap
    exact ((Real.continuous_arcsin.comp
      ((continuous_id.mul continuous_const).div_const 2)).add
      continuous_const).continuousAt
  have hE1 : ∀ᶠ p : ℝ in nhds p₀, 0 < p := eventually_gt_nhds hp₀
  have hwallcont : ContinuousAt (fun p : ℝ => 2 / max p q) p₀ :=
    ContinuousAt.div continuousAt_const (continuousAt_id.max continuousAt_const)
      (lt_of_lt_of_le hq (le_max_right p₀ q)).ne'
  have hE2 : ∀ᶠ p in nhds p₀, x₂ < 2 / max p q :=
    hwallcont.tendsto.eventually_const_lt h₂
  have hE3 : ∀ᶠ p in nhds p₀, chartMap p q x₁ < s := by
    have hlt : chartMap p₀ q x₁ < s := by
      rw [← hround₀]
      exact chartMap_strictMonoOn hp₀ hq ⟨h₁, lt_trans h₁lt hx₀.2⟩ hx₀ h₁lt
    exact (hc x₁).tendsto.eventually_lt_const hlt
  have hE4 : ∀ᶠ p in nhds p₀, s < chartMap p q x₂ := by
    have hlt : s < chartMap p₀ q x₂ := by
      rw [← hround₀]
      exact chartMap_strictMonoOn hp₀ hq hx₀ ⟨lt_trans hx₀.1 h₂gt, h₂⟩ h₂gt
    exact (hc x₂).tendsto.eventually_const_lt hlt
  filter_upwards [hE1, hE2, hE3, hE4] with p hp1 hp2 hp3 hp4
  have hIcc : s ∈ chartMap p q '' Set.Icc x₁ x₂ :=
    chartMap_mem_image_Icc (by linarith [lt_trans h₁lt h₂gt]) ⟨hp3.le, hp4.le⟩
  have hx₁mem : x₁ ∈ Set.Ioo (0 : ℝ) (2 / max p q) :=
    ⟨h₁, by linarith [lt_trans h₁lt h₂gt]⟩
  have hx₂mem : x₂ ∈ Set.Ioo (0 : ℝ) (2 / max p q) :=
    ⟨lt_trans h₁ (lt_trans h₁lt h₂gt), hp2⟩
  have hsub : Set.Icc x₁ x₂ ⊆ Set.Ioo (0 : ℝ) (2 / max p q) := fun w hw =>
    ⟨lt_of_lt_of_le h₁ hw.1, lt_of_le_of_lt hw.2 hp2⟩
  have hmem : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q) :=
    Set.image_mono hsub hIcc
  have hval : chartInvCurv hq s p = chartInv hp1 hq s := dif_pos hp1
  have hmem' := chartInv_mem hp1 hq hmem
  have hround : chartMap p q (chartInv hp1 hq s) = s :=
    chartMap_chartInv hp1 hq hmem
  refine ⟨hp1, hmem, by rw [hval]; exact hround, by rw [hval]; exact hmem', ?_⟩
  rw [hval]
  constructor
  · exact ((chartMap_strictMonoOn hp1 hq).lt_iff_lt hx₁mem hmem').mp
      (by rw [hround]; exact hp3)
  · exact ((chartMap_strictMonoOn hp1 hq).lt_iff_lt hmem' hx₂mem).mp
      (by rw [hround]; exact hp4)

/-- Continuity of the edge-length recovery in the curvature slot at any
achieved turning value: the ε-window `(λ(s) − δ, λ(s) + δ)` is captured by
the eventual sandwich of `eventually_chartInvCurv_mem`. -/
theorem continuousAt_chartInvCurv {p₀ q : ℝ} (hp₀ : 0 < p₀) (hq : 0 < q)
    {s : ℝ} (hs : s ∈ chartMap p₀ q '' Set.Ioo (0 : ℝ) (2 / max p₀ q)) :
    ContinuousAt (chartInvCurv hq s) p₀ := by
  have hx₀ := chartInv_mem hp₀ hq hs
  have hval₀ : chartInvCurv hq s p₀ = chartInv hp₀ hq s := dif_pos hp₀
  rw [ContinuousAt, hval₀, Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := min (ε / 2)
    (min (chartInv hp₀ hq s / 2) ((2 / max p₀ q - chartInv hp₀ hq s) / 2))
    with hδdef
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ chartInv hp₀ hq s / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ (2 / max p₀ q - chartInv hp₀ hq s) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hδ0 : 0 < δ := lt_min (by linarith)
    (lt_min (by linarith [hx₀.1]) (by linarith [hx₀.2]))
  filter_upwards [eventually_chartInvCurv_mem hp₀ hq hs
    (x₁ := chartInv hp₀ hq s - δ) (x₂ := chartInv hp₀ hq s + δ)
    (by linarith [hx₀.1]) (by linarith) (by linarith) (by linarith [hx₀.2])]
    with p hp
  obtain ⟨-, -, -, -, hIoo⟩ := hp
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [hIoo.1], by linarith [hIoo.2]⟩

/-- **Strict differentiability of the edge-length recovery in the curvature
slot** at any achieved turning value, with the implicit-function value
`∂λ/∂p = −(λ/p)·A/(A + B)` (at the symmetric point `p = q = K`,
`s = 2π/n` this is the `ℓ̇ = −ℓ/2K` of `lem:anchor_witness_two_level`).
Route: `Θ(x) = (2/x)·sin(s − arcsin(q·x/2))` is an explicit local left
inverse of `p ↦ λ_{p,q}(s)` — solving the chart equation for the FIRST
curvature — so `HasStrictDerivAt.of_local_left_inverse` applies with the
continuity supplied by `continuousAt_chartInvCurv`. -/
theorem hasStrictDerivAt_chartInvCurv {p₀ q : ℝ} (hp₀ : 0 < p₀) (hq : 0 < q)
    {s : ℝ} (hs : s ∈ chartMap p₀ q '' Set.Ioo (0 : ℝ) (2 / max p₀ q)) :
    HasStrictDerivAt (chartInvCurv hq s)
      (-(chartInv hp₀ hq s
          * (chartSlotDeriv p₀ (chartInv hp₀ hq s)
            / (chartSlotDeriv p₀ (chartInv hp₀ hq s)
              + chartSlotDeriv q (chartInv hp₀ hq s)))
          / p₀)) p₀ := by
  have hmem := chartInv_mem hp₀ hq hs
  set x₀ : ℝ := chartInv hp₀ hq s with hx₀def
  have hx₀pos : 0 < x₀ := hmem.1
  have hwallp : |p₀ * x₀ / 2| < 1 := by
    have h := chartArg_mem hp₀ hq hmem hp₀ (le_max_left p₀ q)
    exact abs_lt.mpr ⟨h.1, h.2⟩
  have hwallq : |q * x₀ / 2| < 1 := by
    have h := chartArg_mem hp₀ hq hmem hq (le_max_right p₀ q)
    exact abs_lt.mpr ⟨h.1, h.2⟩
  have hround : chartMap p₀ q x₀ = s := chartMap_chartInv hp₀ hq hs
  set θ : ℝ → ℝ := fun x => s - Real.arcsin (q * x / 2) with hθdef
  have hθx₀ : θ x₀ = Real.arcsin (p₀ * x₀ / 2) := by
    have h := hround
    unfold chartMap at h
    rw [hθdef]
    dsimp only
    linarith
  have hsin_val : Real.sin (θ x₀) = p₀ * x₀ / 2 := by
    have hlt := abs_lt.mp hwallp
    rw [hθx₀, Real.sin_arcsin (by linarith) (by linarith)]
  have hcos_eq : Real.cos (θ x₀) = Real.sqrt (1 - (p₀ * x₀ / 2) ^ 2) := by
    rw [hθx₀, Real.cos_arcsin]
  have hsq_pos : 0 < 1 - (p₀ * x₀ / 2) ^ 2 := by
    have hlt := abs_lt.mp hwallp
    nlinarith
  have hcos_pos : 0 < Real.cos (θ x₀) := by
    rw [hcos_eq]
    exact Real.sqrt_pos.mpr hsq_pos
  -- the explicit left inverse and its strict derivative at the base length
  have hx₀ne : x₀ ≠ 0 := hx₀pos.ne'
  have hdiv : HasStrictDerivAt (fun x : ℝ => 2 / x) (-(2 / x₀ ^ 2)) x₀ := by
    have h := (hasStrictDerivAt_inv hx₀ne).const_mul (2 : ℝ)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinner : HasStrictDerivAt θ (-(chartSlotDeriv q x₀)) x₀ := by
    rw [hθdef]
    exact (hasStrictDerivAt_arcsinSlot hwallq).const_sub s
  have hsin : HasStrictDerivAt (fun x => Real.sin (θ x))
      (Real.cos (θ x₀) * -(chartSlotDeriv q x₀)) x₀ :=
    (Real.hasStrictDerivAt_sin _).comp x₀ hinner
  have hΘ : HasStrictDerivAt (fun x : ℝ => 2 / x * Real.sin (θ x))
      (-(2 / x₀ ^ 2) * Real.sin (θ x₀)
        + 2 / x₀ * (Real.cos (θ x₀) * -(chartSlotDeriv q x₀))) x₀ :=
    hdiv.mul hsin
  have hA := chartSlotDeriv_pos hp₀ hwallp
  have hB := chartSlotDeriv_pos hq hwallq
  -- the derivative of the left inverse is negative, in particular nonzero
  have hΘ'neg : -(2 / x₀ ^ 2) * Real.sin (θ x₀)
      + 2 / x₀ * (Real.cos (θ x₀) * -(chartSlotDeriv q x₀)) < 0 := by
    have h1 : 0 < Real.sin (θ x₀) := by rw [hsin_val]; positivity
    have h2 : 0 < 2 / x₀ ^ 2 := by positivity
    have h3 : 0 < 2 / x₀ := by positivity
    nlinarith [mul_pos h2 h1, mul_pos h3 (mul_pos hcos_pos hB)]
  -- the eventual round trip `Θ (λ_{p,q}(s)) = p`
  have hev : ∀ᶠ p in nhds p₀,
      (fun x : ℝ => 2 / x * Real.sin (θ x)) (chartInvCurv hq s p) = p := by
    filter_upwards [eventually_chartInvCurv_mem hp₀ hq hs
      (x₁ := x₀ / 2) (x₂ := (x₀ + 2 / max p₀ q) / 2)
      (by positivity) (by linarith) (by linarith [hmem.2]) (by linarith [hmem.2])]
      with p hp
    obtain ⟨hppos, -, hroundp, hIoo, -⟩ := hp
    set x' : ℝ := chartInvCurv hq s p with hx'def
    have hx'pos : 0 < x' := hIoo.1
    have hwall' : p * x' / 2 < 1 := by
      have hmaxp : p ≤ max p q := le_max_left p q
      have h2 : x' < 2 / max p q := hIoo.2
      have hmax0 : 0 < max p q := lt_of_lt_of_le hppos hmaxp
      have : x' * max p q < 2 := (lt_div_iff₀ hmax0).mp h2
      nlinarith
    have hθx' : θ x' = Real.arcsin (p * x' / 2) := by
      have h := hroundp
      unfold chartMap at h
      rw [hθdef]
      dsimp only
      linarith
    have hlow : (-1 : ℝ) ≤ p * x' / 2 := by
      have h0 : (0 : ℝ) ≤ p * x' / 2 := by positivity
      linarith
    have hsin' : Real.sin (θ x') = p * x' / 2 := by
      rw [hθx', Real.sin_arcsin hlow hwall'.le]
    change 2 / x' * Real.sin (θ x') = p
    rw [hsin']
    field_simp
  -- assemble via the local-left-inverse rule and simplify the value
  have hval₀ : chartInvCurv hq s p₀ = x₀ := dif_pos hp₀
  have hcont := continuousAt_chartInvCurv hp₀ hq hs
  rw [← hval₀] at hΘ
  have hmain := HasStrictDerivAt.of_local_left_inverse hcont hΘ
    (by rw [hval₀]; exact hΘ'neg.ne) hev
  have hS₂pos : 0 < Real.sqrt (1 - (q * x₀ / 2) ^ 2) := by
    have hlt := abs_lt.mp hwallq
    apply Real.sqrt_pos.mpr
    nlinarith
  have hcos_A : Real.cos (θ x₀) = p₀ / (2 * chartSlotDeriv p₀ x₀) := by
    have hs₁ : (0 : ℝ) < Real.sqrt (1 - (p₀ * x₀ / 2) ^ 2) :=
      Real.sqrt_pos.mpr hsq_pos
    rw [hcos_eq]
    unfold chartSlotDeriv
    field_simp
  have hderiv_eq : (-(2 / x₀ ^ 2) * Real.sin (θ x₀)
      + 2 / x₀ * (Real.cos (θ x₀) * -(chartSlotDeriv q x₀)))⁻¹
      = -(x₀ * (chartSlotDeriv p₀ x₀
          / (chartSlotDeriv p₀ x₀ + chartSlotDeriv q x₀)) / p₀) := by
    rw [hsin_val, hcos_A]
    have hAB : 0 < chartSlotDeriv p₀ x₀ + chartSlotDeriv q x₀ := add_pos hA hB
    refine inv_eq_of_mul_eq_one_right ?_
    field_simp
    ring
  rw [hval₀, hderiv_eq] at hmain
  exact hmain

/-! ### The two-level chart data: piecewise base lengths

At the two-level profile only the four edges `{0, m−1, m, n−1}` touch a bump
vertex; they all recover the SAME length `chartInvCurv hK (2π/n) (K+ε)` (the
two second-slot cases via `chartInv_comm`), while every other edge carries the
`ε`-independent constant-pair length. This is the piecewise identification
that reduces the `ε`-differentiation of ALL Jacobian data to the single
scalar `hasStrictDerivAt_chartInvCurv`. -/

/-- The two-level profile at a lifted index `j < n`: the bump hits exactly
`j ∈ {0, m}` (as naturals). -/
theorem twoLevelProfile_natCast [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (K ε : ℝ) {j : ℕ} (hj : j < n) :
    twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n)
      = K + (if j = 0 ∨ j = m then ε else 0) := by
  have hm : m < n := by omega
  unfold twoLevelProfile
  congr 1
  by_cases h0 : j = 0 ∨ j = m
  · rw [if_pos h0]
    rcases h0 with rfl | rfl
    · rw [if_pos (Or.inl (by norm_cast))]
    · rw [if_pos (Or.inr rfl)]
  · rw [if_neg ?_, if_neg h0]
    rintro (hc | hc)
    · exact h0 (Or.inl (natCast_zmod_inj hj (by omega)
        (by simpa using hc)))
    · exact h0 (Or.inr (natCast_zmod_inj hj hm hc))

/-- The two-level profile at the SUCCESSOR of a lifted index `j < n`: the
head vertex of edge `j` is a bump vertex exactly for `j ∈ {m−1, n−1}`. -/
theorem twoLevelProfile_natCast_succ [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (K ε : ℝ) {j : ℕ} (hj : j < n) :
    twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1)
      = K + (if j = m - 1 ∨ j = n - 1 then ε else 0) := by
  have hm1 : 1 ≤ m := by omega
  have hcast : ((j : ℕ) : ZMod n) + 1 = (((j + 1 : ℕ)) : ZMod n) := by push_cast; ring
  rw [hcast]
  by_cases hlast : j + 1 = n
  · have hj' : j = n - 1 := by omega
    rw [hlast, ZMod.natCast_self]
    have h0 : (0 : ZMod n) = ((0 : ℕ) : ZMod n) := by norm_cast
    rw [h0, twoLevelProfile_natCast hn K ε (by omega : 0 < n)]
    rw [if_pos (Or.inl rfl), if_pos (Or.inr hj')]
  · have hj1 : j + 1 < n := by omega
    rw [twoLevelProfile_natCast hn K ε hj1]
    congr 1
    by_cases hcond : j = m - 1 ∨ j = n - 1
    · rcases hcond with rfl | rfl
      · rw [if_pos (Or.inr (by omega)), if_pos (Or.inl rfl)]
      · omega
    · rw [if_neg (by omega), if_neg hcond]

/-- **Piecewise base lengths at the two-level profile**: the four special
edges `{0, m−1, m, n−1}` recover `chartInvCurv hK (2π/n) (K+ε)`, every other
edge recovers the constant-pair length — the `ε`-dependence of the whole base
polygon lives in ONE scalar. -/
theorem jacobianBaseLen_twoLevel [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K)
    {j : ℕ} (hj : j < n) :
    jacobianBaseLen (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i)
        ((j : ℕ) : ZMod n)
      = if j = 0 ∨ j = m - 1 ∨ j = m ∨ j = n - 1
        then chartInvCurv hK (2 * Real.pi / n) (K + ε)
        else chartInv hK hK (2 * Real.pi / n) := by
  have hm2 : 2 ≤ m := by omega
  have hKε : 0 < K + ε := by have := abs_lt.mp hε; linarith
  have hcongr : ∀ {p p' q q' : ℝ} (hp : 0 < p) (hq : 0 < q) (hp' : 0 < p')
      (hq' : 0 < q') (s : ℝ), p = p' → q = q' →
      chartInv hp hq s = chartInv hp' hq' s := by
    intro p p' q q' hp hq hp' hq' s hpe hqe
    subst hpe; subst hqe; rfl
  have h1 := twoLevelProfile_natCast (n := n) hn K ε hj
  have h2 := twoLevelProfile_natCast_succ (n := n) hn K ε hj
  -- membership of the base value at this edge, for transport through comm
  have hmem := base_chart_mem_image hn4
    (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i) ((j : ℕ) : ZMod n)
  unfold jacobianBaseLen
  by_cases hsp : j = 0 ∨ j = m - 1 ∨ j = m ∨ j = n - 1
  · rw [if_pos hsp]
    obtain h | h | h | h := hsp
    · -- edge 0: pair (K + ε, K), bump in the tail slot
      have hv1 : twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n) = K + ε := by
        rw [h1, if_pos (Or.inl h)]
      have hv2 : twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1) = K := by
        rw [h2, if_neg (by omega), add_zero]
      rw [chartInvCurv_of_pos hKε hK]
      exact hcongr _ _ hKε hK _ hv1 hv2
    · -- edge m − 1: pair (K, K + ε), bump in the head slot
      have hv1 : twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n) = K := by
        rw [h1, if_neg (by omega), add_zero]
      have hv2 : twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1)
          = K + ε := by
        rw [h2, if_pos (Or.inl h)]
      rw [hv1, hv2] at hmem
      rw [chartInvCurv_of_pos hKε hK,
        ← chartInv_comm hK hKε hmem]
      exact hcongr _ _ hK hKε _ hv1 hv2
    · -- edge m: pair (K + ε, K), bump in the tail slot
      have hv1 : twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n) = K + ε := by
        rw [h1, if_pos (Or.inr h)]
      have hv2 : twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1) = K := by
        rw [h2, if_neg (by omega), add_zero]
      rw [chartInvCurv_of_pos hKε hK]
      exact hcongr _ _ hKε hK _ hv1 hv2
    · -- edge n − 1: pair (K, K + ε), bump in the head slot
      have hv1 : twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n) = K := by
        rw [h1, if_neg (by omega), add_zero]
      have hv2 : twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1)
          = K + ε := by
        rw [h2, if_pos (Or.inr h)]
      rw [hv1, hv2] at hmem
      rw [chartInvCurv_of_pos hKε hK,
        ← chartInv_comm hK hKε hmem]
      exact hcongr _ _ hK hKε _ hv1 hv2
  · rw [if_neg hsp]
    simp only [not_or] at hsp
    obtain ⟨hs0, hsm1, hsm, hsn1⟩ := hsp
    have hv1 : twoLevelProfile (n := n) m K ε ((j : ℕ) : ZMod n) = K := by
      rw [h1, if_neg (by omega), add_zero]
    have hv2 : twoLevelProfile (n := n) m K ε (((j : ℕ) : ZMod n) + 1) = K := by
      rw [h2, if_neg (by omega), add_zero]
    exact hcongr _ _ hK hK _ hv1 hv2

/-! ### Constant-pair evaluations and the two-level length derivative

The explicit base-point data of `lem:anchor_witness_two_level` at `ε = 0`:
the constant-pair base length `ℓ = 2·sin(π/n)/K`, the slot derivative
`A = K/(2·cos(π/n))`, hence `λ' = cos(π/n)/K` and `p = 1/2`; and the strict
derivative `ℓ̇* = −sin(π/n)/K²` of the special-edge length in `ε`. -/

/-- The constant-pair base length is explicit: `λ_{K,K}(2π/n) = 2·sin(π/n)/K`
(the inscribed chord of the circle of radius `1/K` under central angle
`2π/n`). -/
theorem chartInv_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K) :
    chartInv hK hK (2 * Real.pi / n) = 2 * Real.sin (Real.pi / n) / K := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρle : Real.pi / n ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left hπ.le four_pos hn4'
  have hρhalf : Real.pi / n < Real.pi / 2 := lt_of_le_of_lt hρle (by linarith)
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hsin1 : Real.sin (Real.pi / n) < 1 := by
    have h := Real.strictMonoOn_sin (a := Real.pi / n) (b := Real.pi / 2)
      ⟨by linarith, hρhalf.le⟩ ⟨by linarith, le_refl _⟩ hρhalf
    simpa [Real.sin_pi_div_two] using h
  have hx0 : 0 < 2 * Real.sin (Real.pi / n) / K := by positivity
  have hxlt : 2 * Real.sin (Real.pi / n) / K < 2 / K := by
    have h2 : 2 * Real.sin (Real.pi / n) * K⁻¹ < 2 * K⁻¹ :=
      mul_lt_mul_of_pos_right (by linarith) (inv_pos.mpr hK)
    simpa [div_eq_mul_inv] using h2
  have hx : 2 * Real.sin (Real.pi / n) / K ∈
      Set.Ioo (0 : ℝ) (2 / max K K) := by
    rw [max_self]
    exact ⟨hx0, hxlt⟩
  have hmap : chartMap K K (2 * Real.sin (Real.pi / n) / K)
      = 2 * Real.pi / n := by
    unfold chartMap
    have harg : K * (2 * Real.sin (Real.pi / n) / K) / 2
        = Real.sin (Real.pi / n) := by
      field_simp
    rw [harg, Real.arcsin_sin (by linarith) hρhalf.le]
    ring
  rw [← hmap, chartInv_chartMap hK hK hx]

/-- The slot derivative at the constant-pair base length:
`A = K/(2·cos(π/n))`. -/
theorem chartSlotDeriv_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K) :
    chartSlotDeriv K (2 * Real.sin (Real.pi / n) / K)
      = K / (2 * Real.cos (Real.pi / n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hρ0 : (0 : ℝ) ≤ Real.pi / n := by positivity
  unfold chartSlotDeriv
  have harg : K * (2 * Real.sin (Real.pi / n) / K) / 2
      = Real.sin (Real.pi / n) := by
    field_simp
  rw [harg, ← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) hρhalf.le]

/-- `λ'` at a constant anchor: `cos(π/n)/K`, every edge. -/
theorem jacobianLambda'_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K)
    (j : ZMod n) :
    jacobianLambda' (fun _ : ZMod n => hK) j = Real.cos (Real.pi / n) / K := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hρ0 : (0 : ℝ) ≤ Real.pi / n := by positivity
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  unfold jacobianLambda'
  rw [show jacobianBaseLen (fun _ : ZMod n => hK) j
      = chartInv hK hK (2 * Real.pi / n) from rfl,
    chartInv_const hn4 hK, chartSlotDeriv_const hn4 hK]
  field_simp
  ring

/-- The tail-slot share at a constant anchor is `1/2` — killing the
`(2p−1)·E_q` boundary term of the columns at the base point. -/
theorem jacobianShare_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K)
    (j : ZMod n) :
    jacobianShare (fun _ : ZMod n => hK) j = 1 / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hρ0 : (0 : ℝ) ≤ Real.pi / n := by positivity
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  unfold jacobianShare
  rw [show jacobianBaseLen (fun _ : ZMod n => hK) j
      = chartInv hK hK (2 * Real.pi / n) from rfl,
    chartInv_const hn4 hK, chartSlotDeriv_const hn4 hK]
  field_simp
  ring

/-- **The two-level length derivative** (`lem:anchor_witness_two_level`,
first-order table): the special-edge base length moves with strict
`ε`-derivative `ℓ̇* = −sin(π/n)/K²` (i.e. `−ℓ/(2K)`) at `ε = 0`. -/
theorem hasStrictDerivAt_twoLevelLen [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt
      (fun ε : ℝ => chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
      (-(Real.sin (Real.pi / n) / K ^ 2)) 0 := by
  have hmem : 2 * Real.pi / (n : ℝ) ∈ chartMap K K ''
      Set.Ioo (0 : ℝ) (2 / max K K) :=
    base_chart_mem_image hn4 (fun _ : ZMod n => hK) 0
  have hd := hasStrictDerivAt_chartInvCurv (p₀ := K) hK hK hmem
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hρ0 : (0 : ℝ) ≤ Real.pi / n := by positivity
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  -- simplify the derivative value first, then shift the base point
  rw [chartInv_const hn4 hK, chartSlotDeriv_const hn4 hK] at hd
  have hval : -(2 * Real.sin (Real.pi / n) / K
        * (K / (2 * Real.cos (Real.pi / n))
          / (K / (2 * Real.cos (Real.pi / n))
            + K / (2 * Real.cos (Real.pi / n))))
        / K)
      = -(Real.sin (Real.pi / n) / K ^ 2) := by
    field_simp
    ring
  rw [hval] at hd
  have hd' : HasStrictDerivAt (chartInvCurv hK (2 * Real.pi / (n : ℝ)))
      (-(Real.sin (Real.pi / n) / K ^ 2)) (K + 0) := by
    rw [add_zero]
    exact hd
  have hshift : HasStrictDerivAt (fun ε : ℝ => K + ε) 1 0 := by
    simpa using (hasStrictDerivAt_id (0 : ℝ)).const_add K
  simpa [Function.comp_def] using hd'.comp 0 hshift

/-- Every turning angle of the constant base polygon is `2π/n`. -/
theorem turningAngle_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K)
    (i : ZMod n) :
    turningAngle 0 (fun _ : ZMod n => K)
        (fun _ : ZMod n => 2 * Real.sin (Real.pi / n) / K) i
      = 2 * Real.pi / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hρ0 : (0 : ℝ) ≤ Real.pi / n := by positivity
  have harg : K * (2 * Real.sin (Real.pi / n) / K / 2)
      = Real.sin (Real.pi / n) := by
    field_simp
  unfold turningAngle
  dsimp only
  rw [tK_zero, harg, Real.arcsin_sin (by linarith) hρhalf.le]
  ring

/-- Heading of the constant base polygon: `ψ_j = (j+1)·(2π/n)` — the
blueprint gauge of `lem:anchor_witness_two_level` (base point
`E_r = ℓ·e^{i(r+1)α}`, `α = 2π/n`). -/
theorem heading_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K) (j : ℕ) :
    heading (fun _ : ZMod n => K)
        (fun _ : ZMod n => 2 * Real.sin (Real.pi / n) / K) j
      = ((j : ℝ) + 1) * (2 * Real.pi / n) := by
  unfold heading
  rw [Finset.sum_congr rfl fun i _ => turningAngle_const hn4 hK _,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The edge vectors of the constant base polygon:
`E_r = ℓ·e^{i(r+1)α}` with `ℓ = 2·sin(π/n)/K` and `α = 2π/n`. -/
theorem jacobianEdge_const [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K)
    (r : ℕ) :
    jacobianEdge (fun _ : ZMod n => hK) r
      = ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
        * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
            * Complex.I) := by
  have hfun : jacobianBaseLen (fun _ : ZMod n => hK)
      = fun _ : ZMod n => 2 * Real.sin (Real.pi / n) / K :=
    funext fun j => chartInv_const hn4 hK
  unfold jacobianEdge
  rw [hfun, heading_const hn4 hK r]

/-! ### The moving arcsin slots of the two-level turning angles

Every `ε`-dependent arcsin slot of the two-level turning angles has one of
two shapes: the *bump slot* `arcsin((K+ε)·ℓ*(ε)/2)` (bump curvature times
special length) and the *mixed slot* `arcsin(K·ℓ*(ε)/2)` (constant curvature
times special length). Their derivatives `±tan(π/n)/(2K)` are the `ȧ`-table
of `lem:anchor_witness_two_level`; all other slots are constant in `ε`. -/

/-- The bump arcsin slot moves with strict derivative `tan(π/n)/(2K)` at
`ε = 0` (`ȧ₀ = t/2K` in the blueprint's first-order table). -/
theorem hasStrictDerivAt_bumpSlot [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt (fun ε : ℝ => Real.arcsin
        ((K + ε) * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2))
      (Real.tan (Real.pi / n) / (2 * K)) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hsin1 : Real.sin (Real.pi / n) < 1 := by
    have h := Real.strictMonoOn_sin (a := Real.pi / n) (b := Real.pi / 2)
      ⟨by linarith, hρhalf.le⟩ ⟨by linarith, le_refl _⟩ hρhalf
    simpa [Real.sin_pi_div_two] using h
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hval0 : chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)
      = 2 * Real.sin (Real.pi / n) / K := by
    rw [add_zero, chartInvCurv_of_pos hK hK, chartInv_const hn4 hK]
  have hshift : HasStrictDerivAt (fun ε : ℝ => K + ε) 1 0 := by
    simpa using (hasStrictDerivAt_id (0 : ℝ)).const_add K
  have hlen := hasStrictDerivAt_twoLevelLen (n := n) hn4 hK
  have hprod := (hshift.mul hlen).div_const 2
  have hg0 : (K + (0 : ℝ))
        * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2
      = Real.sin (Real.pi / n) := by
    rw [hval0, add_zero]
    field_simp
  have harc : HasStrictDerivAt Real.arcsin
      (1 / Real.sqrt (1 - Real.sin (Real.pi / n) ^ 2))
      ((K + (0 : ℝ)) * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) := by
    rw [hg0]
    exact Real.hasStrictDerivAt_arcsin (by linarith) hsin1.ne
  have hcomp := harc.comp 0 hprod
  simp only [Function.comp_def] at hcomp
  have hderiv : 1 / Real.sqrt (1 - Real.sin (Real.pi / n) ^ 2)
      * ((1 * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)
          + (K + 0) * -(Real.sin (Real.pi / n) / K ^ 2)) / 2)
      = Real.tan (Real.pi / n) / (2 * K) := by
    rw [hval0, add_zero, ← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith)
      hρhalf.le, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  rw [hderiv] at hcomp
  simpa [Pi.mul_apply] using hcomp

/-- The mixed arcsin slot moves with strict derivative `−tan(π/n)/(2K)` at
`ε = 0` (the `−t/2K` entries of the blueprint's first-order table). -/
theorem hasStrictDerivAt_mixedSlot [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt (fun ε : ℝ => Real.arcsin
        (K * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2))
      (-(Real.tan (Real.pi / n) / (2 * K))) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hsin1 : Real.sin (Real.pi / n) < 1 := by
    have h := Real.strictMonoOn_sin (a := Real.pi / n) (b := Real.pi / 2)
      ⟨by linarith, hρhalf.le⟩ ⟨by linarith, le_refl _⟩ hρhalf
    simpa [Real.sin_pi_div_two] using h
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hval0 : chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)
      = 2 * Real.sin (Real.pi / n) / K := by
    rw [add_zero, chartInvCurv_of_pos hK hK, chartInv_const hn4 hK]
  have hlen := hasStrictDerivAt_twoLevelLen (n := n) hn4 hK
  have hprod := (hlen.const_mul K).div_const 2
  have hg0 : K * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2
      = Real.sin (Real.pi / n) := by
    rw [hval0]
    field_simp
  have harc : HasStrictDerivAt Real.arcsin
      (1 / Real.sqrt (1 - Real.sin (Real.pi / n) ^ 2))
      (K * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) := by
    rw [hg0]
    exact Real.hasStrictDerivAt_arcsin (by linarith) hsin1.ne
  have hcomp := harc.comp 0 hprod
  simp only [Function.comp_def] at hcomp
  have hderiv : 1 / Real.sqrt (1 - Real.sin (Real.pi / n) ^ 2)
      * (K * -(Real.sin (Real.pi / n) / K ^ 2) / 2)
      = -(Real.tan (Real.pi / n) / (2 * K)) := by
    rw [← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) hρhalf.le,
      Real.tan_eq_sin_div_cos]
    field_simp
  rw [hderiv] at hcomp
  exact hcomp

/-! ### The ε-total two-level Jacobian data (`lem:anchor_witness_two_level`, R1)

`ε ↦ jacobianBaseLen (twoLevelProfile_pos hK hε)` is not globally well-formed —
the positivity proof needs `|ε| < K` — so the `ε`-differentiation happens on
the TOTAL piecewise functions below, which agree with the Jacobian data on the
window `|ε| < K` (via `jacobianBaseLen_twoLevel`) and are honest functions of
`ε`. The bridge back is `HasStrictDerivAt.congr_of_eventuallyEq` on `|ε| < K`. -/

/-- The ε-total two-level base length of edge `j` (lifted index): the four
special edges carry the moving scalar `chartInvCurv hK (2π/n) (K+ε)`, the rest
the constant-pair length. Agrees with `jacobianBaseLen` of the two-level
profile on the window `|ε| < K` (`twoLevelBaseLen_eq`). -/
noncomputable def twoLevelBaseLen (m : ℕ) {K : ℝ} (hK : 0 < K) (ε : ℝ)
    (j : ℕ) : ℝ :=
  if j = 0 ∨ j = m - 1 ∨ j = m ∨ j = n - 1
  then chartInvCurv hK (2 * Real.pi / n) (K + ε)
  else chartInv hK hK (2 * Real.pi / n)

/-- On the window `|ε| < K` the total base length IS the Jacobian base length
of the two-level profile (restatement of `jacobianBaseLen_twoLevel`). -/
theorem twoLevelBaseLen_eq [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K) {j : ℕ} (hj : j < n) :
    jacobianBaseLen (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i)
        ((j : ℕ) : ZMod n)
      = twoLevelBaseLen (n := n) m hK ε j := by
  unfold twoLevelBaseLen
  exact jacobianBaseLen_twoLevel hn4 hn hK hε hj

/-- At `ε = 0` every total base length is the constant-pair length. -/
theorem twoLevelBaseLen_zero {m : ℕ} {K : ℝ} (hK : 0 < K) (j : ℕ) :
    twoLevelBaseLen (n := n) m hK 0 j = chartInv hK hK (2 * Real.pi / n) := by
  unfold twoLevelBaseLen
  split_ifs with h
  · rw [add_zero, chartInvCurv_of_pos hK hK]
  · rfl

/-- The strict `ε`-derivative of the total base length at `ε = 0`: the four
special edges move at `ℓ̇* = −sin(π/n)/K²`, every other edge is frozen. -/
theorem hasStrictDerivAt_twoLevelBaseLen [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    {K : ℝ} (hK : 0 < K) (j : ℕ) :
    HasStrictDerivAt (fun ε : ℝ => twoLevelBaseLen (n := n) m hK ε j)
      (if j = 0 ∨ j = m - 1 ∨ j = m ∨ j = n - 1
       then -(Real.sin (Real.pi / n) / K ^ 2) else 0) 0 := by
  unfold twoLevelBaseLen
  split_ifs with h
  · exact hasStrictDerivAt_twoLevelLen hn4 hK
  · exact hasStrictDerivAt_const 0 _

/-- `hasStrictDerivAt_bumpSlot`, re-associated to the `κ · (ℓ/2)` shape of
`turningAngle`. -/
private lemma hasStrictDerivAt_bumpSlot' [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt (fun ε : ℝ => Real.arcsin
        ((K + ε) * (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2)))
      (Real.tan (Real.pi / n) / (2 * K)) 0 := by
  simpa only [mul_div_assoc] using hasStrictDerivAt_bumpSlot (n := n) hn4 hK

/-- `hasStrictDerivAt_mixedSlot`, re-associated to the `κ · (ℓ/2)` shape of
`turningAngle`. -/
private lemma hasStrictDerivAt_mixedSlot' [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt (fun ε : ℝ => Real.arcsin
        (K * (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2)))
      (-(Real.tan (Real.pi / n) / (2 * K))) 0 := by
  simpa only [mul_div_assoc] using hasStrictDerivAt_mixedSlot (n := n) hn4 hK

/-- The ε-total two-level turning angle at lifted vertex `i < n`: two arcsin
slots whose curvature factor carries the bump indicator and whose length
factors are the total base lengths of the two adjacent edges (wrap-around
`n − 1` at `i = 0`). -/
noncomputable def twoLevelTheta (m : ℕ) {K : ℝ} (hK : 0 < K) (ε : ℝ)
    (i : ℕ) : ℝ :=
  Real.arcsin ((K + if i = 0 ∨ i = m then ε else 0)
      * (twoLevelBaseLen (n := n) m hK ε (if i = 0 then n - 1 else i - 1) / 2))
    + Real.arcsin ((K + if i = 0 ∨ i = m then ε else 0)
      * (twoLevelBaseLen (n := n) m hK ε i / 2))

/-- On the window `|ε| < K` the total turning angle IS the turning angle of
the two-level profile at its Jacobian base lengths. -/
theorem turningAngle_twoLevel [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K) {i : ℕ}
    (hi : i < n) :
    turningAngle 0 (twoLevelProfile (n := n) m K ε)
        (jacobianBaseLen (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i))
        ((i : ℕ) : ZMod n)
      = twoLevelTheta (n := n) m hK ε i := by
  unfold turningAngle twoLevelTheta
  simp only [tK_zero]
  rw [twoLevelProfile_natCast hn K ε hi,
    twoLevelBaseLen_eq hn4 hn hK hε hi]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · have hcast : ((0 : ℕ) : ZMod n) - 1 = ((n - 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_zero, zero_sub, neg_one_zmod_eq]
    have hj' : n - 1 < n := by omega
    rw [hcast, twoLevelBaseLen_eq hn4 hn hK hε hj', if_pos rfl]
  · have hcast : ((i : ℕ) : ZMod n) - 1 = ((i - 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_sub hipos, Nat.cast_one]
    have hj' : i - 1 < n := by omega
    have hne : ¬ i = 0 := by omega
    rw [hcast, twoLevelBaseLen_eq hn4 hn hK hε hj', if_neg hne]

/-- At `ε = 0` every total turning angle is `2π/n`. -/
theorem twoLevelTheta_zero [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} {K : ℝ}
    (hK : 0 < K) (i : ℕ) :
    twoLevelTheta (n := n) m hK 0 i = 2 * Real.pi / n := by
  have h := turningAngle_const (n := n) hn4 hK 0
  unfold turningAngle at h
  simp only [tK_zero] at h
  rw [← chartInv_const hn4 hK] at h
  unfold twoLevelTheta
  simp only [ite_self, add_zero, twoLevelBaseLen_zero hK]
  exact h

/-- **The strict `ε`-derivative of the total turning angle** at `ε = 0`, for
vertices `i ≤ m`: the two-slot table `ȧ = ±tan(π/n)/(2K)` of
`lem:anchor_witness_two_level` — bump vertices `{0, m}` carry two bump slots,
vertices `1` and `m − 1` carry one (or, at `m = 2`, two) mixed slots, interior
vertices are frozen. -/
theorem hasStrictDerivAt_twoLevelTheta [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) {i : ℕ} (hi : i ≤ m) :
    HasStrictDerivAt (fun ε : ℝ => twoLevelTheta (n := n) m hK ε i)
      ((if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
        else if i = 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)
       + (if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
          else if i = m - 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0))
      0 := by
  have hm2 : 2 ≤ m := by omega
  unfold twoLevelTheta twoLevelBaseLen
  by_cases hbump : i = 0 ∨ i = m
  · have hcondh : i = 0 ∨ i = m - 1 ∨ i = m ∨ i = n - 1 := by
      rcases hbump with h | h <;> omega
    by_cases hi0 : i = 0
    · have hcondt : n - 1 = 0 ∨ n - 1 = m - 1 ∨ n - 1 = m ∨ n - 1 = n - 1 :=
        Or.inr (Or.inr (Or.inr rfl))
      simp only [if_pos hbump, if_pos hi0, if_pos hcondh, or_true, ite_true]
      exact (hasStrictDerivAt_bumpSlot' hn4 hK).add
        (hasStrictDerivAt_bumpSlot' hn4 hK)
    · have him : i = m := hbump.resolve_left hi0
      have hcondt : i - 1 = 0 ∨ i - 1 = m - 1 ∨ i - 1 = m ∨ i - 1 = n - 1 := by
        omega
      simp only [if_pos hbump, if_neg hi0, if_pos hcondt, if_pos hcondh]
      exact (hasStrictDerivAt_bumpSlot' hn4 hK).add
        (hasStrictDerivAt_bumpSlot' hn4 hK)
  · have hi0 : ¬ i = 0 := fun h => hbump (Or.inl h)
    have him : ¬ i = m := fun h => hbump (Or.inr h)
    simp only [if_neg hbump, if_neg hi0, add_zero]
    by_cases hi1 : i = 1
    · have hcondt : i - 1 = 0 ∨ i - 1 = m - 1 ∨ i - 1 = m ∨ i - 1 = n - 1 := by
        omega
      simp only [if_pos hcondt, if_pos hi1]
      by_cases hm : m = 2
      · have hcondh : i = 0 ∨ i = m - 1 ∨ i = m ∨ i = n - 1 := by omega
        have h1m : i = m - 1 := by omega
        simp only [if_pos hcondh, if_pos h1m]
        exact (hasStrictDerivAt_mixedSlot' hn4 hK).add
          (hasStrictDerivAt_mixedSlot' hn4 hK)
      · have hcondh : ¬(i = 0 ∨ i = m - 1 ∨ i = m ∨ i = n - 1) := by omega
        have h1m : ¬ i = m - 1 := by omega
        simp only [if_neg hcondh, if_neg h1m]
        rw [add_zero]
        exact (hasStrictDerivAt_mixedSlot' hn4 hK).add_const _
    · simp only [if_neg hi1]
      have hcondt : ¬(i - 1 = 0 ∨ i - 1 = m - 1 ∨ i - 1 = m ∨ i - 1 = n - 1) := by
        omega
      by_cases hlast : i = m - 1
      · have hcondh : i = 0 ∨ i = m - 1 ∨ i = m ∨ i = n - 1 := Or.inr (Or.inl hlast)
        simp only [if_pos hlast, if_neg hcondt, if_pos hcondh]
        rw [zero_add]
        exact HasStrictDerivAt.const_add _ (hasStrictDerivAt_mixedSlot' hn4 hK)
      · have hcondh : ¬(i = 0 ∨ i = m - 1 ∨ i = m ∨ i = n - 1) := by omega
        simp only [if_neg hlast, if_neg hcondt, if_neg hcondh]
        rw [add_zero]
        exact hasStrictDerivAt_const (0 : ℝ)
          (Real.arcsin (K * (chartInv hK hK (2 * Real.pi / n) / 2))
            + Real.arcsin (K * (chartInv hK hK (2 * Real.pi / n) / 2)))

/-! ### The ε-total two-level headings and their derivative table -/

/-- The heading `ε`-derivative table of `lem:anchor_witness_two_level`
(valid for `j ≤ m`): `ψ̇_j = tan(π/n)/K` at `j ∈ {0, m}`, `0` at
`j = m − 1`, and `tan(π/n)/(2K)` in between. -/
noncomputable def twoLevelHeadDot (m : ℕ) (K : ℝ) (j : ℕ) : ℝ :=
  if j = 0 ∨ j = m then Real.tan (Real.pi / n) / K
  else if j = m - 1 then 0
  else Real.tan (Real.pi / n) / (2 * K)

/-- On the window `|ε| < K` the heading of the two-level profile at its
Jacobian base lengths is the sum of the total turning angles. -/
theorem heading_twoLevel [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K) {j : ℕ} (hj : j < n) :
    heading (twoLevelProfile (n := n) m K ε)
        (jacobianBaseLen (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i)) j
      = ∑ i ∈ Finset.range (j + 1), twoLevelTheta (n := n) m hK ε i := by
  unfold heading
  exact Finset.sum_congr rfl fun i hi => turningAngle_twoLevel hn4 hn hK hε
    (lt_of_le_of_lt (Finset.mem_range_succ_iff.mp hi) hj)

/-- At `ε = 0` the total heading is the constant development `(j+1)·(2π/n)`. -/
theorem sum_twoLevelTheta_zero [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} {K : ℝ}
    (hK : 0 < K) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), twoLevelTheta (n := n) m hK 0 i
      = ((j : ℝ) + 1) * (2 * Real.pi / n) := by
  rw [Finset.sum_congr rfl fun i _ => twoLevelTheta_zero hn4 hK i,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **The strict `ε`-derivative of the total heading** at `ε = 0` for
`j ≤ m`: termwise differentiation of the slot table, evaluated to the
closed-form `twoLevelHeadDot`. -/
theorem hasStrictDerivAt_twoLevelHead [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) {j : ℕ} (hj : j ≤ m) :
    HasStrictDerivAt
      (fun ε : ℝ => ∑ i ∈ Finset.range (j + 1), twoLevelTheta (n := n) m hK ε i)
      (twoLevelHeadDot (n := n) m K j) 0 := by
  have hm2 : 2 ≤ m := by omega
  have hsum : HasStrictDerivAt
      (fun ε : ℝ => ∑ i ∈ Finset.range (j + 1), twoLevelTheta (n := n) m hK ε i)
      (∑ i ∈ Finset.range (j + 1),
        ((if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
          else if i = 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)
         + (if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
            else if i = m - 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)))
      0 := by
    have h := HasStrictDerivAt.sum fun i hi =>
      hasStrictDerivAt_twoLevelTheta hn4 hn hK
        (le_trans (Finset.mem_range_succ_iff.mp hi) hj)
    have hfun : (∑ i ∈ Finset.range (j + 1),
          fun ε : ℝ => twoLevelTheta (n := n) m hK ε i)
        = fun ε : ℝ => ∑ i ∈ Finset.range (j + 1),
            twoLevelTheta (n := n) m hK ε i := by
      funext ε
      simp
    rwa [hfun] at h
  have hval : (∑ i ∈ Finset.range (j + 1),
      ((if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
        else if i = 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)
       + (if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
          else if i = m - 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)))
      = twoLevelHeadDot (n := n) m K j := by
    have hdecomp : ∀ i : ℕ,
        ((if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
          else if i = 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)
         + (if i = 0 ∨ i = m then Real.tan (Real.pi / n) / (2 * K)
            else if i = m - 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0))
        = ((if i = 0 then Real.tan (Real.pi / n) / (2 * K) else 0)
            + (if i = m then Real.tan (Real.pi / n) / (2 * K) else 0)
            + (if i = 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0))
          + ((if i = 0 then Real.tan (Real.pi / n) / (2 * K) else 0)
            + (if i = m then Real.tan (Real.pi / n) / (2 * K) else 0)
            + (if i = m - 1 then -(Real.tan (Real.pi / n) / (2 * K)) else 0)) := by
      intro i
      split_ifs <;> first | ring1 | (exfalso; omega)
    rw [Finset.sum_congr rfl fun i _ => hdecomp i]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
    unfold twoLevelHeadDot
    have hK' : K ≠ 0 := hK.ne'
    have h0j : (0 : ℕ) < j + 1 := by omega
    by_cases hj0 : j = 0
    · rw [if_pos h0j, if_neg (by omega : ¬ m < j + 1),
        if_neg (by omega : ¬ 1 < j + 1), if_neg (by omega : ¬ m - 1 < j + 1),
        if_pos (Or.inl hj0)]
      field_simp
      ring
    · by_cases hjm : j = m
      · rw [if_pos h0j, if_pos (by omega : m < j + 1),
          if_pos (by omega : 1 < j + 1), if_pos (by omega : m - 1 < j + 1),
          if_pos (Or.inr hjm)]
        field_simp
        ring
      · by_cases hjm1 : j = m - 1
        · rw [if_pos h0j, if_neg (by omega : ¬ m < j + 1),
            if_pos (by omega : 1 < j + 1), if_pos (by omega : m - 1 < j + 1),
            if_neg (by omega : ¬(j = 0 ∨ j = m)), if_pos hjm1]
          ring
        · rw [if_pos h0j, if_neg (by omega : ¬ m < j + 1),
            if_pos (by omega : 1 < j + 1), if_neg (by omega : ¬ m - 1 < j + 1),
            if_neg (by omega : ¬(j = 0 ∨ j = m)), if_neg hjm1]
          field_simp
          ring
  rw [← hval]
  exact hsum

/-! ### The free half-block phase sum

`closingJacobianCol_const_eq_zero` at `K = 1` *is* the geometric-sum
evaluation `∑_{r=q+1}^{q+m−1} e^{i(r+1)α} = i·cot(π/n)·e^{i(q+1)α}` — no
`geom_sum` lemma is needed (blueprint R3 note). -/

/-- Real→complex coercion preserves strict differentiability (project-local:
Mathlib has only the non-strict `HasDerivAt.ofReal_comp`). -/
private lemma hasStrictDerivAt_ofReal_comp {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun y => (f y : ℂ)) (f' : ℂ) x := by
  have h := Complex.ofRealCLM.hasStrictFDerivAt.comp_hasStrictDerivAt x hf
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at h
  exact h

/-- **The half-block phase sum at the constant anchor**
(`lem:anchor_witness_two_level`, base-point gauge): for `q < m`,
`∑_{r∈Ico(q+1,q+m)} e^{i(r+1)·2π/n} = i·cot(π/n)·e^{i(q+1)·2π/n}` — extracted
from the exact vanishing of the constant-anchor Jacobian column. -/
theorem sum_exp_Ico_eq [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {q : ℕ} (hq : q < m) :
    ∑ r ∈ Finset.Ico (q + 1) (q + m),
        Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ) * Complex.I)
      = Complex.I
          * ((Real.cos (Real.pi / n) / Real.sin (Real.pi / n) : ℝ) : ℂ)
          * Complex.exp (((((q : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hcos0 : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have h0 := closingJacobianCol_const_eq_zero (K := 1) hn4 hn one_pos hq
  unfold closingJacobianCol at h0
  have hfun : jacobianBaseLen (fun _ : ZMod n => one_pos)
      = fun _ : ZMod n => 2 * Real.sin (Real.pi / n) / 1 :=
    funext fun j => chartInv_const hn4 one_pos
  rw [Finset.sum_congr rfl fun r _ => jacobianEdge_const hn4 one_pos r,
    jacobianLambda'_const hn4 one_pos, jacobianShare_const hn4 one_pos,
    hfun, heading_const hn4 one_pos q] at h0
  set e : ℂ := Complex.exp (((((q : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
    * Complex.I) with he
  set S2 : ℂ := ∑ r ∈ Finset.Ico (q + 1) (q + m),
    Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ) * Complex.I)
    with hS2
  have hsum : (∑ r ∈ Finset.Ico (q + 1) (q + m),
      ((2 * Real.sin (Real.pi / n) / 1 : ℝ) : ℂ)
        * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
            * Complex.I))
      = ((2 * Real.sin (Real.pi / n) / 1 : ℝ) : ℂ) * S2 := by
    rw [hS2, Finset.mul_sum]
  rw [hsum] at h0
  have hkey : Complex.I * ((2 * Real.sin (Real.pi / n) / 1 : ℝ) : ℂ) * S2
      = -(((2 * (Real.cos (Real.pi / n) / 1) : ℝ) : ℂ) * e) := by
    have h20 : ((2 * (1 / 2 : ℝ) - 1 : ℝ) : ℂ) = 0 := by norm_num
    rw [h20, zero_mul, zero_add] at h0
    linear_combination h0
  have h2s : (0 : ℝ) < 2 * Real.sin (Real.pi / n) / 1 := by positivity
  have hne : Complex.I * ((2 * Real.sin (Real.pi / n) / 1 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr h2s.ne')
  apply mul_left_cancel₀ hne
  rw [hkey]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hsC : (Real.sin (Real.pi / n) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsin0.ne'
  have hd : (Real.sin (Real.pi / n) : ℂ)
      * ((Real.cos (Real.pi / n) : ℂ) / (Real.sin (Real.pi / n) : ℂ))
      = (Real.cos (Real.pi / n) : ℂ) := by
    field_simp
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    div_one]
  linear_combination (-2 * (Real.sin (Real.pi / n) : ℂ)
      * ((Real.cos (Real.pi / n) : ℂ) / (Real.sin (Real.pi / n) : ℂ)) * e) * hI
    + (2 * e) * hd

/-! ### The moving slot-derivative data `A(ε), B(ε), λ'(ε), p(ε)` of edge 0

The `ε`-calculus of the chart slot derivatives along the two-level special
edge: `A(ε) = chartSlotDeriv (K+ε) (ℓ*(ε))` and `B(ε) = chartSlotDeriv K
(ℓ*(ε))` with values `Ȧ = (1+cos²ρ)/(4cos³ρ)`, `Ḃ = −sin²ρ/(4cos³ρ)`, hence
`λ̇' = −cosρ/(2K²)` and `ṗ = 1/(4K·cos²ρ)` — the `λ'`, `p` rows of the
first-order table of `lem:anchor_witness_two_level`. -/

/-- Both slot derivatives of the special edge at `ε = 0` equal the
constant-pair value `K/(2cos(π/n))`. -/
theorem twoLevelSlot_zero [NeZero n] (hn4 : 4 ≤ n) {K : ℝ} (hK : 0 < K) :
    chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) K)
      = K / (2 * Real.cos (Real.pi / n)) := by
  rw [chartInvCurv_of_pos hK hK, chartInv_const hn4 hK,
    chartSlotDeriv_const hn4 hK]

/-- The inner wall argument `(K+ε)·ℓ*(ε)/2` of the bump slot moves with strict
derivative `sin(π/n)/(2K)` at `ε = 0` (value `sin(π/n)`). -/
private lemma hasStrictDerivAt_bumpArg [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt
      (fun ε : ℝ => (K + ε) * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2)
      (Real.sin (Real.pi / n) / (2 * K)) 0 := by
  have hval0 : chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)
      = 2 * Real.sin (Real.pi / n) / K := by
    rw [add_zero, chartInvCurv_of_pos hK hK, chartInv_const hn4 hK]
  have hshift : HasStrictDerivAt (fun ε : ℝ => K + ε) 1 0 := by
    simpa using (hasStrictDerivAt_id (0 : ℝ)).const_add K
  have hprod := (hshift.mul (hasStrictDerivAt_twoLevelLen hn4 hK)).div_const 2
  have hval : (1 * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)
      + (K + 0) * -(Real.sin (Real.pi / n) / K ^ 2)) / 2
      = Real.sin (Real.pi / n) / (2 * K) := by
    rw [hval0]
    field_simp
    ring
  rwa [hval] at hprod

/-- The inner wall argument `K·ℓ*(ε)/2` of the mixed slot moves with strict
derivative `−sin(π/n)/(2K)` at `ε = 0` (value `sin(π/n)`). -/
private lemma hasStrictDerivAt_mixedArg [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt
      (fun ε : ℝ => K * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2)
      (-(Real.sin (Real.pi / n) / (2 * K))) 0 := by
  have hprod := ((hasStrictDerivAt_twoLevelLen hn4 hK).const_mul K).div_const 2
  have hval : K * -(Real.sin (Real.pi / n) / K ^ 2) / 2
      = -(Real.sin (Real.pi / n) / (2 * K)) := by
    field_simp
  rwa [hval] at hprod

/-- The wall square-root denominator `2√(1 − arg²)` of a slot derivative,
differentiated along a moving wall argument with value `sin(π/n)` and strict
derivative `d`: derivative `2·(−2·sin(π/n)·d)/(2cos(π/n))`, value `2cos(π/n)`. -/
private lemma hasStrictDerivAt_slotDen [NeZero n] (hn4 : 4 ≤ n)
    {g : ℝ → ℝ} {d : ℝ} (hg : HasStrictDerivAt g d 0)
    (hg0 : g 0 = Real.sin (Real.pi / n)) :
    HasStrictDerivAt (fun ε : ℝ => 2 * Real.sqrt (1 - g ε ^ 2))
      (2 * (-(2 * Real.sin (Real.pi / n) * d) / (2 * Real.cos (Real.pi / n))))
      0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hsin1 : Real.sin (Real.pi / n) < 1 := by
    have h := Real.strictMonoOn_sin (a := Real.pi / n) (b := Real.pi / 2)
      ⟨by linarith, hρhalf.le⟩ ⟨by linarith, le_refl _⟩ hρhalf
    simpa [Real.sin_pi_div_two] using h
  have hsq : HasStrictDerivAt (fun ε : ℝ => 1 - g ε ^ 2) (-(2 * g 0 * d)) 0 := by
    have h := (hg.pow 2).const_sub 1
    have hfun : (fun x : ℝ => 1 - (g ^ 2) x) = fun ε : ℝ => 1 - g ε ^ 2 := by
      funext ε
      simp
    have hval : -(((2 : ℕ) : ℝ) * g 0 ^ (2 - 1) * d) = -(2 * g 0 * d) := by
      norm_num
    rw [hfun, hval] at h
    exact h
  have harg0 : (0 : ℝ) < 1 - g 0 ^ 2 := by
    rw [hg0]
    nlinarith
  have hcomp : HasStrictDerivAt (fun ε : ℝ => 2 * Real.sqrt (1 - g ε ^ 2))
      (2 * (-(2 * g 0 * d) / (2 * Real.sqrt (1 - g 0 ^ 2)))) 0 :=
    (hsq.sqrt harg0.ne').const_mul 2
  have hveq : 2 * (-(2 * g 0 * d) / (2 * Real.sqrt (1 - g 0 ^ 2)))
      = 2 * (-(2 * Real.sin (Real.pi / n) * d) / (2 * Real.cos (Real.pi / n))) := by
    rw [hg0, ← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) hρhalf.le]
  rwa [hveq] at hcomp

/-- **The bump slot derivative moves at `Ȧ = (1+cos²ρ)/(4cos³ρ)`**
(`lem:anchor_witness_two_level`, first-order table, `ρ = π/n`). -/
theorem hasStrictDerivAt_bumpSlotDeriv [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt
      (fun ε : ℝ => chartSlotDeriv (K + ε)
        (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))
      ((1 + Real.cos (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3))
      0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hbarg := hasStrictDerivAt_bumpArg hn4 hK
  have hbarg0 : (K + 0) * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2
      = Real.sin (Real.pi / n) := by
    rw [add_zero, chartInvCurv_of_pos hK hK, chartInv_const hn4 hK]
    field_simp
  have hden := hasStrictDerivAt_slotDen hn4 hbarg hbarg0
  have hshift : HasStrictDerivAt (fun ε : ℝ => K + ε) 1 0 := by
    simpa using (hasStrictDerivAt_id (0 : ℝ)).const_add K
  have hden0 : 2 * Real.sqrt (1 - ((K + 0)
      * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) ^ 2) ≠ 0 := by
    rw [hbarg0, ← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) hρhalf.le]
    positivity
  have hdiv : HasStrictDerivAt
      (fun ε : ℝ => (K + ε) / (2 * Real.sqrt (1 - ((K + ε)
        * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2) ^ 2)))
      ((1 * (2 * Real.sqrt (1 - ((K + 0)
          * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) ^ 2))
        - (K + 0) * (2 * (-(2 * Real.sin (Real.pi / n)
            * (Real.sin (Real.pi / n) / (2 * K)))
          / (2 * Real.cos (Real.pi / n)))))
       / (2 * Real.sqrt (1 - ((K + 0)
          * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) ^ 2)) ^ 2) 0 :=
    hshift.div hden hden0
  have hveq : (1 * (2 * Real.sqrt (1 - ((K + 0)
          * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) ^ 2))
        - (K + 0) * (2 * (-(2 * Real.sin (Real.pi / n)
            * (Real.sin (Real.pi / n) / (2 * K)))
          / (2 * Real.cos (Real.pi / n)))))
       / (2 * Real.sqrt (1 - ((K + 0)
          * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) ^ 2)) ^ 2
      = (1 + Real.cos (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3) := by
    rw [hbarg0, ← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) hρhalf.le,
      add_zero]
    have hss : 2 * Real.sin (Real.pi / n) * (Real.sin (Real.pi / n) / (2 * K))
        = (1 - Real.cos (Real.pi / n) ^ 2) / K := by
      rw [mul_div_assoc', mul_assoc, ← sq, Real.sin_sq,
        mul_div_mul_left _ _ (two_ne_zero)]
    rw [hss]
    field_simp
    ring
  rw [hveq] at hdiv
  unfold chartSlotDeriv
  exact hdiv

/-- **The mixed slot derivative moves at `Ḃ = −sin²ρ/(4cos³ρ)`**
(`lem:anchor_witness_two_level`, first-order table, `ρ = π/n`). -/
theorem hasStrictDerivAt_mixedSlotDeriv [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt
      (fun ε : ℝ => chartSlotDeriv K
        (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))
      (-(Real.sin (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3))
      0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hmarg := hasStrictDerivAt_mixedArg hn4 hK
  have hmarg0 : K * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2
      = Real.sin (Real.pi / n) := by
    rw [add_zero, chartInvCurv_of_pos hK hK, chartInv_const hn4 hK]
    field_simp
  have hden := hasStrictDerivAt_slotDen hn4 hmarg hmarg0
  have hden0 : 2 * Real.sqrt (1 - (K
      * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) ^ 2) ≠ 0 := by
    rw [hmarg0, ← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) hρhalf.le]
    positivity
  have hdiv : HasStrictDerivAt
      (fun ε : ℝ => K / (2 * Real.sqrt (1 - (K
        * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) / 2) ^ 2)))
      ((0 * (2 * Real.sqrt (1 - (K
          * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) ^ 2))
        - K * (2 * (-(2 * Real.sin (Real.pi / n)
            * -(Real.sin (Real.pi / n) / (2 * K)))
          / (2 * Real.cos (Real.pi / n)))))
       / (2 * Real.sqrt (1 - (K
          * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) ^ 2)) ^ 2) 0 :=
    (hasStrictDerivAt_const (0 : ℝ) K).div hden hden0
  have hveq : (0 * (2 * Real.sqrt (1 - (K
          * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) ^ 2))
        - K * (2 * (-(2 * Real.sin (Real.pi / n)
            * -(Real.sin (Real.pi / n) / (2 * K)))
          / (2 * Real.cos (Real.pi / n)))))
       / (2 * Real.sqrt (1 - (K
          * chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0) / 2) ^ 2)) ^ 2
      = -(Real.sin (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3) := by
    rw [hmarg0, ← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) hρhalf.le]
    have hss : 2 * Real.sin (Real.pi / n) * -(Real.sin (Real.pi / n) / (2 * K))
        = -((1 - Real.cos (Real.pi / n) ^ 2) / K) := by
      rw [mul_neg, mul_div_assoc', mul_assoc, ← sq, Real.sin_sq,
        mul_div_mul_left _ _ (two_ne_zero)]
    rw [hss, Real.sin_sq]
    field_simp
    ring
  rw [hveq] at hdiv
  unfold chartSlotDeriv
  exact hdiv

/-- **`λ'(ε)` of the special edge moves at `λ̇' = −cosρ/(2K²)`**
(`lem:anchor_witness_two_level`, first-order table). -/
theorem hasStrictDerivAt_twoLevelLambda' [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt
      (fun ε : ℝ => 1 / (chartSlotDeriv (K + ε)
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))))
      (-(Real.cos (Real.pi / n)) / (2 * K ^ 2)) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hAB : HasStrictDerivAt
      (fun ε : ℝ => chartSlotDeriv (K + ε)
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))
      ((1 + Real.cos (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)
        + -(Real.sin (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)) 0 :=
    (hasStrictDerivAt_bumpSlotDeriv hn4 hK).add
      (hasStrictDerivAt_mixedSlotDeriv hn4 hK)
  have hAB0 : chartSlotDeriv (K + 0)
        (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
      + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
      ≠ 0 := by
    rw [add_zero, twoLevelSlot_zero hn4 hK]
    positivity
  have hdiv : HasStrictDerivAt
      (fun ε : ℝ => 1 / (chartSlotDeriv (K + ε)
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))))
      ((0 * (chartSlotDeriv (K + 0)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)))
        - 1 * ((1 + Real.cos (Real.pi / n) ^ 2)
              / (4 * Real.cos (Real.pi / n) ^ 3)
            + -(Real.sin (Real.pi / n) ^ 2)
              / (4 * Real.cos (Real.pi / n) ^ 3)))
       / (chartSlotDeriv (K + 0)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))) ^ 2)
      0 :=
    (hasStrictDerivAt_const (0 : ℝ) (1 : ℝ)).div hAB hAB0
  have hveq : (0 * (chartSlotDeriv (K + 0)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)))
        - 1 * ((1 + Real.cos (Real.pi / n) ^ 2)
              / (4 * Real.cos (Real.pi / n) ^ 3)
            + -(Real.sin (Real.pi / n) ^ 2)
              / (4 * Real.cos (Real.pi / n) ^ 3)))
       / (chartSlotDeriv (K + 0)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))) ^ 2
      = -(Real.cos (Real.pi / n)) / (2 * K ^ 2) := by
    rw [add_zero, twoLevelSlot_zero hn4 hK, Real.sin_sq]
    field_simp
    ring
  rwa [hveq] at hdiv

/-- **The tail share `p(ε)` of the special edge moves at `ṗ = 1/(4K·cos²ρ)`**
(`lem:anchor_witness_two_level`, first-order table). -/
theorem hasStrictDerivAt_twoLevelShare [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    HasStrictDerivAt
      (fun ε : ℝ => chartSlotDeriv (K + ε)
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        / (chartSlotDeriv (K + ε)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
          + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))))
      (1 / (4 * K * Real.cos (Real.pi / n) ^ 2)) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hA := hasStrictDerivAt_bumpSlotDeriv hn4 hK
  have hAB : HasStrictDerivAt
      (fun ε : ℝ => chartSlotDeriv (K + ε)
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))
      ((1 + Real.cos (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)
        + -(Real.sin (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)) 0 :=
    hA.add (hasStrictDerivAt_mixedSlotDeriv hn4 hK)
  have hAB0 : chartSlotDeriv (K + 0)
        (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
      + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
      ≠ 0 := by
    rw [add_zero, twoLevelSlot_zero hn4 hK]
    positivity
  have hdiv : HasStrictDerivAt
      (fun ε : ℝ => chartSlotDeriv (K + ε)
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        / (chartSlotDeriv (K + ε)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
          + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))))
      (((1 + Real.cos (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)
          * (chartSlotDeriv (K + 0)
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
            + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)))
        - chartSlotDeriv (K + 0)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          * ((1 + Real.cos (Real.pi / n) ^ 2)
              / (4 * Real.cos (Real.pi / n) ^ 3)
            + -(Real.sin (Real.pi / n) ^ 2)
              / (4 * Real.cos (Real.pi / n) ^ 3)))
       / (chartSlotDeriv (K + 0)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))) ^ 2)
      0 :=
    hA.div hAB hAB0
  have hveq : ((1 + Real.cos (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)
          * (chartSlotDeriv (K + 0)
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
            + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)))
        - chartSlotDeriv (K + 0)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          * ((1 + Real.cos (Real.pi / n) ^ 2)
              / (4 * Real.cos (Real.pi / n) ^ 3)
            + -(Real.sin (Real.pi / n) ^ 2)
              / (4 * Real.cos (Real.pi / n) ^ 3)))
       / (chartSlotDeriv (K + 0)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          + chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))) ^ 2
      = 1 / (4 * K * Real.cos (Real.pi / n) ^ 2) := by
    rw [add_zero, twoLevelSlot_zero hn4 hK, Real.sin_sq]
    field_simp
    ring
  rwa [hveq] at hdiv

/-! ### The ε-total two-level Jacobian column and its edge vectors -/

/-- Columns only depend on the curvature profile, not on the positivity
proof. -/
private lemma closingJacobianCol_congr {κs κs' : ZMod n → ℝ} (h : κs = κs')
    (hκs : ∀ i, 0 < κs i) (hκs' : ∀ i, 0 < κs' i) (m q : ℕ) :
    closingJacobianCol m hκs q = closingJacobianCol m hκs' q := by
  subst h
  rfl

/-- **The ε-total two-level Jacobian column**: `closingJacobianCol` of the
two-level profile on the window `|ε| < K`, junk `0` outside — the honest
function of `ε` that `lem:anchor_witness_two_level` differentiates. -/
noncomputable def twoLevelCol (m : ℕ) {K : ℝ} (hK : 0 < K) (q : ℕ)
    (ε : ℝ) : ℂ :=
  if h : |ε| < K
  then closingJacobianCol m
    (fun i => twoLevelProfile_pos (n := n) (m := m) hK h i) q
  else 0

/-- On the window the total column IS the two-level Jacobian column. -/
theorem twoLevelCol_eq [NeZero n] {m : ℕ} {K ε : ℝ} (hK : 0 < K)
    (hε : |ε| < K) (q : ℕ) :
    twoLevelCol (n := n) m hK q ε
      = closingJacobianCol m
          (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i) q :=
  dif_pos hε

/-- At `ε = 0` the total column vanishes exactly (the constant-anchor
degeneracy — the ground of the perturbation). -/
theorem twoLevelCol_zero [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {K : ℝ} (hK : 0 < K) {q : ℕ} (hq : q < m) :
    twoLevelCol (n := n) m hK q 0 = 0 := by
  have h0 : |(0 : ℝ)| < K := by simpa using hK
  rw [twoLevelCol_eq hK h0 q,
    closingJacobianCol_congr (twoLevelProfile_zero (n := n) m K)
      (fun i => twoLevelProfile_pos hK h0 i) (fun _ => hK) m q,
    closingJacobianCol_const_eq_zero hn4 hn hK hq]

/-- On the window the two-level Jacobian edge vector is the total edge vector
(total base length times the exponential of the total heading). -/
theorem jacobianEdge_twoLevel [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K) {r : ℕ}
    (hr : r < n) :
    jacobianEdge (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i) r
      = ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
        * Complex.exp (((∑ i ∈ Finset.range (r + 1),
            twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I) := by
  unfold jacobianEdge
  rw [twoLevelBaseLen_eq hn4 hn hK hε hr, heading_twoLevel hn4 hn hK hε hr]

/-- **The strict `ε`-derivative of the total edge vector** at `ε = 0` for
`r ≤ m`: `Ė_r = (ℓ̇_r + i·ℓ·ψ̇_r)·e^{i(r+1)·2π/n}` with the length and heading
rows of the first-order table (`lem:anchor_witness_two_level`). -/
theorem hasStrictDerivAt_twoLevelEdge [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) {r : ℕ} (hr : r ≤ m) :
    HasStrictDerivAt
      (fun ε : ℝ => ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
        * Complex.exp (((∑ i ∈ Finset.range (r + 1),
            twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
      ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
            then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
          * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
        + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * (Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
            * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) * Complex.I))) 0 := by
  have hlen : HasStrictDerivAt
      (fun ε : ℝ => ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ))
      (((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
          then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ) : ℂ)) 0 :=
    hasStrictDerivAt_ofReal_comp (hasStrictDerivAt_twoLevelBaseLen hn4 hK r)
  have hψ : HasStrictDerivAt
      (fun ε : ℝ => ((∑ i ∈ Finset.range (r + 1),
          twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ))
      ((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) 0 :=
    hasStrictDerivAt_ofReal_comp (hasStrictDerivAt_twoLevelHead hn4 hn hK hr)
  have hinner := hψ.mul_const Complex.I
  have hexp : HasStrictDerivAt
      (fun ε : ℝ => Complex.exp (((∑ i ∈ Finset.range (r + 1),
          twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((∑ i ∈ Finset.range (r + 1),
          twoLevelTheta (n := n) m hK 0 i : ℝ) : ℂ) * Complex.I)
        * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) * Complex.I)) 0 :=
    (Complex.hasStrictDerivAt_exp _).comp 0 hinner
  have hmul : HasStrictDerivAt
      (fun ε : ℝ => ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
        * Complex.exp (((∑ i ∈ Finset.range (r + 1),
            twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
      ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
            then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (r + 1),
              twoLevelTheta (n := n) m hK 0 i : ℝ) : ℂ) * Complex.I)
        + ((twoLevelBaseLen (n := n) m hK 0 r : ℝ) : ℂ)
          * (Complex.exp (((∑ i ∈ Finset.range (r + 1),
              twoLevelTheta (n := n) m hK 0 i : ℝ) : ℂ) * Complex.I)
            * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) * Complex.I))) 0 :=
    hlen.mul hexp
  have hS0 : (∑ i ∈ Finset.range (r + 1), twoLevelTheta (n := n) m hK 0 i)
      = ((r : ℝ) + 1) * (2 * Real.pi / n) := sum_twoLevelTheta_zero hn4 hK r
  have hbl0 : twoLevelBaseLen (n := n) m hK 0 r
      = 2 * Real.sin (Real.pi / n) / K := by
    rw [twoLevelBaseLen_zero hK r, chartInv_const hn4 hK]
  rw [hS0, hbl0] at hmul
  exact hmul

/-! ### The column-0 derivative of the two-level witness (`V₀` row) -/

/-- **The total formula of column 0 on the window**: every ingredient of
`closingJacobianCol` at the two-level profile identified with its ε-total
form — `λ'`, `p` through the moving slot derivatives of the special edge 0,
the heading through the total turning angles, the edges through the total
edge vectors. -/
theorem twoLevelCol_formula₀ [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K) :
    twoLevelCol (n := n) m hK 0 ε
      = ((2 * (1 / (chartSlotDeriv (K + ε)
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
            + chartSlotDeriv K
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))) : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (0 + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I)
        + Complex.I * (((2 * (chartSlotDeriv (K + ε)
                (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
              / (chartSlotDeriv (K + ε)
                  (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
                + chartSlotDeriv K
                  (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))) - 1 : ℝ) : ℂ)
            * (((twoLevelBaseLen (n := n) m hK ε 0 : ℝ) : ℂ)
              * Complex.exp (((∑ i ∈ Finset.range (0 + 1),
                  twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
          + ∑ r ∈ Finset.Ico (0 + 1) (0 + m),
              ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
                * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                    twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I)) := by
  have hm2 : 2 ≤ m := by omega
  rw [twoLevelCol_eq hK hε 0]
  unfold closingJacobianCol
  have hedge : ∀ r ∈ Finset.Ico (0 + 1) (0 + m),
      jacobianEdge (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i) r
        = ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (r + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I) := by
    intro r hr
    have hrn : r < n := by
      have := Finset.mem_Ico.mp hr
      omega
    exact jacobianEdge_twoLevel hn4 hn hK hε hrn
  rw [Finset.sum_congr rfl hedge,
    jacobianEdge_twoLevel hn4 hn hK hε (r := 0) (by omega),
    heading_twoLevel hn4 hn hK hε (j := 0) (by omega)]
  have hbl : jacobianBaseLen
      (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i) ((0 : ℕ) : ZMod n)
      = chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) := by
    rw [twoLevelBaseLen_eq hn4 hn hK hε (j := 0) (by omega)]
    unfold twoLevelBaseLen
    rw [if_pos (Or.inl rfl)]
  have hκ0 : twoLevelProfile (n := n) m K ε ((0 : ℕ) : ZMod n) = K + ε := by
    rw [twoLevelProfile_natCast hn K ε (by omega), if_pos (Or.inl rfl)]
  have hκ1 : twoLevelProfile (n := n) m K ε (((0 : ℕ) : ZMod n) + 1) = K := by
    rw [twoLevelProfile_natCast_succ hn K ε (by omega), if_neg (by omega),
      add_zero]
  unfold jacobianLambda' jacobianShare
  rw [hbl, hκ0, hκ1]

/-- **The half-block edge-derivative sum of column 0**: the middle terms carry
the uniform `iℓ·ψ̇`-rotation, edge `m−1` carries the frozen-heading length
motion; the boundary term collapses through `e^{imα} = −1`. -/
private lemma sum_twoLevelEdgeDot₀ [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (_hK : 0 < K) :
    (∑ r ∈ Finset.Ico (0 + 1) (0 + m),
      ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
            then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
          * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
        + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * (Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
            * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) * Complex.I))))
      = ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I
          * (∑ r ∈ Finset.Ico (0 + 1) (0 + m),
              Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                * Complex.I))
        + (((Real.sin (Real.pi / n) / K ^ 2 : ℝ)) : ℂ)
        + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I := by
  have hm2 : 2 ≤ m := by omega
  have hdec : ∀ r ∈ Finset.Ico (0 + 1) (0 + m),
      ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
            then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
          * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
        + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * (Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
            * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) * Complex.I)))
      = ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I
          * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
        + (if r = m - 1
           then ((-(Real.sin (Real.pi / n) / K ^ 2) : ℝ) : ℂ)
              * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                  * Complex.I)
             - ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
              * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I
              * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                  * Complex.I)
           else 0) := by
    intro r hr
    have hrb := Finset.mem_Ico.mp hr
    by_cases hlast : r = m - 1
    · rw [if_pos hlast, if_pos (Or.inr (Or.inl hlast))]
      have hhd : twoLevelHeadDot (n := n) m K r = 0 := by
        unfold twoLevelHeadDot
        rw [if_neg (by omega), if_pos hlast]
      rw [hhd, Complex.ofReal_zero]
      ring
    · rw [if_neg hlast, if_neg (by omega)]
      have hhd : twoLevelHeadDot (n := n) m K r
          = Real.tan (Real.pi / n) / (2 * K) := by
        unfold twoLevelHeadDot
        rw [if_neg (by omega), if_neg hlast]
      rw [hhd, Complex.ofReal_zero]
      ring
  rw [Finset.sum_congr rfl hdec, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq' (Finset.Ico (0 + 1) (0 + m)) (m - 1)]
  rw [if_pos (by rw [Finset.mem_Ico]; omega)]
  have hargm : (((m - 1 : ℕ) : ℝ) + 1) * (2 * Real.pi / n) = Real.pi := by
    have hnR : (n : ℝ) = 2 * m := by exact_mod_cast congrArg Nat.cast hn
    have hmR : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : (1 : ℕ) ≤ m := by omega
      push_cast [Nat.cast_sub this]
      ring
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    rw [hmR, hnR]
    field_simp
    ring
  rw [hargm, Complex.exp_pi_mul_I, Complex.ofReal_neg]
  ring

/-- **`V₀`** — the first-order value of column 0 of the two-level witness
(`lem:anchor_witness_two_level`, all `m ≥ 2`):
`V₀ = (e^{iα}·(−cosρ + (sinρ + sinρ/cos²ρ)·i) + (−sin²ρ/cosρ + sinρ·i))/K²`,
`ρ = π/n`, `α = 2π/n`. Equal to the blueprint's
`K⁻²e^{iρ}(−sec²ρ + 2i·tanρ)` by the half-angle identity. -/
noncomputable def twoLevelV₀ (K : ℝ) : ℂ :=
  (Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I)
      * (((-(Real.cos (Real.pi / n)) : ℝ) : ℂ)
        + ((Real.sin (Real.pi / n)
            + Real.sin (Real.pi / n) / Real.cos (Real.pi / n) ^ 2 : ℝ) : ℂ)
          * Complex.I)
    + (((-(Real.sin (Real.pi / n) ^ 2 / Real.cos (Real.pi / n)) : ℝ) : ℂ)
        + ((Real.sin (Real.pi / n) : ℝ) : ℂ) * Complex.I))
    / ((K ^ 2 : ℝ) : ℂ)

/-- **The strict `ε`-derivative of column 0 of the two-level witness**
(`lem:anchor_witness_two_level`, R2, uniform in `m ≥ 2`):
`C₀'(0) = V₀`. -/
theorem hasStrictDerivAt_twoLevelCol₀ [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) :
    HasStrictDerivAt (twoLevelCol (n := n) m hK 0) (twoLevelV₀ (n := n) K)
      0 := by
  have hm2 : 2 ≤ m := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  -- the pieces
  have hψ0ℂ : HasStrictDerivAt
      (fun ε : ℝ => ((∑ i ∈ Finset.range (0 + 1),
          twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ))
      ((twoLevelHeadDot (n := n) m K 0 : ℝ) : ℂ) 0 :=
    hasStrictDerivAt_ofReal_comp
      (hasStrictDerivAt_twoLevelHead hn4 hn hK (by omega))
  have hexp0 : HasStrictDerivAt
      (fun ε : ℝ => Complex.exp (((∑ i ∈ Finset.range (0 + 1),
          twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((∑ i ∈ Finset.range (0 + 1),
          twoLevelTheta (n := n) m hK 0 i : ℝ) : ℂ) * Complex.I)
        * (((twoLevelHeadDot (n := n) m K 0 : ℝ) : ℂ) * Complex.I)) 0 :=
    (Complex.hasStrictDerivAt_exp _).comp 0 (hψ0ℂ.mul_const Complex.I)
  have h2Λ := hasStrictDerivAt_ofReal_comp
    ((hasStrictDerivAt_twoLevelLambda' hn4 hK).const_mul 2)
  have hfirst := h2Λ.mul hexp0
  have hsh := hasStrictDerivAt_ofReal_comp
    (((hasStrictDerivAt_twoLevelShare hn4 hK).const_mul 2).sub_const 1)
  have hE0 := hasStrictDerivAt_twoLevelEdge hn4 hn hK (r := 0) (by omega)
  have hsecond := hsh.mul hE0
  have hsum : HasStrictDerivAt
      (fun ε : ℝ => ∑ r ∈ Finset.Ico (0 + 1) (0 + m),
        ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (r + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
      (∑ r ∈ Finset.Ico (0 + 1) (0 + m),
        ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
              then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
            * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                * Complex.I)
          + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
            * (Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                * Complex.I)
              * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) * Complex.I))))
      0 := by
    have h := HasStrictDerivAt.sum (u := Finset.Ico (0 + 1) (0 + m))
      (x := (0 : ℝ))
      (fun r hr => hasStrictDerivAt_twoLevelEdge hn4 hn hK (r := r)
        (by have := Finset.mem_Ico.mp hr; omega))
    have hfun : (∑ r ∈ Finset.Ico (0 + 1) (0 + m),
          fun ε : ℝ => ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
            * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
        = fun ε : ℝ => ∑ r ∈ Finset.Ico (0 + 1) (0 + m),
            ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
              * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                  twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I) := by
      funext ε
      simp
    rwa [hfun] at h
  have hev : ∀ᶠ ε : ℝ in nhds 0, |ε| < K :=
    (continuous_abs.tendsto' 0 0 abs_zero).eventually_lt_const hK
  have htot : HasStrictDerivAt
      (fun ε : ℝ => ((2 * (1 / (chartSlotDeriv (K + ε)
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
            + chartSlotDeriv K
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))) : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (0 + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I)
        + Complex.I * (((2 * (chartSlotDeriv (K + ε)
                (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
              / (chartSlotDeriv (K + ε)
                  (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
                + chartSlotDeriv K
                  (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))) - 1 : ℝ) : ℂ)
            * (((twoLevelBaseLen (n := n) m hK ε 0 : ℝ) : ℂ)
              * Complex.exp (((∑ i ∈ Finset.range (0 + 1),
                  twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
          + ∑ r ∈ Finset.Ico (0 + 1) (0 + m),
              ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
                * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                    twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I)))
      (((2 * (-(Real.cos (Real.pi / n)) / (2 * K ^ 2)) : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (0 + 1),
              twoLevelTheta (n := n) m hK 0 i : ℝ) : ℂ) * Complex.I)
        + ((2 * (1 / (chartSlotDeriv (K + 0)
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
            + chartSlotDeriv K
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)))) : ℝ) : ℂ)
          * (Complex.exp (((∑ i ∈ Finset.range (0 + 1),
              twoLevelTheta (n := n) m hK 0 i : ℝ) : ℂ) * Complex.I)
            * (((twoLevelHeadDot (n := n) m K 0 : ℝ) : ℂ) * Complex.I))
        + Complex.I * (((2 * (1 / (4 * K * Real.cos (Real.pi / n) ^ 2)) : ℝ) : ℂ)
              * (((twoLevelBaseLen (n := n) m hK 0 0 : ℝ) : ℂ)
                * Complex.exp (((∑ i ∈ Finset.range (0 + 1),
                    twoLevelTheta (n := n) m hK 0 i : ℝ) : ℂ) * Complex.I))
            + ((2 * (chartSlotDeriv (K + 0)
                    (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
                  / (chartSlotDeriv (K + 0)
                      (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
                    + chartSlotDeriv K
                      (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)))) - 1 : ℝ) : ℂ)
              * ((((if (0 : ℕ) = 0 ∨ 0 = m - 1 ∨ 0 = m ∨ 0 = n - 1
                    then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
                  * Complex.exp ((((((0 : ℕ) : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                      * Complex.I)
                + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
                  * (Complex.exp ((((((0 : ℕ) : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                      * Complex.I)
                    * (((twoLevelHeadDot (n := n) m K 0 : ℝ) : ℂ) * Complex.I)))
            + ∑ r ∈ Finset.Ico (0 + 1) (0 + m),
                ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
                      then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
                    * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                        * Complex.I)
                  + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
                    * (Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                        * Complex.I)
                      * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ)
                        * Complex.I))))) 0 :=
    hfirst.add ((hsecond.add hsum).const_mul Complex.I)
  rw [sum_twoLevelEdgeDot₀ hn4 hn hK,
    sum_exp_Ico_eq hn4 hn (q := 0) (by omega),
    sum_twoLevelTheta_zero hn4 hK 0] at htot
  have harg1 : (((0 : ℕ) : ℝ) + 1) * (2 * Real.pi / n) = 2 * Real.pi / n := by
    push_cast
    ring
  rw [harg1] at htot
  have hhd0 : twoLevelHeadDot (n := n) m K 0 = Real.tan (Real.pi / n) / K := by
    unfold twoLevelHeadDot
    rw [if_pos (Or.inl rfl)]
  have hE0if : ((if (0 : ℕ) = 0 ∨ 0 = m - 1 ∨ 0 = m ∨ 0 = n - 1
      then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ))
      = -(Real.sin (Real.pi / n) / K ^ 2) := if_pos (Or.inl rfl)
  have hbl00 : twoLevelBaseLen (n := n) m hK 0 0
      = 2 * Real.sin (Real.pi / n) / K := by
    rw [twoLevelBaseLen_zero hK 0, chartInv_const hn4 hK]
  rw [hhd0, hE0if, hbl00, add_zero, twoLevelSlot_zero hn4 hK] at htot
  have hfold : ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
        * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I
        * (Complex.I
          * ((Real.cos (Real.pi / n) / Real.sin (Real.pi / n) : ℝ) : ℂ)
          * Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I))
        = -(((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ)
          * ((Real.cos (Real.pi / n) / Real.sin (Real.pi / n) : ℝ) : ℂ)
          * Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      linear_combination (((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
        * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ)
        * ((Real.cos (Real.pi / n) / Real.sin (Real.pi / n) : ℝ) : ℂ)
        * Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I))
        * Complex.I_mul_I
  rw [hfold] at htot
  have hd := HasStrictDerivAt.congr_of_eventuallyEq htot
    (by filter_upwards [hev] with ε hε
        exact (twoLevelCol_formula₀ hn4 hn hK hε).symm)
  convert hd using 2
  · unfold twoLevelV₀
    have hsC : ((Real.sin (Real.pi / n) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hsin0.ne'
    have hcC : ((Real.cos (Real.pi / n) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hcos.ne'
    have hKC : ((K : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
    rw [Real.tan_eq_sin_div_cos]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_pow]
    field_simp
    linear_combination (-8 * ((Real.cos (Real.pi / (n : ℝ)) : ℝ) : ℂ)
      * ((Real.sin (Real.pi / (n : ℝ)) : ℝ) : ℂ) ^ 2) * Complex.I_mul_I

/-! ### The column-1 derivative of the two-level witness, interior case
`m ≥ 3` (`V₁` row) -/

/-- **The total formula of column 1 on the window** (`m ≥ 3`): edge 1 carries
the constant pair, so `λ'₁` and `p₁` are the explicit constants
`1/(K/(2cosρ)+K/(2cosρ))` and its half share. -/
theorem twoLevelCol_formula₁ [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) (hm3 : 3 ≤ m) {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K) :
    twoLevelCol (n := n) m hK 1 ε
      = ((2 * (1 / (K / (2 * Real.cos (Real.pi / n))
            + K / (2 * Real.cos (Real.pi / n)))) : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (1 + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I)
        + Complex.I * (((2 * (K / (2 * Real.cos (Real.pi / n))
              / (K / (2 * Real.cos (Real.pi / n))
                + K / (2 * Real.cos (Real.pi / n)))) - 1 : ℝ) : ℂ)
            * (((twoLevelBaseLen (n := n) m hK ε 1 : ℝ) : ℂ)
              * Complex.exp (((∑ i ∈ Finset.range (1 + 1),
                  twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
          + ∑ r ∈ Finset.Ico (1 + 1) (1 + m),
              ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
                * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                    twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I)) := by
  rw [twoLevelCol_eq hK hε 1]
  unfold closingJacobianCol
  have hedge : ∀ r ∈ Finset.Ico (1 + 1) (1 + m),
      jacobianEdge (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i) r
        = ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (r + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I) := by
    intro r hr
    have hrn : r < n := by
      have := Finset.mem_Ico.mp hr
      omega
    exact jacobianEdge_twoLevel hn4 hn hK hε hrn
  rw [Finset.sum_congr rfl hedge,
    jacobianEdge_twoLevel hn4 hn hK hε (r := 1) (by omega),
    heading_twoLevel hn4 hn hK hε (j := 1) (by omega)]
  have hbl : jacobianBaseLen
      (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i) ((1 : ℕ) : ZMod n)
      = chartInv hK hK (2 * Real.pi / (n : ℝ)) := by
    rw [twoLevelBaseLen_eq hn4 hn hK hε (j := 1) (by omega)]
    unfold twoLevelBaseLen
    rw [if_neg (by omega)]
  have hκ1 : twoLevelProfile (n := n) m K ε ((1 : ℕ) : ZMod n) = K := by
    rw [twoLevelProfile_natCast hn K ε (by omega), if_neg (by omega), add_zero]
  have hκ2 : twoLevelProfile (n := n) m K ε (((1 : ℕ) : ZMod n) + 1) = K := by
    rw [twoLevelProfile_natCast_succ hn K ε (by omega), if_neg (by omega),
      add_zero]
  unfold jacobianLambda' jacobianShare
  rw [hbl, hκ1, hκ2, chartInv_const hn4 hK, chartSlotDeriv_const hn4 hK]

/-- **The half-block edge-derivative sum of column 1** (`m ≥ 3`): uniform
middle rotation, frozen edge `m−1` (through `e^{imα} = −1`), and the moving
top edge `m` (through `e^{i(m+1)α} = −e^{iα}`). -/
private lemma sum_twoLevelEdgeDot₁ [NeZero n] (_hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) (hm3 : 3 ≤ m) {K : ℝ} (_hK : 0 < K) :
    (∑ r ∈ Finset.Ico (1 + 1) (1 + m),
      ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
            then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
          * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
        + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * (Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
            * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) * Complex.I))))
      = ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I
          * (∑ r ∈ Finset.Ico (1 + 1) (1 + m),
              Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                * Complex.I))
        + ((((Real.sin (Real.pi / n) / K ^ 2 : ℝ)) : ℂ)
          + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
            * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I)
        + ((((Real.sin (Real.pi / n) / K ^ 2 : ℝ)) : ℂ)
          + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
            * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I
          - ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
            * ((Real.tan (Real.pi / n) / K : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have hm2 : 2 ≤ m := by omega
  have hdec : ∀ r ∈ Finset.Ico (1 + 1) (1 + m),
      ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
            then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
          * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
        + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * (Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
            * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) * Complex.I)))
      = ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
          * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I
          * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
              * Complex.I)
        + ((if r = m - 1
           then ((-(Real.sin (Real.pi / n) / K ^ 2) : ℝ) : ℂ)
              * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                  * Complex.I)
             - ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
              * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I
              * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                  * Complex.I)
           else 0)
          + (if r = m
           then ((-(Real.sin (Real.pi / n) / K ^ 2) : ℝ) : ℂ)
              * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                  * Complex.I)
             + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
              * ((Real.tan (Real.pi / n) / K : ℝ) : ℂ) * Complex.I
              * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                  * Complex.I)
             - ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
              * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I
              * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                  * Complex.I)
           else 0)) := by
    intro r hr
    have hrb := Finset.mem_Ico.mp hr
    by_cases hlast : r = m - 1
    · have hnm : ¬ (r = m) := by omega
      rw [if_pos (Or.inr (Or.inl hlast)), if_pos hlast, if_neg hnm]
      have hhd : twoLevelHeadDot (n := n) m K r = 0 := by
        unfold twoLevelHeadDot
        rw [if_neg (by omega), if_pos hlast]
      rw [hhd, Complex.ofReal_zero]
      ring
    · by_cases htop : r = m
      · have hnm1 : ¬ (r = m - 1) := by omega
        rw [if_pos (Or.inr (Or.inr (Or.inl htop))), if_neg hnm1, if_pos htop]
        have hhd : twoLevelHeadDot (n := n) m K r
            = Real.tan (Real.pi / n) / K := by
          unfold twoLevelHeadDot
          rw [if_pos (Or.inr htop)]
        rw [hhd]
        ring
      · rw [if_neg hlast, if_neg htop, if_neg (by omega)]
        have hhd : twoLevelHeadDot (n := n) m K r
            = Real.tan (Real.pi / n) / (2 * K) := by
          unfold twoLevelHeadDot
          rw [if_neg (by omega), if_neg hlast]
        rw [hhd, Complex.ofReal_zero]
        ring
  rw [Finset.sum_congr rfl hdec, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum,
    Finset.sum_ite_eq' (Finset.Ico (1 + 1) (1 + m)) (m - 1),
    Finset.sum_ite_eq' (Finset.Ico (1 + 1) (1 + m)) m]
  rw [if_pos (by rw [Finset.mem_Ico]; omega),
    if_pos (by rw [Finset.mem_Ico]; omega)]
  have hnR : (n : ℝ) = 2 * m := by exact_mod_cast congrArg Nat.cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hargm : (((m - 1 : ℕ) : ℝ) + 1) * (2 * Real.pi / n) = Real.pi := by
    have hmR : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : (1 : ℕ) ≤ m := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hmR, hnR]
    field_simp
    ring
  have hargm1 : (((m : ℕ) : ℝ) + 1) * (2 * Real.pi / n)
      = Real.pi + 2 * Real.pi / n := by
    rw [hnR]
    field_simp
  rw [hargm, hargm1, Complex.exp_pi_mul_I, Complex.ofReal_add,
    Complex.ofReal_neg, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- **`V₁`** — the first-order value of column 1 of the two-level witness for
`m ≥ 3` (`lem:anchor_witness_two_level`):
`V₁ = ((−sin²ρ/cosρ + sinρ·i) + e^{iα}·(sin²ρ/cosρ + sinρ·i))/K²`. Equal to
the blueprint's `2i·K⁻²·tanρ·e^{iρ}` by the half-angle identity. -/
noncomputable def twoLevelV₁ (K : ℝ) : ℂ :=
  ((((-(Real.sin (Real.pi / n) ^ 2 / Real.cos (Real.pi / n)) : ℝ) : ℂ)
      + ((Real.sin (Real.pi / n) : ℝ) : ℂ) * Complex.I)
    + Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I)
      * (((Real.sin (Real.pi / n) ^ 2 / Real.cos (Real.pi / n) : ℝ) : ℂ)
        + ((Real.sin (Real.pi / n) : ℝ) : ℂ) * Complex.I))
    / ((K ^ 2 : ℝ) : ℂ)

/-- **The strict `ε`-derivative of column 1 of the two-level witness**
(`lem:anchor_witness_two_level`, R2, interior case `m ≥ 3`):
`C₁'(0) = V₁`. -/
theorem hasStrictDerivAt_twoLevelCol₁ [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) (hm3 : 3 ≤ m) {K : ℝ} (hK : 0 < K) :
    HasStrictDerivAt (twoLevelCol (n := n) m hK 1) (twoLevelV₁ (n := n) K)
      0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hψ1ℂ : HasStrictDerivAt
      (fun ε : ℝ => ((∑ i ∈ Finset.range (1 + 1),
          twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ))
      ((twoLevelHeadDot (n := n) m K 1 : ℝ) : ℂ) 0 :=
    hasStrictDerivAt_ofReal_comp
      (hasStrictDerivAt_twoLevelHead hn4 hn hK (by omega))
  have hexp1 : HasStrictDerivAt
      (fun ε : ℝ => Complex.exp (((∑ i ∈ Finset.range (1 + 1),
          twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((∑ i ∈ Finset.range (1 + 1),
          twoLevelTheta (n := n) m hK 0 i : ℝ) : ℂ) * Complex.I)
        * (((twoLevelHeadDot (n := n) m K 1 : ℝ) : ℂ) * Complex.I)) 0 :=
    (Complex.hasStrictDerivAt_exp _).comp 0 (hψ1ℂ.mul_const Complex.I)
  have hfirst := hexp1.const_mul
    (((2 * (1 / (K / (2 * Real.cos (Real.pi / n))
      + K / (2 * Real.cos (Real.pi / n)))) : ℝ) : ℂ))
  have hE1 := hasStrictDerivAt_twoLevelEdge hn4 hn hK (r := 1) (by omega)
  have hsecond := hE1.const_mul
    (((2 * (K / (2 * Real.cos (Real.pi / n))
        / (K / (2 * Real.cos (Real.pi / n))
          + K / (2 * Real.cos (Real.pi / n)))) - 1 : ℝ) : ℂ))
  have hsum : HasStrictDerivAt
      (fun ε : ℝ => ∑ r ∈ Finset.Ico (1 + 1) (1 + m),
        ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (r + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
      (∑ r ∈ Finset.Ico (1 + 1) (1 + m),
        ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
              then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
            * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                * Complex.I)
          + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
            * (Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                * Complex.I)
              * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) * Complex.I))))
      0 := by
    have h := HasStrictDerivAt.sum (u := Finset.Ico (1 + 1) (1 + m))
      (x := (0 : ℝ))
      (fun r hr => hasStrictDerivAt_twoLevelEdge hn4 hn hK (r := r)
        (by have := Finset.mem_Ico.mp hr; omega))
    have hfun : (∑ r ∈ Finset.Ico (1 + 1) (1 + m),
          fun ε : ℝ => ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
            * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
        = fun ε : ℝ => ∑ r ∈ Finset.Ico (1 + 1) (1 + m),
            ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
              * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                  twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I) := by
      funext ε
      simp
    rwa [hfun] at h
  have hev : ∀ᶠ ε : ℝ in nhds 0, |ε| < K :=
    (continuous_abs.tendsto' 0 0 abs_zero).eventually_lt_const hK
  have htot : HasStrictDerivAt
      (fun ε : ℝ => ((2 * (1 / (K / (2 * Real.cos (Real.pi / n))
            + K / (2 * Real.cos (Real.pi / n)))) : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (1 + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I)
        + Complex.I * (((2 * (K / (2 * Real.cos (Real.pi / n))
              / (K / (2 * Real.cos (Real.pi / n))
                + K / (2 * Real.cos (Real.pi / n)))) - 1 : ℝ) : ℂ)
            * (((twoLevelBaseLen (n := n) m hK ε 1 : ℝ) : ℂ)
              * Complex.exp (((∑ i ∈ Finset.range (1 + 1),
                  twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
          + ∑ r ∈ Finset.Ico (1 + 1) (1 + m),
              ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
                * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                    twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I)))
      (((2 * (1 / (K / (2 * Real.cos (Real.pi / n))
            + K / (2 * Real.cos (Real.pi / n)))) : ℝ) : ℂ)
          * (Complex.exp (((∑ i ∈ Finset.range (1 + 1),
              twoLevelTheta (n := n) m hK 0 i : ℝ) : ℂ) * Complex.I)
            * (((twoLevelHeadDot (n := n) m K 1 : ℝ) : ℂ) * Complex.I))
        + Complex.I * (((2 * (K / (2 * Real.cos (Real.pi / n))
              / (K / (2 * Real.cos (Real.pi / n))
                + K / (2 * Real.cos (Real.pi / n)))) - 1 : ℝ) : ℂ)
            * ((((if (1 : ℕ) = 0 ∨ 1 = m - 1 ∨ 1 = m ∨ 1 = n - 1
                  then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
                * Complex.exp ((((((1 : ℕ) : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                    * Complex.I)
              + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
                * (Complex.exp ((((((1 : ℕ) : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                    * Complex.I)
                  * (((twoLevelHeadDot (n := n) m K 1 : ℝ) : ℂ) * Complex.I)))
          + ∑ r ∈ Finset.Ico (1 + 1) (1 + m),
              ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
                    then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
                  * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                      * Complex.I)
                + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
                  * (Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                      * Complex.I)
                    * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ)
                      * Complex.I))))) 0 :=
    hfirst.add ((hsecond.add hsum).const_mul Complex.I)
  rw [sum_twoLevelEdgeDot₁ hn4 hn hm3 hK,
    sum_exp_Ico_eq hn4 hn (q := 1) (by omega),
    sum_twoLevelTheta_zero hn4 hK 1] at htot
  have hhd1 : twoLevelHeadDot (n := n) m K 1
      = Real.tan (Real.pi / n) / (2 * K) := by
    unfold twoLevelHeadDot
    rw [if_neg (by omega), if_neg (by omega)]
  have hE1if : ((if (1 : ℕ) = 0 ∨ 1 = m - 1 ∨ 1 = m ∨ 1 = n - 1
      then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) = 0 :=
    if_neg (by omega)
  rw [hhd1, hE1if] at htot
  have hfold : ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
      * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ) * Complex.I
      * (Complex.I
        * ((Real.cos (Real.pi / n) / Real.sin (Real.pi / n) : ℝ) : ℂ)
        * Complex.exp ((((((1 : ℕ) : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
            * Complex.I))
      = -(((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
        * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ)
        * ((Real.cos (Real.pi / n) / Real.sin (Real.pi / n) : ℝ) : ℂ)
        * Complex.exp ((((((1 : ℕ) : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
            * Complex.I)) := by
    linear_combination (((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
      * ((Real.tan (Real.pi / n) / (2 * K) : ℝ) : ℂ)
      * ((Real.cos (Real.pi / n) / Real.sin (Real.pi / n) : ℝ) : ℂ)
      * Complex.exp ((((((1 : ℕ) : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
          * Complex.I)) * Complex.I_mul_I
  rw [hfold] at htot
  have hd := HasStrictDerivAt.congr_of_eventuallyEq htot
    (by filter_upwards [hev] with ε hε
        exact (twoLevelCol_formula₁ hn4 hn hm3 hK hε).symm)
  convert hd using 2
  · unfold twoLevelV₁
    have hsC : ((Real.sin (Real.pi / n) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hsin0.ne'
    have hcC : ((Real.cos (Real.pi / n) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hcos.ne'
    have hKC : ((K : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
    rw [Real.tan_eq_sin_div_cos]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_pow, Complex.ofReal_zero,
      Nat.cast_one]
    field_simp
    linear_combination (2 * ((Real.sin (Real.pi / (n : ℝ)) : ℝ) : ℂ) ^ 2
      * (Complex.exp (Complex.I * 2 * (Real.pi : ℂ) / ((n : ℝ) : ℂ)) - 1))
      * Complex.I_mul_I

/-! ### The column-1 derivative of the two-level witness, boundary case
`m = 2` (`n = 4`): all four edges are special (`V₁` row, `m = 2`) -/

/-- **The total formula of column 1 on the window, `m = 2`**: edge 1 is the
special edge `m − 1`, so it carries the moving pair `(K, K + ε)` — `λ'₁` and
`p₁` are the moving slot expressions with the mixed slot in head position. -/
theorem twoLevelCol_formula₁' [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) (hm2 : m = 2) {K ε : ℝ} (hK : 0 < K) (hε : |ε| < K) :
    twoLevelCol (n := n) m hK 1 ε
      = ((2 * (1 / (chartSlotDeriv K
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
            + chartSlotDeriv (K + ε)
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))) : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (1 + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I)
        + Complex.I * (((2 * (chartSlotDeriv K
                (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
              / (chartSlotDeriv K
                  (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
                + chartSlotDeriv (K + ε)
                  (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))) - 1 : ℝ) : ℂ)
            * (((twoLevelBaseLen (n := n) m hK ε 1 : ℝ) : ℂ)
              * Complex.exp (((∑ i ∈ Finset.range (1 + 1),
                  twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
          + ∑ r ∈ Finset.Ico (1 + 1) (1 + m),
              ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
                * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                    twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I)) := by
  rw [twoLevelCol_eq hK hε 1]
  unfold closingJacobianCol
  have hedge : ∀ r ∈ Finset.Ico (1 + 1) (1 + m),
      jacobianEdge (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i) r
        = ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (r + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I) := by
    intro r hr
    have hrn : r < n := by
      have := Finset.mem_Ico.mp hr
      omega
    exact jacobianEdge_twoLevel hn4 hn hK hε hrn
  rw [Finset.sum_congr rfl hedge,
    jacobianEdge_twoLevel hn4 hn hK hε (r := 1) (by omega),
    heading_twoLevel hn4 hn hK hε (j := 1) (by omega)]
  have hbl : jacobianBaseLen
      (fun i => twoLevelProfile_pos (n := n) (m := m) hK hε i) ((1 : ℕ) : ZMod n)
      = chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε) := by
    rw [twoLevelBaseLen_eq hn4 hn hK hε (j := 1) (by omega)]
    unfold twoLevelBaseLen
    rw [if_pos (Or.inr (Or.inl (by omega)))]
  have hκ1 : twoLevelProfile (n := n) m K ε ((1 : ℕ) : ZMod n) = K := by
    rw [twoLevelProfile_natCast hn K ε (by omega), if_neg (by omega), add_zero]
  have hκ2 : twoLevelProfile (n := n) m K ε (((1 : ℕ) : ZMod n) + 1)
      = K + ε := by
    rw [twoLevelProfile_natCast_succ hn K ε (by omega),
      if_pos (Or.inl (by omega))]
  unfold jacobianLambda' jacobianShare
  rw [hbl, hκ1, hκ2]

/-- The mixed-first tail share `B/(B + A)` of the special edge `m − 1` moves
at `−ṗ = −1/(4K·cos²ρ)` — the column-1 share row for `m = 2`, where edge 1
carries the moving pair in head position. -/
private lemma hasStrictDerivAt_twoLevelShareMixed [NeZero n] (hn4 : 4 ≤ n)
    {K : ℝ} (hK : 0 < K) :
    HasStrictDerivAt
      (fun ε : ℝ => chartSlotDeriv K
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        / (chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
          + chartSlotDeriv (K + ε)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))))
      (-(1 / (4 * K * Real.cos (Real.pi / n) ^ 2))) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hB := hasStrictDerivAt_mixedSlotDeriv hn4 hK
  have hBA : HasStrictDerivAt
      (fun ε : ℝ => chartSlotDeriv K
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        + chartSlotDeriv (K + ε)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))
      (-(Real.sin (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)
        + (1 + Real.cos (Real.pi / n) ^ 2)
          / (4 * Real.cos (Real.pi / n) ^ 3)) 0 :=
    hB.add (hasStrictDerivAt_bumpSlotDeriv hn4 hK)
  have hBA0 : chartSlotDeriv K
        (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
      + chartSlotDeriv (K + 0)
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)) ≠ 0 := by
    rw [add_zero, twoLevelSlot_zero hn4 hK]
    positivity
  have hdiv : HasStrictDerivAt
      (fun ε : ℝ => chartSlotDeriv K
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        / (chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
          + chartSlotDeriv (K + ε)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))))
      ((-(Real.sin (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)
          * (chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
            + chartSlotDeriv (K + 0)
                (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)))
        - chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          * (-(Real.sin (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)
            + (1 + Real.cos (Real.pi / n) ^ 2)
              / (4 * Real.cos (Real.pi / n) ^ 3)))
       / (chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          + chartSlotDeriv (K + 0)
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))) ^ 2) 0 :=
    hB.div hBA hBA0
  have hveq : (-(Real.sin (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)
          * (chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
            + chartSlotDeriv (K + 0)
                (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0)))
        - chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          * (-(Real.sin (Real.pi / n) ^ 2) / (4 * Real.cos (Real.pi / n) ^ 3)
            + (1 + Real.cos (Real.pi / n) ^ 2)
              / (4 * Real.cos (Real.pi / n) ^ 3)))
       / (chartSlotDeriv K (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))
          + chartSlotDeriv (K + 0)
              (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + 0))) ^ 2
      = -(1 / (4 * K * Real.cos (Real.pi / n) ^ 2)) := by
    rw [add_zero, twoLevelSlot_zero hn4 hK, Real.sin_sq]
    field_simp
    ring
  rwa [hveq] at hdiv

/-- **`V₁` for `m = 2`** (`lem:anchor_witness_two_level`, boundary case
`n = 4`): `V₁ = 2√2·i/K²` — the first-order value of column 1 when all four
edges are special. -/
noncomputable def twoLevelV₁' (K : ℝ) : ℂ :=
  ((2 * Real.sqrt 2 / K ^ 2 : ℝ) : ℂ) * Complex.I

/-- **The strict `ε`-derivative of column 1 of the two-level witness, `m = 2`**
(`lem:anchor_witness_two_level`, boundary case `n = 4`):
`C₁'(0) = V₁ = 2√2·i/K²`. -/
theorem hasStrictDerivAt_twoLevelCol₁' [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) (hm2 : m = 2) {K : ℝ} (hK : 0 < K) :
    HasStrictDerivAt (twoLevelCol (n := n) m hK 1) (twoLevelV₁' K) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  have hψ1ℂ : HasStrictDerivAt
      (fun ε : ℝ => ((∑ i ∈ Finset.range (1 + 1),
          twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ))
      ((twoLevelHeadDot (n := n) m K 1 : ℝ) : ℂ) 0 :=
    hasStrictDerivAt_ofReal_comp
      (hasStrictDerivAt_twoLevelHead hn4 hn hK (by omega))
  have hexp1 : HasStrictDerivAt
      (fun ε : ℝ => Complex.exp (((∑ i ∈ Finset.range (1 + 1),
          twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((∑ i ∈ Finset.range (1 + 1),
          twoLevelTheta (n := n) m hK 0 i : ℝ) : ℂ) * Complex.I)
        * (((twoLevelHeadDot (n := n) m K 1 : ℝ) : ℂ) * Complex.I)) 0 :=
    (Complex.hasStrictDerivAt_exp _).comp 0 (hψ1ℂ.mul_const Complex.I)
  have hΛ : HasStrictDerivAt
      (fun ε : ℝ => 1 / (chartSlotDeriv K
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        + chartSlotDeriv (K + ε)
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))))
      (-(Real.cos (Real.pi / n)) / (2 * K ^ 2)) 0 := by
    have h := hasStrictDerivAt_twoLevelLambda' hn4 hK
    have hfun : (fun ε : ℝ => 1 / (chartSlotDeriv (K + ε)
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
        + chartSlotDeriv K
          (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))))
        = (fun ε : ℝ => 1 / (chartSlotDeriv K
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε))
          + chartSlotDeriv (K + ε)
            (chartInvCurv hK (2 * Real.pi / (n : ℝ)) (K + ε)))) := by
      funext ε
      rw [add_comm]
    rwa [hfun] at h
  have h2Λ := hasStrictDerivAt_ofReal_comp (hΛ.const_mul 2)
  have hfirst := h2Λ.mul hexp1
  have hsh := hasStrictDerivAt_ofReal_comp
    (((hasStrictDerivAt_twoLevelShareMixed hn4 hK).const_mul 2).sub_const 1)
  have hE1 := hasStrictDerivAt_twoLevelEdge hn4 hn hK (r := 1) (by omega)
  have hsecond := hsh.mul hE1
  have hsum : HasStrictDerivAt
      (fun ε : ℝ => ∑ r ∈ Finset.Ico (1 + 1) (1 + m),
        ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
          * Complex.exp (((∑ i ∈ Finset.range (r + 1),
              twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
      (∑ r ∈ Finset.Ico (1 + 1) (1 + m),
        ((((if r = 0 ∨ r = m - 1 ∨ r = m ∨ r = n - 1
              then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ)) : ℂ)
            * Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                * Complex.I)
          + ((2 * Real.sin (Real.pi / n) / K : ℝ) : ℂ)
            * (Complex.exp (((((r : ℝ) + 1) * (2 * Real.pi / n) : ℝ) : ℂ)
                * Complex.I)
              * (((twoLevelHeadDot (n := n) m K r : ℝ) : ℂ) * Complex.I))))
      0 := by
    have h := HasStrictDerivAt.sum (u := Finset.Ico (1 + 1) (1 + m))
      (x := (0 : ℝ))
      (fun r hr => hasStrictDerivAt_twoLevelEdge hn4 hn hK (r := r)
        (by have := Finset.mem_Ico.mp hr; omega))
    have hfun : (∑ r ∈ Finset.Ico (1 + 1) (1 + m),
          fun ε : ℝ => ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
            * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I))
        = fun ε : ℝ => ∑ r ∈ Finset.Ico (1 + 1) (1 + m),
            ((twoLevelBaseLen (n := n) m hK ε r : ℝ) : ℂ)
              * Complex.exp (((∑ i ∈ Finset.range (r + 1),
                  twoLevelTheta (n := n) m hK ε i : ℝ) : ℂ) * Complex.I) := by
      funext ε
      simp
    rwa [hfun] at h
  have hev : ∀ᶠ ε : ℝ in nhds 0, |ε| < K :=
    (continuous_abs.tendsto' 0 0 abs_zero).eventually_lt_const hK
  have htot := hfirst.add ((hsecond.add hsum).const_mul Complex.I)
  have hd := HasStrictDerivAt.congr_of_eventuallyEq htot
    (by filter_upwards [hev] with ε hε
        exact (twoLevelCol_formula₁' hn4 hn hm2 hK hε).symm)
  convert hd using 2
  · unfold twoLevelV₁'
    have hIco2 : Finset.Ico (1 + 1) (1 + m) = ({2} : Finset ℕ) := by
      rw [hm2]
      decide
    rw [hIco2, Finset.sum_singleton]
    have hhd1 : twoLevelHeadDot (n := n) m K 1 = 0 := by
      unfold twoLevelHeadDot
      rw [if_neg (by omega), if_pos (by omega)]
    have hhd2 : twoLevelHeadDot (n := n) m K 2
        = Real.tan (Real.pi / n) / K := by
      unfold twoLevelHeadDot
      rw [if_pos (Or.inr (by omega))]
    have hif1 : ((if (1 : ℕ) = 0 ∨ 1 = m - 1 ∨ 1 = m ∨ 1 = n - 1
        then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ))
        = -(Real.sin (Real.pi / n) / K ^ 2) := if_pos (by omega)
    have hif2 : ((if (2 : ℕ) = 0 ∨ 2 = m - 1 ∨ 2 = m ∨ 2 = n - 1
        then -(Real.sin (Real.pi / n) / K ^ 2) else 0 : ℝ))
        = -(Real.sin (Real.pi / n) / K ^ 2) := if_pos (by omega)
    have hbl01 : twoLevelBaseLen (n := n) m hK 0 1
        = 2 * Real.sin (Real.pi / n) / K := by
      rw [twoLevelBaseLen_zero hK 1, chartInv_const hn4 hK]
    rw [hhd1, hhd2, hif1, hif2, hbl01, sum_twoLevelTheta_zero hn4 hK 1,
      add_zero, twoLevelSlot_zero hn4 hK]
    have hn4eq : n = 4 := by omega
    have hnR : ((n : ℕ) : ℝ) = 4 := by
      rw [hn4eq]
      norm_num
    have hρ4 : Real.pi / (n : ℝ) = Real.pi / 4 := by rw [hnR]
    have harg1 : (((1 : ℕ) : ℝ) + 1) * (2 * Real.pi / (n : ℝ)) = Real.pi := by
      rw [hnR]
      push_cast
      ring
    have harg2 : (((2 : ℕ) : ℝ) + 1) * (2 * Real.pi / (n : ℝ))
        = Real.pi / 2 + Real.pi := by
      rw [hnR]
      push_cast
      ring
    have hexp32 : Complex.exp (((Real.pi / 2 + Real.pi : ℝ) : ℂ) * Complex.I)
        = -Complex.I := by
      rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I,
        Complex.ofReal_div, Complex.ofReal_ofNat,
        Complex.exp_pi_div_two_mul_I]
      ring
    rw [harg1, harg2, hρ4, Complex.exp_pi_mul_I, hexp32,
      Real.tan_pi_div_four, Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt two_pos.le]
      norm_num
    have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
    have hsC : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hs2pos.ne'
    have hKC : ((K : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_pow, Complex.ofReal_zero]
    field_simp
    linear_combination ((-8) * ((Real.sqrt 2 : ℝ) : ℂ) ^ 2
        + 16 * ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 * Complex.I) * Complex.I_mul_I
      + (16 * Complex.I) * hs2

/-! ### R4 — slope-limit packaging of the two-level pairing
(`lem:anchor_witness_two_level`) -/

/-- Slope form of a strict `ℂ`-valued derivative at `0` with base value `0`:
the normalized column `C(ε)/ε` tends to `C'(0)` along the punctured
neighborhood — the R4 bridge of `lem:anchor_witness_two_level`. -/
private lemma tendsto_div_ofReal_of_hasStrictDerivAt {f : ℝ → ℂ} {v : ℂ}
    (hf : HasStrictDerivAt f v 0) (hf0 : f 0 = 0) :
    Filter.Tendsto (fun ε : ℝ => f ε / (ε : ℂ))
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds v) := by
  have h := hasDerivAt_iff_tendsto_slope.mp hf.hasDerivAt
  have hs : slope f 0 = fun ε : ℝ => f ε / (ε : ℂ) := by
    funext ε
    rw [slope_def_module, hf0, sub_zero, sub_zero, Complex.real_smul,
      Complex.ofReal_inv]
    ring
  rwa [hs] at h

/-- **R4 — the normalized two-level pairing has a limit**: if the two columns
have strict derivatives `V₀, V₁` at `0`, then
`Im(conj C₀(ε) · C₁(ε))/ε² → Im(conj V₀ · V₁)` along `𝓝[≠] 0`
(`lem:anchor_witness_two_level`, slope-limit step). -/
theorem tendsto_twoLevelPairing [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) {V₀ V₁ : ℂ}
    (h₀ : HasStrictDerivAt (twoLevelCol (n := n) m hK 0) V₀ 0)
    (h₁ : HasStrictDerivAt (twoLevelCol (n := n) m hK 1) V₁ 0) :
    Filter.Tendsto
      (fun ε : ℝ => ((starRingEnd ℂ) (twoLevelCol (n := n) m hK 0 ε)
          * twoLevelCol (n := n) m hK 1 ε).im / ε ^ 2)
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ)
      (nhds (((starRingEnd ℂ) V₀ * V₁).im)) := by
  have hm2 : 2 ≤ m := by omega
  have ht0 := tendsto_div_ofReal_of_hasStrictDerivAt h₀
    (twoLevelCol_zero hn4 hn hK (by omega))
  have ht1 := tendsto_div_ofReal_of_hasStrictDerivAt h₁
    (twoLevelCol_zero hn4 hn hK (by omega))
  have hmul : Filter.Tendsto
      (fun ε : ℝ => (starRingEnd ℂ) (twoLevelCol (n := n) m hK 0 ε / (ε : ℂ))
        * (twoLevelCol (n := n) m hK 1 ε / (ε : ℂ)))
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ)
      (nhds ((starRingEnd ℂ) V₀ * V₁)) := ht0.star.mul ht1
  have him := (Complex.continuous_im.tendsto _).comp hmul
  refine him.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := hε
  have hprod : (starRingEnd ℂ) (twoLevelCol (n := n) m hK 0 ε / (ε : ℂ))
      * (twoLevelCol (n := n) m hK 1 ε / (ε : ℂ))
      = ((starRingEnd ℂ) (twoLevelCol (n := n) m hK 0 ε)
          * twoLevelCol (n := n) m hK 1 ε) / ((ε ^ 2 : ℝ) : ℂ) := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.ofReal_pow]
    ring
  simp only [Function.comp_apply, hprod, Complex.div_ofReal_im]

/-- **R4 — eventual nonvanishing of the two-level pairing**: if
`Im(conj V₀ · V₁) ≠ 0`, then `Im(conj C₀(ε) · C₁(ε)) ≠ 0` for all
sufficiently small `ε ≠ 0` (`lem:anchor_witness_two_level`, conclusion). -/
theorem eventually_twoLevelPairing_ne [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) {V₀ V₁ : ℂ}
    (h₀ : HasStrictDerivAt (twoLevelCol (n := n) m hK 0) V₀ 0)
    (h₁ : HasStrictDerivAt (twoLevelCol (n := n) m hK 1) V₁ 0)
    (hV : ((starRingEnd ℂ) V₀ * V₁).im ≠ 0) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ,
      ((starRingEnd ℂ) (twoLevelCol (n := n) m hK 0 ε)
        * twoLevelCol (n := n) m hK 1 ε).im ≠ 0 := by
  have h := (tendsto_twoLevelPairing hn4 hn hK h₀ h₁).eventually_ne hV
  filter_upwards [h] with ε hne hzero
  exact hne (by rw [hzero, zero_div])

/-! ### The pairing values `Im(conj V₀ · V₁)` -/

/-- **The interior pairing value** (`lem:anchor_witness_two_level`,
`m ≥ 3` row): `Im(conj V₀ · V₁) = −2·tanρ·sec²ρ/K⁴ = −2·sinρ/(cos³ρ·K⁴)`,
nonzero. -/
theorem im_conj_twoLevelV₀_mul_twoLevelV₁ [NeZero n] (hn4 : 4 ≤ n) {K : ℝ}
    (hK : 0 < K) :
    ((starRingEnd ℂ) (twoLevelV₀ (n := n) K) * twoLevelV₁ (n := n) K).im
      = -(2 * Real.sin (Real.pi / n)
          / (Real.cos (Real.pi / n) ^ 3 * K ^ 4)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hc0 : Real.cos (Real.pi / n) ≠ 0 := hcos.ne'
  have hK0 : K ≠ 0 := hK.ne'
  have he : Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (Real.pi / n) ^ 2 - Real.sin (Real.pi / n) ^ 2 : ℝ) : ℂ)
        + ((2 * Real.sin (Real.pi / n) * Real.cos (Real.pi / n) : ℝ) : ℂ)
          * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [show 2 * Real.pi / (n : ℝ) = 2 * (Real.pi / n) by ring,
      Real.cos_two_mul', Real.sin_two_mul]
  unfold twoLevelV₀ twoLevelV₁
  rw [he, map_div₀, Complex.conj_ofReal, div_mul_div_comm,
    ← Complex.ofReal_mul, Complex.div_ofReal_im]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, mul_zero, mul_one,
    add_zero, zero_add, sub_zero, neg_zero, neg_neg, mul_neg,
    neg_mul]
  have hs1 : Real.sin (Real.pi / n) ^ 2 + Real.cos (Real.pi / n) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  field_simp
  linear_combination (Real.sin (Real.pi / n)
      * (-(1 + Real.cos (Real.pi / n) ^ 2) * Real.sin (Real.pi / n) ^ 4
        - (2 + 3 * Real.cos (Real.pi / n) ^ 2
            + 2 * Real.cos (Real.pi / n) ^ 4) * Real.sin (Real.pi / n) ^ 2
        - (2 + 2 * Real.cos (Real.pi / n) ^ 2
            + 2 * Real.cos (Real.pi / n) ^ 4
            + Real.cos (Real.pi / n) ^ 6))) * hs1

/-- **`V₀` at `n = 4`** (`lem:anchor_witness_two_level`, `m = 2` row):
`V₀ = −2√2/K²` — the boundary evaluation of the uniform `twoLevelV₀`. -/
theorem twoLevelV₀_of_four [NeZero n] (hn4' : n = 4) {K : ℝ} (hK : 0 < K) :
    twoLevelV₀ (n := n) K = ((-(2 * Real.sqrt 2) / K ^ 2 : ℝ) : ℂ) := by
  have hnR : ((n : ℕ) : ℝ) = 4 := by
    rw [hn4']
    norm_num
  have hρ4 : Real.pi / (n : ℝ) = Real.pi / 4 := by rw [hnR]
  have hα2 : 2 * Real.pi / (n : ℝ) = Real.pi / 2 := by
    rw [hnR]
    ring
  have hexpI : Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I)
      = Complex.I := by
    rw [hα2, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.exp_pi_div_two_mul_I]
  unfold twoLevelV₀
  rw [hexpI, hρ4, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt two_pos.le]
    norm_num
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hsC : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hs2pos.ne'
  have hKC : ((K : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_neg,
    Complex.ofReal_ofNat, Complex.ofReal_pow]
  field_simp
  linear_combination (4 + ((Real.sqrt 2 : ℝ) : ℂ) ^ 2) * Complex.I_mul_I
    + 2 * hs2

/-- **The boundary pairing value** (`lem:anchor_witness_two_level`, `m = 2`
row): `Im(conj V₀ · V₁) = −8/K⁴`, nonzero. -/
theorem im_conj_twoLevelV₀_mul_twoLevelV₁' [NeZero n] (hn4' : n = 4) {K : ℝ}
    (hK : 0 < K) :
    ((starRingEnd ℂ) (twoLevelV₀ (n := n) K) * twoLevelV₁' K).im
      = -(8 / K ^ 4) := by
  rw [twoLevelV₀_of_four hn4' hK]
  unfold twoLevelV₁'
  rw [Complex.conj_ofReal]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one,
    add_zero, sub_zero]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt two_pos.le
  have hK0 : K ≠ 0 := hK.ne'
  field_simp
  linear_combination (-4) * hs2

/-! ### The two-level witness anchor (`lem:anchor_witness_two_level`) -/

/-- **The two-level witness anchor — explicit nondegenerate pair**
(`lem:anchor_witness_two_level`): for `n = 2m ≥ 4` and `K > 0` the two-level
profile `κ^(ε)` is positive on the window `|ε| < K`, half-period symmetric,
non-constant for `ε ≠ 0`, and its closing pair satisfies
`Im(conj C₀(ε) · C₁(ε)) ≠ 0` for all sufficiently small `ε ≠ 0`. -/
theorem anchorWitness_two_level [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {K : ℝ} (hK : 0 < K) :
    (∀ ε : ℝ, |ε| < K → ∀ j, 0 < twoLevelProfile (n := n) m K ε j)
    ∧ (∀ (ε : ℝ) (i : ZMod n), twoLevelProfile (n := n) m K ε (i + (m : ZMod n))
        = twoLevelProfile (n := n) m K ε i)
    ∧ (∀ ε : ℝ, ε ≠ 0 → twoLevelProfile (n := n) m K ε 1
        ≠ twoLevelProfile (n := n) m K ε 0)
    ∧ ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ,
        ((starRingEnd ℂ) (twoLevelCol (n := n) m hK 0 ε)
          * twoLevelCol (n := n) m hK 1 ε).im ≠ 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπ := Real.pi_pos
  have hρpos : 0 < Real.pi / n := by positivity
  have hρhalf : Real.pi / n < Real.pi / 2 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hπ.le four_pos hn4') (by linarith)
  have hcos : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hρhalf⟩
  have hsin0 : 0 < Real.sin (Real.pi / n) :=
    Real.sin_pos_of_pos_of_lt_pi hρpos (by linarith)
  refine ⟨fun ε hε j => twoLevelProfile_pos hK hε j,
    fun ε i => twoLevelProfile_symm hn K ε i,
    fun ε hε => twoLevelProfile_ne_of_ne hn4 hn hε, ?_⟩
  by_cases hm2 : m = 2
  · refine eventually_twoLevelPairing_ne hn4 hn hK
      (hasStrictDerivAt_twoLevelCol₀ hn4 hn hK)
      (hasStrictDerivAt_twoLevelCol₁' hn4 hn hm2 hK) ?_
    rw [im_conj_twoLevelV₀_mul_twoLevelV₁' (by omega) hK]
    have hpos : (0 : ℝ) < 8 / K ^ 4 := by positivity
    exact neg_ne_zero.mpr hpos.ne'
  · have hm3 : 3 ≤ m := by omega
    refine eventually_twoLevelPairing_ne hn4 hn hK
      (hasStrictDerivAt_twoLevelCol₀ hn4 hn hK)
      (hasStrictDerivAt_twoLevelCol₁ hn4 hn hm3 hK) ?_
    rw [im_conj_twoLevelV₀_mul_twoLevelV₁ hn4 hK]
    have hpos : (0 : ℝ) < 2 * Real.sin (Real.pi / n)
        / (Real.cos (Real.pi / n) ^ 3 * K ^ 4) :=
      div_pos (mul_pos two_pos hsin0)
        (mul_pos (pow_pos hcos 3) (pow_pos hK 4))
    exact neg_ne_zero.mpr hpos.ne'

/-! ## The moving pair rectangle and its fixed-square normalization
(`def:closing_rect`)

The natural domain of the closing 2-cell in the chart coordinates is the
*moving rectangle* `R_t`: at each of the four perturbed edges the chart value
must stay in the closed interval `[0, w_j(t)]`, where
`w_j(t) = chartMap (κ_t j) (κ_t (j+1)) (2 / max ...)` is the *exact wall* of
edge `j` (`lem:chart_wall`). This section builds, per `def:closing_rect`:
the wall widths (`wallWidth`) and their continuity in `t`; the rectangle
endpoint functions (`rectLo`/`rectHi`) with their sign and continuity lemmas;
the per-coordinate piecewise-affine rescale (`rescale`/`rectRescale`,
`Ξ_t : [-1,1]² → R_t`, `Ξ_t 0 = 0`) with joint continuity; and the
fixed-square gap map `H(t,q) = F(t, Ξ_t q)` (`closingRectGap`) with its
continuity on the sub-square supported by the landed window continuity of
`Φ` (`continuousOn_closingGap`). -/

/-- The exact chart wall of a single edge with curvature pair `(p, q)`: the
supremum `chartMap p q (2 / max p q)` of the achievable turning values
(`lem:chart_wall`). For positive `p, q` it equals
`π/2 + arcsin (min p q / max p q)` (`chartWall_eq_pi_div_two_add`), in
particular it exceeds `π/2` (`pi_div_two_lt_chartWall`). -/
noncomputable def chartWall (p q : ℝ) : ℝ := chartMap p q (2 / max p q)

/-- The chart wall in normalized-argument form: at the wall length both
`arcsin` arguments are the curvature ratios `p / max`, `q / max`. -/
theorem chartWall_eq (p q : ℝ) (h : max p q ≠ 0) :
    chartWall p q = Real.arcsin (p / max p q) + Real.arcsin (q / max p q) := by
  unfold chartWall chartMap
  congr 2 <;> field_simp

/-- The exact wall value of `lem:chart_wall`:
`chartWall p q = π/2 + arcsin (min p q / max p q)` for positive curvatures
(the larger ratio saturates at `arcsin 1 = π/2`). -/
theorem chartWall_eq_pi_div_two_add {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    chartWall p q = Real.pi / 2 + Real.arcsin (min p q / max p q) := by
  have hmax : (0 : ℝ) < max p q := lt_of_lt_of_le hp (le_max_left p q)
  rw [chartWall_eq p q hmax.ne']
  rcases le_total p q with h | h
  · rw [max_eq_right h, min_eq_left h, div_self (hp.trans_le h).ne',
      Real.arcsin_one, add_comm]
  · rw [max_eq_left h, min_eq_right h, div_self (hq.trans_le h).ne',
      Real.arcsin_one]

/-- The chart wall exceeds `π/2` (restatement of
`pi_div_two_lt_chartMap_wall` in terms of `chartWall`). -/
theorem pi_div_two_lt_chartWall {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.pi / 2 < chartWall p q :=
  pi_div_two_lt_chartMap_wall hp hq

/-- The chart wall of a continuous positive curvature family is continuous
(via the normalized form `arcsin (p/max) + arcsin (q/max)`; `max` stays
positive). -/
theorem continuous_chartWall_comp {T : Type*} [TopologicalSpace T]
    {p q : T → ℝ} (hp : ∀ τ, 0 < p τ) (_hq : ∀ τ, 0 < q τ)
    (hpc : Continuous p) (hqc : Continuous q) :
    Continuous fun τ => chartWall (p τ) (q τ) := by
  have hmax : ∀ τ, max (p τ) (q τ) ≠ 0 := fun τ =>
    (lt_of_lt_of_le (hp τ) (le_max_left _ _)).ne'
  have hEq : (fun τ => chartWall (p τ) (q τ))
      = fun τ => Real.arcsin (p τ / max (p τ) (q τ))
        + Real.arcsin (q τ / max (p τ) (q τ)) := by
    funext τ; exact chartWall_eq _ _ (hmax τ)
  rw [hEq]
  exact (Real.continuous_arcsin.comp (hpc.div (hpc.max hqc) hmax)).add
    (Real.continuous_arcsin.comp (hqc.div (hpc.max hqc) hmax))

/-- **The moving wall width of edge `j`** along the anchor path
(`def:closing_rect`): the exact chart wall of the pair
`(κ_t j, κ_t (j+1))`, `κ_t = curvPath κs κ t`. -/
noncomputable def wallWidth (κs κ : ZMod n → ℝ) (j : ZMod n) (t : ℝ) : ℝ :=
  chartWall (curvPath κs κ t j) (curvPath κs κ t (j + 1))

/-- The moving wall width exceeds `π/2` along the whole homotopy. -/
theorem pi_div_two_lt_wallWidth {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (j : ZMod n) :
    Real.pi / 2 < wallWidth κs κ j t :=
  pi_div_two_lt_chartWall (curvPath_pos hκs hκ ht0 ht1 j)
    (curvPath_pos hκs hκ ht0 ht1 (j + 1))

/-- The moving wall width is continuous in the homotopy time (on the compact
time interval, where positivity holds). -/
theorem continuous_wallWidth {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) (j : ZMod n) :
    Continuous fun τ : ↥(Set.Icc (0 : ℝ) 1) => wallWidth κs κ j ↑τ :=
  continuous_chartWall_comp (fun τ => curvPath_pos hκs hκ τ.2.1 τ.2.2 j)
    (fun τ => curvPath_pos hκs hκ τ.2.1 τ.2.2 (j + 1))
    ((continuous_curvPath κs κ j).comp continuous_subtype_val)
    ((continuous_curvPath κs κ (j + 1)).comp continuous_subtype_val)

/-! ### The rectangle interval endpoints (`def:closing_rect`, R-b)

A perturbation coordinate `u` enters two opposite edges: with sign `+` at the
edge `e₊` (chart value `α + u`, `α = 2π/n`) and with sign `−` at the edge
`e₋ = e₊ + m` (chart value `α − u`). Keeping both chart values in their walls
`[0, w(t)]` confines `u` to
`[max (−α) (α − w_{e₋}(t)), min (w_{e₊}(t) − α) α]`, an interval with
strictly negative left and strictly positive right endpoint. -/

/-- The left endpoint of a rectangle factor: the constraint of the `−`-signed
edge `e`, `rectLo = max (−α) (α − w_e(t))` with `α = 2π/n`. -/
noncomputable def rectLo (κs κ : ZMod n → ℝ) (e : ZMod n) (t : ℝ) : ℝ :=
  max (-(2 * Real.pi / n)) (2 * Real.pi / n - wallWidth κs κ e t)

/-- The right endpoint of a rectangle factor: the constraint of the
`+`-signed edge `e`, `rectHi = min (w_e(t) − α) α`. -/
noncomputable def rectHi (κs κ : ZMod n → ℝ) (e : ZMod n) (t : ℝ) : ℝ :=
  min (wallWidth κs κ e t - 2 * Real.pi / n) (2 * Real.pi / n)

/-- `α = 2π/n ≤ π/2` for `n ≥ 4` — the base chart value clears every wall
(`w > π/2`). Stated once; feeds all sign lemmas of the rectangle. -/
theorem two_pi_div_le_pi_div_two [NeZero n] (hn4 : 4 ≤ n) :
    2 * Real.pi / n ≤ Real.pi / 2 := by
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hπn4 : Real.pi / n ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left Real.pi_pos.le four_pos hn4'
  rw [mul_div_assoc]
  linarith

/-- The left endpoint is strictly negative (`−α < 0` and `α − w < 0` since
`α ≤ π/2 < w`): the rectangle factor contains `0` in its interior from the
left. -/
theorem rectLo_neg [NeZero n] (hn4 : 4 ≤ n) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (e : ZMod n) : rectLo κs κ e t < 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hα : 0 < 2 * Real.pi / n := by positivity
  have hα2 := two_pi_div_le_pi_div_two (n := n) hn4
  have hw := pi_div_two_lt_wallWidth hκs hκ ht0 ht1 e
  exact max_lt (by linarith) (by linarith)

/-- The right endpoint is strictly positive (`w − α > 0` since `w > π/2 ≥ α`,
and `α > 0`): the rectangle factor contains `0` in its interior from the
right. -/
theorem rectHi_pos [NeZero n] (hn4 : 4 ≤ n) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (e : ZMod n) : 0 < rectHi κs κ e t := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hα : 0 < 2 * Real.pi / n := by positivity
  have hα2 := two_pi_div_le_pi_div_two (n := n) hn4
  have hw := pi_div_two_lt_wallWidth hκs hκ ht0 ht1 e
  exact lt_min (by linarith) hα

/-- The left endpoint never drops below `−α` (needed for the uniform bound
`|Ξ_t(q)| ≤ α·|q|` of the rescale). -/
theorem neg_le_rectLo (κs κ : ZMod n → ℝ) (e : ZMod n) (t : ℝ) :
    -(2 * Real.pi / n) ≤ rectLo κs κ e t := le_max_left _ _

/-- The right endpoint never exceeds `α`. -/
theorem rectHi_le (κs κ : ZMod n → ℝ) (e : ZMod n) (t : ℝ) :
    rectHi κs κ e t ≤ 2 * Real.pi / n := min_le_right _ _

/-- The left endpoint is continuous in the homotopy time. -/
theorem continuous_rectLo {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) (e : ZMod n) :
    Continuous fun τ : ↥(Set.Icc (0 : ℝ) 1) => rectLo κs κ e ↑τ :=
  continuous_const.max
    (continuous_const.sub (continuous_wallWidth hκs hκ e))

/-- The right endpoint is continuous in the homotopy time. -/
theorem continuous_rectHi {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) (e : ZMod n) :
    Continuous fun τ : ↥(Set.Icc (0 : ℝ) 1) => rectHi κs κ e ↑τ :=
  ((continuous_wallWidth hκs hκ e).sub continuous_const).min continuous_const

/-! ### The piecewise-affine rescale of a single factor (`def:closing_rect`, R-c)

`rescale L R` maps `[-1, 0]` affinely onto `[L, 0]` and `[0, 1]` affinely
onto `[0, R]`, fixing `0` — the one-coordinate building block of the
fixed-square normalization `Ξ_t : [-1,1]² → R_t`. -/

/-- The piecewise-affine rescale: `rescale L R x = (−L)·min x 0 + R·max x 0`
(so `x ≤ 0 ↦ (−L)·x` and `x ≥ 0 ↦ R·x`). -/
noncomputable def rescale (L R x : ℝ) : ℝ := -L * min x 0 + R * max x 0

@[simp] lemma rescale_zero (L R : ℝ) : rescale L R 0 = 0 := by
  simp [rescale]

@[simp] lemma rescale_one (L R : ℝ) : rescale L R 1 = R := by
  norm_num [rescale]

@[simp] lemma rescale_neg_one (L R : ℝ) : rescale L R (-1) = L := by
  norm_num [rescale]

/-- The rescale is jointly continuous in the endpoints and the coordinate. -/
theorem continuous_rescale :
    Continuous fun p : (ℝ × ℝ) × ℝ => rescale p.1.1 p.1.2 p.2 := by
  unfold rescale; fun_prop

/-- The rescale of a fixed factor is continuous in the coordinate. -/
theorem continuous_rescale_coord (L R : ℝ) : Continuous (rescale L R) := by
  unfold rescale; fun_prop

/-- The rescale is monotone for `L ≤ 0 ≤ R`. -/
theorem monotone_rescale {L R : ℝ} (hL : L ≤ 0) (hR : 0 ≤ R) :
    Monotone (rescale L R) := by
  intro x y hxy
  unfold rescale
  have h1 : min x 0 ≤ min y 0 := min_le_min hxy le_rfl
  have h2 : max x 0 ≤ max y 0 := max_le_max hxy le_rfl
  have h3 := mul_le_mul_of_nonneg_left h1 (neg_nonneg.mpr hL)
  have h4 := mul_le_mul_of_nonneg_left h2 hR
  linarith

/-- The rescale is strictly monotone for `L < 0 < R` — with continuity and
the endpoint values this makes `Ξ_t` a homeomorphism `[-1,1]² ≃ R_t`. -/
theorem strictMono_rescale {L R : ℝ} (hL : L < 0) (hR : 0 < R) :
    StrictMono (rescale L R) := by
  intro x y hxy
  unfold rescale
  rcases le_or_gt y 0 with hy | hy
  · have hx : x < 0 := lt_of_lt_of_le hxy hy
    rw [min_eq_left hx.le, min_eq_left hy, max_eq_right hx.le, max_eq_right hy]
    nlinarith
  · rcases le_or_gt x 0 with hx | hx
    · rw [min_eq_left hx, min_eq_right hy.le, max_eq_right hx, max_eq_left hy.le]
      nlinarith
    · rw [min_eq_right hx.le, min_eq_right hy.le, max_eq_left hx.le,
        max_eq_left hy.le]
      nlinarith

/-- The rescale maps `[-1, 1]` into `[L, R]`. -/
theorem rescale_mem_Icc {L R : ℝ} (hL : L ≤ 0) (hR : 0 ≤ R) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : rescale L R x ∈ Set.Icc L R :=
  ⟨by simpa using monotone_rescale hL hR hx.1,
   by simpa using monotone_rescale hL hR hx.2⟩

/-- The rescale maps `[-1, 1]` *onto* `[L, R]` (surjectivity of the
fixed-square normalization onto the moving rectangle). -/
theorem rescale_image_Icc {L R : ℝ} (hL : L ≤ 0) (hR : 0 ≤ R) :
    rescale L R '' Set.Icc (-1 : ℝ) 1 = Set.Icc L R := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact rescale_mem_Icc hL hR hx
  · have h := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1)
      (continuous_rescale_coord L R).continuousOn
    rwa [rescale_neg_one, rescale_one] at h

/-- Uniform bound of the rescale: if both endpoints are within `C` of `0`
then `|rescale L R x| ≤ C·|x|` — with `C = α` this puts the normalized cell
inside the `ℓ¹`-ball of radius `α·(|q.1| + |q.2|)`. -/
theorem abs_rescale_le {L R C x : ℝ} (hCL : -C ≤ L) (hL : L ≤ 0)
    (hR : 0 ≤ R) (hRC : R ≤ C) : |rescale L R x| ≤ C * |x| := by
  unfold rescale
  rcases le_or_gt x 0 with hx | hx
  · rw [min_eq_left hx, max_eq_right hx, mul_zero, add_zero, abs_mul,
      abs_of_nonneg (neg_nonneg.mpr hL)]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg x)
  · rw [min_eq_right hx.le, max_eq_left hx.le, mul_zero, zero_add, abs_mul,
      abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_right hRC (abs_nonneg x)

/-! ### The fixed-square normalization `Ξ_t : [-1,1]² → R_t`
(`def:closing_rect`, R-c) -/

/-- **The fixed-square normalization `Ξ`** (`def:closing_rect`): the
per-coordinate piecewise-affine rescale onto the moving rectangle — the
`u`-factor is `[rectLo (a+m), rectHi a]` (edge `a` carries `+u`, edge `a+m`
carries `−u`), the `v`-factor is `[rectLo (b+m), rectHi b]`. -/
noncomputable def rectRescale (κs κ : ZMod n → ℝ) (m : ℕ) (a b : ZMod n)
    (t : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (rescale (rectLo κs κ (a + m) t) (rectHi κs κ a t) q.1,
   rescale (rectLo κs κ (b + m) t) (rectHi κs κ b t) q.2)

/-- The normalization fixes the center: `Ξ_t 0 = 0` for every `t`. -/
@[simp] lemma rectRescale_zero (κs κ : ZMod n → ℝ) (m : ℕ) (a b : ZMod n)
    (t : ℝ) : rectRescale κs κ m a b t (0, 0) = (0, 0) := by
  simp [rectRescale]

/-- Continuity of a single rescaled factor in `(t, coordinate)` — the
building block of `continuous_rectRescale`. -/
theorem continuous_rescale_factor {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) (e₀ e₁ : ZMod n) :
    Continuous fun x : ↥(Set.Icc (0 : ℝ) 1) × ℝ =>
      rescale (rectLo κs κ e₀ ↑x.1) (rectHi κs κ e₁ ↑x.1) x.2 :=
  continuous_rescale.comp
    ((((continuous_rectLo hκs hκ e₀).comp continuous_fst).prodMk
      ((continuous_rectHi hκs hκ e₁).comp continuous_fst)).prodMk
      continuous_snd)

/-- The normalization is jointly continuous in the homotopy time and the
square coordinate. -/
theorem continuous_rectRescale {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) (m : ℕ) (a b : ZMod n) :
    Continuous fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
      rectRescale κs κ m a b ↑x.1 x.2 := by
  unfold rectRescale
  refine Continuous.prodMk ?_ ?_ <;>
  · exact continuous_rescale.comp (Continuous.prodMk
      (Continuous.prodMk
        (by exact (continuous_rectLo hκs hκ _).comp continuous_fst)
        (by exact (continuous_rectHi hκs hκ _).comp continuous_fst))
      (by fun_prop))

/-- The normalization maps the fixed square into the moving rectangle,
coordinate by coordinate. -/
theorem rectRescale_mem [NeZero n] (hn4 : 4 ≤ n) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) (m : ℕ) (a b : ZMod n)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {q : ℝ × ℝ}
    (hq1 : q.1 ∈ Set.Icc (-1 : ℝ) 1) (hq2 : q.2 ∈ Set.Icc (-1 : ℝ) 1) :
    (rectRescale κs κ m a b t q).1 ∈
        Set.Icc (rectLo κs κ (a + m) t) (rectHi κs κ a t)
      ∧ (rectRescale κs κ m a b t q).2 ∈
        Set.Icc (rectLo κs κ (b + m) t) (rectHi κs κ b t) :=
  ⟨rescale_mem_Icc (rectLo_neg hn4 hκs hκ ht0 ht1 (a + m)).le
    (rectHi_pos hn4 hκs hκ ht0 ht1 a).le hq1,
   rescale_mem_Icc (rectLo_neg hn4 hκs hκ ht0 ht1 (b + m)).le
    (rectHi_pos hn4 hκs hκ ht0 ht1 b).le hq2⟩

/-- The `ℓ¹` bound of the normalization: `‖Ξ_t(q)‖₁ ≤ α·‖q‖₁` with
`α = 2π/n` — the sub-square `‖q‖₁ ≤ ρ·n/(2π)` of the fixed square lands
inside the `ℓ¹`-ball of any radius `ρ`, connecting the rectangle layer to the
landed window continuity of `Φ`. -/
theorem abs_rectRescale_le [NeZero n] (hn4 : 4 ≤ n) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) (m : ℕ) (a b : ZMod n)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (q : ℝ × ℝ) :
    |(rectRescale κs κ m a b t q).1| + |(rectRescale κs κ m a b t q).2|
      ≤ 2 * Real.pi / n * (|q.1| + |q.2|) := by
  have h1 : |(rectRescale κs κ m a b t q).1| ≤ 2 * Real.pi / n * |q.1| :=
    abs_rescale_le (neg_le_rectLo κs κ (a + m) t)
      (rectLo_neg hn4 hκs hκ ht0 ht1 (a + m)).le
      (rectHi_pos hn4 hκs hκ ht0 ht1 a).le (rectHi_le κs κ a t)
  have h2 : |(rectRescale κs κ m a b t q).2| ≤ 2 * Real.pi / n * |q.2| :=
    abs_rescale_le (neg_le_rectLo κs κ (b + m) t)
      (rectLo_neg hn4 hκs hκ ht0 ht1 (b + m)).le
      (rectHi_pos hn4 hκs hκ ht0 ht1 b).le (rectHi_le κs κ b t)
  have := mul_add (2 * Real.pi / n) |q.1| |q.2|
  linarith

/-! ### The rectangle is the natural chart domain (`def:closing_rect`)

Per-edge evaluation of the antisymmetric perturbation on a *nondegenerate*
pair configuration (the four edges `a, a+m, b, b+m` pairwise distinct), and
the wall membership: for `q` in the fixed square every chart value of
`Ξ_t(q)` lies in its closed wall interval `[0, w_j(t)]`. -/

/-- On a nondegenerate configuration, edge `a` carries exactly `α + u`. -/
theorem chartPerturb_apply_fst (m : ℕ) {a b : ZMod n} (z : ℝ × ℝ)
    (ham : a ≠ a + m) (hab : a ≠ b) (habm : a ≠ b + m) :
    chartPerturb m a b z a = 2 * Real.pi / n + z.1 := by
  simp [chartPerturb, ham, hab, habm]

/-- On a nondegenerate configuration, edge `a + m` carries exactly `α − u`. -/
theorem chartPerturb_apply_fst' (m : ℕ) {a b : ZMod n} (z : ℝ × ℝ)
    (ham : a + m ≠ a) (hamb : a + m ≠ b) (hambm : a + m ≠ b + m) :
    chartPerturb m a b z (a + m) = 2 * Real.pi / n - z.1 := by
  simp [chartPerturb, ham, hamb, hambm, sub_eq_add_neg]

/-- On a nondegenerate configuration, edge `b` carries exactly `α + v`. -/
theorem chartPerturb_apply_snd (m : ℕ) {a b : ZMod n} (z : ℝ × ℝ)
    (hba : b ≠ a) (hbam : b ≠ a + m) (hbm : b ≠ b + m) :
    chartPerturb m a b z b = 2 * Real.pi / n + z.2 := by
  simp [chartPerturb, hba, hbam, hbm]

/-- On a nondegenerate configuration, edge `b + m` carries exactly `α − v`. -/
theorem chartPerturb_apply_snd' (m : ℕ) {a b : ZMod n} (z : ℝ × ℝ)
    (hbma : b + m ≠ a) (hbmam : b + m ≠ a + m) (hbm : b + m ≠ b) :
    chartPerturb m a b z (b + m) = 2 * Real.pi / n - z.2 := by
  simp [chartPerturb, hbma, hbmam, hbm, sub_eq_add_neg]

/-- Away from the four perturbed edges the chart value is the base `α`. -/
theorem chartPerturb_apply_of_ne (m : ℕ) {a b j : ZMod n} (z : ℝ × ℝ)
    (hja : j ≠ a) (hjam : j ≠ a + m) (hjb : j ≠ b) (hjbm : j ≠ b + m) :
    chartPerturb m a b z j = 2 * Real.pi / n := by
  simp [chartPerturb, hja, hjam, hjb, hjbm]

/-- **The moving rectangle is the natural chart domain** (`def:closing_rect`):
for a nondegenerate pair configuration (`m ≠ 0` in `ZMod n`, `a ≠ b`,
`a ≠ b + m`, `b ≠ a + m`) and any `q` in the fixed square `[-1,1]²`, every
perturbed chart value of the normalized point `Ξ_t(q)` lies in its closed
wall interval `[0, w_j(t)]` — the four perturbed edges by the choice of the
rectangle endpoints, the free edges because `0 < α ≤ π/2 < w_j(t)`. -/
theorem chartPerturb_rectRescale_mem_wall [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {q : ℝ × ℝ}
    (hq1 : q.1 ∈ Set.Icc (-1 : ℝ) 1) (hq2 : q.2 ∈ Set.Icc (-1 : ℝ) 1)
    (j : ZMod n) :
    chartPerturb m a b (rectRescale κs κ m a b t q) j
      ∈ Set.Icc 0 (wallWidth κs κ j t) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hα0 : 0 < 2 * Real.pi / n := by positivity
  have hα2 := two_pi_div_le_pi_div_two (n := n) hn4
  have haam : a ≠ a + m := fun h => hm0 (left_eq_add.mp h)
  have hbbm : b ≠ b + m := fun h => hm0 (left_eq_add.mp h)
  have hambm : a + (m : ZMod n) ≠ b + m := fun h => hab (add_right_cancel h)
  obtain ⟨⟨hu1, hu2⟩, hv1, hv2⟩ :=
    rectRescale_mem hn4 hκs hκ m a b ht0 ht1 hq1 hq2
  by_cases hja : j = a
  · rw [hja, chartPerturb_apply_fst m _ haam hab habm]
    refine ⟨?_, ?_⟩
    · have := neg_le_rectLo κs κ (a + m) t
      linarith
    · have : rectHi κs κ a t ≤ wallWidth κs κ a t - 2 * Real.pi / n :=
        min_le_left _ _
      linarith
  by_cases hjam : j = a + m
  · rw [hjam, chartPerturb_apply_fst' m _ haam.symm hbam.symm hambm]
    refine ⟨?_, ?_⟩
    · have := rectHi_le κs κ a t
      linarith
    · have : 2 * Real.pi / n - wallWidth κs κ (a + m) t
          ≤ rectLo κs κ (a + m) t := le_max_right _ _
      linarith
  by_cases hjb : j = b
  · rw [hjb, chartPerturb_apply_snd m _ hab.symm hbam hbbm]
    refine ⟨?_, ?_⟩
    · have := neg_le_rectLo κs κ (b + m) t
      linarith
    · have : rectHi κs κ b t ≤ wallWidth κs κ b t - 2 * Real.pi / n :=
        min_le_left _ _
      linarith
  by_cases hjbm : j = b + m
  · rw [hjbm, chartPerturb_apply_snd' m _ habm.symm hambm.symm hbbm.symm]
    refine ⟨?_, ?_⟩
    · have := rectHi_le κs κ b t
      linarith
    · have : 2 * Real.pi / n - wallWidth κs κ (b + m) t
          ≤ rectLo κs κ (b + m) t := le_max_right _ _
      linarith
  · rw [chartPerturb_apply_of_ne m _ hja hjam hjb hjbm]
    have hw := pi_div_two_lt_wallWidth hκs hκ ht0 ht1 j
    exact ⟨hα0.le, by linarith⟩

/-! ### The closed-wall edge-length recovery (`def:closing_rect`, R-d)

Extending `F(t, ·)` to the CLOSED rectangle needs the edge-length recovery on
the closed chart interval `[0, w]` — including the collapse value `s = 0`
(length `0`) and the saturation value `s = w` (length `2/max`), which the
open-interval `chartInv` treats as junk. The chart is strictly monotone on
the *closed* moderate interval (`arcsin` is strictly monotone on the closed
`[-1, 1]`), so a choice-based closed recovery is a genuine two-sided inverse,
and the landed compact-to-Hausdorff engine `continuousOn_inv_family` yields
its joint continuity — no new analytic input is needed. -/

/-- The single-edge chart is strictly increasing on the CLOSED moderate
interval `[0, 2/max]` (for positive `p, q`): the `arcsin` arguments stay in
the closed `[-1, 1]`, where `arcsin` is still strictly monotone. -/
theorem chartMap_strictMonoOn_Icc {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    StrictMonoOn (chartMap p q) (Set.Icc (0 : ℝ) (2 / max p q)) := by
  have hmax : (0 : ℝ) < max p q := lt_of_lt_of_le hp (le_max_left p q)
  have key : ∀ r : ℝ, 0 < r → r ≤ max p q → ∀ w ∈ Set.Icc (0 : ℝ) (2 / max p q),
      r * w / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro r hr hrle w hw
    have h1 : r * w ≤ max p q * w := mul_le_mul_of_nonneg_right hrle hw.1
    have h2 : max p q * w ≤ max p q * (2 / max p q) :=
      mul_le_mul_of_nonneg_left hw.2 hmax.le
    have h3 : max p q * (2 / max p q) = 2 := by field_simp
    constructor
    · nlinarith [hw.1]
    · linarith
  intro x hx y hy hxy
  unfold chartMap
  have h1 : Real.arcsin (p * x / 2) < Real.arcsin (p * y / 2) :=
    Real.strictMonoOn_arcsin (key p hp (le_max_left _ _) x hx)
      (key p hp (le_max_left _ _) y hy)
      (by have := mul_lt_mul_of_pos_left hxy hp; linarith)
  have h2 : Real.arcsin (q * x / 2) < Real.arcsin (q * y / 2) :=
    Real.strictMonoOn_arcsin (key q hq (le_max_right _ _) x hx)
      (key q hq (le_max_right _ _) y hy)
      (by have := mul_lt_mul_of_pos_left hxy hq; linarith)
  exact add_lt_add h1 h2

/-- The achievable closed chart values are exactly `[0, chartWall p q]`
(monotone continuous image of the closed moderate interval; the endpoints
are the collapse value `0` and the saturation value `chartWall`). This is
the bridge from the wall membership `[0, w_j(t)]` of
`chartPerturb_rectRescale_mem_wall` to the domain of the closed recovery. -/
theorem chartMap_image_Icc_eq {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    chartMap p q '' Set.Icc (0 : ℝ) (2 / max p q)
      = Set.Icc (0 : ℝ) (chartWall p q) := by
  have hmax : (0 : ℝ) < max p q := lt_of_lt_of_le hp (le_max_left p q)
  have hD : (0 : ℝ) ≤ 2 / max p q := by positivity
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hmono := (chartMap_strictMonoOn_Icc hp hq).monotoneOn
    constructor
    · have := hmono (Set.left_mem_Icc.mpr hD) hx hx.1
      rwa [chartMap_zero] at this
    · exact hmono hx (Set.right_mem_Icc.mpr hD) hx.2
  · have h := intermediate_value_Icc hD (chartMap_continuous p q).continuousOn
    rwa [chartMap_zero] at h

/-- The closed-wall edge-length recovery `λ̄` of `def:closing_rect`: a choice
of preimage of the chart value in the CLOSED moderate interval `[0, 2/max]`;
total (junk `0` off the achievable interval), no positivity proof arguments.
Strict monotonicity of the closed chart makes it the unique — hence genuine
two-sided — inverse there, agreeing with the open recovery `chartInv` on the
open window (`chartInvIcc_eq_chartInv`). -/
noncomputable def chartInvIcc (p q s : ℝ) : ℝ := by
  classical
  exact if h : s ∈ chartMap p q '' Set.Icc (0 : ℝ) (2 / max p q) then
    h.choose else 0

/-- The closed recovery lands in the closed moderate interval. -/
theorem chartInvIcc_mem {p q s : ℝ}
    (h : s ∈ chartMap p q '' Set.Icc (0 : ℝ) (2 / max p q)) :
    chartInvIcc p q s ∈ Set.Icc (0 : ℝ) (2 / max p q) := by
  classical
  rw [chartInvIcc, dif_pos h]
  exact h.choose_spec.1

/-- Round-trip: the closed recovery is a right inverse of the chart on the
achievable closed interval. -/
theorem chartMap_chartInvIcc {p q s : ℝ}
    (h : s ∈ chartMap p q '' Set.Icc (0 : ℝ) (2 / max p q)) :
    chartMap p q (chartInvIcc p q s) = s := by
  classical
  rw [chartInvIcc, dif_pos h]
  exact h.choose_spec.2

/-- On the OPEN achievable window the closed recovery agrees with the landed
open recovery `chartInv` (both are preimages; the closed chart is injective). -/
theorem chartInvIcc_eq_chartInv {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {s : ℝ}
    (hs : s ∈ chartMap p q '' Set.Ioo (0 : ℝ) (2 / max p q)) :
    chartInvIcc p q s = chartInv hp hq s := by
  have hsIcc : s ∈ chartMap p q '' Set.Icc (0 : ℝ) (2 / max p q) :=
    Set.image_mono Set.Ioo_subset_Icc_self hs
  refine (chartMap_strictMonoOn_Icc hp hq).injOn (chartInvIcc_mem hsIcc)
    (Set.Ioo_subset_Icc_self (chartInv_mem hp hq hs)) ?_
  rw [chartMap_chartInvIcc hsIcc, chartMap_chartInv hp hq hs]

/-- **Joint continuity of the closed-wall edge-length recovery over a compact
curvature family** (`def:closing_rect`, R-d): for continuous positive
curvature families `p q : T → ℝ` on a compact Hausdorff `T`, the closed
recovery `(τ, s) ↦ chartInvIcc (p τ) (q τ) s` is jointly continuous on the
pairs whose value is achieved in the CLOSED moderate interval — i.e. on the
full closed chart intervals `[0, chartWall]`, saturation and collapse faces
included. Same normalization + compact-to-Hausdorff route as the landed
`continuousOn_chartInv_family`, with window `[c, d] = [0, 1]` (admissible
because the closed chart is strictly monotone, `chartMap_strictMonoOn_Icc`). -/
theorem continuousOn_chartInvIcc_family {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [T2Space T] {p q : T → ℝ} (hp : ∀ τ, 0 < p τ)
    (hq : ∀ τ, 0 < q τ) (hpc : Continuous p) (hqc : Continuous q) :
    ContinuousOn (fun x : T × ℝ => chartInvIcc (p x.1) (q x.1) x.2)
      {x : T × ℝ | x.2 ∈ chartMap (p x.1) (q x.1) ''
        Set.Icc (0 : ℝ) (2 / max (p x.1) (q x.1))} := by
  have hmax : ∀ τ, 0 < max (p τ) (q τ) := fun τ =>
    lt_of_lt_of_le (hp τ) (le_max_left _ _)
  have hone : ∀ τ : T, 2 / max (p τ) (q τ) * (max (p τ) (q τ) / 2) = 1 := by
    intro τ
    rw [div_mul_div_comm, mul_comm (max (p τ) (q τ)) 2,
      div_self (mul_ne_zero two_ne_zero (hmax τ).ne')]
  have hone' : ∀ τ : T, max (p τ) (q τ) / 2 * (2 / max (p τ) (q τ)) = 1 := by
    intro τ
    rw [div_mul_div_comm, mul_comm 2 (max (p τ) (q τ)),
      div_self (mul_ne_zero (hmax τ).ne' two_ne_zero)]
  set g : T → ℝ → ℝ :=
    fun τ y => chartMap (p τ) (q τ) (y * (2 / max (p τ) (q τ))) with hg
  set inv : T → ℝ → ℝ :=
    fun τ s => chartInvIcc (p τ) (q τ) s * (max (p τ) (q τ) / 2) with hinv
  -- the normalized closed window maps into the closed moderate interval
  have hscale : ∀ τ, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      y * (2 / max (p τ) (q τ)) ∈ Set.Icc (0 : ℝ) (2 / max (p τ) (q τ)) := by
    intro τ y hy
    have h2 : (0 : ℝ) < 2 / max (p τ) (q τ) := div_pos two_pos (hmax τ)
    refine ⟨mul_nonneg hy.1 h2.le, ?_⟩
    calc y * (2 / max (p τ) (q τ)) ≤ 1 * (2 / max (p τ) (q τ)) :=
          mul_le_mul_of_nonneg_right hy.2 h2.le
      _ = 2 / max (p τ) (q τ) := one_mul _
  -- joint continuity of the normalized family
  have hgc : Continuous fun x : T × ℝ => g x.1 x.2 := by
    have hinner : Continuous fun x : T × ℝ => x.2 * (2 / max (p x.1) (q x.1)) :=
      continuous_snd.mul (continuous_const.div
        ((hpc.max hqc).comp continuous_fst) fun x => (hmax x.1).ne')
    simp only [hg, chartMap]
    exact (Real.continuous_arcsin.comp
        (((hpc.comp continuous_fst).mul hinner).div_const 2)).add
      (Real.continuous_arcsin.comp
        (((hqc.comp continuous_fst).mul hinner).div_const 2))
  -- injectivity on the normalized closed window
  have hinj : ∀ τ, Set.InjOn (g τ) (Set.Icc (0 : ℝ) 1) := by
    intro τ y₁ h₁ y₂ h₂ hEq
    simp only [hg] at hEq
    have := (chartMap_strictMonoOn_Icc (hp τ) (hq τ)).injOn
      (hscale τ y₁ h₁) (hscale τ y₂ h₂) hEq
    exact mul_right_cancel₀ (div_pos two_pos (hmax τ)).ne' this
  -- the normalized value set is the closed achievable interval
  have hset : ∀ τ : T, g τ '' Set.Icc (0 : ℝ) 1
      = chartMap (p τ) (q τ) ''
          Set.Icc (0 : ℝ) (2 / max (p τ) (q τ)) := by
    intro τ
    have himg : (fun y : ℝ => y * (2 / max (p τ) (q τ))) '' Set.Icc (0 : ℝ) 1
        = Set.Icc (0 * (2 / max (p τ) (q τ))) (1 * (2 / max (p τ) (q τ))) :=
      Set.image_mul_right_Icc zero_le_one (div_pos two_pos (hmax τ)).le
    calc g τ '' Set.Icc (0 : ℝ) 1
        = chartMap (p τ) (q τ) ''
            ((fun y : ℝ => y * (2 / max (p τ) (q τ))) '' Set.Icc (0 : ℝ) 1) := by
          rw [Set.image_image]
      _ = _ := by rw [himg, zero_mul, one_mul]
  -- the normalized closed recovery is a two-sided inverse on the value set
  have hinv1 : ∀ τ s, s ∈ g τ '' Set.Icc (0 : ℝ) 1 → g τ (inv τ s) = s := by
    intro τ s hs
    rw [hset τ] at hs
    simp only [hg, hinv]
    rw [mul_assoc, hone' τ, mul_one]
    exact chartMap_chartInvIcc hs
  have hinv2 : ∀ τ s, s ∈ g τ '' Set.Icc (0 : ℝ) 1 →
      inv τ s ∈ Set.Icc (0 : ℝ) 1 := by
    intro τ s hs
    rw [hset τ] at hs
    obtain ⟨h1, h2⟩ := chartInvIcc_mem hs
    simp only [hinv]
    have hhalf : (0 : ℝ) < max (p τ) (q τ) / 2 := div_pos (hmax τ) two_pos
    refine ⟨mul_nonneg h1 hhalf.le, ?_⟩
    calc chartInvIcc (p τ) (q τ) s * (max (p τ) (q τ) / 2)
        ≤ 2 / max (p τ) (q τ) * (max (p τ) (q τ) / 2) :=
          mul_le_mul_of_nonneg_right h2 hhalf.le
      _ = 1 := hone τ
  have hmain := continuousOn_inv_family (g := g) (a := 0) (b := 1)
    hgc hinj hinv1 hinv2
  -- back to the original scale
  have hfactor : Continuous fun x : T × ℝ => 2 / max (p x.1) (q x.1) :=
    continuous_const.div ((hpc.max hqc).comp continuous_fst)
      fun x => (hmax x.1).ne'
  have hfinal : ContinuousOn (fun x : T × ℝ => chartInvIcc (p x.1) (q x.1) x.2)
      {x : T × ℝ | x.2 ∈ g x.1 '' Set.Icc (0 : ℝ) 1} := by
    refine (hmain.mul hfactor.continuousOn).congr fun x _ => ?_
    simp only [hinv, Pi.mul_apply]
    rw [mul_assoc, hone' x.1, mul_one]
  have hsets : {x : T × ℝ | x.2 ∈ chartMap (p x.1) (q x.1) ''
        Set.Icc (0 : ℝ) (2 / max (p x.1) (q x.1))}
      = {x : T × ℝ | x.2 ∈ g x.1 '' Set.Icc (0 : ℝ) 1} := by
    ext x
    simp only [Set.mem_setOf_eq, hset x.1]
  rw [hsets]
  exact hfinal

/-! ### The closed-rectangle 2-cell and the fixed-square gap map `H`
(`def:closing_rect`) -/

/-- **The closed-rectangle 2-cell `Φ̄`** (`def:closing_rect`): the closing
2-cell extended to the CLOSED walls via the closed-wall recovery
`chartInvIcc`; total in all arguments (no positivity/time proofs needed).
Agrees with the landed `closingCell` wherever the chart values are achieved
in the open moderate window (`closingCellIcc_eq_closingCell`). -/
noncomputable def closingCellIcc (m : ℕ) (a b : ZMod n) (κs κ : ZMod n → ℝ)
    (t : ℝ) (z : ℝ × ℝ) : ZMod n → ℝ := fun j =>
  chartInvIcc (curvPath κs κ t j) (curvPath κs κ t (j + 1))
    (chartPerturb m a b z j)

/-- On the open achievable window the closed-rectangle 2-cell agrees with the
landed open 2-cell `Φ` — zeros of the fixed-square gap map in the open cell
are zeros of the landed gap map `F`. -/
theorem closingCellIcc_eq_closingCell (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {z : ℝ × ℝ}
    (hmem : ∀ j : ZMod n, chartPerturb m a b z j ∈
      chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
        Set.Ioo (0 : ℝ)
          (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) :
    closingCellIcc m a b κs κ t z = closingCell m a b hκs hκ ht0 ht1 z := by
  funext j
  exact chartInvIcc_eq_chartInv (curvPath_pos hκs hκ ht0 ht1 j)
    (curvPath_pos hκs hκ ht0 ht1 (j + 1)) (hmem j)

/-- **The fixed-square gap map `H`** (`def:closing_rect`):
`H(t, q) = F̄(t, Ξ_t(q))` — the closure gap of the closed-rectangle 2-cell at
the normalized point. Total; continuous on `[0,1] × [-1,1]²`
(`continuousOn_closingRectGap`); agrees with the landed open gap map `F`
wherever the chart values stay in the open window
(`closingRectGap_eq_closingGap`) — in particular at the center
(`closingRectGap_center`). The in-tree fixed-domain winding engine applies
to `H` on the fixed square. -/
noncomputable def closingRectGap (m : ℕ) (a b : ZMod n) (κs κ : ZMod n → ℝ)
    (t : ℝ) (q : ℝ × ℝ) : ℂ :=
  closureGap (curvPath κs κ t)
    (closingCellIcc m a b κs κ t (rectRescale κs κ m a b t q))

/-- Where the chart values of the normalized point stay in the open window,
the fixed-square gap map is the landed gap map `F` at `Ξ_t(q)`. -/
theorem closingRectGap_eq_closingGap (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {q : ℝ × ℝ}
    (hmem : ∀ j : ZMod n,
      chartPerturb m a b (rectRescale κs κ m a b t q) j ∈
        chartMap (curvPath κs κ t j) (curvPath κs κ t (j + 1)) ''
          Set.Ioo (0 : ℝ)
            (2 / max (curvPath κs κ t j) (curvPath κs κ t (j + 1)))) :
    closingRectGap m a b κs κ t q
      = closingGap m a b hκs hκ ht0 ht1 (rectRescale κs κ m a b t q) := by
  unfold closingRectGap closingGap
  rw [closingCellIcc_eq_closingCell m a b hκs hκ ht0 ht1 hmem]

/-- At the center of the fixed square the fixed-square gap map is the landed
gap map at the center of the 2-cell: `H(t, 0) = F(t, 0)` — the anchor values
(`closingGap_center_eq_zero`, `anchorGap_center_eq_zero`) transfer to `H`. -/
theorem closingRectGap_center [NeZero n] (hn4 : 4 ≤ n) (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    closingRectGap m a b κs κ t (0, 0)
      = closingGap m a b hκs hκ ht0 ht1 (0, 0) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hα0 : 0 < 2 * Real.pi / n := by positivity
  have hα2 := two_pi_div_le_pi_div_two (n := n) hn4
  unfold closingRectGap closingGap
  rw [rectRescale_zero,
    closingCellIcc_eq_closingCell m a b hκs hκ ht0 ht1 fun j => ?_]
  rw [chartPerturb_zero]
  refine chartMap_mem_image (curvPath_pos hκs hκ ht0 ht1 j)
    (curvPath_pos hκs hκ ht0 ht1 (j + 1)) hα0 ?_
  have hw := pi_div_two_lt_chartMap_wall (curvPath_pos hκs hκ ht0 ht1 j)
    (curvPath_pos hκs hκ ht0 ht1 (j + 1))
  linarith

/-- Joint continuity of the closed-rectangle 2-cell at the normalized point,
edge by edge, on the FULL fixed square: the chart value of `Ξ_t(q)` stays in
the closed achievable interval (`chartPerturb_rectRescale_mem_wall` +
`chartMap_image_Icc_eq`), where the closed recovery family is continuous. -/
theorem continuousOn_closingRectCell_apply [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) (j : ZMod n) :
    ContinuousOn (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        closingCellIcc m a b κs κ ↑x.1 (rectRescale κs κ m a b ↑x.1 x.2) j)
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) |
        x.2.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2.2 ∈ Set.Icc (-1 : ℝ) 1} := by
  have hfam := continuousOn_chartInvIcc_family
    (p := fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvPath κs κ (↑τ) j)
    (q := fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvPath κs κ (↑τ) (j + 1))
    (fun τ => curvPath_pos hκs hκ τ.2.1 τ.2.2 j)
    (fun τ => curvPath_pos hκs hκ τ.2.1 τ.2.2 (j + 1))
    ((continuous_curvPath κs κ j).comp continuous_subtype_val)
    ((continuous_curvPath κs κ (j + 1)).comp continuous_subtype_val)
  have hcomp : Continuous fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
      ((x.1, chartPerturb m a b (rectRescale κs κ m a b ↑x.1 x.2) j)
        : ↥(Set.Icc (0 : ℝ) 1) × ℝ) :=
    continuous_fst.prodMk ((continuous_chartPerturb m a b j).comp
      (continuous_rectRescale hκs hκ m a b))
  have hmaps : Set.MapsTo
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        ((x.1, chartPerturb m a b (rectRescale κs κ m a b ↑x.1 x.2) j)
          : ↥(Set.Icc (0 : ℝ) 1) × ℝ))
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) |
        x.2.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2.2 ∈ Set.Icc (-1 : ℝ) 1}
      {x : ↥(Set.Icc (0 : ℝ) 1) × ℝ | x.2 ∈
        chartMap (curvPath κs κ (↑x.1) j) (curvPath κs κ (↑x.1) (j + 1)) ''
          Set.Icc (0 : ℝ)
            (2 / max (curvPath κs κ (↑x.1) j)
              (curvPath κs κ (↑x.1) (j + 1)))} := by
    rintro x ⟨hx1, hx2⟩
    have hwall := chartPerturb_rectRescale_mem_wall hn4 hm0 hab habm hbam
      hκs hκ x.1.2.1 x.1.2.2 hx1 hx2 j
    rw [Set.mem_setOf_eq, chartMap_image_Icc_eq
      (curvPath_pos hκs hκ x.1.2.1 x.1.2.2 j)
      (curvPath_pos hκs hκ x.1.2.1 x.1.2.2 (j + 1))]
    exact hwall
  exact (hfam.comp hcomp.continuousOn hmaps).congr fun x _ => rfl

/-- **Continuity of the fixed-square gap map on the whole fixed square**
(`def:closing_rect`): for a nondegenerate pair configuration,
`(t, q) ↦ H(t, q)` is continuous on `[0,1] × [-1,1]²` — walls included. The
fixed-domain winding engine (`windingNumberC` on `∂[-1,1]²` parametrized
loops) applies to `H` with no moving-domain bookkeeping. -/
theorem continuousOn_closingRectGap [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) :
    ContinuousOn (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        closingRectGap m a b κs κ ↑x.1 x.2)
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) |
        x.2.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2.2 ∈ Set.Icc (-1 : ℝ) 1} := by
  have hpair : ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        ((curvPath κs κ (↑x.1),
          closingCellIcc m a b κs κ (↑x.1) (rectRescale κs κ m a b (↑x.1) x.2)) :
          (ZMod n → ℝ) × (ZMod n → ℝ)))
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) |
        x.2.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2.2 ∈ Set.Icc (-1 : ℝ) 1} := by
    refine ContinuousOn.prodMk ?_ ?_
    · refine Continuous.continuousOn (continuous_pi fun i => ?_)
      exact (continuous_curvPath κs κ i).comp
        (continuous_subtype_val.comp continuous_fst)
    · exact continuousOn_pi.mpr fun j =>
        continuousOn_closingRectCell_apply hn4 hm0 hab habm hbam hκs hκ j
  exact (continuous_closureGap.comp_continuousOn hpair).congr fun x _ => rfl

/-! ### The geometry of the closed faces (`def:closing_rect`)

The closed recovery at the collapse value `s = 0` is the zero length and at
the saturation value `s = chartWall` is the diameter length `2/max`; on the
boundary of the fixed square each face either saturates its `+`-edge or
collapses its `−`-edge (the exact-wall `∂R_t` of
`lem:closure_boundary_exclusion`). -/

/-- The closed recovery of the collapse value is the zero length. -/
theorem chartInvIcc_zero {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    chartInvIcc p q 0 = 0 := by
  have hD : (0 : ℝ) ≤ 2 / max p q := by
    have := lt_of_lt_of_le hp (le_max_left p q); positivity
  have h0 : (0 : ℝ) ∈ chartMap p q '' Set.Icc (0 : ℝ) (2 / max p q) :=
    ⟨0, Set.left_mem_Icc.mpr hD, chartMap_zero p q⟩
  refine (chartMap_strictMonoOn_Icc hp hq).injOn (chartInvIcc_mem h0)
    (Set.left_mem_Icc.mpr hD) ?_
  rw [chartMap_chartInvIcc h0, chartMap_zero]

/-- The closed recovery of the saturation value is the diameter length
`2/max` (the arcsin-saturated edge of `lem:chart_wall`). -/
theorem chartInvIcc_wall {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    chartInvIcc p q (chartWall p q) = 2 / max p q := by
  have hD : (0 : ℝ) ≤ 2 / max p q := by
    have := lt_of_lt_of_le hp (le_max_left p q); positivity
  have hw : chartWall p q ∈ chartMap p q '' Set.Icc (0 : ℝ) (2 / max p q) :=
    ⟨2 / max p q, Set.right_mem_Icc.mpr hD, rfl⟩
  refine (chartMap_strictMonoOn_Icc hp hq).injOn (chartInvIcc_mem hw)
    (Set.right_mem_Icc.mpr hD) ?_
  rw [chartMap_chartInvIcc hw]
  rfl

/-- Boundary-face dichotomy, right `u`-face (`q.1 = 1`): the normalized point
saturates edge `a` (`s = w_a(t)`) or collapses edge `a + m` (`s = 0`). -/
theorem chartPerturb_rectRescale_face_fst_hi [NeZero n] {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) (κs κ : ZMod n → ℝ) (t : ℝ) {q : ℝ × ℝ}
    (hq : q.1 = 1) :
    chartPerturb m a b (rectRescale κs κ m a b t q) a = wallWidth κs κ a t
      ∨ chartPerturb m a b (rectRescale κs κ m a b t q) (a + m) = 0 := by
  have haam : a ≠ a + m := fun h => hm0 (left_eq_add.mp h)
  have hambm : a + (m : ZMod n) ≠ b + m := fun h => hab (add_right_cancel h)
  have hu : (rectRescale κs κ m a b t q).1 = rectHi κs κ a t := by
    simp [rectRescale, hq]
  rcases le_total (wallWidth κs κ a t - 2 * Real.pi / n) (2 * Real.pi / n)
    with h | h
  · left
    rw [chartPerturb_apply_fst m _ haam hab habm, hu, rectHi, min_eq_left h]
    ring
  · right
    rw [chartPerturb_apply_fst' m _ haam.symm hbam.symm hambm, hu, rectHi,
      min_eq_right h]
    ring

/-- Boundary-face dichotomy, left `u`-face (`q.1 = -1`): the normalized point
collapses edge `a` (`s = 0`) or saturates edge `a + m` (`s = w_{a+m}(t)`). -/
theorem chartPerturb_rectRescale_face_fst_lo [NeZero n] {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) (κs κ : ZMod n → ℝ) (t : ℝ) {q : ℝ × ℝ}
    (hq : q.1 = -1) :
    chartPerturb m a b (rectRescale κs κ m a b t q) a = 0
      ∨ chartPerturb m a b (rectRescale κs κ m a b t q) (a + m)
        = wallWidth κs κ (a + m) t := by
  have haam : a ≠ a + m := fun h => hm0 (left_eq_add.mp h)
  have hambm : a + (m : ZMod n) ≠ b + m := fun h => hab (add_right_cancel h)
  have hu : (rectRescale κs κ m a b t q).1 = rectLo κs κ (a + m) t := by
    simp [rectRescale, hq]
  rcases le_total (2 * Real.pi / n - wallWidth κs κ (a + m) t)
    (-(2 * Real.pi / n)) with h | h
  · left
    rw [chartPerturb_apply_fst m _ haam hab habm, hu, rectLo, max_eq_left h]
    ring
  · right
    rw [chartPerturb_apply_fst' m _ haam.symm hbam.symm hambm, hu, rectLo,
      max_eq_right h]
    ring

/-- Boundary-face dichotomy, right `v`-face (`q.2 = 1`): the normalized point
saturates edge `b` (`s = w_b(t)`) or collapses edge `b + m` (`s = 0`). -/
theorem chartPerturb_rectRescale_face_snd_hi [NeZero n] {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) (κs κ : ZMod n → ℝ) (t : ℝ) {q : ℝ × ℝ}
    (hq : q.2 = 1) :
    chartPerturb m a b (rectRescale κs κ m a b t q) b = wallWidth κs κ b t
      ∨ chartPerturb m a b (rectRescale κs κ m a b t q) (b + m) = 0 := by
  have hbbm : b ≠ b + m := fun h => hm0 (left_eq_add.mp h)
  have hambm : a + (m : ZMod n) ≠ b + m := fun h => hab (add_right_cancel h)
  have hv : (rectRescale κs κ m a b t q).2 = rectHi κs κ b t := by
    simp [rectRescale, hq]
  rcases le_total (wallWidth κs κ b t - 2 * Real.pi / n) (2 * Real.pi / n)
    with h | h
  · left
    rw [chartPerturb_apply_snd m _ hab.symm hbam hbbm, hv, rectHi,
      min_eq_left h]
    ring
  · right
    rw [chartPerturb_apply_snd' m _ habm.symm hambm.symm hbbm.symm, hv,
      rectHi, min_eq_right h]
    ring

/-- Boundary-face dichotomy, left `v`-face (`q.2 = -1`): the normalized point
collapses edge `b` (`s = 0`) or saturates edge `b + m` (`s = w_{b+m}(t)`). -/
theorem chartPerturb_rectRescale_face_snd_lo [NeZero n] {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) (κs κ : ZMod n → ℝ) (t : ℝ) {q : ℝ × ℝ}
    (hq : q.2 = -1) :
    chartPerturb m a b (rectRescale κs κ m a b t q) b = 0
      ∨ chartPerturb m a b (rectRescale κs κ m a b t q) (b + m)
        = wallWidth κs κ (b + m) t := by
  have hbbm : b ≠ b + m := fun h => hm0 (left_eq_add.mp h)
  have hambm : a + (m : ZMod n) ≠ b + m := fun h => hab (add_right_cancel h)
  have hv : (rectRescale κs κ m a b t q).2 = rectLo κs κ (b + m) t := by
    simp [rectRescale, hq]
  rcases le_total (2 * Real.pi / n - wallWidth κs κ (b + m) t)
    (-(2 * Real.pi / n)) with h | h
  · left
    rw [chartPerturb_apply_snd m _ hab.symm hbam hbbm, hv, rectLo,
      max_eq_left h]
    ring
  · right
    rw [chartPerturb_apply_snd' m _ habm.symm hambm.symm hbbm.symm, hv,
      rectLo, max_eq_right h]
    ring

/-! ## The winding of the `t = 0` boundary loop (`lem:closure_winding_t0`)

The assembly of the closing rigidity into a winding statement: on a small
Euclidean circle `z(t) = ρ'·(cos 2πt, sin 2πt)` inside both the continuity
window and the rigidity radius, the boundary loop `t ↦ F(0, z(t))` of the
`t = 0` gap map is a pointwise perturbation (of relative size `≤ 1/2`) of the
nonsingular real-linear loop `t ↦ L(z(t)) = ρ'(a·e^{2πit} + b·e^{−2πit})`,
`a = ½(C_a − i C_b)`, `b = ½(C_a + i C_b)`, so Rouché
(`Gluck.windingNumberC_eq_of_perturb`) transfers the linear winding
`sgn(‖a‖ − ‖b‖) = sgn Im(conj C_a · C_b) = ±1`
(`Gluck.windingNumberC_linearLoop`) to `F(0,·)`. -/

/-- **The `t = 0` continuity window of the clean anchor gap.** The `t = 0`
slice of the joint continuity package (`exists_closingCell_window` +
`continuousOn_closingGap` at `κ = κs`): there is `ρw > 0` with
`z ↦ F(0,z) = anchorGap z` continuous on the closed `ℓ¹`-ball of radius `ρw`. -/
theorem exists_anchorGap_continuousOn [NeZero n] (hn4 : 4 ≤ n) (m : ℕ)
    (a b : ZMod n) {κs : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) :
    ∃ ρw : ℝ, 0 < ρw ∧
      ContinuousOn (anchorGap m a b hκs)
        {z : ℝ × ℝ | |z.1| + |z.2| ≤ ρw} := by
  obtain ⟨ρ, c, d, hρ0, _hρ2πn, hc0, hcd, hd1, hwin⟩ :=
    exists_closingCell_window hn4 m hκs hκs
  have hcont := continuousOn_closingGap m a b hκs hκs hc0 hcd hd1
    (Z := {z : ℝ × ℝ | |z.1| + |z.2| ≤ ρ})
    (fun t ht0 ht1 z hz j => hwin t ht0 ht1 z hz a b j)
  refine ⟨ρ, hρ0, ?_⟩
  have hemb : Continuous fun z : ℝ × ℝ =>
      (((⟨0, by norm_num⟩ : ↥(Set.Icc (0 : ℝ) 1)), z) :
        ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ)) :=
    continuous_const.prodMk continuous_id
  have hmaps : Set.MapsTo
      (fun z : ℝ × ℝ =>
        (((⟨0, by norm_num⟩ : ↥(Set.Icc (0 : ℝ) 1)), z) :
          ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ)))
      {z : ℝ × ℝ | |z.1| + |z.2| ≤ ρ}
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) | |x.2.1| + |x.2.2| ≤ ρ} :=
    fun z hz => hz
  have hcomp := hcont.comp hemb.continuousOn hmaps
  refine hcomp.congr fun z _ => ?_
  exact (closingGap_zero_eq_anchorGap m a b hκs hκs _ _ z).symm

/-- **The exposed linear estimate of the `t = 0` rigidity**
(`lem:closure_boundary_rigidity`, quantitative form): at a nondegenerate
half-period-symmetric anchor there are `σ > 0` and a radius `ρr > 0` with the
`σ_min` lower bound `σ(|u| + |v|) ≤ ‖u·C_a + v·C_b‖` and the strict-derivative
remainder bound `‖F(0,z) − (z₁·C_a + z₂·C_b)‖ ≤ (σ/2)·‖z‖` on `‖z‖ ≤ ρr`.
This re-exposes the two internal estimates of `anchorGap_zero_iff` for the
winding assembly (`lem:closure_winding_t0`), where the *pointwise* comparison
`‖F − Lz‖ < ‖Lz‖` on a circle is needed, not just the zero-set conclusion. -/
theorem anchorGap_linear_estimate [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    (hn : n = 2 * m) {a b : ℕ} (ha : a < m) (hb : b < m) {κs : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (hL : ((starRingEnd ℂ) (closingJacobianCol m hκs a)
        * closingJacobianCol m hκs b).im ≠ 0) :
    ∃ σ ρr : ℝ, 0 < σ ∧ 0 < ρr ∧
      (∀ u v : ℝ, σ * (|u| + |v|) ≤
        ‖u • closingJacobianCol m hκs a + v • closingJacobianCol m hκs b‖) ∧
      ∀ z : ℝ × ℝ, ‖z‖ ≤ ρr →
        ‖anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs z
            - (z.1 • closingJacobianCol m hκs a
              + z.2 • closingJacobianCol m hκs b)‖
          ≤ σ / 2 * ‖z‖ := by
  obtain ⟨σ, hσ, hbound⟩ := norm_smul_add_smul_ge hL
  have hd := hasStrictFDerivAt_anchorGap hn4 m ((a : ℕ) : ZMod n)
    ((b : ℕ) : ZMod n) hκs
  rw [anchorGapDeriv_eq hn4 hn ha hb hκs hsym] at hd
  set L : ℝ × ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (closingJacobianCol m hκs a)
      + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (closingJacobianCol m hκs b)
    with hLdef
  have h0 : anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs 0 = 0 :=
    anchorGap_center_eq_zero hn4 hn _ _ hκs hsym
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hd.hasFDerivAt
  have hev : ∀ᶠ z : ℝ × ℝ in nhds 0,
      ‖anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs z - L z‖
        ≤ σ / 2 * ‖z‖ := by
    have hhalf : (0 : ℝ) < σ / 2 := by positivity
    filter_upwards [Asymptotics.isLittleO_iff.mp hlo hhalf] with z hz
    simpa [h0] using hz
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ0, hδ⟩ := hev
  refine ⟨σ, δ / 2, hσ, by positivity, hbound, fun z hz => ?_⟩
  have hsmall := hδ (show dist z 0 < δ by
    rw [dist_zero_right]; linarith)
  have hLz : L z = z.1 • closingJacobianCol m hκs a
      + z.2 • closingJacobianCol m hκs b := by
    simp [hLdef]
  rwa [hLz] at hsmall

/-! ### The linear boundary loop in exponential coordinates
(`lem:closure_winding_t0`, step (a))

The restriction of the real-linear map `L(z) = z₁·C_a + z₂·C_b` to the
Euclidean circle is the model loop `a·e^{iθ} + b·e^{−iθ}` with
`a = ½(C_a − i C_b)`, `b = ½(C_a + i C_b)`, and the determinant identity
`‖a‖² − ‖b‖² = Im(conj C_a · C_b)` decides which exponential term dominates.
Pure `ℂ`-identities — project-local because Mathlib has no topological winding
number and hence no library home for the `z ↦ a z + b z̄` boundary-loop
normal form. -/

/-- The real-linear map `(cos θ, sin θ) ↦ cos θ·C_a + sin θ·C_b` on the unit
circle in exponential coordinates: `a·e^{iθ} + b·e^{−iθ}` with
`a = (C_a − i C_b)/2`, `b = (C_a + i C_b)/2` (Euler substitution). -/
theorem cos_smul_add_sin_smul (Ca Cb : ℂ) (θ : ℝ) :
    (Real.cos θ) • Ca + (Real.sin θ) • Cb
      = (Ca - Complex.I * Cb) / 2 * Complex.exp ((θ : ℂ) * Complex.I)
        + (Ca + Complex.I * Cb) / 2
          * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  simp only [Complex.real_smul, Complex.ofReal_cos, Complex.ofReal_sin]
  linear_combination (Cb * Complex.sin (θ : ℂ)) * Complex.I_sq

/-- Polarization: the norm-square gap of the exponential-coordinate pair is
the pairing determinant, `‖(C_a − i C_b)/2‖² − ‖(C_a + i C_b)/2‖²
= Im(conj C_a · C_b)`. -/
theorem norm_pair_sq_sub (Ca Cb : ℂ) :
    ‖(Ca - Complex.I * Cb) / 2‖ ^ 2 - ‖(Ca + Complex.I * Cb) / 2‖ ^ 2
      = ((starRingEnd ℂ) Ca * Cb).im := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- The forward exponential term dominates iff the pairing determinant is
positive: `‖(C_a + i C_b)/2‖ < ‖(C_a − i C_b)/2‖ ↔ 0 < Im(conj C_a · C_b)`. -/
theorem norm_pair_lt_iff (Ca Cb : ℂ) :
    ‖(Ca + Complex.I * Cb) / 2‖ < ‖(Ca - Complex.I * Cb) / 2‖ ↔
      0 < ((starRingEnd ℂ) Ca * Cb).im := by
  rw [← norm_pair_sq_sub, sub_pos]
  constructor
  · intro h
    nlinarith [norm_nonneg ((Ca + Complex.I * Cb) / 2),
      norm_nonneg ((Ca - Complex.I * Cb) / 2)]
  · intro h
    nlinarith [norm_nonneg ((Ca + Complex.I * Cb) / 2),
      norm_nonneg ((Ca - Complex.I * Cb) / 2)]

/-- Nondegeneracy of the pairing separates the exponential-coordinate norms:
`Im(conj C_a · C_b) ≠ 0 → ‖(C_a − i C_b)/2‖ ≠ ‖(C_a + i C_b)/2‖` — the
hypothesis of `Gluck.windingNumberC_linearLoop` for the linear boundary
loop. -/
theorem norm_pair_ne {Ca Cb : ℂ} (hL : ((starRingEnd ℂ) Ca * Cb).im ≠ 0) :
    ‖(Ca - Complex.I * Cb) / 2‖ ≠ ‖(Ca + Complex.I * Cb) / 2‖ := by
  intro h
  apply hL
  rw [← norm_pair_sq_sub, h, sub_self]

/-! ### The capstone: winding `±1` at `t = 0` (`lem:closure_winding_t0`) -/

/-- **Winding `±1` at `t = 0`** (`lem:closure_winding_t0`): under the
hypotheses of the `t = 0` rigidity (`closingGap_zero_iff`), for every `ρ > 0`
there is a circle radius `0 < ρ' ≤ ρ` such that the boundary loop
`t ↦ F(0, ρ'·(cos 2πt, sin 2πt))` of the `t = 0` gap map is continuous,
nowhere zero, and has winding number `sgn Im(conj C_a · C_b) = ±1` about the
origin.  Rouché (`Gluck.windingNumberC_eq_of_perturb`) against the linear
boundary loop `Gluck.linearLoop (ρ'·(C_a − i C_b)/2) (ρ'·(C_a + i C_b)/2)`,
whose winding is `Gluck.windingNumberC_linearLoop`; the pointwise comparison
`‖F(0,z) − Lz‖ ≤ (σ/2)‖z‖_∞ ≤ (σ/2)(|z₁|+|z₂|) < σ(|z₁|+|z₂|) ≤ ‖Lz‖` comes
from `anchorGap_linear_estimate`. -/
theorem closure_winding_t0 [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {a b : ℕ} (ha : a < m) (hb : b < m) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (hL : ((starRingEnd ℂ) (closingJacobianCol m hκs a)
        * closingJacobianCol m hκs b).im ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) (ht0 : (0 : ℝ) ≤ 0) (ht1 : (0 : ℝ) ≤ 1) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧
      ∃ (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0),
        (∀ t : unitInterval,
          γ t = closingGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs hκ
            ht0 ht1
            (ρ' * Real.cos (2 * Real.pi * t), ρ' * Real.sin (2 * Real.pi * t))) ∧
        windingNumberC γ hγ =
          if 0 < ((starRingEnd ℂ) (closingJacobianCol m hκs a)
              * closingJacobianCol m hκs b).im then 1 else -1 := by
  set Ca := closingJacobianCol m hκs a with hCadef
  set Cb := closingJacobianCol m hκs b with hCbdef
  obtain ⟨ρw, hρw0, hcont⟩ :=
    exists_anchorGap_continuousOn hn4 m ((a : ℕ) : ZMod n)
      ((b : ℕ) : ZMod n) hκs
  obtain ⟨σ, ρr, hσ, hρr, hbound, hrem⟩ :=
    anchorGap_linear_estimate hn4 hn ha hb hκs hsym hL
  refine ⟨min ρ (min (ρw / 2) ρr), lt_min hρ (lt_min (by positivity) hρr),
    min_le_left _ _, ?_⟩
  set ρ' := min ρ (min (ρw / 2) ρr) with hρ'def
  have hρ'0 : 0 < ρ' := lt_min hρ (lt_min (by positivity) hρr)
  have hρ'w : 2 * ρ' ≤ ρw := by
    have h := (min_le_right ρ _).trans (min_le_left (ρw / 2) ρr)
    rw [hρ'def]; linarith
  have hρ'r : ρ' ≤ ρr := (min_le_right ρ _).trans (min_le_right (ρw / 2) ρr)
  -- the Euclidean circle of radius ρ'
  set zc : unitInterval → ℝ × ℝ := fun t =>
    (ρ' * Real.cos (2 * Real.pi * t), ρ' * Real.sin (2 * Real.pi * t))
    with hzcdef
  have habs : ∀ t : unitInterval,
      |(zc t).1| ≤ ρ' ∧ |(zc t).2| ≤ ρ' := by
    intro t
    constructor
    · rw [abs_mul, abs_of_pos hρ'0]
      calc ρ' * |Real.cos (2 * Real.pi * t)| ≤ ρ' * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hρ'0.le
        _ = ρ' := mul_one _
    · rw [abs_mul, abs_of_pos hρ'0]
      calc ρ' * |Real.sin (2 * Real.pi * t)| ≤ ρ' * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hρ'0.le
        _ = ρ' := mul_one _
  have hzℓ1 : ∀ t : unitInterval, |(zc t).1| + |(zc t).2| ≤ ρw := by
    intro t
    have h := habs t
    linarith [h.1, h.2]
  have hzsup : ∀ t : unitInterval, ‖zc t‖ ≤ ρr := by
    intro t
    have h := habs t
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (max_le h.1 h.2).trans hρ'r
  have hzne : ∀ t : unitInterval, (0 : ℝ) < |(zc t).1| + |(zc t).2| := by
    intro t
    by_contra hc
    push Not at hc
    have h1 : |(zc t).1| = 0 :=
      le_antisymm (by linarith [abs_nonneg (zc t).2]) (abs_nonneg _)
    have h2 : |(zc t).2| = 0 :=
      le_antisymm (by linarith [abs_nonneg (zc t).1]) (abs_nonneg _)
    rw [abs_eq_zero] at h1 h2
    have hcos : Real.cos (2 * Real.pi * t) = 0 := by
      have : ρ' * Real.cos (2 * Real.pi * t) = 0 := h1
      exact (mul_eq_zero.mp this).resolve_left hρ'0.ne'
    have hsin : Real.sin (2 * Real.pi * t) = 0 := by
      have : ρ' * Real.sin (2 * Real.pi * t) = 0 := h2
      exact (mul_eq_zero.mp this).resolve_left hρ'0.ne'
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    rw [hsin, hcos] at this
    norm_num at this
  -- the boundary loop `γ`
  have hγc : Continuous fun t : unitInterval =>
      anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs (zc t) := by
    refine hcont.comp_continuous ?_ fun t => hzℓ1 t
    exact (continuous_const.mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_subtype_val))).prodMk
      (continuous_const.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_subtype_val)))
  set γ : C(unitInterval, ℂ) :=
    ⟨fun t => anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs (zc t),
      hγc⟩ with hγdef
  -- the linear boundary loop and its coefficients
  set la : ℂ := (ρ' : ℂ) * ((Ca - Complex.I * Cb) / 2) with hladef
  set lb : ℂ := (ρ' : ℂ) * ((Ca + Complex.I * Cb) / 2) with hlbdef
  have hnρ' : ‖((ρ' : ℝ) : ℂ)‖ = ρ' := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ'0]
  have hlab : ‖la‖ ≠ ‖lb‖ := by
    rw [hladef, hlbdef, norm_mul, norm_mul, hnρ']
    intro h
    exact norm_pair_ne hL (mul_left_cancel₀ hρ'0.ne' h)
  set γL : C(unitInterval, ℂ) := linearLoop la lb with hγLdef
  have hγLne : ∀ t, γL t ≠ 0 := linearLoop_ne_zero la lb hlab
  -- the linear loop is `L` on the circle
  have hγLpt : ∀ t : unitInterval,
      γL t = (zc t).1 • Ca + (zc t).2 • Cb := by
    intro t
    rw [hγLdef, linearLoop_apply]
    have hpair := cos_smul_add_sin_smul Ca Cb (2 * Real.pi * (t : ℝ))
    simp only [hzcdef, Complex.real_smul] at hpair ⊢
    push_cast at hpair ⊢
    rw [hladef, hlbdef]
    linear_combination (-((ρ' : ℝ) : ℂ)) * hpair
  -- the pointwise Rouché comparison on the circle
  have hpert : ∀ t : unitInterval, ‖γ t - γL t‖ < ‖γL t‖ := by
    intro t
    have hz := hrem (zc t) (hzsup t)
    have hlow : σ * (|(zc t).1| + |(zc t).2|) ≤ ‖γL t‖ := by
      rw [hγLpt t]; exact hbound _ _
    have hsuple : ‖zc t‖ ≤ |(zc t).1| + |(zc t).2| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _))
        (le_add_of_nonneg_left (abs_nonneg _))
    have hγt : γ t = anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs
        (zc t) := rfl
    calc ‖γ t - γL t‖
        = ‖anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs (zc t)
            - ((zc t).1 • Ca + (zc t).2 • Cb)‖ := by rw [hγt, hγLpt t]
      _ ≤ σ / 2 * ‖zc t‖ := hz
      _ ≤ σ / 2 * (|(zc t).1| + |(zc t).2|) :=
          mul_le_mul_of_nonneg_left hsuple (by positivity)
      _ < σ * (|(zc t).1| + |(zc t).2|) := by nlinarith [hzne t]
      _ ≤ ‖γL t‖ := hlow
  -- `γ` is nowhere zero
  have hγne : ∀ t, γ t ≠ 0 := by
    intro t h
    have hp := hpert t
    rw [h, zero_sub, norm_neg] at hp
    exact lt_irrefl _ hp
  -- `γ` is a loop
  have hγloop : γ 0 = γ 1 := by
    change anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs (zc 0)
      = anchorGap m ((a : ℕ) : ZMod n) ((b : ℕ) : ZMod n) hκs (zc 1)
    congr 1
    simp only [hzcdef, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one,
      Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi]
  -- Rouché transfer + the linear winding value
  have heq := windingNumberC_eq_of_perturb γL γ hγLne hγne
    (linearLoop_loop la lb) hγloop hpert
  have hval := windingNumberC_linearLoop la lb hlab
  refine ⟨γ, hγne, fun t => ?_, ?_⟩
  · rw [closingGap_zero_eq_anchorGap]
    rfl
  · rw [← heq]
    have hcond : (‖lb‖ < ‖la‖) ↔ (0 < ((starRingEnd ℂ) Ca * Cb).im) := by
      rw [hladef, hlbdef, norm_mul, norm_mul, hnρ']
      constructor
      · intro h
        exact (norm_pair_lt_iff Ca Cb).mp (lt_of_mul_lt_mul_left h hρ'0.le)
      · intro h
        exact mul_lt_mul_of_pos_left ((norm_pair_lt_iff Ca Cb).mpr h) hρ'0
    calc windingNumberC γL hγLne
        = if ‖lb‖ < ‖la‖ then (1 : ℝ) else -1 := hval
      _ = if 0 < ((starRingEnd ℂ) Ca * Cb).im then (1 : ℝ) else -1 := by
          simp only [hcond]

/-! ## The a priori trimmed-box endgame (`Gluck_Discrete_Closing.tex`, @089)

The surviving exclusion architecture moves the degree argument from the exact
wall `∂R_t` (REFUTED: genuine collapse-side wall zeros) to a *trimmed* box
whose faces sit strictly inside the moderate domain. This section builds, in
order: the collapse-only-walls fact for `n ≥ 8` (`lem:collapse_only_walls`),
the trimmed endpoint functions and the trimmed rescaling / gap map
(`def:trimmed_rect`), and the conditional `t = 0` winding transfer
(`lem:trimmed_winding_t0`). -/

/-! ### Collapse-only walls for `n ≥ 8` (`lem:collapse_only_walls`)

For `n ≥ 8` the base chart value `2α = 4π/n ≤ π/2 < w_k(t)`, so on the natural
rectangle the saturation candidates `w_k(t) − α` never bind: all four interval
endpoints of `R_t` equal `±α`. -/

/-- `4π/n ≤ π/2` for `n ≥ 8`: twice the base chart value clears `π/2`, so every
wall (`> π/2`) strictly exceeds `2α`. This is the `n ≥ 8` sharpening of
`two_pi_div_le_pi_div_two`. -/
private theorem four_pi_div_le_pi_div_two [NeZero n] (hn8 : 8 ≤ n) :
    4 * Real.pi / n ≤ Real.pi / 2 := by
  have hn8' : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hπn8 : Real.pi / n ≤ Real.pi / 8 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hn8'
  rw [mul_div_assoc]
  linarith

/-- **Collapse-only walls for `n ≥ 8`** (`lem:collapse_only_walls`): both
interval endpoints of every natural-rectangle factor equal `±α`
(`α = 2π/n`) — the saturation candidates `w_k(t) − α` never bind because
`w_k(t) > π/2 ≥ 4π/n = 2α`. Hence every face of `R_t` (and of any trimmed
sub-box with saturation margin `d = 0`) is a collapse face. -/
theorem rect_walls_collapse_of_eight_le [NeZero n] (hn8 : 8 ≤ n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (e : ZMod n) :
    rectLo κs κ e t = -(2 * Real.pi / n) ∧ rectHi κs κ e t = 2 * Real.pi / n := by
  have h4 := four_pi_div_le_pi_div_two (n := n) hn8
  have hα : (4 : ℝ) * Real.pi / n = 2 * (2 * Real.pi / n) := by ring
  rw [hα] at h4
  have hw := pi_div_two_lt_wallWidth hκs hκ ht0 ht1 e
  constructor
  · rw [rectLo, max_eq_left]
    linarith
  · rw [rectHi, min_eq_right]
    linarith

/-! ### The trimmed rectangle endpoints (`def:trimmed_rect`)

For collapse margin `ε ≥ 0` (edge-length units) and saturation margin `d ≥ 0`
(chart units), the trimmed rectangle moves each interval endpoint of the
natural rectangle `R_t` inward so every perturbed slot `k` stays in
`[τ_{t,k}(ε), w_k(t) − d]`. The collapse chart margin of edge `e` at time `t`
is `τ_{t,e}(ε) = chartMap (κ_t e) (κ_t (e+1)) ε` (`chartMargin`). -/

/-- The collapse chart margin `τ_{t,e}(ε) = chartMap (κ_t e)(κ_t (e+1)) ε`: the
chart value of an edge of length `ε` at homotopy time `t`. -/
noncomputable def chartMargin (κs κ : ZMod n → ℝ) (e : ZMod n) (t ε : ℝ) : ℝ :=
  chartMap (curvPath κs κ t e) (curvPath κs κ t (e + 1)) ε

@[simp] lemma chartMargin_zero (κs κ : ZMod n → ℝ) (e : ZMod n) (t : ℝ) :
    chartMargin κs κ e t 0 = 0 := by simp [chartMargin]

/-- The collapse chart margin is nonnegative for `ε ≥ 0` (both curvatures are
positive, so both `arcsin` summands are nonnegative). -/
private theorem chartMargin_nonneg {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (e : ZMod n)
    {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ chartMargin κs κ e t ε := by
  have hp := curvPath_pos hκs hκ ht0 ht1 e
  have hq := curvPath_pos hκs hκ ht0 ht1 (e + 1)
  unfold chartMargin chartMap
  have h1 : 0 ≤ Real.arcsin (curvPath κs κ t e * ε / 2) :=
    Real.arcsin_nonneg.mpr (by positivity)
  have h2 : 0 ≤ Real.arcsin (curvPath κs κ t (e + 1) * ε / 2) :=
    Real.arcsin_nonneg.mpr (by positivity)
  linarith

/-- The collapse chart margin is continuous in the homotopy time. -/
private theorem continuous_chartMargin {κs κ : ZMod n → ℝ} (e : ZMod n) (ε : ℝ) :
    Continuous fun τ : ↥(Set.Icc (0 : ℝ) 1) => chartMargin κs κ e ↑τ ε := by
  unfold chartMargin chartMap
  have hc1 : Continuous fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvPath κs κ (↑τ) e :=
    (continuous_curvPath κs κ e).comp continuous_subtype_val
  have hc2 : Continuous fun τ : ↥(Set.Icc (0 : ℝ) 1) =>
      curvPath κs κ (↑τ) (e + 1) :=
    (continuous_curvPath κs κ (e + 1)).comp continuous_subtype_val
  exact (Real.continuous_arcsin.comp ((hc1.mul continuous_const).div_const 2)).add
    (Real.continuous_arcsin.comp ((hc2.mul continuous_const).div_const 2))

/-- The trimmed left endpoint of the factor with `+`-signed edge `eplus` and
`−`-signed edge `eminus`: `max (τ_{t,eplus}(ε) − α, α − w_{eminus}(t) + d)`
(collapse of `eplus` trimmed by `ε`, saturation of `eminus` trimmed by `d`).
Indexed by the edge *pair*, so no `n = 2m` identity is needed to name the
partner. -/
noncomputable def trimLo (κs κ : ZMod n → ℝ) (eplus eminus : ZMod n)
    (t ε d : ℝ) : ℝ :=
  max (chartMargin κs κ eplus t ε - 2 * Real.pi / n)
      (2 * Real.pi / n - wallWidth κs κ eminus t + d)

/-- The trimmed right endpoint of the factor with `+`-signed edge `eplus` and
`−`-signed edge `eminus`: `min (α − τ_{t,eminus}(ε), w_{eplus}(t) − α − d)`
(collapse of `eminus` trimmed by `ε`, saturation of `eplus` trimmed by `d`). -/
noncomputable def trimHi (κs κ : ZMod n → ℝ) (eplus eminus : ZMod n)
    (t ε d : ℝ) : ℝ :=
  min (2 * Real.pi / n - chartMargin κs κ eminus t ε)
      (wallWidth κs κ eplus t - 2 * Real.pi / n - d)

/-- The trimmed box is a sub-box of the natural rectangle: for `ε, d ≥ 0` the
trimmed left endpoint sits to the right of the natural `rectLo eminus`. -/
private theorem rectLo_le_trimLo {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (eplus eminus : ZMod n) {ε d : ℝ} (hε : 0 ≤ ε) (hd : 0 ≤ d) :
    rectLo κs κ eminus t ≤ trimLo κs κ eplus eminus t ε d := by
  unfold rectLo trimLo
  refine max_le_max ?_ ?_
  · have := chartMargin_nonneg hκs hκ ht0 ht1 eplus hε; linarith
  · linarith

/-- The trimmed box is a sub-box of the natural rectangle: for `ε, d ≥ 0` the
trimmed right endpoint sits to the left of the natural `rectHi eplus`. -/
private theorem trimHi_le_rectHi {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (eplus eminus : ZMod n) {ε d : ℝ} (hε : 0 ≤ ε) (hd : 0 ≤ d) :
    trimHi κs κ eplus eminus t ε d ≤ rectHi κs κ eplus t := by
  unfold rectHi trimHi
  refine le_min ?_ ?_
  · exact (min_le_right _ _).trans (by linarith)
  · refine (min_le_left _ _).trans ?_
    have := chartMargin_nonneg hκs hκ ht0 ht1 eminus hε; linarith

/-- The trimmed left endpoint is continuous in the homotopy time. -/
private theorem continuous_trimLo {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) (eplus eminus : ZMod n) (ε d : ℝ) :
    Continuous fun τ : ↥(Set.Icc (0 : ℝ) 1) => trimLo κs κ eplus eminus ↑τ ε d := by
  unfold trimLo
  exact ((continuous_chartMargin eplus ε).sub continuous_const).max
    ((continuous_const.sub (continuous_wallWidth hκs hκ eminus)).add continuous_const)

/-- The trimmed right endpoint is continuous in the homotopy time. -/
private theorem continuous_trimHi {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) (eplus eminus : ZMod n) (ε d : ℝ) :
    Continuous fun τ : ↥(Set.Icc (0 : ℝ) 1) => trimHi κs κ eplus eminus ↑τ ε d := by
  unfold trimHi
  exact (continuous_const.sub (continuous_chartMargin eminus ε)).min
    (((continuous_wallWidth hκs hκ eplus).sub continuous_const).sub continuous_const)

/-! ### The trimmed rescaling `Ξ^tr_t : [-1,1]² → R^tr_t` (`def:trimmed_rect`)

Verbatim the landed `rectRescale` / `closingRectGap` fixed-square layer with
the four endpoint functions replaced by their trimmed versions. The trimmed
box being a sub-box of the natural rectangle transfers wall membership (hence
continuity of the gap map) once the margins are *admissible* — the trimmed
endpoints straddle `0`. -/

/-- **Admissibility of the trimmed margins at time `t`** (`def:trimmed_rect`):
each trimmed factor contains `0` (both endpoints on the correct side). This is
the pointwise hypothesis under which `Ξ^tr_t` maps the fixed square into the
trimmed box. -/
def TrimAdm (κs κ : ZMod n → ℝ) (m : ℕ) (a b : ZMod n) (ε d t : ℝ) : Prop :=
  trimLo κs κ a (a + (m : ZMod n)) t ε d ≤ 0 ∧
    0 ≤ trimHi κs κ a (a + (m : ZMod n)) t ε d ∧
    trimLo κs κ b (b + (m : ZMod n)) t ε d ≤ 0 ∧
    0 ≤ trimHi κs κ b (b + (m : ZMod n)) t ε d

/-- **The trimmed fixed-square normalization `Ξ^tr`** (`def:trimmed_rect`): the
per-coordinate piecewise-affine rescale onto the trimmed sub-box — the
`u`-factor is `[trimLo a (a+m), trimHi a (a+m)]` (`+`-edge `a`, `−`-edge
`a+m`), the `v`-factor is `[trimLo b (b+m), trimHi b (b+m)]`. Fixes the
center: `Ξ^tr_t(0) = 0`. -/
noncomputable def trimmedRectRescale (κs κ : ZMod n → ℝ) (m : ℕ) (a b : ZMod n)
    (ε d t : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (rescale (trimLo κs κ a (a + (m : ZMod n)) t ε d)
      (trimHi κs κ a (a + (m : ZMod n)) t ε d) q.1,
   rescale (trimLo κs κ b (b + (m : ZMod n)) t ε d)
      (trimHi κs κ b (b + (m : ZMod n)) t ε d) q.2)

/-- The trimmed normalization fixes the center: `Ξ^tr_t 0 = 0` for every `t`. -/
@[simp] lemma trimmedRectRescale_zero (κs κ : ZMod n → ℝ) (m : ℕ) (a b : ZMod n)
    (ε d t : ℝ) : trimmedRectRescale κs κ m a b ε d t (0, 0) = (0, 0) := by
  simp [trimmedRectRescale]

/-- The trimmed normalization is jointly continuous in the homotopy time and the
square coordinate. -/
theorem continuous_trimmedRectRescale {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) (m : ℕ) (a b : ZMod n) (ε d : ℝ) :
    Continuous fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
      trimmedRectRescale κs κ m a b ε d ↑x.1 x.2 := by
  unfold trimmedRectRescale
  refine Continuous.prodMk ?_ ?_
  · exact continuous_rescale.comp (((((continuous_trimLo hκs hκ
      a (a + (m : ZMod n)) ε d).comp continuous_fst).prodMk
      ((continuous_trimHi hκs hκ a (a + (m : ZMod n)) ε d).comp
        continuous_fst))).prodMk (by fun_prop))
  · exact continuous_rescale.comp (((((continuous_trimLo hκs hκ
      b (b + (m : ZMod n)) ε d).comp continuous_fst).prodMk
      ((continuous_trimHi hκs hκ b (b + (m : ZMod n)) ε d).comp
        continuous_fst))).prodMk (by fun_prop))

/-- Under admissibility the trimmed normalization maps the fixed square into the
trimmed box, coordinate by coordinate. -/
theorem trimmedRectRescale_mem {κs κ : ZMod n → ℝ} (m : ℕ) (a b : ZMod n)
    {ε d t : ℝ} (hadm : TrimAdm κs κ m a b ε d t) {q : ℝ × ℝ}
    (hq1 : q.1 ∈ Set.Icc (-1 : ℝ) 1) (hq2 : q.2 ∈ Set.Icc (-1 : ℝ) 1) :
    (trimmedRectRescale κs κ m a b ε d t q).1 ∈
        Set.Icc (trimLo κs κ a (a + (m : ZMod n)) t ε d)
          (trimHi κs κ a (a + (m : ZMod n)) t ε d)
      ∧ (trimmedRectRescale κs κ m a b ε d t q).2 ∈
        Set.Icc (trimLo κs κ b (b + (m : ZMod n)) t ε d)
          (trimHi κs κ b (b + (m : ZMod n)) t ε d) :=
  ⟨rescale_mem_Icc hadm.1 hadm.2.1 hq1,
   rescale_mem_Icc hadm.2.2.1 hadm.2.2.2 hq2⟩

/-- **The trimmed box is the natural chart domain** (`def:trimmed_rect`): under
admissibility every perturbed chart value of the trimmed normalized point
`Ξ^tr_t(q)` lies in its closed wall interval `[0, w_j(t)]` — the trimmed box
being a sub-box of the natural rectangle, the same endpoint bounds apply. -/
theorem chartPerturb_trimmedRectRescale_mem_wall [NeZero n] (hn4 : 4 ≤ n)
    {m : ℕ} {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b)
    (habm : a ≠ b + m) (hbam : b ≠ a + m) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {ε d t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hadm : TrimAdm κs κ m a b ε d t) {q : ℝ × ℝ}
    (hq1 : q.1 ∈ Set.Icc (-1 : ℝ) 1) (hq2 : q.2 ∈ Set.Icc (-1 : ℝ) 1)
    (j : ZMod n) :
    chartPerturb m a b (trimmedRectRescale κs κ m a b ε d t q) j
      ∈ Set.Icc 0 (wallWidth κs κ j t) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hα0 : 0 < 2 * Real.pi / n := by positivity
  have hα2 := two_pi_div_le_pi_div_two (n := n) hn4
  have haam : a ≠ a + m := fun h => hm0 (left_eq_add.mp h)
  have hbbm : b ≠ b + m := fun h => hm0 (left_eq_add.mp h)
  have hambm : a + (m : ZMod n) ≠ b + m := fun h => hab (add_right_cancel h)
  obtain ⟨⟨hu1, hu2⟩, hv1, hv2⟩ := trimmedRectRescale_mem m a b hadm hq1 hq2
  -- sub-box bounds: trimmed endpoints sit inside the natural rectangle
  have hLoa : -(2 * Real.pi / n) ≤ trimLo κs κ a (a + (m : ZMod n)) t ε d :=
    (neg_le_rectLo κs κ (a + (m : ZMod n)) t).trans
      (rectLo_le_trimLo hκs hκ ht0 ht1 a (a + (m : ZMod n)) hε hd)
  have hLob : -(2 * Real.pi / n) ≤ trimLo κs κ b (b + (m : ZMod n)) t ε d :=
    (neg_le_rectLo κs κ (b + (m : ZMod n)) t).trans
      (rectLo_le_trimLo hκs hκ ht0 ht1 b (b + (m : ZMod n)) hε hd)
  have hLoam : 2 * Real.pi / n - wallWidth κs κ (a + m) t
      ≤ trimLo κs κ a (a + (m : ZMod n)) t ε d :=
    (le_max_right _ _).trans (rectLo_le_trimLo hκs hκ ht0 ht1 a
      (a + (m : ZMod n)) hε hd)
  have hLobm : 2 * Real.pi / n - wallWidth κs κ (b + m) t
      ≤ trimLo κs κ b (b + (m : ZMod n)) t ε d :=
    (le_max_right _ _).trans (rectLo_le_trimLo hκs hκ ht0 ht1 b
      (b + (m : ZMod n)) hε hd)
  have hHiaw : trimHi κs κ a (a + (m : ZMod n)) t ε d
      ≤ wallWidth κs κ a t - 2 * Real.pi / n :=
    (trimHi_le_rectHi hκs hκ ht0 ht1 a (a + (m : ZMod n)) hε hd).trans
      (min_le_left _ _)
  have hHibw : trimHi κs κ b (b + (m : ZMod n)) t ε d
      ≤ wallWidth κs κ b t - 2 * Real.pi / n :=
    (trimHi_le_rectHi hκs hκ ht0 ht1 b (b + (m : ZMod n)) hε hd).trans
      (min_le_left _ _)
  have hHiaα : trimHi κs κ a (a + (m : ZMod n)) t ε d ≤ 2 * Real.pi / n :=
    (trimHi_le_rectHi hκs hκ ht0 ht1 a (a + (m : ZMod n)) hε hd).trans
      (rectHi_le κs κ a t)
  have hHibα : trimHi κs κ b (b + (m : ZMod n)) t ε d ≤ 2 * Real.pi / n :=
    (trimHi_le_rectHi hκs hκ ht0 ht1 b (b + (m : ZMod n)) hε hd).trans
      (rectHi_le κs κ b t)
  by_cases hja : j = a
  · rw [hja, chartPerturb_apply_fst m _ haam hab habm]
    exact ⟨by linarith, by linarith⟩
  by_cases hjam : j = a + m
  · rw [hjam, chartPerturb_apply_fst' m _ haam.symm hbam.symm hambm]
    exact ⟨by linarith, by linarith⟩
  by_cases hjb : j = b
  · rw [hjb, chartPerturb_apply_snd m _ hab.symm hbam hbbm]
    exact ⟨by linarith, by linarith⟩
  by_cases hjbm : j = b + m
  · rw [hjbm, chartPerturb_apply_snd' m _ habm.symm hambm.symm hbbm.symm]
    exact ⟨by linarith, by linarith⟩
  · rw [chartPerturb_apply_of_ne m _ hja hjam hjb hjbm]
    have hw := pi_div_two_lt_wallWidth hκs hκ ht0 ht1 j
    exact ⟨hα0.le, by linarith⟩

/-! ### The trimmed fixed-square gap map `H^tr` (`def:trimmed_rect`) -/

/-- **The trimmed fixed-square gap map `H^tr`** (`def:trimmed_rect`):
`H^tr(t, q) = F̄(t, Ξ^tr_t(q))` — the closure gap of the closed-rectangle
2-cell at the trimmed normalized point. Total; continuous on `[0,1] × [-1,1]²`
for admissible margins (`continuousOn_trimmedRectGap`); agrees at the center
with the landed gap map (`trimmedRectGap_center`). Mirrors `closingRectGap`
with the trimmed normalization. -/
noncomputable def trimmedRectGap (m : ℕ) (a b : ZMod n) (κs κ : ZMod n → ℝ)
    (ε d t : ℝ) (q : ℝ × ℝ) : ℂ :=
  closureGap (curvPath κs κ t)
    (closingCellIcc m a b κs κ t (trimmedRectRescale κs κ m a b ε d t q))

/-- At the center of the fixed square the trimmed gap map is the landed gap map
at the center of the 2-cell: `H^tr(t, 0) = F(t, 0)`. -/
private theorem trimmedRectGap_center [NeZero n] (hn4 : 4 ≤ n) (m : ℕ) (a b : ZMod n)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    {ε d t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    trimmedRectGap m a b κs κ ε d t (0, 0)
      = closingGap m a b hκs hκ ht0 ht1 (0, 0) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hα0 : 0 < 2 * Real.pi / n := by positivity
  have hα2 := two_pi_div_le_pi_div_two (n := n) hn4
  unfold trimmedRectGap closingGap
  rw [trimmedRectRescale_zero,
    closingCellIcc_eq_closingCell m a b hκs hκ ht0 ht1 fun j => ?_]
  rw [chartPerturb_zero]
  refine chartMap_mem_image (curvPath_pos hκs hκ ht0 ht1 j)
    (curvPath_pos hκs hκ ht0 ht1 (j + 1)) hα0 ?_
  have hw := pi_div_two_lt_chartMap_wall (curvPath_pos hκs hκ ht0 ht1 j)
    (curvPath_pos hκs hκ ht0 ht1 (j + 1))
  linarith

/-- Joint continuity of the closed-rectangle 2-cell at the trimmed normalized
point, edge by edge, on the FULL fixed square — the analog of
`continuousOn_closingRectCell_apply`, using the trimmed wall membership. -/
theorem continuousOn_trimmedRectCell_apply [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) {ε d : ℝ} (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hadm : ∀ τ : ↥(Set.Icc (0 : ℝ) 1), TrimAdm κs κ m a b ε d ↑τ) (j : ZMod n) :
    ContinuousOn (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        closingCellIcc m a b κs κ ↑x.1
          (trimmedRectRescale κs κ m a b ε d ↑x.1 x.2) j)
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) |
        x.2.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2.2 ∈ Set.Icc (-1 : ℝ) 1} := by
  have hfam := continuousOn_chartInvIcc_family
    (p := fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvPath κs κ (↑τ) j)
    (q := fun τ : ↥(Set.Icc (0 : ℝ) 1) => curvPath κs κ (↑τ) (j + 1))
    (fun τ => curvPath_pos hκs hκ τ.2.1 τ.2.2 j)
    (fun τ => curvPath_pos hκs hκ τ.2.1 τ.2.2 (j + 1))
    ((continuous_curvPath κs κ j).comp continuous_subtype_val)
    ((continuous_curvPath κs κ (j + 1)).comp continuous_subtype_val)
  have hcomp : Continuous fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
      ((x.1, chartPerturb m a b (trimmedRectRescale κs κ m a b ε d ↑x.1 x.2) j)
        : ↥(Set.Icc (0 : ℝ) 1) × ℝ) :=
    continuous_fst.prodMk ((continuous_chartPerturb m a b j).comp
      (continuous_trimmedRectRescale hκs hκ m a b ε d))
  have hmaps : Set.MapsTo
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        ((x.1, chartPerturb m a b (trimmedRectRescale κs κ m a b ε d ↑x.1 x.2) j)
          : ↥(Set.Icc (0 : ℝ) 1) × ℝ))
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) |
        x.2.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2.2 ∈ Set.Icc (-1 : ℝ) 1}
      {x : ↥(Set.Icc (0 : ℝ) 1) × ℝ | x.2 ∈
        chartMap (curvPath κs κ (↑x.1) j) (curvPath κs κ (↑x.1) (j + 1)) ''
          Set.Icc (0 : ℝ)
            (2 / max (curvPath κs κ (↑x.1) j)
              (curvPath κs κ (↑x.1) (j + 1)))} := by
    rintro x ⟨hx1, hx2⟩
    have hwall := chartPerturb_trimmedRectRescale_mem_wall hn4 hm0 hab habm hbam
      hκs hκ x.1.2.1 x.1.2.2 hε hd (hadm x.1) hx1 hx2 j
    rw [Set.mem_setOf_eq, chartMap_image_Icc_eq
      (curvPath_pos hκs hκ x.1.2.1 x.1.2.2 j)
      (curvPath_pos hκs hκ x.1.2.1 x.1.2.2 (j + 1))]
    exact hwall
  exact (hfam.comp hcomp.continuousOn hmaps).congr fun x _ => rfl

/-- **Continuity of the trimmed fixed-square gap map on the whole fixed square**
(`def:trimmed_rect`): for a nondegenerate pair configuration and admissible
margins, `(t, q) ↦ H^tr(t, q)` is continuous on `[0,1] × [-1,1]²` — walls
included. The analog of `continuousOn_closingRectGap`. -/
theorem continuousOn_trimmedRectGap [NeZero n] (hn4 : 4 ≤ n) {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i)
    (hκ : ∀ i, 0 < κ i) {ε d : ℝ} (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hadm : ∀ τ : ↥(Set.Icc (0 : ℝ) 1), TrimAdm κs κ m a b ε d ↑τ) :
    ContinuousOn (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        trimmedRectGap m a b κs κ ε d ↑x.1 x.2)
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) |
        x.2.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2.2 ∈ Set.Icc (-1 : ℝ) 1} := by
  have hpair : ContinuousOn
      (fun x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) =>
        ((curvPath κs κ (↑x.1),
          closingCellIcc m a b κs κ (↑x.1)
            (trimmedRectRescale κs κ m a b ε d (↑x.1) x.2)) :
          (ZMod n → ℝ) × (ZMod n → ℝ)))
      {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) |
        x.2.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2.2 ∈ Set.Icc (-1 : ℝ) 1} := by
    refine ContinuousOn.prodMk ?_ ?_
    · refine Continuous.continuousOn (continuous_pi fun i => ?_)
      exact (continuous_curvPath κs κ i).comp
        (continuous_subtype_val.comp continuous_fst)
    · exact continuousOn_pi.mpr fun j =>
        continuousOn_trimmedRectCell_apply hn4 hm0 hab habm hbam hκs hκ hε hd
          hadm j
  exact (continuous_closureGap.comp_continuousOn hpair).congr fun x _ => rfl

/-! ### The trimmed boundary-face dichotomy (`def:trimmed_rect`)

On each face of `[-1,1]²` the trimmed normalized point sits AT its trimmed
extreme, reporting which perturbed slot is saturated to `w − d` or collapsed
to the chart margin `τ(ε)`. The trimmed analogs of the four
`chartPerturb_rectRescale_face_*` lemmas: the collapse value `0` becomes the
margin `chartMargin`, the saturation value `w` becomes `w − d`. -/

/-- Trimmed dichotomy, right `u`-face (`q.1 = 1`): edge `a` saturates to
`w_a(t) − d` or edge `a + m` collapses to the margin `τ_{t,a+m}(ε)`. -/
theorem chartPerturb_trimmedRectRescale_face_fst_hi [NeZero n] {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) (κs κ : ZMod n → ℝ) (ε d t : ℝ) {q : ℝ × ℝ}
    (hq : q.1 = 1) :
    chartPerturb m a b (trimmedRectRescale κs κ m a b ε d t q) a
        = wallWidth κs κ a t - d
      ∨ chartPerturb m a b (trimmedRectRescale κs κ m a b ε d t q) (a + m)
        = chartMargin κs κ (a + (m : ZMod n)) t ε := by
  have haam : a ≠ a + m := fun h => hm0 (left_eq_add.mp h)
  have hambm : a + (m : ZMod n) ≠ b + m := fun h => hab (add_right_cancel h)
  have hu : (trimmedRectRescale κs κ m a b ε d t q).1
      = trimHi κs κ a (a + (m : ZMod n)) t ε d := by
    simp [trimmedRectRescale, hq]
  rcases le_total (2 * Real.pi / n - chartMargin κs κ (a + (m : ZMod n)) t ε)
      (wallWidth κs κ a t - 2 * Real.pi / n - d) with h | h
  · right
    rw [chartPerturb_apply_fst' m _ haam.symm hbam.symm hambm, hu, trimHi,
      min_eq_left h]
    ring
  · left
    rw [chartPerturb_apply_fst m _ haam hab habm, hu, trimHi, min_eq_right h]
    ring

/-- Trimmed dichotomy, left `u`-face (`q.1 = -1`): edge `a` collapses to the
margin `τ_{t,a}(ε)` or edge `a + m` saturates to `w_{a+m}(t) − d`. -/
theorem chartPerturb_trimmedRectRescale_face_fst_lo [NeZero n] {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) (κs κ : ZMod n → ℝ) (ε d t : ℝ) {q : ℝ × ℝ}
    (hq : q.1 = -1) :
    chartPerturb m a b (trimmedRectRescale κs κ m a b ε d t q) a
        = chartMargin κs κ a t ε
      ∨ chartPerturb m a b (trimmedRectRescale κs κ m a b ε d t q) (a + m)
        = wallWidth κs κ (a + m) t - d := by
  have haam : a ≠ a + m := fun h => hm0 (left_eq_add.mp h)
  have hambm : a + (m : ZMod n) ≠ b + m := fun h => hab (add_right_cancel h)
  have hu : (trimmedRectRescale κs κ m a b ε d t q).1
      = trimLo κs κ a (a + (m : ZMod n)) t ε d := by
    simp [trimmedRectRescale, hq]
  rcases le_total (chartMargin κs κ a t ε - 2 * Real.pi / n)
      (2 * Real.pi / n - wallWidth κs κ (a + (m : ZMod n)) t + d) with h | h
  · right
    rw [chartPerturb_apply_fst' m _ haam.symm hbam.symm hambm, hu, trimLo,
      max_eq_right h]
    ring
  · left
    rw [chartPerturb_apply_fst m _ haam hab habm, hu, trimLo, max_eq_left h]
    ring

/-- Trimmed dichotomy, right `v`-face (`q.2 = 1`): edge `b` saturates to
`w_b(t) − d` or edge `b + m` collapses to the margin `τ_{t,b+m}(ε)`. -/
theorem chartPerturb_trimmedRectRescale_face_snd_hi [NeZero n] {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) (κs κ : ZMod n → ℝ) (ε d t : ℝ) {q : ℝ × ℝ}
    (hq : q.2 = 1) :
    chartPerturb m a b (trimmedRectRescale κs κ m a b ε d t q) b
        = wallWidth κs κ b t - d
      ∨ chartPerturb m a b (trimmedRectRescale κs κ m a b ε d t q) (b + m)
        = chartMargin κs κ (b + (m : ZMod n)) t ε := by
  have hbbm : b ≠ b + m := fun h => hm0 (left_eq_add.mp h)
  have hambm : a + (m : ZMod n) ≠ b + m := fun h => hab (add_right_cancel h)
  have hv : (trimmedRectRescale κs κ m a b ε d t q).2
      = trimHi κs κ b (b + (m : ZMod n)) t ε d := by
    simp [trimmedRectRescale, hq]
  rcases le_total (2 * Real.pi / n - chartMargin κs κ (b + (m : ZMod n)) t ε)
      (wallWidth κs κ b t - 2 * Real.pi / n - d) with h | h
  · right
    rw [chartPerturb_apply_snd' m _ habm.symm hambm.symm hbbm.symm, hv, trimHi,
      min_eq_left h]
    ring
  · left
    rw [chartPerturb_apply_snd m _ hab.symm hbam hbbm, hv, trimHi, min_eq_right h]
    ring

/-- Trimmed dichotomy, left `v`-face (`q.2 = -1`): edge `b` collapses to the
margin `τ_{t,b}(ε)` or edge `b + m` saturates to `w_{b+m}(t) − d`. -/
theorem chartPerturb_trimmedRectRescale_face_snd_lo [NeZero n] {m : ℕ}
    {a b : ZMod n} (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m)
    (hbam : b ≠ a + m) (κs κ : ZMod n → ℝ) (ε d t : ℝ) {q : ℝ × ℝ}
    (hq : q.2 = -1) :
    chartPerturb m a b (trimmedRectRescale κs κ m a b ε d t q) b
        = chartMargin κs κ b t ε
      ∨ chartPerturb m a b (trimmedRectRescale κs κ m a b ε d t q) (b + m)
        = wallWidth κs κ (b + m) t - d := by
  have hbbm : b ≠ b + m := fun h => hm0 (left_eq_add.mp h)
  have hambm : a + (m : ZMod n) ≠ b + m := fun h => hab (add_right_cancel h)
  have hv : (trimmedRectRescale κs κ m a b ε d t q).2
      = trimLo κs κ b (b + (m : ZMod n)) t ε d := by
    simp [trimmedRectRescale, hq]
  rcases le_total (chartMargin κs κ b t ε - 2 * Real.pi / n)
      (2 * Real.pi / n - wallWidth κs κ (b + (m : ZMod n)) t + d) with h | h
  · right
    rw [chartPerturb_apply_snd' m _ habm.symm hambm.symm hbbm.symm, hv, trimLo,
      max_eq_right h]
    ring
  · left
    rw [chartPerturb_apply_snd m _ hab.symm hbam hbbm, hv, trimLo, max_eq_left h]
    ring

/-! ### The a priori datum (`def:apriori_datum`)

The exclusion architecture packages the two surviving hard leaves as a
predicate on the margins `(ε, d)`: admissibility, boundary exclusion of `H^tr`
over the whole homotopy (property 1), and `t = 0` anchor rigidity on the
trimmed box (property 2). `lem:trimmed_winding_t0` and `lem:closure_persists`
consume such a datum; `lem:closure_boundary_exclusion` and
`lem:closure_window_rigidity` (both HELD) assert one exists. -/

/-- The boundary `∂[-1,1]²` of the fixed square: points in the closed square
with at least one coordinate at `±1`. -/
def squareBoundary : Set (ℝ × ℝ) :=
  {q | q.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ q.2 ∈ Set.Icc (-1 : ℝ) 1 ∧
    (|q.1| = 1 ∨ |q.2| = 1)}

/-- **An a priori datum** (`def:apriori_datum`): a pair of margins `(ε, d)`
with `0 < ε`, `0 ≤ d`, admissible over the whole homotopy, and satisfying the
two surviving hard-leaf properties — (1) *exclusion*: `H^tr(t, q) ≠ 0` for
every `t ∈ [0,1]` and `q ∈ ∂[-1,1]²`; (2) *anchor rigidity*: `H^tr(0, q) ≠ 0`
for every `q ∈ [-1,1]² \ {0}` (equivalently `F(0, z) ≠ 0` on the trimmed box
minus its center, since `Ξ^tr_0` is a bijection fixing `0`). Phrased entirely
via the landed total gap map `trimmedRectGap`. -/
def AprioriDatum (m : ℕ) (a b : ZMod n) (κs κ : ZMod n → ℝ) (ε d : ℝ) : Prop :=
  0 < ε ∧ 0 ≤ d ∧
    (∀ τ : ↥(Set.Icc (0 : ℝ) 1), TrimAdm κs κ m a b ε d ↑τ) ∧
    (∀ τ : ↥(Set.Icc (0 : ℝ) 1), ∀ q ∈ squareBoundary,
      trimmedRectGap m a b κs κ ε d ↑τ q ≠ 0) ∧
    (∀ q : ℝ × ℝ, q.1 ∈ Set.Icc (-1 : ℝ) 1 → q.2 ∈ Set.Icc (-1 : ℝ) 1 →
      q ≠ 0 → trimmedRectGap m a b κs κ ε d 0 q ≠ 0)

/-- Property 1 (exclusion) extracted from an a priori datum. -/
theorem AprioriDatum.exclusion {m : ℕ} {a b : ZMod n} {κs κ : ZMod n → ℝ}
    {ε d : ℝ} (h : AprioriDatum m a b κs κ ε d) :
    ∀ τ : ↥(Set.Icc (0 : ℝ) 1), ∀ q ∈ squareBoundary,
      trimmedRectGap m a b κs κ ε d ↑τ q ≠ 0 := h.2.2.2.1

/-- Property 2 (anchor rigidity) extracted from an a priori datum. -/
theorem AprioriDatum.rigidity {m : ℕ} {a b : ZMod n} {κs κ : ZMod n → ℝ}
    {ε d : ℝ} (h : AprioriDatum m a b κs κ ε d) :
    ∀ q : ℝ × ℝ, q.1 ∈ Set.Icc (-1 : ℝ) 1 → q.2 ∈ Set.Icc (-1 : ℝ) 1 →
      q ≠ 0 → trimmedRectGap m a b κs κ ε d 0 q ≠ 0 := h.2.2.2.2

/-- The admissibility carried by an a priori datum. -/
theorem AprioriDatum.adm {m : ℕ} {a b : ZMod n} {κs κ : ZMod n → ℝ}
    {ε d : ℝ} (h : AprioriDatum m a b κs κ ε d) :
    ∀ τ : ↥(Set.Icc (0 : ℝ) 1), TrimAdm κs κ m a b ε d ↑τ := h.2.2.1

/-! ## Project-local Mathlib supplement — box-radial boundary parametrization
(`def:box_radial_boundary`)

For an axis-aligned box `B = [Lu,Hu]×[Lv,Hv]` with the origin interior
(`Lu < 0 < Hu`, `Lv < 0 < Hv`) we build the Minkowski gauge `g` and the radial
boundary map `boxRadial θ = r(θ)·(cos θ, sin θ) ∈ ∂B`, `r(θ) = 1/g(cos θ,
sin θ)`. The trimmed rectangle `R^tr_0` is such a box once its margins are
admissible; this map is the box-radial boundary loop consumed by
`lem:trimmed_winding_t0` (the ray direction is exactly `(cos θ, sin θ)`, so the
ray homotopy lands on `closure_winding_t0`'s circle loop without a
reparametrization). -/

/-- Per-coordinate gauge of `[L, H]` (`L < 0 < H`): `max (x/H) (x/L)`, equal to
`x/H` for `x ≥ 0` and `x/L` for `x ≤ 0` — both `≥ 0`, vanishing only at `0`. -/
noncomputable def gaugeCoord (L H x : ℝ) : ℝ := max (x / H) (x / L)

/-- The per-coordinate gauge is continuous (division by the constant endpoints,
`max`). -/
lemma continuous_gaugeCoord (L H : ℝ) : Continuous (gaugeCoord L H) :=
  (continuous_id.div_const H).max (continuous_id.div_const L)

/-- Positive homogeneity of the per-coordinate gauge for nonnegative scalars. -/
private lemma gaugeCoord_smul (L H : ℝ) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    gaugeCoord L H (c * x) = c * gaugeCoord L H x := by
  unfold gaugeCoord
  rw [mul_div_assoc, mul_div_assoc, mul_max_of_nonneg _ _ hc]

/-- The per-coordinate gauge is `≥ 0` on the whole line when `L < 0 < H`. -/
private lemma gaugeCoord_nonneg {L H : ℝ} (hL : L < 0) (hH : 0 < H) (x : ℝ) :
    0 ≤ gaugeCoord L H x := by
  rcases le_or_gt 0 x with hx | hx
  · exact le_max_of_le_left (div_nonneg hx hH.le)
  · exact le_max_of_le_right (div_nonneg_of_nonpos hx.le hL.le)

/-- The per-coordinate gauge is `> 0` off the origin when `L < 0 < H`. -/
private lemma gaugeCoord_pos {L H : ℝ} (hL : L < 0) (hH : 0 < H) {x : ℝ} (hx : x ≠ 0) :
    0 < gaugeCoord L H x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · exact lt_max_of_lt_right (div_pos_of_neg_of_neg hx hL)
  · exact lt_max_of_lt_left (div_pos hx hH)

/-- Sub-level set of the per-coordinate gauge: `g(x) ≤ 1 ⟹ x ∈ [L, H]`. -/
private lemma gaugeCoord_le_one_imp_mem {L H : ℝ} (hL : L < 0) (hH : 0 < H) {x : ℝ}
    (hx : gaugeCoord L H x ≤ 1) : x ∈ Set.Icc L H := by
  have h1 : x / H ≤ 1 := (le_max_left _ _).trans hx
  have h2 : x / L ≤ 1 := (le_max_right _ _).trans hx
  refine ⟨?_, (div_le_one hH).mp h1⟩
  have := (div_le_iff_of_neg hL).mp h2
  linarith

/-- On `|x| ≤ 1` the per-coordinate gauge is bounded by `1 / min H (-L)`. -/
private lemma gaugeCoord_le_of_abs_le_one {L H : ℝ} (hL : L < 0) (hH : 0 < H) {x : ℝ}
    (hx : |x| ≤ 1) : gaugeCoord L H x ≤ 1 / min H (-L) := by
  have hmin : 0 < min H (-L) := lt_min hH (by linarith)
  have hnL : (0 : ℝ) < -L := by linarith
  refine max_le ?_ ?_
  · calc x / H ≤ |x| / H := by gcongr; exact le_abs_self x
      _ ≤ 1 / H := by gcongr
      _ ≤ 1 / min H (-L) := one_div_le_one_div_of_le hmin (min_le_left _ _)
  · have hstep : x / L ≤ |x| / (-L) := by
      have h := le_abs_self (x / L)
      rwa [abs_div, abs_of_neg hL] at h
    calc x / L ≤ |x| / (-L) := hstep
      _ ≤ 1 / (-L) := by gcongr
      _ ≤ 1 / min H (-L) := one_div_le_one_div_of_le hmin (min_le_right _ _)

/-- The box gauge (Minkowski functional) of `[Lu,Hu]×[Lv,Hv]`: the max of the
two per-coordinate gauges. -/
noncomputable def boxGauge (Lu Hu Lv Hv : ℝ) (z : ℝ × ℝ) : ℝ :=
  max (gaugeCoord Lu Hu z.1) (gaugeCoord Lv Hv z.2)

/-- The box gauge is continuous. -/
private lemma continuous_boxGauge (Lu Hu Lv Hv : ℝ) :
    Continuous (boxGauge Lu Hu Lv Hv) :=
  ((continuous_gaugeCoord Lu Hu).comp continuous_fst).max
    ((continuous_gaugeCoord Lv Hv).comp continuous_snd)

/-- Positive homogeneity of the box gauge for nonnegative scalars. -/
private lemma boxGauge_smul (Lu Hu Lv Hv : ℝ) {c : ℝ} (hc : 0 ≤ c) (z : ℝ × ℝ) :
    boxGauge Lu Hu Lv Hv (c * z.1, c * z.2) = c * boxGauge Lu Hu Lv Hv z := by
  unfold boxGauge
  simp only [gaugeCoord_smul Lu Hu hc, gaugeCoord_smul Lv Hv hc]
  rw [mul_max_of_nonneg _ _ hc]

/-- The box gauge is `> 0` on the unit circle (`cos θ, sin θ` are never both
zero). -/
private lemma boxGauge_pos_cos_sin {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) (θ : ℝ) :
    0 < boxGauge Lu Hu Lv Hv (Real.cos θ, Real.sin θ) := by
  rcases eq_or_ne (Real.cos θ) 0 with hc | hc
  · have hs : Real.sin θ ≠ 0 := by
      intro hs
      have := Real.sin_sq_add_cos_sq θ
      rw [hs, hc] at this; norm_num at this
    exact lt_of_lt_of_le (gaugeCoord_pos hLv hHv hs) (le_max_right _ _)
  · exact lt_of_lt_of_le (gaugeCoord_pos hLu hHu hc) (le_max_left _ _)

/-- The box gauge on the unit circle is bounded by `1 / ρ_B`, where
`ρ_B = min (min Hu (-Lu)) (min Hv (-Lv))` is the in-radius of the box. -/
private lemma boxGauge_cos_sin_le {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) (θ : ℝ) :
    boxGauge Lu Hu Lv Hv (Real.cos θ, Real.sin θ)
      ≤ 1 / min (min Hu (-Lu)) (min Hv (-Lv)) := by
  have hu := gaugeCoord_le_of_abs_le_one hLu hHu (Real.abs_cos_le_one θ)
  have hv := gaugeCoord_le_of_abs_le_one hLv hHv (Real.abs_sin_le_one θ)
  have hρB : 0 < min (min Hu (-Lu)) (min Hv (-Lv)) :=
    lt_min (lt_min hHu (by linarith)) (lt_min hHv (by linarith))
  refine max_le ?_ ?_
  · exact hu.trans (one_div_le_one_div_of_le hρB (min_le_left _ _))
  · exact hv.trans (one_div_le_one_div_of_le hρB (min_le_right _ _))

/-- The box in-radius `ρ_B := min (min Hu (-Lu)) (min Hv (-Lv))` — the radius of
the largest centered disk inside the box. -/
noncomputable def boxInradius (Lu Hu Lv Hv : ℝ) : ℝ :=
  min (min Hu (-Lu)) (min Hv (-Lv))

/-- The box in-radius is positive when the origin is interior. -/
private lemma boxInradius_pos {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) : 0 < boxInradius Lu Hu Lv Hv :=
  lt_min (lt_min hHu (by linarith)) (lt_min hHv (by linarith))

/-- The box-radial scalar `r(θ) = 1 / g(cos θ, sin θ)`. -/
noncomputable def boxRadialR (Lu Hu Lv Hv θ : ℝ) : ℝ :=
  (boxGauge Lu Hu Lv Hv (Real.cos θ, Real.sin θ))⁻¹

/-- **The box-radial boundary map** (`def:box_radial_boundary`): the angle `θ`
mapped to the unique positive multiple `r(θ)·(cos θ, sin θ)` of the unit
direction lying on `∂([Lu,Hu]×[Lv,Hv])`, `r(θ) = 1/g(cos θ, sin θ)`. -/
noncomputable def boxRadial (Lu Hu Lv Hv θ : ℝ) : ℝ × ℝ :=
  (boxRadialR Lu Hu Lv Hv θ * Real.cos θ, boxRadialR Lu Hu Lv Hv θ * Real.sin θ)

/-- The box-radial scalar is positive. -/
private lemma boxRadialR_pos {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) (θ : ℝ) : 0 < boxRadialR Lu Hu Lv Hv θ :=
  inv_pos.mpr (boxGauge_pos_cos_sin hLu hHu hLv hHv θ)

/-- The box-radial scalar is `≥ ρ_B` — the ray reaches the boundary only past
the in-radius (so the closed disk `D_{ρ'}` for any `ρ' ≤ ρ_B` lies inside the
box). -/
private lemma boxInradius_le_boxRadialR {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) (θ : ℝ) :
    boxInradius Lu Hu Lv Hv ≤ boxRadialR Lu Hu Lv Hv θ := by
  have hρB : 0 < boxInradius Lu Hu Lv Hv := boxInradius_pos hLu hHu hLv hHv
  have hg := boxGauge_cos_sin_le hLu hHu hLv hHv θ
  have hgpos := boxGauge_pos_cos_sin hLu hHu hLv hHv θ
  rw [boxRadialR, boxInradius] at *
  calc min (min Hu (-Lu)) (min Hv (-Lv))
      = (1 / min (min Hu (-Lu)) (min Hv (-Lv)))⁻¹ := by rw [one_div, inv_inv]
    _ ≤ _ := inv_anti₀ hgpos hg

/-- The box-radial map is continuous. -/
theorem continuous_box_radial {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) : Continuous (boxRadial Lu Hu Lv Hv) := by
  have hg : Continuous fun θ =>
      boxGauge Lu Hu Lv Hv (Real.cos θ, Real.sin θ) :=
    (continuous_boxGauge _ _ _ _).comp (Real.continuous_cos.prodMk Real.continuous_sin)
  have hr : Continuous (boxRadialR Lu Hu Lv Hv) :=
    hg.inv₀ fun θ => (boxGauge_pos_cos_sin hLu hHu hLv hHv θ).ne'
  exact (hr.mul Real.continuous_cos).prodMk (hr.mul Real.continuous_sin)

/-- The box-radial map is `2π`-periodic. -/
private lemma boxRadial_periodic (Lu Hu Lv Hv θ : ℝ) :
    boxRadial Lu Hu Lv Hv (θ + 2 * Real.pi) = boxRadial Lu Hu Lv Hv θ := by
  simp only [boxRadial, boxRadialR, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The box gauge of a box-radial point is `1`: the map lands on `∂B`. -/
theorem box_gauge_box_radial {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) (θ : ℝ) :
    boxGauge Lu Hu Lv Hv (boxRadial Lu Hu Lv Hv θ) = 1 := by
  have hgpos := boxGauge_pos_cos_sin hLu hHu hLv hHv θ
  have hrpos := boxRadialR_pos hLu hHu hLv hHv θ
  have hsmul := boxGauge_smul Lu Hu Lv Hv hrpos.le (Real.cos θ, Real.sin θ)
  change boxGauge Lu Hu Lv Hv
      (boxRadialR Lu Hu Lv Hv θ * Real.cos θ,
       boxRadialR Lu Hu Lv Hv θ * Real.sin θ) = 1
  rw [hsmul, boxRadialR, inv_mul_cancel₀ hgpos.ne']

/-- **On boundary**: each coordinate of a box-radial point lies in its factor
interval — `boxRadial θ ∈ [Lu,Hu]×[Lv,Hv]`. -/
private lemma boxRadial_mem {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) (θ : ℝ) :
    (boxRadial Lu Hu Lv Hv θ).1 ∈ Set.Icc Lu Hu ∧
      (boxRadial Lu Hu Lv Hv θ).2 ∈ Set.Icc Lv Hv := by
  have h1 := box_gauge_box_radial hLu hHu hLv hHv θ
  refine ⟨gaugeCoord_le_one_imp_mem hLu hHu ?_,
    gaugeCoord_le_one_imp_mem hLv hHv ?_⟩
  · exact (le_max_left _ _).trans_eq h1
  · exact (le_max_right _ _).trans_eq h1

/-- The Euclidean norm-square of a box-radial point is `r(θ)²`: since
`cos² + sin² = 1`, `‖boxRadial θ‖₂ = r(θ) ≥ ρ_B`. -/
private lemma boxRadial_normSq {Lu Hu Lv Hv : ℝ} (θ : ℝ) :
    (boxRadial Lu Hu Lv Hv θ).1 ^ 2 + (boxRadial Lu Hu Lv Hv θ).2 ^ 2
      = boxRadialR Lu Hu Lv Hv θ ^ 2 := by
  simp only [boxRadial]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith [this]

/-- The box-radial scalar is continuous. -/
private lemma continuous_boxRadialR {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) : Continuous (boxRadialR Lu Hu Lv Hv) := by
  have hg : Continuous fun θ =>
      boxGauge Lu Hu Lv Hv (Real.cos θ, Real.sin θ) :=
    (continuous_boxGauge _ _ _ _).comp
      (Real.continuous_cos.prodMk Real.continuous_sin)
  exact hg.inv₀ fun θ => (boxGauge_pos_cos_sin hLu hHu hLv hHv θ).ne'

/-- A box-radial point is nonzero (positive radius times a unit direction). -/
private lemma boxRadial_ne_zero {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) (θ : ℝ) : boxRadial Lu Hu Lv Hv θ ≠ 0 := by
  intro h
  have hr := boxRadialR_pos hLu hHu hLv hHv θ
  have h1 : boxRadialR Lu Hu Lv Hv θ * Real.cos θ = 0 := congrArg Prod.fst h
  have h2 : boxRadialR Lu Hu Lv Hv θ * Real.sin θ = 0 := congrArg Prod.snd h
  have hcos : Real.cos θ = 0 := (mul_eq_zero.mp h1).resolve_left hr.ne'
  have hsin : Real.sin θ = 0 := (mul_eq_zero.mp h2).resolve_left hr.ne'
  have := Real.sin_sq_add_cos_sq θ
  rw [hcos, hsin] at this; norm_num at this

/-- Segment membership in a factor interval containing `0`: if `L ≤ r·c ≤ H`
(the boundary point) and `0 < lam ≤ r`, then the shrunk point `lam·c` also lies
in `[L, H]` (the interval is `0`-star-shaped). -/
private lemma seg_mem_Icc {L H lam r c : ℝ} (hL0 : L ≤ 0) (hH0 : 0 ≤ H)
    (hlam : 0 < lam) (hlr : lam ≤ r) (hlo : L ≤ r * c) (hhi : r * c ≤ H) :
    L ≤ lam * c ∧ lam * c ≤ H := by
  rcases le_or_gt 0 c with hc | hc
  · exact ⟨le_trans hL0 (mul_nonneg hlam.le hc),
      le_trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hlr) hc]) hhi⟩
  · refine ⟨le_trans hlo ?_, le_trans ?_ hH0⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hlr) (neg_nonneg.mpr hc.le)]
    · nlinarith [mul_pos hlam (neg_pos.mpr hc)]

/-- **Box-radial vs small-circle winding transfer** (core of
`lem:trimmed_winding_t0`): for a gap map `G` that is continuous on a box
`[Lu,Hu]×[Lv,Hv]` with interior origin and nowhere zero off the center, the
box-radial *boundary* loop `s ↦ G(boxRadial(2πs))` and the *small-circle* loop
`s ↦ G(ρ'·(cos 2πs, sin 2πs))` (any `ρ' ≤ ρ_B`) have the *same* winding number
about `0`. The straight-line *ray* homotopy `λ_σ(s)·(cos 2πs, sin 2πs)`,
`λ_σ(s) = (1-σ)r(2πs) + σρ' ∈ [ρ', r(2πs)]`, stays in the box off the center
(`seg_mem_Icc`, `boxRadial_mem`), so `G` is nowhere zero along it; the box-radial
choice makes the ray direction exactly `(cos 2πs, sin 2πs)`, so the `σ = 1` end
is the small-circle loop with *no* reparametrization. Consumes only the public
homotopy invariance `windingNumberC_eq_of_homotopy` (`thm:winding_number_c_homotopy`). -/
lemma boxRadial_winding_eq {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) {G : ℝ × ℝ → ℂ}
    (hGcont : ContinuousOn G
      {z : ℝ × ℝ | z.1 ∈ Set.Icc Lu Hu ∧ z.2 ∈ Set.Icc Lv Hv})
    (hGne : ∀ z : ℝ × ℝ, z.1 ∈ Set.Icc Lu Hu → z.2 ∈ Set.Icc Lv Hv →
      z ≠ 0 → G z ≠ 0)
    {ρ' : ℝ} (hρ'0 : 0 < ρ') (hρ'B : ρ' ≤ boxInradius Lu Hu Lv Hv)
    (γ₀ γ₁ : C(unitInterval, ℂ)) (hγ₀ : ∀ s, γ₀ s ≠ 0) (hγ₁ : ∀ s, γ₁ s ≠ 0)
    (hγ₀eq : ∀ s : unitInterval, γ₀ s = G (boxRadial Lu Hu Lv Hv (2 * Real.pi * ↑s)))
    (hγ₁eq : ∀ s : unitInterval, γ₁ s
      = G (ρ' * Real.cos (2 * Real.pi * ↑s), ρ' * Real.sin (2 * Real.pi * ↑s))) :
    windingNumberC γ₀ hγ₀ = windingNumberC γ₁ hγ₁ := by
  -- the ray parameter `λ_σ(s)` and the ray point `p(σ,s)`
  set lam : unitInterval × unitInterval → ℝ := fun st =>
    (1 - (↑st.1 : ℝ)) * boxRadialR Lu Hu Lv Hv (2 * Real.pi * ↑st.2)
      + (↑st.1 : ℝ) * ρ' with hlamdef
  set p : unitInterval × unitInterval → ℝ × ℝ := fun st =>
    (lam st * Real.cos (2 * Real.pi * ↑st.2),
     lam st * Real.sin (2 * Real.pi * ↑st.2)) with hpdef
  -- continuity of `p`
  have hval1 : Continuous fun st : unitInterval × unitInterval => (↑st.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hval2 : Continuous fun st : unitInterval × unitInterval => (↑st.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hR : Continuous fun st : unitInterval × unitInterval =>
      boxRadialR Lu Hu Lv Hv (2 * Real.pi * ↑st.2) :=
    (continuous_boxRadialR hLu hHu hLv hHv).comp (continuous_const.mul hval2)
  have hlam : Continuous lam :=
    ((continuous_const.sub hval1).mul hR).add (hval1.mul continuous_const)
  have hcos : Continuous fun st : unitInterval × unitInterval =>
      Real.cos (2 * Real.pi * ↑st.2) :=
    Real.continuous_cos.comp (continuous_const.mul hval2)
  have hsin : Continuous fun st : unitInterval × unitInterval =>
      Real.sin (2 * Real.pi * ↑st.2) :=
    Real.continuous_sin.comp (continuous_const.mul hval2)
  have hp : Continuous p := (hlam.mul hcos).prodMk (hlam.mul hsin)
  -- `λ_σ(s) ∈ [ρ', r(2πs)]` and `p(σ,s) ∈ box \ {0}`
  have hlam_bounds : ∀ st : unitInterval × unitInterval,
      0 < lam st ∧ lam st ≤ boxRadialR Lu Hu Lv Hv (2 * Real.pi * ↑st.2) := by
    intro st
    have hσ0 : (0 : ℝ) ≤ ↑st.1 := st.1.2.1
    have hσ1 : (↑st.1 : ℝ) ≤ 1 := st.1.2.2
    have h1s : (0 : ℝ) ≤ 1 - ↑st.1 := by linarith
    have hrge : ρ' ≤ boxRadialR Lu Hu Lv Hv (2 * Real.pi * ↑st.2) :=
      le_trans hρ'B (boxInradius_le_boxRadialR hLu hHu hLv hHv _)
    constructor
    · have := mul_le_mul_of_nonneg_left hrge h1s
      simp only [hlamdef]; nlinarith [hρ'0]
    · have := mul_le_mul_of_nonneg_left hrge hσ0
      simp only [hlamdef]; nlinarith
  have hpmem : ∀ st : unitInterval × unitInterval,
      p st ∈ {z : ℝ × ℝ | z.1 ∈ Set.Icc Lu Hu ∧ z.2 ∈ Set.Icc Lv Hv} := by
    intro st
    obtain ⟨hlpos, hlle⟩ := hlam_bounds st
    obtain ⟨hm1, hm2⟩ := boxRadial_mem hLu hHu hLv hHv (2 * Real.pi * ↑st.2)
    rw [Set.mem_Icc] at hm1 hm2
    refine ⟨Set.mem_Icc.mpr (seg_mem_Icc hLu.le hHu.le hlpos hlle hm1.1 hm1.2),
      Set.mem_Icc.mpr (seg_mem_Icc hLv.le hHv.le hlpos hlle hm2.1 hm2.2)⟩
  have hpne : ∀ st : unitInterval × unitInterval, p st ≠ 0 := by
    intro st h
    obtain ⟨hlpos, _⟩ := hlam_bounds st
    have h1 : lam st * Real.cos (2 * Real.pi * ↑st.2) = 0 := congrArg Prod.fst h
    have h2 : lam st * Real.sin (2 * Real.pi * ↑st.2) = 0 := congrArg Prod.snd h
    have hcos0 : Real.cos (2 * Real.pi * ↑st.2) = 0 :=
      (mul_eq_zero.mp h1).resolve_left hlpos.ne'
    have hsin0 : Real.sin (2 * Real.pi * ↑st.2) = 0 :=
      (mul_eq_zero.mp h2).resolve_left hlpos.ne'
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * ↑st.2)
    rw [hcos0, hsin0] at this; norm_num at this
  -- the homotopy
  set H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun st => G (p st), hGcont.comp_continuous hp hpmem⟩ with hHdef
  have hHne : ∀ st, H st ≠ 0 := by
    intro st
    obtain ⟨hm1, hm2⟩ := hpmem st
    exact hGne (p st) hm1 hm2 (hpne st)
  have h0 : ∀ t : unitInterval, H (0, t) = γ₀ t := by
    intro t
    rw [hγ₀eq]
    change G (p (0, t)) = _
    congr 1
    simp only [hpdef, hlamdef, boxRadial, Set.Icc.coe_zero, sub_zero, one_mul,
      zero_mul, add_zero]
  have h1 : ∀ t : unitInterval, H (1, t) = γ₁ t := by
    intro t
    rw [hγ₁eq]
    change G (p (1, t)) = _
    congr 1
    simp only [hpdef, hlamdef, Set.Icc.coe_one, sub_self, zero_mul, one_mul,
      zero_add]
  have hloop : ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
    intro s
    change G (p (s, 0)) = G (p (s, 1))
    congr 1
    have hR0 : boxRadialR Lu Hu Lv Hv 0 = boxRadialR Lu Hu Lv Hv (2 * Real.pi) := by
      simp only [boxRadialR, Real.cos_zero, Real.sin_zero, Real.cos_two_pi,
        Real.sin_two_pi]
    simp only [hpdef, hlamdef, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero,
      mul_one, Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi]
    rw [hR0]
  exact windingNumberC_eq_of_homotopy γ₀ γ₁ hγ₀ hγ₁ H hHne h0 h1 hloop

/-- **Rigidity transfer to the natural box** (`lem:trimmed_winding_t0`,
zero-freeness bridge): property 2 of `def:apriori_datum` — rigidity of
`H^tr(0,·)` on the fixed square minus its center — transports to zero-freeness
of the *Icc gap map in natural chart coordinates* `z ↦ F̄(0, Ξ_0^{-1}·z)` on the
trimmed box `R^tr_0 \ {0}`, since `Ξ^tr_0 = trimmedRectRescale …0` maps the
square onto the box (`rescale_image_Icc`) fixing `0`. This discharges the
`hGne` hypothesis of `boxRadial_winding_eq` for the discrete gap map. -/
lemma trimmedRectGap_natural_ne_zero {m : ℕ} {a b : ZMod n} {κs κ : ZMod n → ℝ}
    {ε d : ℝ} (hadm : TrimAdm κs κ m a b ε d 0)
    (hrig : ∀ q : ℝ × ℝ, q.1 ∈ Set.Icc (-1 : ℝ) 1 → q.2 ∈ Set.Icc (-1 : ℝ) 1 →
      q ≠ 0 → trimmedRectGap m a b κs κ ε d 0 q ≠ 0)
    {z : ℝ × ℝ}
    (hz1 : z.1 ∈ Set.Icc (trimLo κs κ a (a + (m : ZMod n)) 0 ε d)
      (trimHi κs κ a (a + (m : ZMod n)) 0 ε d))
    (hz2 : z.2 ∈ Set.Icc (trimLo κs κ b (b + (m : ZMod n)) 0 ε d)
      (trimHi κs κ b (b + (m : ZMod n)) 0 ε d))
    (hznz : z ≠ 0) :
    closureGap (curvPath κs κ 0) (closingCellIcc m a b κs κ 0 z) ≠ 0 := by
  rw [← rescale_image_Icc hadm.1 hadm.2.1] at hz1
  rw [← rescale_image_Icc hadm.2.2.1 hadm.2.2.2] at hz2
  obtain ⟨q1, hq1mem, hq1⟩ := hz1
  obtain ⟨q2, hq2mem, hq2⟩ := hz2
  have hqz : trimmedRectRescale κs κ m a b ε d 0 (q1, q2) = z := by
    simp only [trimmedRectRescale, hq1, hq2, Prod.mk.eta]
  have hqnz : (q1, q2) ≠ 0 := by
    intro h
    apply hznz
    rw [← hqz, h]
    simp [trimmedRectRescale, rescale]
  have hne := hrig (q1, q2) hq1mem hq2mem hqnz
  unfold trimmedRectGap at hne
  rwa [hqz] at hne

/-- **Per-`t` rigidity transfer to the natural box** (`hbd`/C1 companion of
`certified_degree_continuation` at the discrete chart, general `t`): rigidity of
`H^tr(t,·)` on the fixed square minus its center transports to zero-freeness of
the Icc gap map in natural chart coordinates `z ↦ F̄(t, Ξ_t^{-1}·z)` on the
trimmed box `R^tr_t \ {0}`, for an *arbitrary* time `t`. This generalizes the
`t = 0` case `trimmedRectGap_natural_ne_zero`; the proof is identical, since
`Ξ^tr_t = trimmedRectRescale …t` maps the square onto the box (`rescale_image_Icc`
under `TrimAdm … t`) fixing `0` for every `t`. Rigidity (`hrig`) is kept as a
hypothesis — this is a coordinate transport, NOT a C1 discharge; it supplies the
per-`τ` boundary zero-freeness input `hbd` of `certified_degree_continuation`
once rigidity of the square gap map is established at each time. -/
lemma trimmedRectGap_natural_ne_zero_tau {m : ℕ} {a b : ZMod n}
    {κs κ : ZMod n → ℝ} {ε d t : ℝ} (hadm : TrimAdm κs κ m a b ε d t)
    (hrig : ∀ q : ℝ × ℝ, q.1 ∈ Set.Icc (-1 : ℝ) 1 → q.2 ∈ Set.Icc (-1 : ℝ) 1 →
      q ≠ 0 → trimmedRectGap m a b κs κ ε d t q ≠ 0)
    {z : ℝ × ℝ}
    (hz1 : z.1 ∈ Set.Icc (trimLo κs κ a (a + (m : ZMod n)) t ε d)
      (trimHi κs κ a (a + (m : ZMod n)) t ε d))
    (hz2 : z.2 ∈ Set.Icc (trimLo κs κ b (b + (m : ZMod n)) t ε d)
      (trimHi κs κ b (b + (m : ZMod n)) t ε d))
    (hznz : z ≠ 0) :
    closureGap (curvPath κs κ t) (closingCellIcc m a b κs κ t z) ≠ 0 := by
  rw [← rescale_image_Icc hadm.1 hadm.2.1] at hz1
  rw [← rescale_image_Icc hadm.2.2.1 hadm.2.2.2] at hz2
  obtain ⟨q1, hq1mem, hq1⟩ := hz1
  obtain ⟨q2, hq2mem, hq2⟩ := hz2
  have hqz : trimmedRectRescale κs κ m a b ε d t (q1, q2) = z := by
    simp only [trimmedRectRescale, hq1, hq2, Prod.mk.eta]
  have hqnz : (q1, q2) ≠ 0 := by
    intro h
    apply hznz
    rw [← hqz, h]
    simp [trimmedRectRescale, rescale]
  have hne := hrig (q1, q2) hq1mem hq2mem hqnz
  unfold trimmedRectGap at hne
  rwa [hqz] at hne

/-! ### Inverse of the fixed-square normalization (`Ξ^tr_0`)⁻¹ : box → square

To transport the *square*-coordinate continuity of `H^tr(0,·)`
(`continuousOn_trimmedRectGap`) to *natural*-box coordinates (needed to feed
`boxRadial_winding_eq`), we build the per-coordinate right inverse of `rescale`
and the induced `trimmedRectRescaleInv`, a continuous section box → square. -/

/-- The right inverse of `rescale L R` on `L < 0 < R`: `max y 0 / R +
min y 0 / (-L)` (i.e. `y/R` for `y ≥ 0`, `y/(-L)` for `y ≤ 0`). -/
noncomputable def rescaleInv (L R y : ℝ) : ℝ := max y 0 / R + min y 0 / (-L)

/-- The inverse rescale is continuous. -/
private lemma continuous_rescaleInv (L R : ℝ) : Continuous (rescaleInv L R) := by
  unfold rescaleInv; fun_prop

/-- `rescale L R` is a right inverse of `rescaleInv L R` on `L < 0 < R`. -/
private lemma rescale_rescaleInv {L R : ℝ} (hL : L < 0) (hR : 0 < R) (y : ℝ) :
    rescale L R (rescaleInv L R y) = y := by
  have hnL : (0 : ℝ) < -L := by linarith
  have hRne : R ≠ 0 := hR.ne'
  have hLne : L ≠ 0 := hL.ne
  have hnLne : (-L) ≠ 0 := hnL.ne'
  rcases le_or_gt 0 y with hy | hy
  · have hw : rescaleInv L R y = y / R := by
      rw [rescaleInv, max_eq_left hy, min_eq_right hy, zero_div, add_zero]
    have hyR : (0 : ℝ) ≤ y / R := div_nonneg hy hR.le
    rw [hw, rescale, min_eq_right hyR, max_eq_left hyR]
    field_simp
    ring
  · have hw : rescaleInv L R y = y / (-L) := by
      rw [rescaleInv, max_eq_right hy.le, min_eq_left hy.le, zero_div, zero_add]
    have hyL : y / (-L) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hy.le hnL.le
    rw [hw, rescale, min_eq_left hyL, max_eq_right hyL]
    field_simp
    ring

/-- The inverse rescale maps the factor interval `[L, R]` into `[-1, 1]`. -/
private lemma rescaleInv_mem_Icc {L R : ℝ} (hL : L < 0) (hR : 0 < R) {y : ℝ}
    (hy : y ∈ Set.Icc L R) : rescaleInv L R y ∈ Set.Icc (-1 : ℝ) 1 := by
  have hnL : (0 : ℝ) < -L := by linarith
  rcases le_or_gt 0 y with hy0 | hy0
  · have hw : rescaleInv L R y = y / R := by
      rw [rescaleInv, max_eq_left hy0, min_eq_right hy0, zero_div, add_zero]
    rw [hw]
    exact ⟨le_trans (by norm_num) (div_nonneg hy0 hR.le), (div_le_one hR).mpr hy.2⟩
  · have hw : rescaleInv L R y = y / (-L) := by
      rw [rescaleInv, max_eq_right hy0.le, min_eq_left hy0.le, zero_div, zero_add]
    rw [hw]
    refine ⟨?_, le_trans (div_nonpos_of_nonpos_of_nonneg hy0.le hnL.le) (by norm_num)⟩
    rw [le_div_iff₀ hnL]; nlinarith [hy.1]

/-- The pair inverse `(Ξ^tr_t)⁻¹ : box → square` — the per-coordinate inverse
rescale on the two trimmed factors. -/
noncomputable def trimmedRectRescaleInv (κs κ : ZMod n → ℝ) (m : ℕ) (a b : ZMod n)
    (ε d t : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (rescaleInv (trimLo κs κ a (a + (m : ZMod n)) t ε d)
      (trimHi κs κ a (a + (m : ZMod n)) t ε d) z.1,
   rescaleInv (trimLo κs κ b (b + (m : ZMod n)) t ε d)
      (trimHi κs κ b (b + (m : ZMod n)) t ε d) z.2)

/-- The pair inverse is continuous. -/
lemma continuous_trimmedRectRescaleInv (κs κ : ZMod n → ℝ) (m : ℕ) (a b : ZMod n)
    (ε d t : ℝ) : Continuous (trimmedRectRescaleInv κs κ m a b ε d t) :=
  ((continuous_rescaleInv _ _).comp continuous_fst).prodMk
    ((continuous_rescaleInv _ _).comp continuous_snd)

/-- `Ξ^tr_t` is a right inverse of `(Ξ^tr_t)⁻¹` on a strictly-interior box. -/
lemma trimmedRectRescale_trimmedRectRescaleInv {κs κ : ZMod n → ℝ} {m : ℕ}
    {a b : ZMod n} {ε d t : ℝ}
    (hLu : trimLo κs κ a (a + (m : ZMod n)) t ε d < 0)
    (hHu : 0 < trimHi κs κ a (a + (m : ZMod n)) t ε d)
    (hLv : trimLo κs κ b (b + (m : ZMod n)) t ε d < 0)
    (hHv : 0 < trimHi κs κ b (b + (m : ZMod n)) t ε d) (z : ℝ × ℝ) :
    trimmedRectRescale κs κ m a b ε d t (trimmedRectRescaleInv κs κ m a b ε d t z)
      = z := by
  simp only [trimmedRectRescale, trimmedRectRescaleInv,
    rescale_rescaleInv hLu hHu, rescale_rescaleInv hLv hHv, Prod.mk.eta]

/-- The pair inverse maps the trimmed box into the fixed square. -/
lemma trimmedRectRescaleInv_mem_square {κs κ : ZMod n → ℝ} {m : ℕ} {a b : ZMod n}
    {ε d t : ℝ}
    (hLu : trimLo κs κ a (a + (m : ZMod n)) t ε d < 0)
    (hHu : 0 < trimHi κs κ a (a + (m : ZMod n)) t ε d)
    (hLv : trimLo κs κ b (b + (m : ZMod n)) t ε d < 0)
    (hHv : 0 < trimHi κs κ b (b + (m : ZMod n)) t ε d) {z : ℝ × ℝ}
    (hz1 : z.1 ∈ Set.Icc (trimLo κs κ a (a + (m : ZMod n)) t ε d)
      (trimHi κs κ a (a + (m : ZMod n)) t ε d))
    (hz2 : z.2 ∈ Set.Icc (trimLo κs κ b (b + (m : ZMod n)) t ε d)
      (trimHi κs κ b (b + (m : ZMod n)) t ε d)) :
    (trimmedRectRescaleInv κs κ m a b ε d t z).1 ∈ Set.Icc (-1 : ℝ) 1 ∧
      (trimmedRectRescaleInv κs κ m a b ε d t z).2 ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨rescaleInv_mem_Icc hLu hHu hz1, rescaleInv_mem_Icc hLv hHv hz2⟩

/-- **Continuity of the natural-box Icc gap map** (`lem:trimmed_winding_t0`,
continuity bridge): the gap map in natural chart coordinates
`z ↦ F̄(0, Ξ_0^{-1}·z)` is continuous on the trimmed box `R^tr_0`. Proof: it
equals `H^tr(0,·) ∘ (Ξ^tr_0)⁻¹`, and `continuousOn_trimmedRectGap` (square
continuity) composes with the continuous section `(Ξ^tr_0)⁻¹ : box → square`.
This discharges the `hGcont` hypothesis of `boxRadial_winding_eq`. -/
lemma continuousOn_naturalGap [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} {a b : ZMod n}
    (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m) (hbam : b ≠ a + m)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {ε d : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hadm : ∀ τ : ↥(Set.Icc (0 : ℝ) 1), TrimAdm κs κ m a b ε d ↑τ)
    (hLu : trimLo κs κ a (a + (m : ZMod n)) 0 ε d < 0)
    (hHu : 0 < trimHi κs κ a (a + (m : ZMod n)) 0 ε d)
    (hLv : trimLo κs κ b (b + (m : ZMod n)) 0 ε d < 0)
    (hHv : 0 < trimHi κs κ b (b + (m : ZMod n)) 0 ε d) :
    ContinuousOn
      (fun z => closureGap (curvPath κs κ 0) (closingCellIcc m a b κs κ 0 z))
      {z : ℝ × ℝ |
        z.1 ∈ Set.Icc (trimLo κs κ a (a + (m : ZMod n)) 0 ε d)
          (trimHi κs κ a (a + (m : ZMod n)) 0 ε d) ∧
        z.2 ∈ Set.Icc (trimLo κs κ b (b + (m : ZMod n)) 0 ε d)
          (trimHi κs κ b (b + (m : ZMod n)) 0 ε d)} := by
  have hEq : (fun z => closureGap (curvPath κs κ 0) (closingCellIcc m a b κs κ 0 z))
      = fun z => trimmedRectGap m a b κs κ ε d 0
        (trimmedRectRescaleInv κs κ m a b ε d 0 z) := by
    funext z
    rw [trimmedRectGap,
      trimmedRectRescale_trimmedRectRescaleInv hLu hHu hLv hHv]
  rw [hEq]
  -- `H^tr(0,·)` is continuous on the fixed square
  have hsq : ContinuousOn (fun q : ℝ × ℝ => trimmedRectGap m a b κs κ ε d 0 q)
      {q : ℝ × ℝ | q.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ q.2 ∈ Set.Icc (-1 : ℝ) 1} := by
    have hfull := continuousOn_trimmedRectGap hn4 hm0 hab habm hbam hκs hκ hε hd hadm
    have hι : Continuous fun q : ℝ × ℝ =>
        (((0 : ↥(Set.Icc (0 : ℝ) 1)), q) : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ)) :=
      continuous_const.prodMk continuous_id
    have hmaps : Set.MapsTo
        (fun q : ℝ × ℝ => (((0 : ↥(Set.Icc (0 : ℝ) 1)), q) :
          ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ)))
        {q : ℝ × ℝ | q.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ q.2 ∈ Set.Icc (-1 : ℝ) 1}
        {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) |
          x.2.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2.2 ∈ Set.Icc (-1 : ℝ) 1} :=
      fun q hq => hq
    exact (hfull.comp hι.continuousOn hmaps).congr fun q _ => rfl
  exact hsq.comp (continuous_trimmedRectRescaleInv κs κ m a b ε d 0).continuousOn
    fun z hz => trimmedRectRescaleInv_mem_square hLu hHu hLv hHv hz.1 hz.2

/-- **Per-`τ` continuity of the natural-box Icc gap map** (`hGcont` of
`certified_degree_continuation` at the discrete chart, general `τ`): the gap map
`z ↦ F̄(τ, Ξ_τ^{-1}·z)` is continuous on the trimmed box `R^tr_τ` for an
*arbitrary* fixed `τ ∈ [0,1]`. This generalizes the `τ = 0` case
`continuousOn_naturalGap`; the proof is identical, restricting the joint
`(t, q)`-continuity of `continuousOn_trimmedRectGap` to the fixed slice `t = τ`
(via the constant section `q ↦ (τ, q)`) and composing with the continuous
section `(Ξ^tr_τ)⁻¹`. Verdict- and domain-independent: no joint `(t,s)`
continuity is required, only per-`τ` continuity in the box point. -/
lemma continuousOn_naturalGap_tau [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} {a b : ZMod n}
    (hm0 : (m : ZMod n) ≠ 0) (hab : a ≠ b) (habm : a ≠ b + m) (hbam : b ≠ a + m)
    {κs κ : ZMod n → ℝ} (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i) {ε d : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hadm : ∀ τ : ↥(Set.Icc (0 : ℝ) 1), TrimAdm κs κ m a b ε d ↑τ)
    (τ : ↥(Set.Icc (0 : ℝ) 1))
    (hLu : trimLo κs κ a (a + (m : ZMod n)) ↑τ ε d < 0)
    (hHu : 0 < trimHi κs κ a (a + (m : ZMod n)) ↑τ ε d)
    (hLv : trimLo κs κ b (b + (m : ZMod n)) ↑τ ε d < 0)
    (hHv : 0 < trimHi κs κ b (b + (m : ZMod n)) ↑τ ε d) :
    ContinuousOn
      (fun z => closureGap (curvPath κs κ ↑τ) (closingCellIcc m a b κs κ ↑τ z))
      {z : ℝ × ℝ |
        z.1 ∈ Set.Icc (trimLo κs κ a (a + (m : ZMod n)) ↑τ ε d)
          (trimHi κs κ a (a + (m : ZMod n)) ↑τ ε d) ∧
        z.2 ∈ Set.Icc (trimLo κs κ b (b + (m : ZMod n)) ↑τ ε d)
          (trimHi κs κ b (b + (m : ZMod n)) ↑τ ε d)} := by
  have hEq : (fun z => closureGap (curvPath κs κ ↑τ)
        (closingCellIcc m a b κs κ ↑τ z))
      = fun z => trimmedRectGap m a b κs κ ε d ↑τ
        (trimmedRectRescaleInv κs κ m a b ε d ↑τ z) := by
    funext z
    rw [trimmedRectGap,
      trimmedRectRescale_trimmedRectRescaleInv hLu hHu hLv hHv]
  rw [hEq]
  -- `H^tr(τ,·)` is continuous on the fixed square (slice at `t = τ`)
  have hsq : ContinuousOn (fun q : ℝ × ℝ => trimmedRectGap m a b κs κ ε d ↑τ q)
      {q : ℝ × ℝ | q.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ q.2 ∈ Set.Icc (-1 : ℝ) 1} := by
    have hfull := continuousOn_trimmedRectGap hn4 hm0 hab habm hbam hκs hκ hε hd hadm
    have hι : Continuous fun q : ℝ × ℝ =>
        ((τ, q) : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ)) :=
      continuous_const.prodMk continuous_id
    have hmaps : Set.MapsTo
        (fun q : ℝ × ℝ => ((τ, q) : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ)))
        {q : ℝ × ℝ | q.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ q.2 ∈ Set.Icc (-1 : ℝ) 1}
        {x : ↥(Set.Icc (0 : ℝ) 1) × (ℝ × ℝ) |
          x.2.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2.2 ∈ Set.Icc (-1 : ℝ) 1} :=
      fun q hq => hq
    exact (hfull.comp hι.continuousOn hmaps).congr fun q _ => rfl
  exact hsq.comp (continuous_trimmedRectRescaleInv κs κ m a b ε d ↑τ).continuousOn
    fun z hz => trimmedRectRescaleInv_mem_square hLu hHu hLv hHv hz.1 hz.2

/-- A centered circle of radius `≤ ρ_B` sits inside the box. -/
private lemma circle_mem_box {Lu Hu Lv Hv : ℝ} {ρ' : ℝ} (hρ'0 : 0 < ρ')
    (hρ'B : ρ' ≤ boxInradius Lu Hu Lv Hv) (θ : ℝ) :
    ρ' * Real.cos θ ∈ Set.Icc Lu Hu ∧ ρ' * Real.sin θ ∈ Set.Icc Lv Hv := by
  have hb1 : ρ' ≤ Hu := le_trans hρ'B ((min_le_left _ _).trans (min_le_left _ _))
  have hb2 : ρ' ≤ -Lu := le_trans hρ'B ((min_le_left _ _).trans (min_le_right _ _))
  have hb3 : ρ' ≤ Hv := le_trans hρ'B ((min_le_right _ _).trans (min_le_left _ _))
  have hb4 : ρ' ≤ -Lv := le_trans hρ'B ((min_le_right _ _).trans (min_le_right _ _))
  have hac : |ρ' * Real.cos θ| ≤ ρ' := by
    rw [abs_mul, abs_of_pos hρ'0]; nlinarith [Real.abs_cos_le_one θ, abs_nonneg (Real.cos θ)]
  have has : |ρ' * Real.sin θ| ≤ ρ' := by
    rw [abs_mul, abs_of_pos hρ'0]; nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ)]
  rw [abs_le] at hac has
  exact ⟨⟨by linarith [hac.1], by linarith [hac.2]⟩,
    ⟨by linarith [has.1], by linarith [has.2]⟩⟩

/-! ### The conditional `t = 0` winding transfer (`lem:trimmed_winding_t0`) -/

/-- **Continuity of the box-radial boundary loop** (`lem:trimmed_winding_t0`,
continuity of `γ_□`): for a gap map `G` continuous on the box
`[Lu,Hu]×[Lv,Hv]` (origin interior), the box-radial boundary loop
`s ↦ G(boxRadial(2πs))` is continuous. `G` is kept *abstract* here — exactly as
inside `boxRadial_winding_eq` — so that `ContinuousOn.comp_continuous` never
unfolds the concrete discrete gap map, sidestepping the `whnf` divergence that
blocks the inlined form. -/
private lemma boxRadialLoop_continuous {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0)
    (hHu : 0 < Hu) (hLv : Lv < 0) (hHv : 0 < Hv) {G : ℝ × ℝ → ℂ}
    (hG : ContinuousOn G
      {z : ℝ × ℝ | z.1 ∈ Set.Icc Lu Hu ∧ z.2 ∈ Set.Icc Lv Hv}) :
    Continuous (fun s : unitInterval =>
      G (boxRadial Lu Hu Lv Hv (2 * Real.pi * ↑s))) := by
  -- Compose in two stages so `comp_continuous`'s higher-order unification sees
  -- `?f := boxRadial Lu Hu Lv Hv` (a clean partial application, over the `ℝ`
  -- angle domain) rather than the `2π↑s` lambda over the `unitInterval` subtype
  -- domain — the latter makes `whnf` diverge (the @092 blocker).
  have hGbr : Continuous (fun θ : ℝ => G (boxRadial Lu Hu Lv Hv θ)) :=
    hG.comp_continuous (continuous_box_radial hLu hHu hLv hHv)
      (fun θ => boxRadial_mem hLu hHu hLv hHv θ)
  exact hGbr.comp (continuous_subtype_val.const_mul _)

/-! ### Project-local Mathlib supplement — the box→disk degree bridge

The in-tree planar degree principle `Gluck.exists_zero_of_boundary_winding`
(`chap:winding`) is stated for the *unit disk*: a boundary loop with nonzero
winding forces an interior zero. The trimmed-box chart lives on a rectangle,
not a disk, so we bridge the two by the **radial gauge homeomorphism**
`boxProj w = (‖w‖ / g(w)) • w` (with `g = boxGauge`), which satisfies the key
identity `boxGauge (boxProj w) = ‖w‖`: it maps the closed unit disk onto the
closed box, the open disk onto the open box, and the unit sphere onto
`∂(box)`, sending `Circle.exp θ` to `boxRadial θ`. Transporting a map `G` on
the box through `boxProj` lands it on the disk with the box-radial boundary
loop as its disk-boundary loop. -/

/-- Coordinate lower bound for the per-coordinate gauge: the half-width
`max H (-L)` times the gauge dominates `|x|`. -/
private lemma abs_le_gaugeCoord_mul {L H : ℝ} (hL : L < 0) (hH : 0 < H) (x : ℝ)
    (hg : 0 ≤ gaugeCoord L H x) : |x| ≤ max H (-L) * gaugeCoord L H x := by
  have h1 : x / H ≤ gaugeCoord L H x := le_max_left _ _
  have h2 : x / L ≤ gaugeCoord L H x := le_max_right _ _
  have hMH : H ≤ max H (-L) := le_max_left _ _
  have hML : -L ≤ max H (-L) := le_max_right _ _
  have hLne : L ≠ 0 := hL.ne
  have hHne : H ≠ 0 := hH.ne'
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have hxeq : H * (x / H) = x := by field_simp
    calc x = H * (x / H) := hxeq.symm
      _ ≤ H * gaugeCoord L H x := by nlinarith [hH.le]
      _ ≤ max H (-L) * gaugeCoord L H x := by nlinarith
  · rw [abs_of_neg hx]
    have hxeq : (-L) * (x / L) = -x := by field_simp
    calc -x = (-L) * (x / L) := hxeq.symm
      _ ≤ (-L) * gaugeCoord L H x := by nlinarith [neg_pos.mpr hL]
      _ ≤ max H (-L) * gaugeCoord L H x := by nlinarith

/-- The box gauge dominates the Euclidean/`Prod`-sup norm up to the outer
radius `max (max Hu (-Lu)) (max Hv (-Lv))`. Powers continuity of `boxProj` at
the origin. -/
private lemma norm_le_boxOuter_mul_boxGauge {Lu Hu Lv Hv : ℝ}
    (hLu : Lu < 0) (hHu : 0 < Hu) (hLv : Lv < 0) (hHv : 0 < Hv) (z : ℝ × ℝ) :
    ‖z‖ ≤ max (max Hu (-Lu)) (max Hv (-Lv)) * boxGauge Lu Hu Lv Hv z := by
  have hu := abs_le_gaugeCoord_mul hLu hHu z.1 (gaugeCoord_nonneg hLu hHu z.1)
  have hv := abs_le_gaugeCoord_mul hLv hHv z.2 (gaugeCoord_nonneg hLv hHv z.2)
  have hMu : max Hu (-Lu) ≤ max (max Hu (-Lu)) (max Hv (-Lv)) := le_max_left _ _
  have hMv : max Hv (-Lv) ≤ max (max Hu (-Lu)) (max Hv (-Lv)) := le_max_right _ _
  have hM0 : 0 ≤ max (max Hu (-Lu)) (max Hv (-Lv)) :=
    (le_trans hHu.le (le_max_left _ _)).trans hMu
  have gcu := gaugeCoord_nonneg hLu hHu z.1
  have gcv := gaugeCoord_nonneg hLv hHv z.2
  have hbu : gaugeCoord Lu Hu z.1 ≤ boxGauge Lu Hu Lv Hv z := le_max_left _ _
  have hbv : gaugeCoord Lv Hv z.2 ≤ boxGauge Lu Hu Lv Hv z := le_max_right _ _
  rw [Prod.norm_def]
  simp only [Real.norm_eq_abs]
  apply max_le
  · calc |z.1| ≤ max Hu (-Lu) * gaugeCoord Lu Hu z.1 := hu
      _ ≤ max (max Hu (-Lu)) (max Hv (-Lv)) * gaugeCoord Lu Hu z.1 := by nlinarith
      _ ≤ max (max Hu (-Lu)) (max Hv (-Lv)) * boxGauge Lu Hu Lv Hv z := by nlinarith
  · calc |z.2| ≤ max Hv (-Lv) * gaugeCoord Lv Hv z.2 := hv
      _ ≤ max (max Hu (-Lu)) (max Hv (-Lv)) * gaugeCoord Lv Hv z.2 := by nlinarith
      _ ≤ max (max Hu (-Lu)) (max Hv (-Lv)) * boxGauge Lu Hu Lv Hv z := by nlinarith

/-- The box gauge is positive off the origin. -/
private lemma boxGauge_pos_of_ne {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) {z : ℝ × ℝ} (hz : z ≠ 0) :
    0 < boxGauge Lu Hu Lv Hv z := by
  have hz' : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
    rw [← not_and_or]; intro h; exact hz (Prod.ext h.1 h.2)
  rcases hz' with h | h
  · exact lt_of_lt_of_le (gaugeCoord_pos hLu hHu h) (le_max_left _ _)
  · exact lt_of_lt_of_le (gaugeCoord_pos hLv hHv h) (le_max_right _ _)

/-- **The radial gauge map** (box side): rescale `w : ℂ` (viewed as `(w.re,
w.im)`) to gauge-radius `‖w‖`. -/
noncomputable def boxProj (Lu Hu Lv Hv : ℝ) (w : ℂ) : ℝ × ℝ :=
  (‖w‖ / boxGauge Lu Hu Lv Hv (w.re, w.im)) • (w.re, w.im)

/-- Key identity: the box gauge of `boxProj w` equals `‖w‖`. -/
private lemma boxGauge_boxProj {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) (w : ℂ) :
    boxGauge Lu Hu Lv Hv (boxProj Lu Hu Lv Hv w) = ‖w‖ := by
  rcases eq_or_ne (w.re, w.im) (0 : ℝ × ℝ) with hz | hz
  · have hw0 : w = 0 := Complex.ext (congrArg Prod.fst hz) (congrArg Prod.snd hz)
    simp [boxProj, hw0, boxGauge, gaugeCoord]
  · have hgpos := boxGauge_pos_of_ne hLu hHu hLv hHv hz
    have hc : (0 : ℝ) ≤ ‖w‖ / boxGauge Lu Hu Lv Hv (w.re, w.im) :=
      div_nonneg (norm_nonneg _) hgpos.le
    change boxGauge Lu Hu Lv Hv
        ((‖w‖ / boxGauge Lu Hu Lv Hv (w.re, w.im)) • (w.re, w.im)) = ‖w‖
    have hsm : ((‖w‖ / boxGauge Lu Hu Lv Hv (w.re, w.im)) • (w.re, w.im) : ℝ × ℝ)
        = ((‖w‖ / boxGauge Lu Hu Lv Hv (w.re, w.im)) * w.re,
           (‖w‖ / boxGauge Lu Hu Lv Hv (w.re, w.im)) * w.im) := by
      rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul]
    rw [hsm, boxGauge_smul Lu Hu Lv Hv hc (w.re, w.im), div_mul_cancel₀ _ hgpos.ne']

/-- `boxProj` is continuous (the origin is handled by the norm squeeze). -/
private lemma continuous_boxProj {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) : Continuous (boxProj Lu Hu Lv Hv) := by
  set M := max (max Hu (-Lu)) (max Hv (-Lv)) with hM
  rw [continuous_iff_continuousAt]
  intro w
  rcases eq_or_ne w 0 with h0 | h0
  · subst h0
    have h00 : boxProj Lu Hu Lv Hv 0 = 0 := by simp [boxProj]
    have hbound : ∀ v : ℂ, ‖boxProj Lu Hu Lv Hv v‖ ≤ M * ‖v‖ := fun v => by
      have := norm_le_boxOuter_mul_boxGauge hLu hHu hLv hHv (boxProj Lu Hu Lv Hv v)
      rwa [boxGauge_boxProj hLu hHu hLv hHv v] at this
    rw [ContinuousAt, h00, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun v => norm_nonneg _) hbound
    have ht : Filter.Tendsto (fun v : ℂ => ‖v‖) (nhds 0) (nhds 0) := by
      simpa using (continuous_norm.tendsto (0 : ℂ))
    simpa using ht.const_mul M
  · have hne : (w.re, w.im) ≠ (0 : ℝ × ℝ) := by
      intro h; exact h0 (Complex.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    have hgpos := boxGauge_pos_of_ne hLu hHu hLv hHv hne
    have hvecC : Continuous (fun v : ℂ => (v.re, v.im)) :=
      Complex.continuous_re.prodMk Complex.continuous_im
    have hscal : ContinuousAt (fun v : ℂ => ‖v‖ / boxGauge Lu Hu Lv Hv (v.re, v.im)) w :=
      (continuous_norm.continuousAt).div
        (((continuous_boxGauge Lu Hu Lv Hv).comp hvecC).continuousAt) hgpos.ne'
    exact hscal.smul hvecC.continuousAt

/-- `boxProj` sends `Circle.exp θ` to the box-radial boundary point at angle
`θ`. -/
private lemma boxProj_circle (Lu Hu Lv Hv θ : ℝ) :
    boxProj Lu Hu Lv Hv (Circle.exp θ) = boxRadial Lu Hu Lv Hv θ := by
  have hre : ((Circle.exp θ : ℂ)).re = Real.cos θ := by
    rw [Circle.coe_exp]; simp [Complex.exp_ofReal_mul_I_re]
  have him : ((Circle.exp θ : ℂ)).im = Real.sin θ := by
    rw [Circle.coe_exp]; simp [Complex.exp_ofReal_mul_I_im]
  have hnorm : ‖(Circle.exp θ : ℂ)‖ = 1 := by rw [Circle.norm_coe]
  simp only [boxProj, boxRadial, boxRadialR, hre, him, hnorm, one_div]
  rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul]

/-- `boxProj` maps the closed unit disk into the closed box. -/
private lemma boxProj_mem_box {Lu Hu Lv Hv : ℝ} (hLu : Lu < 0) (hHu : 0 < Hu)
    (hLv : Lv < 0) (hHv : 0 < Hv) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    (boxProj Lu Hu Lv Hv w).1 ∈ Set.Icc Lu Hu ∧
      (boxProj Lu Hu Lv Hv w).2 ∈ Set.Icc Lv Hv := by
  have hg : boxGauge Lu Hu Lv Hv (boxProj Lu Hu Lv Hv w) ≤ 1 := by
    rw [boxGauge_boxProj hLu hHu hLv hHv w]; exact hw
  refine ⟨gaugeCoord_le_one_imp_mem hLu hHu ?_, gaugeCoord_le_one_imp_mem hLv hHv ?_⟩
  · exact (le_max_left _ _).trans hg
  · exact (le_max_right _ _).trans hg

/-- **Interior zero from a nonzero box-radial winding** (project-local
supplement for `thm:certified_degree_continuation`). A map `G` continuous on
the box `[Lu,Hu]×[Lv,Hv]` (origin interior), nonzero on the box boundary
`{boxGauge = 1}`, whose box-radial boundary loop `γ` (with `γ s = G (boxRadial …
(2πs))`) has nonzero winding about `0`, must vanish at an interior box point
(`boxGauge z < 1`). Transports `G` through the radial gauge homeomorphism
`boxProj` onto the unit disk, where the box-radial loop is exactly the
disk-boundary loop, and applies `Gluck.exists_zero_of_boundary_winding`. -/
theorem exists_zero_of_boxRadial_winding {Lu Hu Lv Hv : ℝ}
    (hLu : Lu < 0) (hHu : 0 < Hu) (hLv : Lv < 0) (hHv : 0 < Hv)
    {G : ℝ × ℝ → ℂ}
    (hGcont : ContinuousOn G {z : ℝ × ℝ | z.1 ∈ Set.Icc Lu Hu ∧ z.2 ∈ Set.Icc Lv Hv})
    (hGbd : ∀ z : ℝ × ℝ, boxGauge Lu Hu Lv Hv z = 1 → G z ≠ 0)
    (γ : C(unitInterval, ℂ)) (hγ : ∀ s, γ s ≠ 0)
    (hγeq : ∀ s : unitInterval, γ s = G (boxRadial Lu Hu Lv Hv (2 * Real.pi * ↑s)))
    (hw : windingNumberC γ hγ ≠ 0) :
    ∃ z : ℝ × ℝ, boxGauge Lu Hu Lv Hv z < 1 ∧ G z = 0 := by
  set F : ℂ → ℂ := fun w => G (boxProj Lu Hu Lv Hv w) with hFdef
  -- `F = G ∘ boxProj` is continuous on the closed unit disk
  have hFcont : ContinuousOn F (Metric.closedBall 0 1) := by
    refine hGcont.comp (continuous_boxProj hLu hHu hLv hHv).continuousOn ?_
    intro w hw
    have : ‖w‖ ≤ 1 := by simpa [dist_zero_right] using Metric.mem_closedBall.1 hw
    exact boxProj_mem_box hLu hHu hLv hHv this
  -- `F` is nonzero on the boundary circle
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) 1, F z ≠ 0 := by
    intro z hz
    have hznorm : ‖z‖ = 1 := by rwa [mem_sphere_zero_iff_norm] at hz
    refine hGbd (boxProj Lu Hu Lv Hv z) ?_
    rw [boxGauge_boxProj hLu hHu hLv hHv z]; exact hznorm
  -- the disk-boundary loop of `F` coincides pointwise with `γ`
  have heq : ∀ t : unitInterval, diskBoundaryLoop F hFcont t = γ t := by
    intro t
    change F (Circle.exp (2 * Real.pi * ↑t)) = γ t
    rw [hFdef]
    simp only
    rw [boxProj_circle, ← hγeq t]
  have hwind : windingNumberC (diskBoundaryLoop F hFcont)
      (diskBoundaryLoop_ne_zero F hFcont hbd) ≠ 0 := by
    rw [windingNumberC_congr heq]; exact hw
  obtain ⟨w, hwball, hFw⟩ := exists_zero_of_boundary_winding F hFcont hbd hwind
  refine ⟨boxProj Lu Hu Lv Hv w, ?_, hFw⟩
  rw [boxGauge_boxProj hLu hHu hLv hHv w]
  simpa [dist_zero_right] using Metric.mem_ball.1 hwball

-- Below the box-radial facts are only *applied* (never unfolded): making
-- `boxRadial`/`boxRadialR` `local irreducible` keeps `set`/`rfl`/`ContinuousMap`
-- defeq checks from whnf-diverging on the deeply-nested gauge functional.
attribute [local irreducible] boxRadial boxRadialR

/-- **Trimmed-boundary winding at `t = 0` — conditional transfer**
(`lem:trimmed_winding_t0`): given the `t = 0` anchor-rigidity (`hrig`, property 2
of `def:apriori_datum`) of the trimmed gap map on the fixed square minus its
center, the *box-radial* boundary loop
`γ_□(s) = F̄(0, boxRadial_{R^tr_0}(2πs))` of the natural-box gap map is nowhere
zero and its winding about `0` is `sgn Im(conj C_a · C_b) = ±1`. Proof: the
box-radial loop and the small-circle loop of `closure_winding_t0` have equal
winding (`boxRadial_winding_eq`, ray homotopy); the small-circle loop coincides
with `closure_winding_t0`'s standard `ρ'`-circle loop for `ρ'` small enough that
the perturbed chart values stay in the open moderate window
(`eventually_chartPerturb_mem` + `closingCellIcc_eq_closingCell`), whose winding
is the `±1`. Consumes the landed bricks `continuousOn_naturalGap`,
`trimmedRectGap_natural_ne_zero`, `boxRadial_winding_eq`, `closure_winding_t0`. -/
theorem trimmed_winding_t0 [NeZero n] (hn4 : 4 ≤ n) {m : ℕ} (hn : n = 2 * m)
    {a b : ℕ} (ha : a < m) (hb : b < m) {κs κ : ZMod n → ℝ}
    (hκs : ∀ i, 0 < κs i) (hκ : ∀ i, 0 < κ i)
    (hsym : ∀ i : ZMod n, κs (i + (m : ZMod n)) = κs i)
    (hL : ((starRingEnd ℂ) (closingJacobianCol m hκs a)
        * closingJacobianCol m hκs b).im ≠ 0)
    (hm0 : (m : ZMod n) ≠ 0) (hab : (a : ZMod n) ≠ (b : ZMod n))
    (habm : (a : ZMod n) ≠ (b : ZMod n) + (m : ZMod n))
    (hbam : (b : ZMod n) ≠ (a : ZMod n) + (m : ZMod n))
    {ε d : ℝ} (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hadm : ∀ τ : ↥(Set.Icc (0 : ℝ) 1),
      TrimAdm κs κ m (a : ZMod n) (b : ZMod n) ε d ↑τ)
    (hLu : trimLo κs κ (a : ZMod n) ((a : ZMod n) + (m : ZMod n)) 0 ε d < 0)
    (hHu : 0 < trimHi κs κ (a : ZMod n) ((a : ZMod n) + (m : ZMod n)) 0 ε d)
    (hLv : trimLo κs κ (b : ZMod n) ((b : ZMod n) + (m : ZMod n)) 0 ε d < 0)
    (hHv : 0 < trimHi κs κ (b : ZMod n) ((b : ZMod n) + (m : ZMod n)) 0 ε d)
    (hrig : ∀ q : ℝ × ℝ, q.1 ∈ Set.Icc (-1 : ℝ) 1 → q.2 ∈ Set.Icc (-1 : ℝ) 1 →
      q ≠ 0 → trimmedRectGap m (a : ZMod n) (b : ZMod n) κs κ ε d 0 q ≠ 0) :
    ∃ (γ : C(unitInterval, ℂ)) (hγ : ∀ s, γ s ≠ 0),
      (∀ s : unitInterval, γ s = closureGap (curvPath κs κ 0)
        (closingCellIcc m (a : ZMod n) (b : ZMod n) κs κ 0
          (boxRadial (trimLo κs κ (a : ZMod n) ((a : ZMod n) + (m : ZMod n)) 0 ε d)
            (trimHi κs κ (a : ZMod n) ((a : ZMod n) + (m : ZMod n)) 0 ε d)
            (trimLo κs κ (b : ZMod n) ((b : ZMod n) + (m : ZMod n)) 0 ε d)
            (trimHi κs κ (b : ZMod n) ((b : ZMod n) + (m : ZMod n)) 0 ε d)
            (2 * Real.pi * ↑s)))) ∧
      windingNumberC γ hγ =
        if 0 < ((starRingEnd ℂ) (closingJacobianCol m hκs a)
            * closingJacobianCol m hκs b).im then 1 else -1 := by
  set A : ZMod n := (a : ZMod n) with hAdef
  set B : ZMod n := (b : ZMod n) with hBdef
  set Lu := trimLo κs κ A (A + (m : ZMod n)) 0 ε d with hLudef
  set Hu := trimHi κs κ A (A + (m : ZMod n)) 0 ε d with hHudef
  set Lv := trimLo κs κ B (B + (m : ZMod n)) 0 ε d with hLvdef
  set Hv := trimHi κs κ B (B + (m : ZMod n)) 0 ε d with hHvdef
  -- continuity of the natural-box gap map on the box
  have hGcont : ContinuousOn
      (fun z => closureGap (curvPath κs κ 0) (closingCellIcc m A B κs κ 0 z))
      {z : ℝ × ℝ | z.1 ∈ Set.Icc Lu Hu ∧ z.2 ∈ Set.Icc Lv Hv} :=
    continuousOn_naturalGap hn4 hm0 hab habm hbam hκs hκ hε hd hadm hLu hHu hLv hHv
  -- zero-freeness of the natural-box gap map off the center
  have hadm0 : TrimAdm κs κ m A B ε d 0 := by
    have := hadm 0; simpa only [Set.Icc.coe_zero] using this
  have hGne : ∀ z : ℝ × ℝ, z.1 ∈ Set.Icc Lu Hu → z.2 ∈ Set.Icc Lv Hv →
      z ≠ 0 → closureGap (curvPath κs κ 0) (closingCellIcc m A B κs κ 0 z) ≠ 0 := by
    intro z hz1 hz2 hznz
    exact trimmedRectGap_natural_ne_zero hadm0 hrig hz1 hz2 hznz
  -- the box-radial boundary loop `γ_□`
  have hcont0 : Continuous (fun s : unitInterval =>
      closureGap (curvPath κs κ 0)
        (closingCellIcc m A B κs κ 0 (boxRadial Lu Hu Lv Hv (2 * Real.pi * ↑s)))) :=
    boxRadialLoop_continuous hLu hHu hLv hHv hGcont
  -- build `γ_□` with `toFun` INFERRED from `hcont0` (via `⟨_, hcont0⟩`) rather
  -- than re-elaborated: this avoids a `set`/`kabstract` defeq pass that
  -- whnf-diverges on the `boxRadial` subterm of the goal.
  let γ₀ : C(unitInterval, ℂ) := ⟨_, hcont0⟩
  have hγ₀ne : ∀ s, γ₀ s ≠ 0 := by
    intro s
    obtain ⟨h1, h2⟩ := boxRadial_mem hLu hHu hLv hHv (2 * Real.pi * ↑s)
    exact hGne _ h1 h2 (boxRadial_ne_zero hLu hHu hLv hHv (2 * Real.pi * ↑s))
  -- the small circle radius: `ρ'` from `closure_winding_t0`, kept inside the box
  -- and small enough to keep the perturbed chart values in the open window
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp
    (eventually_chartPerturb_mem hn4 m A B hκs)
  have hρB : 0 < boxInradius Lu Hu Lv Hv := boxInradius_pos hLu hHu hLv hHv
  obtain ⟨ρ', hρ'0, hρ'ρ0, γc, hγc_ne, hγc_eq, hγc_wind⟩ :=
    closure_winding_t0 hn4 hn ha hb hκs hκ hsym hL
      (lt_min hρB (half_pos hδ0)) (le_refl (0 : ℝ)) zero_le_one
  have hρ'B : ρ' ≤ boxInradius Lu Hu Lv Hv := hρ'ρ0.trans (min_le_left _ _)
  have hρ'δ : ρ' ≤ δ / 2 := hρ'ρ0.trans (min_le_right _ _)
  -- the perturbed chart values on the small circle stay in the open window
  have hmem_circle : ∀ s : unitInterval, ∀ j : ZMod n,
      chartPerturb m A B
        (ρ' * Real.cos (2 * Real.pi * ↑s), ρ' * Real.sin (2 * Real.pi * ↑s)) j ∈
        chartMap (curvPath κs κ 0 j) (curvPath κs κ 0 (j + 1)) ''
          Set.Ioo (0 : ℝ)
            (2 / max (curvPath κs κ 0 j) (curvPath κs κ 0 (j + 1))) := by
    intro s
    have hz : dist
        (ρ' * Real.cos (2 * Real.pi * ↑s), ρ' * Real.sin (2 * Real.pi * ↑s))
        (0 : ℝ × ℝ) < δ := by
      rw [dist_zero_right, Prod.norm_def]
      simp only [Real.norm_eq_abs]
      have hc : |ρ' * Real.cos (2 * Real.pi * ↑s)| ≤ ρ' := by
        rw [abs_mul, abs_of_pos hρ'0]
        nlinarith [Real.abs_cos_le_one (2 * Real.pi * (↑s : ℝ)),
          abs_nonneg (Real.cos (2 * Real.pi * (↑s : ℝ)))]
      have hsn : |ρ' * Real.sin (2 * Real.pi * ↑s)| ≤ ρ' := by
        rw [abs_mul, abs_of_pos hρ'0]
        nlinarith [Real.abs_sin_le_one (2 * Real.pi * (↑s : ℝ)),
          abs_nonneg (Real.sin (2 * Real.pi * (↑s : ℝ)))]
      have hmax := max_le hc hsn
      linarith
    simpa only [curvPath_zero] using hδ hz
  -- the small-circle loop is the natural-box gap map on the circle
  have hγ₁eq : ∀ s : unitInterval, γc s = closureGap (curvPath κs κ 0)
      (closingCellIcc m A B κs κ 0
        (ρ' * Real.cos (2 * Real.pi * ↑s), ρ' * Real.sin (2 * Real.pi * ↑s))) := by
    intro s
    rw [hγc_eq s]
    change closureGap (curvPath κs κ 0)
        (closingCell m A B hκs hκ (le_refl (0 : ℝ)) zero_le_one _)
      = closureGap (curvPath κs κ 0) (closingCellIcc m A B κs κ 0 _)
    rw [closingCellIcc_eq_closingCell m A B hκs hκ (le_refl (0 : ℝ)) zero_le_one
      (hmem_circle s)]
  -- transfer the winding from the small circle to the box-radial loop
  have hwind := boxRadial_winding_eq hLu hHu hLv hHv hGcont hGne hρ'0 hρ'B
    γ₀ γc hγ₀ne hγc_ne (fun s => rfl) hγ₁eq
  refine ⟨γ₀, hγ₀ne, fun s => rfl, ?_⟩
  rw [hwind, hγc_wind]

/-! ### The verdict-independent Route-3 core — certified degree continuation -/

/-- **Certified degree continuation** (blueprint `thm:certified_degree_continuation`,
verdict-independent Route-3 core). A moving box `[Lu τ, Hu τ] × [Lv τ, Hv τ]`
(origin interior for every `τ ∈ [0,1]`) carrying a gap family `G` that is
(i) continuous on its box at each fixed time, (ii) zero-free on the moving box
boundary `{boxGauge = 1}` for every time (**C1**), (iii) jointly continuous as a
boundary loop over `(time, loop-parameter)`, and whose (iv) `τ = 0` box-radial
boundary loop has nonzero winding about `0` (**C2**, supplied by
`trimmed_winding_t0`), has, for every `τ ∈ [0,1]`, an interior box zero of `G τ`
(`boxGauge z < 1 ∧ G τ z = 0`). The boundary winding is constant along the path
by homotopy invariance (`windingNumberC_eq_of_homotopy`, homotopy scaling time
`0 → τ`), hence nonzero for every `τ` by C2; the box→disk degree bridge
`exists_zero_of_boxRadial_winding` then produces the interior zero. Kept abstract
in the box/gap data so the deep `(time, box-point)` joint continuity of the
discrete chart enters only through `hjoint`; C1/C2 remain hypotheses, as intended
for this brick (their discharge is the deferred boundary-zero-free question). -/
theorem certified_degree_continuation
    {Lu Hu Lv Hv : ℝ → ℝ} {G : ℝ → ℝ × ℝ → ℂ}
    (hLu : ∀ τ : unitInterval, Lu ↑τ < 0) (hHu : ∀ τ : unitInterval, 0 < Hu ↑τ)
    (hLv : ∀ τ : unitInterval, Lv ↑τ < 0) (hHv : ∀ τ : unitInterval, 0 < Hv ↑τ)
    (hGcont : ∀ τ : unitInterval, ContinuousOn (G ↑τ)
      {z : ℝ × ℝ | z.1 ∈ Set.Icc (Lu ↑τ) (Hu ↑τ) ∧ z.2 ∈ Set.Icc (Lv ↑τ) (Hv ↑τ)})
    (hbd : ∀ τ : unitInterval, ∀ z : ℝ × ℝ,
      boxGauge (Lu ↑τ) (Hu ↑τ) (Lv ↑τ) (Hv ↑τ) z = 1 → G ↑τ z ≠ 0)
    (hjoint : Continuous (fun p : unitInterval × unitInterval =>
      G ↑p.1 (boxRadial (Lu ↑p.1) (Hu ↑p.1) (Lv ↑p.1) (Hv ↑p.1)
        (2 * Real.pi * ↑p.2))))
    (γ₀ : C(unitInterval, ℂ)) (hγ₀ : ∀ s, γ₀ s ≠ 0)
    (hγ₀eq : ∀ s : unitInterval,
      γ₀ s = G 0 (boxRadial (Lu 0) (Hu 0) (Lv 0) (Hv 0) (2 * Real.pi * ↑s)))
    (hw0 : windingNumberC γ₀ hγ₀ ≠ 0) :
    ∀ τ : unitInterval, ∃ z : ℝ × ℝ,
      boxGauge (Lu ↑τ) (Hu ↑τ) (Lv ↑τ) (Hv ↑τ) z < 1 ∧ G ↑τ z = 0 := by
  -- the moving boundary loop is nowhere zero (C1 + `boxGauge` is `1` on `∂B`)
  have hloop_ne : ∀ τ : unitInterval, ∀ θ : ℝ,
      G ↑τ (boxRadial (Lu ↑τ) (Hu ↑τ) (Lv ↑τ) (Hv ↑τ) θ) ≠ 0 := fun τ θ =>
    hbd τ _ (box_gauge_box_radial (hLu τ) (hHu τ) (hLv τ) (hHv τ) θ)
  intro τ
  -- the box-radial boundary loop at time `τ`, bundled as `C(I, ℂ)`
  have hγτcont : Continuous (fun s : unitInterval =>
      G ↑τ (boxRadial (Lu ↑τ) (Hu ↑τ) (Lv ↑τ) (Hv ↑τ) (2 * Real.pi * ↑s))) :=
    hjoint.comp (continuous_const.prodMk continuous_id)
  set γτ : C(unitInterval, ℂ) := ⟨_, hγτcont⟩ with hγτdef
  have hγτ : ∀ s, γτ s ≠ 0 := fun s => hloop_ne τ _
  -- winding of `γτ` equals winding of `γ₀` via the time-scaling homotopy `u ↦ u·τ`
  have hwind : windingNumberC γτ hγτ = windingNumberC γ₀ hγ₀ := by
    set p : unitInterval → unitInterval :=
      fun u => ⟨↑u * ↑τ, unitInterval.mul_mem u.2 τ.2⟩ with hpdef
    have hpcont : Continuous p :=
      Continuous.subtype_mk (continuous_subtype_val.mul continuous_const) _
    have hHcont : Continuous (fun q : unitInterval × unitInterval =>
        G ↑(p q.1) (boxRadial (Lu ↑(p q.1)) (Hu ↑(p q.1)) (Lv ↑(p q.1))
          (Hv ↑(p q.1)) (2 * Real.pi * ↑q.2))) :=
      hjoint.comp ((hpcont.comp continuous_fst).prodMk continuous_snd)
    set H : C(unitInterval × unitInterval, ℂ) := ⟨_, hHcont⟩ with hHdef
    have hHne : ∀ q, H q ≠ 0 := fun q => hloop_ne (p q.1) _
    have h0 : ∀ s : unitInterval, H (0, s) = γ₀ s := by
      intro s
      have hp0 : p 0 = (0 : unitInterval) := by
        apply Subtype.ext; simp [hpdef]
      change G ↑(p 0) (boxRadial (Lu ↑(p 0)) (Hu ↑(p 0)) (Lv ↑(p 0)) (Hv ↑(p 0))
          (2 * Real.pi * ↑s)) = γ₀ s
      rw [hp0, hγ₀eq s]
      norm_num
    have h1 : ∀ s : unitInterval, H (1, s) = γτ s := by
      intro s
      have hp1 : p 1 = τ := by
        apply Subtype.ext; simp [hpdef]
      change G ↑(p 1) (boxRadial (Lu ↑(p 1)) (Hu ↑(p 1)) (Lv ↑(p 1)) (Hv ↑(p 1))
          (2 * Real.pi * ↑s)) = γτ s
      rw [hp1]; rfl
    have hloopH : ∀ u : unitInterval, H (u, 0) = H (u, 1) := by
      intro u
      change G ↑(p u) (boxRadial (Lu ↑(p u)) (Hu ↑(p u)) (Lv ↑(p u)) (Hv ↑(p u))
          (2 * Real.pi * ↑(0 : unitInterval)))
        = G ↑(p u) (boxRadial (Lu ↑(p u)) (Hu ↑(p u)) (Lv ↑(p u)) (Hv ↑(p u))
          (2 * Real.pi * ↑(1 : unitInterval)))
      have e0 : (2 * Real.pi * ↑(0 : unitInterval) : ℝ) = 0 := by norm_num
      have e1 : (2 * Real.pi * ↑(1 : unitInterval) : ℝ) = 0 + 2 * Real.pi := by
        norm_num
      rw [e0, e1, boxRadial_periodic]
    exact (windingNumberC_eq_of_homotopy γ₀ γτ hγ₀ hγτ H hHne h0 h1 hloopH).symm
  have hwτ : windingNumberC γτ hγτ ≠ 0 := by rw [hwind]; exact hw0
  exact exists_zero_of_boxRadial_winding (hLu τ) (hHu τ) (hLv τ) (hHv τ)
    (hGcont τ) (hbd τ) γτ hγτ (fun s => rfl) hwτ

/-! ## Project-local Mathlib supplement — abstract Rouché-composition closure spine -/

/-- **Rouché-once closure spine** (blueprint `thm:rouche_closes`, `sec:closure_rouche`).
Given a box `B` with the origin interior (`Lu < 0 < Hu`, `Lv < 0 < Hv`) and two continuous
maps `Gm, Gt` on `B̄` whose box-radial boundary loops are `γm, γt`, if the model loop `γm`
is nowhere zero with winding `≠ 0` about the origin and the Rouché inequality
`‖Gt z − Gm z‖ < ‖Gm z‖` holds at every boundary point (`boxGauge = 1`), then `Gt` has a
zero in the open interior of `B`.  This is the Rouché analogue of
`certified_degree_continuation`: the model margin and the perturbation bound enter as
hypotheses, so the lemma is verdict- and `D7`-independent — the abstract spine of the
pivoted closing route.  It is a pure composition of `windingNumberC_eq_of_perturb` (the
straight-line homotopy stays zero-free by the reverse triangle inequality) and
`exists_zero_of_boxRadial_winding` (nonzero boundary winding ⇒ interior zero via the box
gauge). -/
theorem rouche_closes {Lu Hu Lv Hv : ℝ}
    (hLu : Lu < 0) (hHu : 0 < Hu) (hLv : Lv < 0) (hHv : 0 < Hv)
    {Gm Gt : ℝ × ℝ → ℂ}
    (hGtcont : ContinuousOn Gt
      {z : ℝ × ℝ | z.1 ∈ Set.Icc Lu Hu ∧ z.2 ∈ Set.Icc Lv Hv})
    (γm γt : C(unitInterval, ℂ))
    (hγm : ∀ s, γm s ≠ 0)
    (hγm_eq : ∀ s : unitInterval,
      γm s = Gm (boxRadial Lu Hu Lv Hv (2 * Real.pi * ↑s)))
    (hγt_eq : ∀ s : unitInterval,
      γt s = Gt (boxRadial Lu Hu Lv Hv (2 * Real.pi * ↑s)))
    (hwm : windingNumberC γm hγm ≠ 0)
    (hbd : ∀ z : ℝ × ℝ, boxGauge Lu Hu Lv Hv z = 1 →
      ‖Gt z - Gm z‖ < ‖Gm z‖) :
    ∃ z : ℝ × ℝ, boxGauge Lu Hu Lv Hv z < 1 ∧ Gt z = 0 := by
  -- Rouché inequality along the box-radial loops (each loop point has `boxGauge = 1`)
  have hpert : ∀ s : unitInterval, ‖γt s - γm s‖ < ‖γm s‖ := by
    intro s
    rw [hγt_eq s, hγm_eq s]
    exact hbd _ (box_gauge_box_radial hLu hHu hLv hHv (2 * Real.pi * ↑s))
  -- the true loop is nowhere zero (reverse triangle inequality)
  have hγt : ∀ s, γt s ≠ 0 := by
    intro s
    have htri : ‖γm s‖ - ‖γt s‖ ≤ ‖γt s - γm s‖ := by
      have := norm_sub_norm_le (γm s) (γt s)
      rwa [norm_sub_rev] at this
    have hpos : 0 < ‖γt s‖ := by have := hpert s; linarith
    exact norm_pos_iff.1 hpos
  -- boundary loops close (`boxRadial` is `2π`-periodic)
  have e0 : (2 * Real.pi * ↑(0 : unitInterval) : ℝ) = 0 := by norm_num
  have e1 : (2 * Real.pi * ↑(1 : unitInterval) : ℝ) = 0 + 2 * Real.pi := by norm_num
  have hloopm : γm 0 = γm 1 := by
    rw [hγm_eq 0, hγm_eq 1, e0, e1, boxRadial_periodic]
  have hloopt : γt 0 = γt 1 := by
    rw [hγt_eq 0, hγt_eq 1, e0, e1, boxRadial_periodic]
  -- equal winding via the straight-line Rouché homotopy
  have hwind : windingNumberC γm hγm = windingNumberC γt hγt :=
    windingNumberC_eq_of_perturb γm γt hγm hγt hloopm hloopt hpert
  have hwt : windingNumberC γt hγt ≠ 0 := by rw [← hwind]; exact hwm
  -- the true map is nonzero on the box boundary (reverse triangle from Rouché)
  have hGtbd : ∀ z : ℝ × ℝ, boxGauge Lu Hu Lv Hv z = 1 → Gt z ≠ 0 := by
    intro z hz
    have htri : ‖Gm z‖ - ‖Gt z‖ ≤ ‖Gt z - Gm z‖ := by
      have := norm_sub_norm_le (Gm z) (Gt z)
      rwa [norm_sub_rev] at this
    have hpos : 0 < ‖Gt z‖ := by have := hbd z hz; linarith
    exact norm_pos_iff.1 hpos
  exact exists_zero_of_boxRadial_winding hLu hHu hLv hHv hGtcont hGtbd γt hγt hγt_eq hwt

/- USER (2026-07-16, from discuss): scaffolding `def:four_bar_anchor` here.
   Two constraints the blueprint prose does not make explicit:

   1. RECENTER. `rouche_closes` uses an origin-interior box (Lu<0<Hu, Lv<0<Hv)
      and concludes a zero with `boxGauge < 1` — i.e. INSIDE an origin-centered
      box. The four-bar core sits at the true angles (Φ₁*, Φ₃*), not at (0,0).
      Parameterize `fourBarAnchor` by DISPLACEMENT from the core:
      Φ₁ = Φ₁* + z.1, Φ₃ = Φ₃* + z.2 (carry Φ₁*, Φ₃* as parameters), so the
      zero lands at the origin and a small [-δ,δ]² box is the disk D. The naive
      `Φ₁ z = z.1` puts the zero at the true angle and rouche_closes will not apply.

   2. DFV BRANCH ONLY. State the Step-1 quadrilateral inequality on `DFV κ c`
      (+ 0 < c), NOT on `DiscreteFourVertexPos` — the const branch has no window
      and is already handled by `realizesMenger_of_const`. Cleanest: prove the
      pure inequality on four reals s₁ s₂ ℓ₁ ℓ₂ with a separating threshold, then
      a thin DFV adapter. The window gives a SINGLE threshold 1/c with
      s₁,s₂ < 1/c < ℓ₁,ℓ₂ (radii ρ = 1/κ): use
      `one_div_lt_one_div_of_lt` per value, then `linarith`. -/

/-! ## Project-local Mathlib supplement — the four-bar anchor bricks -/

/-- **Four-bar anchor closure-gap map — recentered at the core** (blueprint
`def:four_bar_anchor`, `sec:closure_rouche`).  Given the four block radii
`ρ j = 1/κ_{i_j}` of a positive DFV window and core junction angles
`Φ₁ Φ₂ Φ₃` (with `Φ₀ = 0` and `Φ₄ = 2π` fixed), the block-level closure gap
parameterized by the **displacement** `z = (z₁, z₂)` from the core:

  `E_model z = (1/i)·[(ρ₀−ρ₁)e^{i(Φ₁+z₁)} + (ρ₁−ρ₂)e^{iΦ₂}
                      + (ρ₂−ρ₃)e^{i(Φ₃+z₂)} + (ρ₃−ρ₀)e^{2πi}]`.

Recentring is binding (USER 2026-07-16): `rouche_closes` consumes an
origin-interior box and concludes a zero with `boxGauge < 1`, while the
four-bar core sits at the true angles `(Φ₁, Φ₃)`; carrying the core angles as
parameters puts the core zero at `z = 0`, so a small square `[-δ,δ]²` is the
Rouché disk `D`.  The naive `Φ₁ z = z₁` parameterization would place the zero
at the true angle, where `rouche_closes` does not apply. -/
noncomputable def fourBarAnchor (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ) (z : ℝ × ℝ) : ℂ :=
  1 / Complex.I *
    (((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I)
      + ((ρ 1 - ρ 2 : ℝ) : ℂ) * Complex.exp ((Φ₂ : ℂ) * Complex.I)
      + ((ρ 2 - ρ 3 : ℝ) : ℂ) * Complex.exp (((Φ₃ + z.2 : ℝ) : ℂ) * Complex.I)
      + ((ρ 3 - ρ 0 : ℝ) : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I))

/-- The four-bar anchor is continuous in the displacement — the model-side
regularity input consumed (as `ContinuousOn`) by `rouche_closes`. -/
theorem continuous_fourBarAnchor (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ) :
    Continuous (fourBarAnchor ρ Φ₁ Φ₂ Φ₃) := by
  unfold fourBarAnchor
  fun_prop

/-- At the displacement origin the anchor is the four-bar closure equation at
the core angles (the `e^{2πi}` factor collapses to `1`): the core condition
`fourBarAnchor ρ Φ₁ Φ₂ Φ₃ 0 = 0` is exactly
`(ρ₀−ρ₁)e^{iΦ₁} + (ρ₁−ρ₂)e^{iΦ₂} + (ρ₂−ρ₃)e^{iΦ₃} + (ρ₃−ρ₀) = 0`. -/
theorem fourBarAnchor_zero (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ) :
    fourBarAnchor ρ Φ₁ Φ₂ Φ₃ 0 =
      1 / Complex.I *
        (((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp ((Φ₁ : ℂ) * Complex.I)
          + ((ρ 1 - ρ 2 : ℝ) : ℂ) * Complex.exp ((Φ₂ : ℂ) * Complex.I)
          + ((ρ 2 - ρ 3 : ℝ) : ℂ) * Complex.exp ((Φ₃ : ℂ) * Complex.I)
          + ((ρ 3 - ρ 0 : ℝ) : ℂ)) := by
  simp [fourBarAnchor]

/-- **Strict four-bar quadrilateral inequality — pure form** (blueprint
`lem:four_bar_quad_strict`).  Project-local: pure ordered-field arithmetic on
five reals with a separating threshold `s₁, s₂ < T < ℓ₁, ℓ₂`.  The four cyclic
sides `c₁ = ℓ₁−s₁`, `c₂ = ℓ₁−s₂`, `c₃ = ℓ₂−s₂`, `c₄ = ℓ₂−s₁` are all positive,
each slack `(∑ other three) − cⱼ` equals twice an explicit
(large value − small value) gap, and each side is strictly less than the sum
of the other three.  The slack identities are stated explicitly because the
model-margin lemma reuses them quantitatively. -/
theorem fourBar_quad_strict {s₁ s₂ ℓ₁ ℓ₂ T : ℝ}
    (hs₁ : s₁ < T) (hs₂ : s₂ < T) (hℓ₁ : T < ℓ₁) (hℓ₂ : T < ℓ₂) :
    (0 < ℓ₁ - s₁ ∧ 0 < ℓ₁ - s₂ ∧ 0 < ℓ₂ - s₂ ∧ 0 < ℓ₂ - s₁) ∧
    ((ℓ₁ - s₂) + (ℓ₂ - s₂) + (ℓ₂ - s₁) - (ℓ₁ - s₁) = 2 * (ℓ₂ - s₂) ∧
      (ℓ₁ - s₁) + (ℓ₂ - s₂) + (ℓ₂ - s₁) - (ℓ₁ - s₂) = 2 * (ℓ₂ - s₁) ∧
      (ℓ₁ - s₁) + (ℓ₁ - s₂) + (ℓ₂ - s₁) - (ℓ₂ - s₂) = 2 * (ℓ₁ - s₁) ∧
      (ℓ₁ - s₁) + (ℓ₁ - s₂) + (ℓ₂ - s₂) - (ℓ₂ - s₁) = 2 * (ℓ₁ - s₂)) ∧
    (ℓ₁ - s₁ < (ℓ₁ - s₂) + (ℓ₂ - s₂) + (ℓ₂ - s₁) ∧
      ℓ₁ - s₂ < (ℓ₁ - s₁) + (ℓ₂ - s₂) + (ℓ₂ - s₁) ∧
      ℓ₂ - s₂ < (ℓ₁ - s₁) + (ℓ₁ - s₂) + (ℓ₂ - s₁) ∧
      ℓ₂ - s₁ < (ℓ₁ - s₁) + (ℓ₁ - s₂) + (ℓ₂ - s₂)) :=
  ⟨⟨by linarith, by linarith, by linarith, by linarith⟩,
    ⟨by ring, by ring, by ring, by ring⟩,
    ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

/-- **DFV window radii satisfy the strict quadrilateral inequality — thin
adapter** (blueprint `lem:dfv_radii_quad`).  On the `DFV` branch only (window
level `0 < c`, all values positive): the block radii `ρⱼ = 1/κ_{iⱼ}` separate
across the single threshold `1/c` (reciprocal is strictly antitone on
`(0,∞)`), so with `s₁ = ρ₁, ℓ₁ = ρ₂, s₂ = ρ₃, ℓ₂ = ρ₄` the four sides
`ρ₂−ρ₁, ρ₂−ρ₃, ρ₄−ρ₃, ρ₄−ρ₁` are positive and satisfy the strict
quadrilateral inequality of `fourBar_quad_strict`.  The constant branch of
`DiscreteFourVertexPos` has no window and is already handled by
`realizesMenger_of_const`. -/
theorem dfv_fourBar_quad {κ : ZMod n → ℝ} {c : ℝ} (hc : 0 < c)
    (hpos : ∀ i, 0 < κ i) (h : DFV κ c) :
    ∃ i₁ i₂ i₃ i₄ : ℕ, i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n ∧
      (1 / κ ((i₁ : ℕ) : ZMod n) < 1 / c ∧ 1 / c < 1 / κ ((i₂ : ℕ) : ZMod n) ∧
        1 / κ ((i₃ : ℕ) : ZMod n) < 1 / c ∧ 1 / c < 1 / κ ((i₄ : ℕ) : ZMod n)) ∧
      (0 < 1 / κ ((i₂ : ℕ) : ZMod n) - 1 / κ ((i₁ : ℕ) : ZMod n) ∧
        0 < 1 / κ ((i₂ : ℕ) : ZMod n) - 1 / κ ((i₃ : ℕ) : ZMod n) ∧
        0 < 1 / κ ((i₄ : ℕ) : ZMod n) - 1 / κ ((i₃ : ℕ) : ZMod n) ∧
        0 < 1 / κ ((i₄ : ℕ) : ZMod n) - 1 / κ ((i₁ : ℕ) : ZMod n)) ∧
      (1 / κ ((i₂ : ℕ) : ZMod n) - 1 / κ ((i₁ : ℕ) : ZMod n) <
          (1 / κ ((i₂ : ℕ) : ZMod n) - 1 / κ ((i₃ : ℕ) : ZMod n))
            + (1 / κ ((i₄ : ℕ) : ZMod n) - 1 / κ ((i₃ : ℕ) : ZMod n))
            + (1 / κ ((i₄ : ℕ) : ZMod n) - 1 / κ ((i₁ : ℕ) : ZMod n)) ∧
        1 / κ ((i₂ : ℕ) : ZMod n) - 1 / κ ((i₃ : ℕ) : ZMod n) <
          (1 / κ ((i₂ : ℕ) : ZMod n) - 1 / κ ((i₁ : ℕ) : ZMod n))
            + (1 / κ ((i₄ : ℕ) : ZMod n) - 1 / κ ((i₃ : ℕ) : ZMod n))
            + (1 / κ ((i₄ : ℕ) : ZMod n) - 1 / κ ((i₁ : ℕ) : ZMod n)) ∧
        1 / κ ((i₄ : ℕ) : ZMod n) - 1 / κ ((i₃ : ℕ) : ZMod n) <
          (1 / κ ((i₂ : ℕ) : ZMod n) - 1 / κ ((i₁ : ℕ) : ZMod n))
            + (1 / κ ((i₂ : ℕ) : ZMod n) - 1 / κ ((i₃ : ℕ) : ZMod n))
            + (1 / κ ((i₄ : ℕ) : ZMod n) - 1 / κ ((i₁ : ℕ) : ZMod n)) ∧
        1 / κ ((i₄ : ℕ) : ZMod n) - 1 / κ ((i₁ : ℕ) : ZMod n) <
          (1 / κ ((i₂ : ℕ) : ZMod n) - 1 / κ ((i₁ : ℕ) : ZMod n))
            + (1 / κ ((i₂ : ℕ) : ZMod n) - 1 / κ ((i₃ : ℕ) : ZMod n))
            + (1 / κ ((i₄ : ℕ) : ZMod n) - 1 / κ ((i₃ : ℕ) : ZMod n))) := by
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, hκ1, hκ2, hκ3, hκ4⟩ := h
  have r1 : 1 / κ ((i₁ : ℕ) : ZMod n) < 1 / c := one_div_lt_one_div_of_lt hc hκ1
  have r2 : 1 / c < 1 / κ ((i₂ : ℕ) : ZMod n) := one_div_lt_one_div_of_lt (hpos _) hκ2
  have r3 : 1 / κ ((i₃ : ℕ) : ZMod n) < 1 / c := one_div_lt_one_div_of_lt hc hκ3
  have r4 : 1 / c < 1 / κ ((i₄ : ℕ) : ZMod n) := one_div_lt_one_div_of_lt (hpos _) hκ4
  obtain ⟨hsides, -, hquad⟩ := fourBar_quad_strict r1 r3 r2 r4
  exact ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, ⟨r1, r2, r3, r4⟩, hsides, hquad⟩

/-- The displacement derivative of the four-bar anchor at `z`: the continuous
`ℝ`-linear map `h ↦ (ρ₀−ρ₁)e^{i(Φ₁+z₁)}·h₁ + (ρ₂−ρ₃)e^{i(Φ₃+z₂)}·h₂`
(DGPV Prop 15.2 — the `1/i` prefactor cancels the chain-rule factor `i`).
Its two columns are the Jacobian columns of the model-margin transversality
argument. -/
noncomputable def fourBarAnchorDeriv (ρ : Fin 4 → ℝ) (Φ₁ Φ₃ : ℝ) (z : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℂ :=
  (((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I)) •
      Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)
    + (((ρ 2 - ρ 3 : ℝ) : ℂ) * Complex.exp (((Φ₃ + z.2 : ℝ) : ℂ) * Complex.I)) •
      Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem fourBarAnchorDeriv_apply (ρ : Fin 4 → ℝ) (Φ₁ Φ₃ : ℝ)
    (z h : ℝ × ℝ) :
    fourBarAnchorDeriv ρ Φ₁ Φ₃ z h =
      ((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I)
          * (h.1 : ℂ)
        + ((ρ 2 - ρ 3 : ℝ) : ℂ) * Complex.exp (((Φ₃ + z.2 : ℝ) : ℂ) * Complex.I)
          * (h.2 : ℂ) := by
  simp [fourBarAnchorDeriv, smul_eq_mul]

/-- **Strict differentiability of the four-bar anchor** (DGPV Prop 15.2,
displacement form): at every displacement `z` the anchor has strict Fréchet
derivative `fourBarAnchorDeriv ρ Φ₁ Φ₃ z` — chain rule through `exp(i·)` on
the two displaced slots, the two pinned slots being constant. -/
theorem hasStrictFDerivAt_fourBarAnchor (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ)
    (z : ℝ × ℝ) :
    HasStrictFDerivAt (fourBarAnchor ρ Φ₁ Φ₂ Φ₃)
      (fourBarAnchorDeriv ρ Φ₁ Φ₃ z) z := by
  -- slot 1: `w ↦ (ρ₀−ρ₁)·exp(i(Φ₁+w₁))`
  have h1 : HasStrictFDerivAt (fun w : ℝ × ℝ => (Φ₁ + w.1 : ℝ))
      (ContinuousLinearMap.fst ℝ ℝ ℝ) z := hasStrictFDerivAt_fst.const_add Φ₁
  have h1C : HasStrictFDerivAt (fun w : ℝ × ℝ => ((Φ₁ + w.1 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) z :=
    Complex.ofRealCLM.hasStrictFDerivAt.comp z h1
  have h1I := h1C.mul_const Complex.I
  have hexp1 : HasStrictDerivAt Complex.exp
      (Complex.exp (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I))
      (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I) := Complex.hasStrictDerivAt_exp _
  have hd1 := hexp1.comp_hasStrictFDerivAt z h1I
  have hT1 := hd1.const_mul (((ρ 0 - ρ 1 : ℝ) : ℂ))
  -- slot 3: `w ↦ (ρ₂−ρ₃)·exp(i(Φ₃+w₂))`
  have h3 : HasStrictFDerivAt (fun w : ℝ × ℝ => (Φ₃ + w.2 : ℝ))
      (ContinuousLinearMap.snd ℝ ℝ ℝ) z := hasStrictFDerivAt_snd.const_add Φ₃
  have h3C : HasStrictFDerivAt (fun w : ℝ × ℝ => ((Φ₃ + w.2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
    Complex.ofRealCLM.hasStrictFDerivAt.comp z h3
  have h3I := h3C.mul_const Complex.I
  have hexp3 : HasStrictDerivAt Complex.exp
      (Complex.exp (((Φ₃ + z.2 : ℝ) : ℂ) * Complex.I))
      (((Φ₃ + z.2 : ℝ) : ℂ) * Complex.I) := Complex.hasStrictDerivAt_exp _
  have hd3 := hexp3.comp_hasStrictFDerivAt z h3I
  have hT3 := hd3.const_mul (((ρ 2 - ρ 3 : ℝ) : ℂ))
  -- assemble: constants in slots 2 and 4, then the `1/i` prefactor
  have hsum := ((hT1.add_const
      (((ρ 1 - ρ 2 : ℝ) : ℂ) * Complex.exp ((Φ₂ : ℂ) * Complex.I))).add
    hT3).add_const
      (((ρ 3 - ρ 0 : ℝ) : ℂ)
        * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I))
  have hf := hsum.const_mul (1 / Complex.I)
  refine HasStrictFDerivAt.congr_fderiv hf ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [fourBarAnchorDeriv, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  field_simp

/-- Two complex columns with nonzero real `2×2` determinant
`A.re·B.im − A.im·B.re = Im(conj A · B)` span `ℝ²`: the real-linear map
`v ↦ A·v₁ + B·v₂` is injective.  Cramer core of the four-bar transversality. -/
private lemma injective_columns_of_det_ne_zero {A B : ℂ}
    (h : A.re * B.im - A.im * B.re ≠ 0) :
    Function.Injective fun v : ℝ × ℝ => A * (v.1 : ℂ) + B * (v.2 : ℂ) := by
  intro v w hvw
  simp only at hvw
  have hre := congrArg Complex.re hvw
  have him := congrArg Complex.im hvw
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre him
  have key1 : (A.re * B.im - A.im * B.re) * (v.1 - w.1) = 0 := by
    linear_combination B.im * hre - B.re * him
  have key2 : (A.re * B.im - A.im * B.re) * (v.2 - w.2) = 0 := by
    linear_combination A.re * him - A.im * hre
  have h1 : v.1 = w.1 := by
    rcases mul_eq_zero.mp key1 with h' | h'
    · exact absurd h' h
    · linarith [sub_eq_zero.mp h']
  have h2 : v.2 = w.2 := by
    rcases mul_eq_zero.mp key2 with h' | h'
    · exact absurd h' h
    · linarith [sub_eq_zero.mp h']
  exact Prod.ext h1 h2

/-- **Transversality of the four-bar anchor derivative** (DGPV Prop 15.2,
Step 3 of `lem:model_margin`): the Jacobian columns `(ρ₀−ρ₁)e^{i(Φ₁+z₁)}` and
`(ρ₂−ρ₃)e^{i(Φ₃+z₂)}` are `ℝ`-independent — the derivative is injective — as
soon as both side coefficients are nonzero and the displaced angles are not
parallel mod `π` (`sin((Φ₃+z₂)−(Φ₁+z₁)) ≠ 0`): the determinant is
`(ρ₀−ρ₁)(ρ₂−ρ₃)·sin((Φ₃+z₂)−(Φ₁+z₁))`. -/
theorem fourBarAnchorDeriv_injective (ρ : Fin 4 → ℝ) (Φ₁ Φ₃ : ℝ) (z : ℝ × ℝ)
    (h01 : ρ 0 ≠ ρ 1) (h23 : ρ 2 ≠ ρ 3)
    (hsin : Real.sin ((Φ₃ + z.2) - (Φ₁ + z.1)) ≠ 0) :
    Function.Injective (fourBarAnchorDeriv ρ Φ₁ Φ₃ z) := by
  set A : ℂ :=
    ((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I) with hA
  set B : ℂ :=
    ((ρ 2 - ρ 3 : ℝ) : ℂ) * Complex.exp (((Φ₃ + z.2 : ℝ) : ℂ) * Complex.I) with hB
  have hdet : A.re * B.im - A.im * B.re
      = (ρ 0 - ρ 1) * (ρ 2 - ρ 3)
        * Real.sin ((Φ₃ + z.2) - (Φ₁ + z.1)) := by
    simp only [hA, hB, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Real.sin_sub, zero_mul, sub_zero, add_zero]
    ring
  have hne : A.re * B.im - A.im * B.re ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero
      (mul_ne_zero (sub_ne_zero.2 h01) (sub_ne_zero.2 h23)) hsin
  have heq : ⇑(fourBarAnchorDeriv ρ Φ₁ Φ₃ z)
      = fun v : ℝ × ℝ => A * (v.1 : ℂ) + B * (v.2 : ℂ) := by
    funext v
    rw [fourBarAnchorDeriv_apply, hA, hB]
  rw [heq]
  exact injective_columns_of_det_ne_zero hne

/-- The transverse four-bar anchor derivative is a continuous linear
**equivalence** `ℝ² ≃L ℂ` (injective + equal finite rank ⇒ bijective) — the
form the inverse-function machinery consumes. -/
theorem fourBarAnchorDeriv_exists_equiv (ρ : Fin 4 → ℝ) (Φ₁ Φ₃ : ℝ)
    (z : ℝ × ℝ) (h01 : ρ 0 ≠ ρ 1) (h23 : ρ 2 ≠ ρ 3)
    (hsin : Real.sin ((Φ₃ + z.2) - (Φ₁ + z.1)) ≠ 0) :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] ℂ,
      (e : (ℝ × ℝ) →L[ℝ] ℂ) = fourBarAnchorDeriv ρ Φ₁ Φ₃ z := by
  have hinj : Function.Injective
      ((fourBarAnchorDeriv ρ Φ₁ Φ₃ z) : (ℝ × ℝ) →ₗ[ℝ] ℂ) :=
    fourBarAnchorDeriv_injective ρ Φ₁ Φ₃ z h01 h23 hsin
  have hrank : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ ℂ := by
    rw [Module.finrank_eq_card_basis Complex.basisOneI]
    simp
  have hsurj : Function.Surjective
      ((fourBarAnchorDeriv ρ Φ₁ Φ₃ z) : (ℝ × ℝ) →ₗ[ℝ] ℂ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  refine ⟨(LinearEquiv.ofBijective
      ((fourBarAnchorDeriv ρ Φ₁ Φ₃ z) : (ℝ × ℝ) →ₗ[ℝ] ℂ)
      ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  exact ContinuousLinearMap.ext fun v => rfl

/-- **Transverse core zero of the four-bar anchor is isolated** (Step 3 of
`lem:model_margin`, isolation half): at a transverse displacement `z₀`
(nonzero side coefficients, displaced angles nonparallel mod `π`) the anchor
is locally injective, so on a punctured neighborhood of `z₀` it never returns
to its value at `z₀`.  With `fourBarAnchor ρ Φ₁ Φ₂ Φ₃ z₀ = 0` this makes the
core zero isolated — the qualitative content behind the positive Rouché
margin `m(κ) = min_{∂D} ‖E_model‖ > 0` on a small box boundary. -/
theorem fourBarAnchor_isolated_zero (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ)
    (z₀ : ℝ × ℝ) (h01 : ρ 0 ≠ ρ 1) (h23 : ρ 2 ≠ ρ 3)
    (hsin : Real.sin ((Φ₃ + z₀.2) - (Φ₁ + z₀.1)) ≠ 0) :
    ∀ᶠ w in nhdsWithin z₀ {z₀}ᶜ,
      fourBarAnchor ρ Φ₁ Φ₂ Φ₃ w ≠ fourBarAnchor ρ Φ₁ Φ₂ Φ₃ z₀ := by
  obtain ⟨e, he⟩ := fourBarAnchorDeriv_exists_equiv ρ Φ₁ Φ₃ z₀ h01 h23 hsin
  have hf : HasStrictFDerivAt (fourBarAnchor ρ Φ₁ Φ₂ Φ₃)
      (e : (ℝ × ℝ) →L[ℝ] ℂ) z₀ := by
    rw [he]; exact hasStrictFDerivAt_fourBarAnchor ρ Φ₁ Φ₂ Φ₃ z₀
  have hlinv := HasStrictFDerivAt.eventually_left_inverse hf
  have himg := HasStrictFDerivAt.localInverse_apply_image hf
  filter_upwards [nhdsWithin_le_nhds hlinv, self_mem_nhdsWithin] with w hw hne
  intro hcontra
  exact hne (by rw [← hw, hcontra, himg]; exact Set.mem_singleton z₀)

/-- **Positive Rouché margin of the transverse four-bar core on small box
boundaries** (`lem:model_margin`, margin half — the `m(κ) > 0` packaging):
if the recentered anchor has a transverse core zero at the displacement
origin (`E_model(0) = 0`, nonzero side coefficients, core angles nonparallel
mod `π`), then there is `δ₀ > 0` such that on **every** origin-centered square
of half-side `δ ≤ δ₀` the anchor is bounded below by a positive margin `m` on
the box boundary `{boxGauge = 1}` — exactly the model-side inputs of
`rouche_closes` (`hγm` nowhere-zero via `box_gauge_box_radial`, and the strict
majorant for the Rouché inequality `‖E_true − E_model‖ < m ≤ ‖E_model‖`).
The `δ`-quantifier is universal below `δ₀` so the box can later be shrunk to
fit the `ε`-collapse geometry after `κ` is fixed — the per-`κ` (non-uniform)
margin the pivoted route needs. -/
theorem fourBarAnchor_boundary_margin (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ)
    (h01 : ρ 0 ≠ ρ 1) (h23 : ρ 2 ≠ ρ 3)
    (hsin : Real.sin (Φ₃ - Φ₁) ≠ 0)
    (hzero : fourBarAnchor ρ Φ₁ Φ₂ Φ₃ 0 = 0) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ m > 0, ∀ z : ℝ × ℝ, boxGauge (-δ) δ (-δ) δ z = 1 →
        m ≤ ‖fourBarAnchor ρ Φ₁ Φ₂ Φ₃ z‖ := by
  have hsin' : Real.sin ((Φ₃ + (0 : ℝ × ℝ).2) - (Φ₁ + (0 : ℝ × ℝ).1)) ≠ 0 := by
    simpa using hsin
  have hev := fourBarAnchor_isolated_zero ρ Φ₁ Φ₂ Φ₃ 0 h01 h23 hsin'
  rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, by positivity, fun δ hδ hδε => ?_⟩
  have hLu : -δ < 0 := neg_lt_zero.2 hδ
  set S : Set (ℝ × ℝ) := {z | boxGauge (-δ) δ (-δ) δ z = 1} with hS
  have hSclosed : IsClosed S :=
    isClosed_eq (continuous_boxGauge _ _ _ _) continuous_const
  have hnorm : ∀ z ∈ S, ‖z‖ ≤ δ := by
    intro z hz
    have hb := norm_le_boxOuter_mul_boxGauge hLu hδ hLu hδ z
    rw [show boxGauge (-δ) δ (-δ) δ z = 1 from hz] at hb
    simpa [neg_neg, max_self] using hb
  have hSsub : S ⊆ Metric.closedBall 0 δ := fun z hz => by
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm z hz
  have hScompact : IsCompact S :=
    (isCompact_closedBall (0 : ℝ × ℝ) δ).of_isClosed_subset hSclosed hSsub
  have hfne : ∀ z ∈ S, fourBarAnchor ρ Φ₁ Φ₂ Φ₃ z ≠ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h0
      have h1 : boxGauge (-δ) δ (-δ) δ z = 1 := hz
      rw [h0] at h1
      simp [boxGauge, gaugeCoord] at h1
    have hdist : dist z 0 < ε := by
      rw [dist_zero_right]
      calc ‖z‖ ≤ δ := hnorm z hz
        _ ≤ ε / 2 := hδε
        _ < ε := by linarith
    have hne0 := hball ⟨Metric.mem_ball.2 hdist, hz0⟩
    simpa [hzero] using hne0
  rcases S.eq_empty_or_nonempty with hempty | hne
  · exact ⟨1, one_pos, fun z hz =>
      absurd (show z ∈ S from hz) (by simp [hempty])⟩
  · obtain ⟨z₀, hz₀S, hmin⟩ := hScompact.exists_isMinOn hne
      ((continuous_fourBarAnchor ρ Φ₁ Φ₂ Φ₃).norm.continuousOn)
    exact ⟨‖fourBarAnchor ρ Φ₁ Φ₂ Φ₃ z₀‖,
      norm_pos_iff.2 (hfne z₀ hz₀S), fun z hz => (isMinOn_iff.mp hmin) z hz⟩

/-! ## Project-local Mathlib supplement — the adjacent displacement slice
(`def:four_bar_anchor_adj`, iter-101 — the critical path)

The iter-100 `(1,3)` slice displaces a *non-consecutive* junction pair; its
Jacobian determinant `∝ sin(Φ₃−Φ₁)` degenerates on the parallelogram stratum
and at near-trapezoid cores.  The source (`notes/plans/discrete_plan.md` §5.1 item 3:
"consecutive junctions give independent directions") prescribes the
*adjacent* pair: displacing junctions `1, 2` (junction `3` pinned) gives
determinant `(ρ₀−ρ₁)(ρ₁−ρ₂)·sin(Φ₂−Φ₁) = −c₁c₂·sin(Φ₂−Φ₁) ≠ 0` at *every*
strictly convex core, since adjacent heading gaps lie in `(0,π)`.  The
`(1,3)` chain above is retained as proved material and is the verbatim proof
template for this chain. -/

/-- **Four-bar anchor — adjacent displacement slice** (blueprint
`def:four_bar_anchor_adj`, `sec:closure_rouche`).  Same data as
`fourBarAnchor` (block radii `ρ`, core junction angles `Φ₁ Φ₂ Φ₃`), but the
two displacement variables enter through the **consecutive** junctions `1, 2`
with junction `3` pinned:

  `E_adj z = (1/i)·[(ρ₀−ρ₁)e^{i(Φ₁+z₁)} + (ρ₁−ρ₂)e^{i(Φ₂+z₂)}
                    + (ρ₂−ρ₃)e^{iΦ₃} + (ρ₃−ρ₀)e^{2πi}]`.

Recentring is exactly as in `fourBarAnchor` (binding, USER 2026-07-16): the
core zero sits at `z = 0` and a small square `[−δ,δ]²` is the Rouché disk.
Pointwise `fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z = fourBarAnchor ρ Φ₁ (Φ₂ + z.2) Φ₃
(z.1, 0)` (`fourBarAnchorAdj_eq_fourBarAnchor`). -/
noncomputable def fourBarAnchorAdj (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ)
    (z : ℝ × ℝ) : ℂ :=
  1 / Complex.I *
    (((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I)
      + ((ρ 1 - ρ 2 : ℝ) : ℂ) * Complex.exp (((Φ₂ + z.2 : ℝ) : ℂ) * Complex.I)
      + ((ρ 2 - ρ 3 : ℝ) : ℂ) * Complex.exp ((Φ₃ : ℂ) * Complex.I)
      + ((ρ 3 - ρ 0 : ℝ) : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I))

/-- The adjacent-slice anchor is pointwise the `(1,3)`-slice anchor with the
pinned middle angle displaced: `E_adj(z) = E_{(1,3)}` at core angles
`Φ₁, Φ₂ + z₂, Φ₃` evaluated at displacement `(z₁, 0)`. -/
theorem fourBarAnchorAdj_eq_fourBarAnchor (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ)
    (z : ℝ × ℝ) :
    fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z
      = fourBarAnchor ρ Φ₁ (Φ₂ + z.2) Φ₃ ((z.1, 0) : ℝ × ℝ) := by
  simp [fourBarAnchorAdj, fourBarAnchor]

/-- The adjacent-slice anchor is continuous in the displacement — the
model-side regularity input consumed (as `ContinuousOn`) by `rouche_closes`
(blueprint `lem:four_bar_anchor_adj_cont`). -/
theorem continuous_fourBarAnchorAdj (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ) :
    Continuous (fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃) := by
  unfold fourBarAnchorAdj
  fun_prop

/-- At the displacement origin the adjacent-slice anchor is the four-bar
closure equation at the core angles (blueprint `lem:four_bar_anchor_adj_zero`;
the `e^{2πi}` factor collapses to `1`): `fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ 0 = 0`
is exactly `(ρ₀−ρ₁)e^{iΦ₁} + (ρ₁−ρ₂)e^{iΦ₂} + (ρ₂−ρ₃)e^{iΦ₃} + (ρ₃−ρ₀) = 0`. -/
theorem fourBarAnchorAdj_zero (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ) :
    fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ 0 =
      1 / Complex.I *
        (((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp ((Φ₁ : ℂ) * Complex.I)
          + ((ρ 1 - ρ 2 : ℝ) : ℂ) * Complex.exp ((Φ₂ : ℂ) * Complex.I)
          + ((ρ 2 - ρ 3 : ℝ) : ℂ) * Complex.exp ((Φ₃ : ℂ) * Complex.I)
          + ((ρ 3 - ρ 0 : ℝ) : ℂ)) := by
  simp [fourBarAnchorAdj]

/-! ## Project-local Mathlib supplement — the tangential core construction
(Step-2 leaves of `lem:model_margin`, `sec:closure_rouche`)

The convex-existence leaf is discharged by an explicit *tangential
quadrilateral*: the four-bar sides always satisfy the Pitot identity
`c₁ + c₃ = c₂ + c₄`, so a quadrilateral with these sides circumscribes a
circle; the inradius is fixed by a single arctan-IVT, and strict convexity is
automatic (every heading gap is `2·arctan(tⱼ/r) ∈ (0,π)`).  Probe:
`references/verify_tangential_core.py`, 22 000 configurations, 0 failures. -/

/-- **Pitot tangent lengths** (blueprint `lem:pitot_tangent_lengths`).
Positive sides `a₀, a₁, a₂, a₃` with the Pitot identity `a₀ + a₂ = a₁ + a₃`
split into positive tangent lengths: `aₖ = tₖ + t_{k+1}` cyclically.  The
witness is `t₀ = τ` for `τ` the midpoint of the nonempty bracket
`(max 0 (a₀−a₁), min a₀ a₃)` — pure ordered-field arithmetic. -/
theorem pitot_tangent_lengths {a₀ a₁ a₂ a₃ : ℝ} (h0 : 0 < a₀) (h1 : 0 < a₁)
    (h2 : 0 < a₂) (h3 : 0 < a₃) (hpitot : a₀ + a₂ = a₁ + a₃) :
    ∃ t₀ t₁ t₂ t₃ : ℝ, (0 < t₀ ∧ 0 < t₁ ∧ 0 < t₂ ∧ 0 < t₃) ∧
      a₀ = t₀ + t₁ ∧ a₁ = t₁ + t₂ ∧ a₂ = t₂ + t₃ ∧ a₃ = t₃ + t₀ := by
  have hlo0 : (0 : ℝ) ≤ max 0 (a₀ - a₁) := le_max_left _ _
  have hlo1 : a₀ - a₁ ≤ max 0 (a₀ - a₁) := le_max_right _ _
  have hhi0 : min a₀ a₃ ≤ a₀ := min_le_left _ _
  have hhi1 : min a₀ a₃ ≤ a₃ := min_le_right _ _
  have hbr : max 0 (a₀ - a₁) < min a₀ a₃ :=
    max_lt (lt_min h0 h3) (lt_min (by linarith) (by linarith))
  set τ : ℝ := (max 0 (a₀ - a₁) + min a₀ a₃) / 2 with hτ
  refine ⟨τ, a₀ - τ, a₁ - a₀ + τ, a₃ - τ,
    ⟨by rw [hτ]; linarith, by rw [hτ]; linarith, by rw [hτ]; linarith,
      by rw [hτ]; linarith⟩,
    by ring, by ring, by linarith, by ring⟩

/-- **Half-angle junction identity** (blueprint `lem:exp_two_arctan`): for
`r > 0` and `t : ℝ`, `e^{2i·arctan(t/r)} = (r + it)/(r − it)`.  From
`Real.cos_arctan` / `Real.sin_arctan`, `e^{i·arctan(t/r)} =
(r + it)/√(r² + t²)`; squaring kills the square root since
`(r − it)(r + it) = r² + t²`. -/
theorem exp_two_arctan {r : ℝ} (hr : 0 < r) (t : ℝ) :
    Complex.exp (((2 * Real.arctan (t / r) : ℝ) : ℂ) * Complex.I)
      = ((r : ℂ) + (t : ℂ) * Complex.I) / ((r : ℂ) - (t : ℂ) * Complex.I) := by
  have hden : ((r : ℂ) - (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re,
      mul_zero, mul_one, sub_zero] at hre
    exact hr.ne' hre
  have hsplit : (((2 * Real.arctan (t / r) : ℝ) : ℂ)) * Complex.I
      = ((Real.arctan (t / r) : ℝ) : ℂ) * Complex.I
        + ((Real.arctan (t / r) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  set s : ℝ := Real.sqrt (1 + (t / r) ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 + (t / r) ^ 2 := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hexp1 : Complex.exp (((Real.arctan (t / r) : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (Real.arctan (t / r)) : ℝ) : ℂ)
        + ((Real.sin (Real.arctan (t / r)) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hsplit, Complex.exp_add, hexp1, Real.cos_arctan, Real.sin_arctan,
    ← hsdef, eq_div_iff hden]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  have hs2C : ((s : ℝ) : ℂ) ^ 2 * (r : ℂ) ^ 2 = (r : ℂ) ^ 2 + (t : ℂ) ^ 2 := by
    have h : ((s ^ 2 * r ^ 2 : ℝ) : ℂ) = ((r ^ 2 + t ^ 2 : ℝ) : ℂ) := by
      norm_cast
      rw [hs2]
      field_simp
    push_cast at h
    exact h
  push_cast
  field_simp
  linear_combination (-(((r : ℂ) + (t : ℂ) * Complex.I))) * hs2C
    - ((r : ℂ) + (t : ℂ) * Complex.I) * (t : ℂ) ^ 2 * Complex.I_sq

/-! ### The adjacent-slice margin chain (`lem:four_bar_anchor_adj_margin`)

Verbatim mirror of the `(1,3)`-slice chain with the displaced slots renamed
(slot 2 displaced instead of slot 3; Cramer determinant
`(ρ₀−ρ₁)(ρ₁−ρ₂)·sin((Φ₂+z₂)−(Φ₁+z₁))`).  The mirror intermediates are
implementation details (`private`); only the definition, continuity, the core
equation, the margin package and the winding brick are consumed downstream. -/

/-- The displacement derivative of the adjacent-slice anchor at `z`: the
continuous `ℝ`-linear map `h ↦ (ρ₀−ρ₁)e^{i(Φ₁+z₁)}·h₁ + (ρ₁−ρ₂)e^{i(Φ₂+z₂)}·h₂`
(consecutive junction directions; the `1/i` prefactor cancels the chain-rule
factor `i`). -/
noncomputable def fourBarAnchorAdjDeriv (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ : ℝ)
    (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  (((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I)) •
      Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)
    + (((ρ 1 - ρ 2 : ℝ) : ℂ) * Complex.exp (((Φ₂ + z.2 : ℝ) : ℂ) * Complex.I)) •
      Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] private theorem fourBarAnchorAdjDeriv_apply (ρ : Fin 4 → ℝ)
    (Φ₁ Φ₂ : ℝ) (z h : ℝ × ℝ) :
    fourBarAnchorAdjDeriv ρ Φ₁ Φ₂ z h =
      ((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I)
          * (h.1 : ℂ)
        + ((ρ 1 - ρ 2 : ℝ) : ℂ) * Complex.exp (((Φ₂ + z.2 : ℝ) : ℂ) * Complex.I)
          * (h.2 : ℂ) := by
  simp [fourBarAnchorAdjDeriv, smul_eq_mul]

/-- Strict differentiability of the adjacent-slice anchor: chain rule through
`exp(i·)` on the two displaced consecutive slots, the two pinned slots being
constant (mirror of `hasStrictFDerivAt_fourBarAnchor`). -/
private theorem hasStrictFDerivAt_fourBarAnchorAdj (ρ : Fin 4 → ℝ)
    (Φ₁ Φ₂ Φ₃ : ℝ) (z : ℝ × ℝ) :
    HasStrictFDerivAt (fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃)
      (fourBarAnchorAdjDeriv ρ Φ₁ Φ₂ z) z := by
  -- slot 1: `w ↦ (ρ₀−ρ₁)·exp(i(Φ₁+w₁))`
  have h1 : HasStrictFDerivAt (fun w : ℝ × ℝ => (Φ₁ + w.1 : ℝ))
      (ContinuousLinearMap.fst ℝ ℝ ℝ) z := hasStrictFDerivAt_fst.const_add Φ₁
  have h1C : HasStrictFDerivAt (fun w : ℝ × ℝ => ((Φ₁ + w.1 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) z :=
    Complex.ofRealCLM.hasStrictFDerivAt.comp z h1
  have h1I := h1C.mul_const Complex.I
  have hexp1 : HasStrictDerivAt Complex.exp
      (Complex.exp (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I))
      (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I) := Complex.hasStrictDerivAt_exp _
  have hd1 := hexp1.comp_hasStrictFDerivAt z h1I
  have hT1 := hd1.const_mul (((ρ 0 - ρ 1 : ℝ) : ℂ))
  -- slot 2: `w ↦ (ρ₁−ρ₂)·exp(i(Φ₂+w₂))`
  have h2 : HasStrictFDerivAt (fun w : ℝ × ℝ => (Φ₂ + w.2 : ℝ))
      (ContinuousLinearMap.snd ℝ ℝ ℝ) z := hasStrictFDerivAt_snd.const_add Φ₂
  have h2C : HasStrictFDerivAt (fun w : ℝ × ℝ => ((Φ₂ + w.2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
    Complex.ofRealCLM.hasStrictFDerivAt.comp z h2
  have h2I := h2C.mul_const Complex.I
  have hexp2 : HasStrictDerivAt Complex.exp
      (Complex.exp (((Φ₂ + z.2 : ℝ) : ℂ) * Complex.I))
      (((Φ₂ + z.2 : ℝ) : ℂ) * Complex.I) := Complex.hasStrictDerivAt_exp _
  have hd2 := hexp2.comp_hasStrictFDerivAt z h2I
  have hT2 := hd2.const_mul (((ρ 1 - ρ 2 : ℝ) : ℂ))
  -- assemble: constants in slots 3 and 4, then the `1/i` prefactor
  have hsum := ((hT1.add hT2).add_const
      (((ρ 2 - ρ 3 : ℝ) : ℂ) * Complex.exp ((Φ₃ : ℂ) * Complex.I))).add_const
      (((ρ 3 - ρ 0 : ℝ) : ℂ)
        * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I))
  have hf := hsum.const_mul (1 / Complex.I)
  refine HasStrictFDerivAt.congr_fderiv hf ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [fourBarAnchorAdjDeriv, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  field_simp

/-- Transversality of the adjacent-slice derivative: the consecutive-junction
columns `(ρ₀−ρ₁)e^{i(Φ₁+z₁)}` and `(ρ₁−ρ₂)e^{i(Φ₂+z₂)}` are `ℝ`-independent
as soon as both side coefficients are nonzero and the displaced angles are
not parallel mod `π`; the determinant is
`(ρ₀−ρ₁)(ρ₁−ρ₂)·sin((Φ₂+z₂)−(Φ₁+z₁))`. -/
private theorem fourBarAnchorAdjDeriv_injective (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ : ℝ)
    (z : ℝ × ℝ) (h01 : ρ 0 ≠ ρ 1) (h12 : ρ 1 ≠ ρ 2)
    (hsin : Real.sin ((Φ₂ + z.2) - (Φ₁ + z.1)) ≠ 0) :
    Function.Injective (fourBarAnchorAdjDeriv ρ Φ₁ Φ₂ z) := by
  set A : ℂ :=
    ((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp (((Φ₁ + z.1 : ℝ) : ℂ) * Complex.I) with hA
  set B : ℂ :=
    ((ρ 1 - ρ 2 : ℝ) : ℂ) * Complex.exp (((Φ₂ + z.2 : ℝ) : ℂ) * Complex.I) with hB
  have hdet : A.re * B.im - A.im * B.re
      = (ρ 0 - ρ 1) * (ρ 1 - ρ 2)
        * Real.sin ((Φ₂ + z.2) - (Φ₁ + z.1)) := by
    simp only [hA, hB, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Real.sin_sub, zero_mul, sub_zero, add_zero]
    ring
  have hne : A.re * B.im - A.im * B.re ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero
      (mul_ne_zero (sub_ne_zero.2 h01) (sub_ne_zero.2 h12)) hsin
  have heq : ⇑(fourBarAnchorAdjDeriv ρ Φ₁ Φ₂ z)
      = fun v : ℝ × ℝ => A * (v.1 : ℂ) + B * (v.2 : ℂ) := by
    funext v
    rw [fourBarAnchorAdjDeriv_apply, hA, hB]
  rw [heq]
  exact injective_columns_of_det_ne_zero hne

/-- The transverse adjacent-slice derivative is a continuous linear
equivalence `ℝ² ≃L ℂ` (injective + equal finite rank ⇒ bijective). -/
private theorem fourBarAnchorAdjDeriv_exists_equiv (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ : ℝ)
    (z : ℝ × ℝ) (h01 : ρ 0 ≠ ρ 1) (h12 : ρ 1 ≠ ρ 2)
    (hsin : Real.sin ((Φ₂ + z.2) - (Φ₁ + z.1)) ≠ 0) :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] ℂ,
      (e : (ℝ × ℝ) →L[ℝ] ℂ) = fourBarAnchorAdjDeriv ρ Φ₁ Φ₂ z := by
  have hinj : Function.Injective
      ((fourBarAnchorAdjDeriv ρ Φ₁ Φ₂ z) : (ℝ × ℝ) →ₗ[ℝ] ℂ) :=
    fourBarAnchorAdjDeriv_injective ρ Φ₁ Φ₂ z h01 h12 hsin
  have hrank : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ ℂ := by
    rw [Module.finrank_eq_card_basis Complex.basisOneI]
    simp
  have hsurj : Function.Surjective
      ((fourBarAnchorAdjDeriv ρ Φ₁ Φ₂ z) : (ℝ × ℝ) →ₗ[ℝ] ℂ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  refine ⟨(LinearEquiv.ofBijective
      ((fourBarAnchorAdjDeriv ρ Φ₁ Φ₂ z) : (ℝ × ℝ) →ₗ[ℝ] ℂ)
      ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  exact ContinuousLinearMap.ext fun v => rfl

/-- A transverse zero of the adjacent-slice anchor is isolated (inverse
function theorem at the strict derivative, mirror of
`fourBarAnchor_isolated_zero`). -/
private theorem fourBarAnchorAdj_isolated_zero (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ)
    (z₀ : ℝ × ℝ) (h01 : ρ 0 ≠ ρ 1) (h12 : ρ 1 ≠ ρ 2)
    (hsin : Real.sin ((Φ₂ + z₀.2) - (Φ₁ + z₀.1)) ≠ 0) :
    ∀ᶠ w in nhdsWithin z₀ {z₀}ᶜ,
      fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ w ≠ fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z₀ := by
  obtain ⟨e, he⟩ := fourBarAnchorAdjDeriv_exists_equiv ρ Φ₁ Φ₂ z₀ h01 h12 hsin
  have hf : HasStrictFDerivAt (fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃)
      (e : (ℝ × ℝ) →L[ℝ] ℂ) z₀ := by
    rw [he]; exact hasStrictFDerivAt_fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z₀
  have hlinv := HasStrictFDerivAt.eventually_left_inverse hf
  have himg := HasStrictFDerivAt.localInverse_apply_image hf
  filter_upwards [nhdsWithin_le_nhds hlinv, self_mem_nhdsWithin] with w hw hne
  intro hcontra
  exact hne (by rw [← hw, hcontra, himg]; exact Set.mem_singleton z₀)

/-- **Adjacent-slice boundary margin** (blueprint
`lem:four_bar_anchor_adj_margin` — the `m(κ) > 0` packaging on the adjacent
slice): if the recentered adjacent anchor has a transverse core zero at the
displacement origin (`E_adj(0) = 0`, nonzero consecutive side coefficients,
adjacent core gap nonparallel mod `π`), there is `δ₀ > 0` such that on
**every** origin-centered square of half-side `δ ≤ δ₀` the anchor is bounded
below by a positive margin `m` on the box boundary `{boxGauge = 1}` — the
model-side inputs of `rouche_closes`.  The `δ`-quantifier is universal below
`δ₀` so the box can be shrunk after `κ` is fixed (per-`κ`, non-uniform). -/
theorem fourBarAnchorAdj_boundary_margin (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ)
    (h01 : ρ 0 ≠ ρ 1) (h12 : ρ 1 ≠ ρ 2)
    (hsin : Real.sin (Φ₂ - Φ₁) ≠ 0)
    (hzero : fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ 0 = 0) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ m > 0, ∀ z : ℝ × ℝ, boxGauge (-δ) δ (-δ) δ z = 1 →
        m ≤ ‖fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z‖ := by
  have hsin' : Real.sin ((Φ₂ + (0 : ℝ × ℝ).2) - (Φ₁ + (0 : ℝ × ℝ).1)) ≠ 0 := by
    simpa using hsin
  have hev := fourBarAnchorAdj_isolated_zero ρ Φ₁ Φ₂ Φ₃ 0 h01 h12 hsin'
  rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, by positivity, fun δ hδ hδε => ?_⟩
  have hLu : -δ < 0 := neg_lt_zero.2 hδ
  set S : Set (ℝ × ℝ) := {z | boxGauge (-δ) δ (-δ) δ z = 1} with hS
  have hSclosed : IsClosed S :=
    isClosed_eq (continuous_boxGauge _ _ _ _) continuous_const
  have hnorm : ∀ z ∈ S, ‖z‖ ≤ δ := by
    intro z hz
    have hb := norm_le_boxOuter_mul_boxGauge hLu hδ hLu hδ z
    rw [show boxGauge (-δ) δ (-δ) δ z = 1 from hz] at hb
    simpa [neg_neg, max_self] using hb
  have hSsub : S ⊆ Metric.closedBall 0 δ := fun z hz => by
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm z hz
  have hScompact : IsCompact S :=
    (isCompact_closedBall (0 : ℝ × ℝ) δ).of_isClosed_subset hSclosed hSsub
  have hfne : ∀ z ∈ S, fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z ≠ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h0
      have h1 : boxGauge (-δ) δ (-δ) δ z = 1 := hz
      rw [h0] at h1
      simp [boxGauge, gaugeCoord] at h1
    have hdist : dist z 0 < ε := by
      rw [dist_zero_right]
      calc ‖z‖ ≤ δ := hnorm z hz
        _ ≤ ε / 2 := hδε
        _ < ε := by linarith
    have hne0 := hball ⟨Metric.mem_ball.2 hdist, hz0⟩
    simpa [hzero] using hne0
  rcases S.eq_empty_or_nonempty with hempty | hne
  · exact ⟨1, one_pos, fun z hz =>
      absurd (show z ∈ S from hz) (by simp [hempty])⟩
  · obtain ⟨z₀, hz₀S, hmin⟩ := hScompact.exists_isMinOn hne
      ((continuous_fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃).norm.continuousOn)
    exact ⟨‖fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z₀‖,
      norm_pos_iff.2 (hfne z₀ hz₀S), fun z hz => (isMinOn_iff.mp hmin) z hz⟩

/-! ### The remaining tangential leaves (`lem:tangential_inradius`,
`lem:tangential_closure`, `lem:four_bar_core_exists`) -/

/-- **Tangential inradius** (blueprint `lem:tangential_inradius`): for
positive tangent lengths there is an inradius `r > 0` with
`∑ⱼ arctan(tⱼ/r) = π`.  Explicit IVT bracket — at `r = 2·max tⱼ` every
summand is `< arctan 1 = π/4`, at `r = (min tⱼ)/2` every summand is
`> π/4` — so no limit computation is needed.  Uniqueness (`f` strictly
decreasing) is true but not needed. -/
theorem tangential_inradius {t₀ t₁ t₂ t₃ : ℝ} (h0 : 0 < t₀) (h1 : 0 < t₁)
    (h2 : 0 < t₂) (h3 : 0 < t₃) :
    ∃ r : ℝ, 0 < r ∧
      Real.arctan (t₀ / r) + Real.arctan (t₁ / r) + Real.arctan (t₂ / r)
        + Real.arctan (t₃ / r) = Real.pi := by
  set M : ℝ := max (max t₀ t₁) (max t₂ t₃) with hM
  set μ : ℝ := min (min t₀ t₁) (min t₂ t₃) with hμ
  have hμ0 : 0 < μ := lt_min (lt_min h0 h1) (lt_min h2 h3)
  have hμM : μ ≤ M :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (le_max_left t₀ t₁) (le_max_left _ _)))
  set f : ℝ → ℝ := fun r =>
    Real.arctan (t₀ / r) + Real.arctan (t₁ / r) + Real.arctan (t₂ / r)
      + Real.arctan (t₃ / r) with hf
  have hlo : (0 : ℝ) < μ / 2 := by positivity
  have hhi : (0 : ℝ) < 2 * M := by linarith
  have hle : μ / 2 ≤ 2 * M := by linarith
  -- continuity on the bracket (`r ≠ 0` there)
  have hfc : ContinuousOn f (Set.Icc (μ / 2) (2 * M)) := by
    have hterm : ∀ t : ℝ, ContinuousOn
        (fun r : ℝ => Real.arctan (t / r)) (Set.Icc (μ / 2) (2 * M)) := by
      intro t
      refine Real.continuous_arctan.comp_continuousOn ?_
      exact continuousOn_const.div continuousOn_id
        fun r hr => (lt_of_lt_of_le hlo hr.1).ne'
    exact (((hterm t₀).add (hterm t₁)).add (hterm t₂)).add (hterm t₃)
  -- upper end: every summand `< π/4`
  have hupper : ∀ t : ℝ, 0 < t → t ≤ M → Real.arctan (t / (2 * M)) < π / 4 := by
    intro t ht htM
    have hx : t / (2 * M) < 1 := by
      rw [div_lt_one hhi]
      linarith
    calc Real.arctan (t / (2 * M)) < Real.arctan 1 :=
          Real.arctan_lt_arctan_iff.mpr hx
      _ = π / 4 := Real.arctan_one
  -- lower end: every summand `> π/4`
  have hlower : ∀ t : ℝ, μ ≤ t → π / 4 < Real.arctan (t / (μ / 2)) := by
    intro t hμt
    have hx : (1 : ℝ) < t / (μ / 2) := by
      rw [lt_div_iff₀ hlo]
      linarith
    calc π / 4 = Real.arctan 1 := Real.arctan_one.symm
      _ < Real.arctan (t / (μ / 2)) := Real.arctan_lt_arctan_iff.mpr hx
  have hfhi : f (2 * M) < π := by
    have h₀ := hupper t₀ h0 (le_trans (le_max_left t₀ t₁) (le_max_left _ _))
    have h₁ := hupper t₁ h1 (le_trans (le_max_right t₀ t₁) (le_max_left _ _))
    have h₂ := hupper t₂ h2 (le_trans (le_max_left t₂ t₃) (le_max_right _ _))
    have h₃ := hupper t₃ h3 (le_trans (le_max_right t₂ t₃) (le_max_right _ _))
    rw [hf]
    dsimp only
    linarith
  have hflo : π < f (μ / 2) := by
    have h₀ := hlower t₀ (le_trans (min_le_left _ _) (min_le_left _ _))
    have h₁ := hlower t₁ (le_trans (min_le_left _ _) (min_le_right _ _))
    have h₂ := hlower t₂ (le_trans (min_le_right _ _) (min_le_left _ _))
    have h₃ := hlower t₃ (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [hf]
    dsimp only
    linarith
  -- IVT on the decreasing bracket
  have hmem : π ∈ Set.Icc (f (2 * M)) (f (μ / 2)) := ⟨hfhi.le, hflo.le⟩
  obtain ⟨r, hrmem, hfr⟩ := intermediate_value_Icc' hle hfc hmem
  exact ⟨r, lt_of_lt_of_le hlo hrmem.1, hfr⟩

/-- **Tangential closure** (blueprint `lem:tangential_closure`): if the four
half-gaps `2·arctan(tⱼ/r)` sum to `2π`, the tangential quadrilateral with
sides `aₖ = tₖ + t_{k+1}` and cumulative headings `g₀ = 0`,
`g_{k+1} = g_k + 2·arctan(t_{k+1}/r)` closes: `∑ₖ aₖ e^{i g_k} = 0`, and
every heading gap lies in `(0, π)` (strict convexity is automatic).  The
junction identity `e^{i(g_{k+1}−g_k)} = (r + i t_{k+1})/(r − i t_{k+1})`
(`exp_two_arctan`) makes the expanded sum telescope. -/
theorem tangential_closure {r t₀ t₁ t₂ t₃ : ℝ} (hr : 0 < r)
    (h0 : 0 < t₀) (h1 : 0 < t₁) (h2 : 0 < t₂) (h3 : 0 < t₃)
    (hsum : 2 * Real.arctan (t₀ / r) + 2 * Real.arctan (t₁ / r)
        + 2 * Real.arctan (t₂ / r) + 2 * Real.arctan (t₃ / r) = 2 * Real.pi)
    {g₁ g₂ g₃ : ℝ}
    (hg₁ : g₁ = 2 * Real.arctan (t₁ / r))
    (hg₂ : g₂ = g₁ + 2 * Real.arctan (t₂ / r))
    (hg₃ : g₃ = g₂ + 2 * Real.arctan (t₃ / r)) :
    (((t₀ + t₁ : ℝ) : ℂ)
        + ((t₁ + t₂ : ℝ) : ℂ) * Complex.exp ((g₁ : ℂ) * Complex.I)
        + ((t₂ + t₃ : ℝ) : ℂ) * Complex.exp ((g₂ : ℂ) * Complex.I)
        + ((t₃ + t₀ : ℝ) : ℂ) * Complex.exp ((g₃ : ℂ) * Complex.I) = 0) ∧
      (0 < g₁ ∧ g₁ < π) ∧ (0 < g₂ - g₁ ∧ g₂ - g₁ < π) ∧
      (0 < g₃ - g₂ ∧ g₃ - g₂ < π) ∧
      (0 < 2 * π - g₃ ∧ 2 * π - g₃ < π) := by
  -- the four half-gaps lie in `(0, π)`
  have hgap : ∀ t : ℝ, 0 < t →
      0 < 2 * Real.arctan (t / r) ∧ 2 * Real.arctan (t / r) < π := by
    intro t ht
    constructor
    · have := Real.arctan_pos.mpr (div_pos ht hr)
      linarith
    · have := Real.arctan_lt_pi_div_two (t / r)
      linarith
  obtain ⟨hp0, hq0⟩ := hgap t₀ h0
  obtain ⟨hp1, hq1⟩ := hgap t₁ h1
  obtain ⟨hp2, hq2⟩ := hgap t₂ h2
  obtain ⟨hp3, hq3⟩ := hgap t₃ h3
  -- nonzero denominators
  have hden : ∀ t : ℝ, ((r : ℂ) - (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re,
      mul_zero, mul_one, sub_zero] at hre
    exact hr.ne' hre
  -- junction identities
  have hj0 : Complex.exp ((g₁ : ℂ) * Complex.I)
      * ((r : ℂ) - (t₁ : ℂ) * Complex.I) = (r : ℂ) + (t₁ : ℂ) * Complex.I := by
    rw [hg₁, exp_two_arctan hr t₁, div_mul_cancel₀ _ (hden t₁)]
  have hj1 : Complex.exp ((g₂ : ℂ) * Complex.I)
      * ((r : ℂ) - (t₂ : ℂ) * Complex.I)
      = ((r : ℂ) + (t₂ : ℂ) * Complex.I)
        * Complex.exp ((g₁ : ℂ) * Complex.I) := by
    have hsplit : ((g₂ : ℝ) : ℂ) * Complex.I
        = ((g₁ : ℝ) : ℂ) * Complex.I
          + ((2 * Real.arctan (t₂ / r) : ℝ) : ℂ) * Complex.I := by
      rw [hg₂]
      push_cast
      ring
    rw [hsplit, Complex.exp_add, exp_two_arctan hr t₂, mul_assoc,
      div_mul_cancel₀ _ (hden t₂)]
    ring
  have hj2 : Complex.exp ((g₃ : ℂ) * Complex.I)
      * ((r : ℂ) - (t₃ : ℂ) * Complex.I)
      = ((r : ℂ) + (t₃ : ℂ) * Complex.I)
        * Complex.exp ((g₂ : ℂ) * Complex.I) := by
    have hsplit : ((g₃ : ℝ) : ℂ) * Complex.I
        = ((g₂ : ℝ) : ℂ) * Complex.I
          + ((2 * Real.arctan (t₃ / r) : ℝ) : ℂ) * Complex.I := by
      rw [hg₃]
      push_cast
      ring
    rw [hsplit, Complex.exp_add, exp_two_arctan hr t₃, mul_assoc,
      div_mul_cancel₀ _ (hden t₃)]
    ring
  have hj3 : ((r : ℂ) + (t₀ : ℂ) * Complex.I)
      * Complex.exp ((g₃ : ℂ) * Complex.I)
      = (r : ℂ) - (t₀ : ℂ) * Complex.I := by
    have hclose : ((g₃ : ℝ) : ℂ) * Complex.I
        + ((2 * Real.arctan (t₀ / r) : ℝ) : ℂ) * Complex.I
        = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
      have hg3sum : g₃ + 2 * Real.arctan (t₀ / r) = 2 * Real.pi := by
        rw [hg₃, hg₂, hg₁]
        linarith
      push_cast [← hg3sum]
      ring
    have hexp1 : Complex.exp ((g₃ : ℂ) * Complex.I)
        * Complex.exp (((2 * Real.arctan (t₀ / r) : ℝ) : ℂ) * Complex.I)
        = 1 := by
      rw [← Complex.exp_add, hclose]
      push_cast
      rw [show (2 : ℂ) * Real.pi * Complex.I = 2 * Real.pi * Complex.I by ring]
      exact Complex.exp_two_pi_mul_I
    have h := congrArg (· * ((r : ℂ) - (t₀ : ℂ) * Complex.I)) hexp1
    simp only [one_mul] at h
    rw [exp_two_arctan hr t₀, mul_assoc, div_mul_cancel₀ _ (hden t₀)] at h
    linear_combination h
  -- gap bounds
  refine ⟨?_, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  -- telescoped closure from the four junction identities
  push_cast
  linear_combination Complex.I * hj0 + Complex.I * hj1 + Complex.I * hj2
    - Complex.I * hj3
    + ((t₁ : ℂ) * (1 + Complex.exp ((g₁ : ℂ) * Complex.I))
      + (t₂ : ℂ) * (Complex.exp ((g₁ : ℂ) * Complex.I)
        + Complex.exp ((g₂ : ℂ) * Complex.I))
      + (t₃ : ℂ) * (Complex.exp ((g₂ : ℂ) * Complex.I)
        + Complex.exp ((g₃ : ℂ) * Complex.I))
      + (t₀ : ℂ) * (Complex.exp ((g₃ : ℂ) * Complex.I) + 1)) * Complex.I_sq

/-- **Four-bar core exists — strictly convex, adjacent-slice ready**
(blueprint `lem:four_bar_core_exists`).  Under the DFV radii separation
`ρ₀, ρ₂ < T < ρ₁, ρ₃` there are core angles `0 < Φ₁ < Φ₂ < Φ₃ < 2π` with all
four cyclic gaps in `(0, π)` and `fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ 0 = 0`.
Construction: the sides `c₄ = ρ₃−ρ₀, c₃ = ρ₃−ρ₂, c₂ = ρ₁−ρ₂, c₁ = ρ₁−ρ₀`
are positive with the Pitot identity `c₄ + c₂ = c₃ + c₁`; split into tangent
lengths (`pitot_tangent_lengths`), fix the inradius (`tangential_inradius`),
close the tangential quadrilateral (`tangential_closure`), then transport
along the dictionary `Φ₁ = g₃ − π`, `Φ₂ = g₂`, `Φ₃ = g₁ + π` (the sign flips
`e^{±iπ} = −1` absorb the negative coefficients). -/
theorem fourBar_core_exists (ρ : Fin 4 → ℝ) {T : ℝ}
    (h0T : ρ 0 < T) (h2T : ρ 2 < T) (hT1 : T < ρ 1) (hT3 : T < ρ 3) :
    ∃ Φ₁ Φ₂ Φ₃ : ℝ,
      (0 < Φ₁ ∧ Φ₁ < Φ₂ ∧ Φ₂ < Φ₃ ∧ Φ₃ < 2 * π) ∧
      (Φ₁ < π ∧ Φ₂ - Φ₁ < π ∧ Φ₃ - Φ₂ < π ∧ 2 * π - Φ₃ < π) ∧
      fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ 0 = 0 := by
  -- the reordered sides `(a₀, a₁, a₂, a₃) = (c₄, c₃, c₂, c₁)` and Pitot
  obtain ⟨t₀, t₁, t₂, t₃, ⟨ht0, ht1, ht2, ht3⟩, ha₀, ha₁, ha₂, ha₃⟩ :=
    pitot_tangent_lengths (a₀ := ρ 3 - ρ 0) (a₁ := ρ 3 - ρ 2)
      (a₂ := ρ 1 - ρ 2) (a₃ := ρ 1 - ρ 0)
      (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  obtain ⟨r, hr, hS⟩ := tangential_inradius ht0 ht1 ht2 ht3
  have hsum : 2 * Real.arctan (t₀ / r) + 2 * Real.arctan (t₁ / r)
      + 2 * Real.arctan (t₂ / r) + 2 * Real.arctan (t₃ / r) = 2 * π := by
    linarith
  obtain ⟨hclose, ⟨hg₁0, hg₁π⟩, ⟨hg₂₁0, hg₂₁π⟩, ⟨hg₃₂0, hg₃₂π⟩,
      ⟨hg₃0, hg₃π⟩⟩ :=
    tangential_closure hr ht0 ht1 ht2 ht3 hsum (g₁ := 2 * Real.arctan (t₁ / r))
      (g₂ := 2 * Real.arctan (t₁ / r) + 2 * Real.arctan (t₂ / r))
      (g₃ := 2 * Real.arctan (t₁ / r) + 2 * Real.arctan (t₂ / r)
        + 2 * Real.arctan (t₃ / r)) rfl rfl rfl
  set g₁ : ℝ := 2 * Real.arctan (t₁ / r) with hg₁def
  set g₂ : ℝ := g₁ + 2 * Real.arctan (t₂ / r) with hg₂def
  set g₃ : ℝ := g₂ + 2 * Real.arctan (t₃ / r) with hg₃def
  refine ⟨g₃ - π, g₂, g₁ + π,
    ⟨by linarith, by linarith, by linarith, by linarith⟩,
    ⟨by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
  -- the anchor at the displacement origin under the dictionary
  rw [fourBarAnchorAdj_zero]
  have hE₁ : Complex.exp (((g₃ - π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((g₃ : ℂ) * Complex.I) := by
    have hsplit : ((g₃ - π : ℝ) : ℂ) * Complex.I
        = (g₃ : ℂ) * Complex.I - (π : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hsplit, Complex.exp_sub, Complex.exp_pi_mul_I]
    field_simp
  have hE₃ : Complex.exp (((g₁ + π : ℝ) : ℂ) * Complex.I)
      = -Complex.exp ((g₁ : ℂ) * Complex.I) := by
    have hsplit : ((g₁ + π : ℝ) : ℂ) * Complex.I
        = (g₁ : ℂ) * Complex.I + (π : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hS0 : ((ρ 0 - ρ 1 : ℝ) : ℂ)
        * Complex.exp (((g₃ - π : ℝ) : ℂ) * Complex.I)
      + ((ρ 1 - ρ 2 : ℝ) : ℂ) * Complex.exp (((g₂ : ℝ) : ℂ) * Complex.I)
      + ((ρ 2 - ρ 3 : ℝ) : ℂ)
        * Complex.exp (((g₁ + π : ℝ) : ℂ) * Complex.I)
      + ((ρ 3 - ρ 0 : ℝ) : ℂ) = 0 := by
    rw [hE₁, hE₃]
    have ha₀C : ((ρ 3 - ρ 0 : ℝ) : ℂ) = ((t₀ + t₁ : ℝ) : ℂ) := by
      exact_mod_cast congrArg Complex.ofReal ha₀
    have ha₁C : ((ρ 3 - ρ 2 : ℝ) : ℂ) = ((t₁ + t₂ : ℝ) : ℂ) := by
      exact_mod_cast congrArg Complex.ofReal ha₁
    have ha₂C : ((ρ 1 - ρ 2 : ℝ) : ℂ) = ((t₂ + t₃ : ℝ) : ℂ) := by
      exact_mod_cast congrArg Complex.ofReal ha₂
    have ha₃C : ((ρ 1 - ρ 0 : ℝ) : ℂ) = ((t₃ + t₀ : ℝ) : ℂ) := by
      exact_mod_cast congrArg Complex.ofReal ha₃
    push_cast at ha₀C ha₁C ha₂C ha₃C hclose ⊢
    linear_combination hclose
      + Complex.exp ((g₃ : ℂ) * Complex.I) * ha₃C
      + Complex.exp ((g₂ : ℂ) * Complex.I) * ha₂C
      + Complex.exp ((g₁ : ℂ) * Complex.I) * ha₁C
      + ha₀C
  rw [hS0, mul_zero]

/-! ### The adjacent-slice boundary winding (`lem:four_bar_anchor_adj_winding`)

Technique of `closure_winding_t0`, transferred to the adjacent anchor: the
box-radial boundary loop of a small origin-centered square has the same
winding as a small-circle loop (`boxRadial_winding_eq`, ray homotopy), and on
the circle the anchor is a pointwise Rouché perturbation of the nonsingular
linear loop `linearLoop (δ(C_a−iC_b)/2) (δ(C_a+iC_b)/2)` whose winding is
`sgn Im(conj C_a·C_b) = sgn[(ρ₀−ρ₁)(ρ₁−ρ₂)sin(Φ₂−Φ₁)] = −1`
(`windingNumberC_linearLoop`; the DFV window signs `ρ₀ < ρ₁`, `ρ₂ < ρ₁` and
the convex-core gap `sin(Φ₂−Φ₁) > 0` pin the determinant negative). -/

/-- **Adjacent-slice boundary winding `−1`** (blueprint
`lem:four_bar_anchor_adj_winding`): at a transverse convex core of the
recentered adjacent anchor (DFV window signs `ρ₀ < ρ₁`, `ρ₂ < ρ₁`, adjacent
core gap `sin(Φ₂ − Φ₁) > 0`, `E_adj(0) = 0`) there is `δ₁ > 0` such that for
every `0 < δ ≤ δ₁` the box-radial boundary loop
`s ↦ E_adj(boxRadial(2πs))` of the origin-centered square of half-side `δ`
is nowhere zero with winding number `−1` about the origin — the
nonzero-winding input of `rouche_closes` on the model side.  (The DFV-sign
hypotheses are stated as strict inequalities rather than `≠` because they pin
the Jacobian determinant `(ρ₀−ρ₁)(ρ₁−ρ₂)sin(Φ₂−Φ₁) < 0`, hence the winding
value; with `≠` alone the winding would be `±1`.) -/
theorem fourBarAnchorAdj_boundary_winding (ρ : Fin 4 → ℝ) (Φ₁ Φ₂ Φ₃ : ℝ)
    (h01 : ρ 0 < ρ 1) (h21 : ρ 2 < ρ 1)
    (hsin : 0 < Real.sin (Φ₂ - Φ₁))
    (hzero : fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ 0 = 0) :
    ∃ δ₁ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∃ (γ : C(unitInterval, ℂ)) (hγ : ∀ s, γ s ≠ 0),
        (∀ s : unitInterval, γ s = fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃
            (boxRadial (-δ) δ (-δ) δ (2 * Real.pi * ↑s))) ∧
        windingNumberC γ hγ = -1 := by
  -- the Jacobian columns at the core and the negative pairing determinant
  set Ca : ℂ := ((ρ 0 - ρ 1 : ℝ) : ℂ) * Complex.exp ((Φ₁ : ℂ) * Complex.I)
    with hCadef
  set Cb : ℂ := ((ρ 1 - ρ 2 : ℝ) : ℂ) * Complex.exp ((Φ₂ : ℂ) * Complex.I)
    with hCbdef
  have hLval : ((starRingEnd ℂ) Ca * Cb).im
      = (ρ 0 - ρ 1) * (ρ 1 - ρ 2) * Real.sin (Φ₂ - Φ₁) := by
    simp only [hCadef, hCbdef, Complex.mul_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_sub,
      zero_mul, sub_zero, add_zero, neg_mul]
    ring
  have hLneg : ((starRingEnd ℂ) Ca * Cb).im < 0 := by
    rw [hLval]
    have h1 : ρ 0 - ρ 1 < 0 := by linarith
    have h2 : 0 < ρ 1 - ρ 2 := by linarith
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h1 h2) hsin
  have hLne : ((starRingEnd ℂ) Ca * Cb).im ≠ 0 := hLneg.ne
  -- σ_min lower bound and the strict-derivative remainder bound at the core
  obtain ⟨σ, hσ, hbound⟩ := norm_smul_add_smul_ge hLne
  have hd := hasStrictFDerivAt_fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ 0
  have hLz : ∀ z : ℝ × ℝ, fourBarAnchorAdjDeriv ρ Φ₁ Φ₂ 0 z
      = z.1 • Ca + z.2 • Cb := by
    intro z
    rw [fourBarAnchorAdjDeriv_apply]
    simp only [Prod.fst_zero, Prod.snd_zero, add_zero, hCadef, hCbdef,
      Complex.real_smul]
    ring
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hd.hasFDerivAt
  have hev : ∀ᶠ z : ℝ × ℝ in nhds 0,
      ‖fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z - (z.1 • Ca + z.2 • Cb)‖
        ≤ σ / 2 * ‖z‖ := by
    have hhalf : (0 : ℝ) < σ / 2 := by positivity
    filter_upwards [Asymptotics.isLittleO_iff.mp hlo hhalf] with z hz
    rw [← hLz z]
    simpa [hzero] using hz
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ρr₂, hρr₂, hδρr⟩ := hev
  set ρr : ℝ := ρr₂ / 2 with hρrdef
  have hρr : 0 < ρr := by positivity
  have hrem : ∀ z : ℝ × ℝ, ‖z‖ ≤ ρr →
      ‖fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z - (z.1 • Ca + z.2 • Cb)‖
        ≤ σ / 2 * ‖z‖ := by
    intro z hz
    exact hδρr (show dist z 0 < ρr₂ by rw [dist_zero_right]; rw [hρrdef] at hz; linarith)
  -- the anchor is nowhere zero on the punctured ball of radius `ρr`
  have hne_ball : ∀ z : ℝ × ℝ, z ≠ 0 → ‖z‖ ≤ ρr →
      fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z ≠ 0 := by
    intro z hz0 hzr h
    have hrem' := hrem z hzr
    rw [h, zero_sub, norm_neg] at hrem'
    have hlow : σ * (|z.1| + |z.2|) ≤ ‖z.1 • Ca + z.2 • Cb‖ := hbound _ _
    have hsuple : ‖z‖ ≤ |z.1| + |z.2| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _))
        (le_add_of_nonneg_left (abs_nonneg _))
    have hpos : 0 < |z.1| + |z.2| :=
      lt_of_lt_of_le (norm_pos_iff.2 hz0) hsuple
    nlinarith
  refine ⟨ρr, hρr, fun δ hδ hδρ => ?_⟩
  have hLu : -δ < 0 := neg_lt_zero.2 hδ
  -- NB: local abbreviations below use `let` + `rfl`-equations, NOT `set` —
  -- `set`'s occurrence abstraction (kabstract) diverges at `whnf` against
  -- this context (the @102 hotspot: 370s+ in `Mathlib.Tactic.setTactic`).
  let G : ℝ × ℝ → ℂ := fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃
  -- points of the box have sup-norm `≤ δ ≤ ρr`
  have hbox_norm : ∀ z : ℝ × ℝ, z.1 ∈ Set.Icc (-δ) δ → z.2 ∈ Set.Icc (-δ) δ →
      ‖z‖ ≤ ρr := by
    intro z hz1 hz2
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_trans (max_le (abs_le.mpr ⟨hz1.1, hz1.2⟩)
      (abs_le.mpr ⟨hz2.1, hz2.2⟩)) hδρ
  have hGne : ∀ z : ℝ × ℝ, z.1 ∈ Set.Icc (-δ) δ → z.2 ∈ Set.Icc (-δ) δ →
      z ≠ 0 → G z ≠ 0 :=
    fun z hz1 hz2 hz0 => hne_ball z hz0 (hbox_norm z hz1 hz2)
  -- the box-radial boundary loop (two-stage composition via
  -- `boxRadialLoop_continuous` — the inlined `comp` form diverges at `whnf`,
  -- the @092 blocker)
  have hγ₀c : Continuous fun s : unitInterval =>
      G (boxRadial (-δ) δ (-δ) δ (2 * Real.pi * ↑s)) :=
    boxRadialLoop_continuous hLu hδ hLu hδ
      ((continuous_fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃).continuousOn)
  -- build `γ_□` with `toFun` INFERRED from `hγ₀c` (via `⟨_, hγ₀c⟩`) rather
  -- than re-elaborated: re-elaborating the lambda triggers a defeq pass that
  -- whnf-diverges on the `boxRadial`/anchor subterms (same fix as
  -- `trimmed_winding_t0`'s `γ₀`).
  let γ₀ : C(unitInterval, ℂ) := ⟨_, hγ₀c⟩
  have hγ₀ne : ∀ s, γ₀ s ≠ 0 := by
    intro s
    obtain ⟨hm1, hm2⟩ := boxRadial_mem hLu hδ hLu hδ (2 * Real.pi * ↑s)
    exact hGne _ hm1 hm2 (boxRadial_ne_zero hLu hδ hLu hδ _)
  -- the small-circle loop at radius `δ`
  let zc : unitInterval → ℝ × ℝ := fun s =>
    (δ * Real.cos (2 * Real.pi * ↑s), δ * Real.sin (2 * Real.pi * ↑s))
  have hzcdef : zc = fun s : unitInterval =>
      (δ * Real.cos (2 * Real.pi * ↑s), δ * Real.sin (2 * Real.pi * ↑s)) := rfl
  have hzc_norm : ∀ s : unitInterval, ‖zc s‖ ≤ ρr := by
    intro s
    have h1 : |(zc s).1| ≤ δ := by
      rw [abs_mul, abs_of_pos hδ]
      calc δ * |Real.cos (2 * Real.pi * (s : ℝ))| ≤ δ * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hδ.le
        _ = δ := mul_one _
    have h2 : |(zc s).2| ≤ δ := by
      rw [abs_mul, abs_of_pos hδ]
      calc δ * |Real.sin (2 * Real.pi * (s : ℝ))| ≤ δ * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hδ.le
        _ = δ := mul_one _
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (max_le h1 h2).trans hδρ
  have hzc_ne : ∀ s : unitInterval, zc s ≠ 0 := by
    intro s h
    have h1 : δ * Real.cos (2 * Real.pi * ↑s) = 0 := congrArg Prod.fst h
    have h2 : δ * Real.sin (2 * Real.pi * ↑s) = 0 := congrArg Prod.snd h
    have hcos : Real.cos (2 * Real.pi * ↑s) = 0 :=
      (mul_eq_zero.mp h1).resolve_left hδ.ne'
    have hsin0 : Real.sin (2 * Real.pi * ↑s) = 0 :=
      (mul_eq_zero.mp h2).resolve_left hδ.ne'
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * ↑s)
    rw [hcos, hsin0] at this
    norm_num at this
  -- (same two-stage split as `hγ₀c`: compose over the `ℝ` angle domain first)
  have hGcirc : Continuous fun θ : ℝ =>
      G (δ * Real.cos θ, δ * Real.sin θ) :=
    (continuous_fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃).comp
      ((continuous_const.mul Real.continuous_cos).prodMk
        (continuous_const.mul Real.continuous_sin))
  have hγ₁c : Continuous fun s : unitInterval => G (zc s) :=
    hGcirc.comp (continuous_subtype_val.const_mul _)
  let γ₁ : C(unitInterval, ℂ) := ⟨_, hγ₁c⟩
  have hγ₁ne : ∀ s, γ₁ s ≠ 0 :=
    fun s => hne_ball (zc s) (hzc_ne s) (hzc_norm s)
  -- the box-radial loop and the circle loop have equal winding (ray homotopy)
  have hinr : δ ≤ boxInradius (-δ) δ (-δ) δ := by
    simp [boxInradius]
  have htrans : windingNumberC γ₀ hγ₀ne = windingNumberC γ₁ hγ₁ne :=
    boxRadial_winding_eq hLu hδ hLu hδ
      ((continuous_fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃).continuousOn) hGne hδ hinr
      γ₀ γ₁ hγ₀ne hγ₁ne (fun s => rfl) (fun s => rfl)
  -- the linear boundary loop and its coefficients
  let la : ℂ := (δ : ℂ) * ((Ca - Complex.I * Cb) / 2)
  let lb : ℂ := (δ : ℂ) * ((Ca + Complex.I * Cb) / 2)
  have hladef : la = (δ : ℂ) * ((Ca - Complex.I * Cb) / 2) := rfl
  have hlbdef : lb = (δ : ℂ) * ((Ca + Complex.I * Cb) / 2) := rfl
  have hnδ : ‖((δ : ℝ) : ℂ)‖ = δ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have hlab : ‖la‖ ≠ ‖lb‖ := by
    rw [hladef, hlbdef, norm_mul, norm_mul, hnδ]
    intro h
    exact norm_pair_ne hLne (mul_left_cancel₀ hδ.ne' h)
  let γL : C(unitInterval, ℂ) := linearLoop la lb
  have hγLdef : γL = linearLoop la lb := rfl
  have hγLne : ∀ t, γL t ≠ 0 := linearLoop_ne_zero la lb hlab
  -- the linear loop is the derivative on the circle
  have hγLpt : ∀ s : unitInterval,
      γL s = (zc s).1 • Ca + (zc s).2 • Cb := by
    intro s
    rw [hγLdef, linearLoop_apply]
    have hpair := cos_smul_add_sin_smul Ca Cb (2 * Real.pi * (s : ℝ))
    simp only [hzcdef, Complex.real_smul] at hpair ⊢
    push_cast at hpair ⊢
    rw [hladef, hlbdef]
    linear_combination (-((δ : ℝ) : ℂ)) * hpair
  -- the pointwise Rouché comparison on the circle
  have hzne : ∀ s : unitInterval, (0 : ℝ) < |(zc s).1| + |(zc s).2| := by
    intro s
    have hsuple : ‖zc s‖ ≤ |(zc s).1| + |(zc s).2| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _))
        (le_add_of_nonneg_left (abs_nonneg _))
    exact lt_of_lt_of_le (norm_pos_iff.2 (hzc_ne s)) hsuple
  have hpert : ∀ s : unitInterval, ‖γ₁ s - γL s‖ < ‖γL s‖ := by
    intro s
    have hz := hrem (zc s) (hzc_norm s)
    have hlow : σ * (|(zc s).1| + |(zc s).2|) ≤ ‖γL s‖ := by
      rw [hγLpt s]; exact hbound _ _
    have hsuple : ‖zc s‖ ≤ |(zc s).1| + |(zc s).2| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _))
        (le_add_of_nonneg_left (abs_nonneg _))
    calc ‖γ₁ s - γL s‖
        = ‖fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ (zc s)
            - ((zc s).1 • Ca + (zc s).2 • Cb)‖ := by rw [hγLpt s]; rfl
      _ ≤ σ / 2 * ‖zc s‖ := hz
      _ ≤ σ / 2 * (|(zc s).1| + |(zc s).2|) :=
          mul_le_mul_of_nonneg_left hsuple (by positivity)
      _ < σ * (|(zc s).1| + |(zc s).2|) := by nlinarith [hzne s]
      _ ≤ ‖γL s‖ := hlow
  -- the circle loop closes
  have hγ₁loop : γ₁ 0 = γ₁ 1 := by
    change G (zc 0) = G (zc 1)
    congr 1
    simp only [hzcdef, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one,
      Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi]
  -- Rouché transfer + the linear winding value (reverse term dominates)
  have heq := windingNumberC_eq_of_perturb γL γ₁ hγLne hγ₁ne
    (linearLoop_loop la lb) hγ₁loop hpert
  have hval := windingNumberC_linearLoop la lb hlab
  have hnotlt : ¬(‖lb‖ < ‖la‖) := by
    rw [hladef, hlbdef, norm_mul, norm_mul, hnδ]
    intro h
    have := (norm_pair_lt_iff Ca Cb).mp (lt_of_mul_lt_mul_left h hδ.le)
    linarith [hLneg]
  refine ⟨γ₀, hγ₀ne, fun s => rfl, ?_⟩
  rw [htrans, ← heq, hval, if_neg hnotlt]

/-! ### The model-margin assembly (`lem:model_margin`)

Per-`κ` packaging of the whole adjacent-slice model side: for every positive
DFV window the radii separate across `1/c` (`dfv_fourBar_quad`), the
tangential construction produces a strictly convex core with
`E_adj(0) = 0` (`fourBar_core_exists`), and at that core the transversality
determinant `(ρ₀−ρ₁)(ρ₁−ρ₂)sin(Φ₂−Φ₁)` is automatically negative — so the
boundary-margin package (`fourBarAnchorAdj_boundary_margin`) and the
boundary-winding `−1` package (`fourBarAnchorAdj_boundary_winding`) apply
with no stratum branch, under one common box-size threshold `δ₀`. -/

/-- **Model margin — D7, per-`κ`, all positive DFV windows** (blueprint
`lem:model_margin`).  For a positive DFV profile (`DFV κ c`, `0 < c`, all
values positive) there are window indices `i₁ < i₂ < i₃ < i₄ < i₁ + n`, block
radii `ρ = (1/κ_{i₁}, 1/κ_{i₂}, 1/κ_{i₃}, 1/κ_{i₄})` and core junction angles
`0 < Φ₁ < Φ₂ < Φ₃ < 2π` with all four cyclic gaps in `(0, π)`, such that the
recentered adjacent-slice anchor has `E_adj(0) = 0` and there is a box-size
threshold `δ₀ > 0` below which **every** origin-centered square boundary of
half-side `δ` carries both model-side inputs of `rouche_closes`: a positive
lower margin `m ≤ ‖E_adj‖` and box-radial boundary winding `−1`.  The margin
is per-`κ` (chosen after `κ`), not uniform over DFV; no stratum hypothesis —
the tangential core makes the Jacobian determinant negative at every window,
including the parallelogram stratum. -/
theorem fourBar_model_margin {κ : ZMod n → ℝ} {c : ℝ} (hc : 0 < c)
    (hpos : ∀ i, 0 < κ i) (h : DFV κ c) :
    ∃ i₁ i₂ i₃ i₄ : ℕ, (i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁ + n) ∧
      ∃ ρ : Fin 4 → ℝ,
        (ρ 0 = 1 / κ ((i₁ : ℕ) : ZMod n) ∧ ρ 1 = 1 / κ ((i₂ : ℕ) : ZMod n) ∧
          ρ 2 = 1 / κ ((i₃ : ℕ) : ZMod n) ∧ ρ 3 = 1 / κ ((i₄ : ℕ) : ZMod n)) ∧
        ∃ Φ₁ Φ₂ Φ₃ : ℝ,
          (0 < Φ₁ ∧ Φ₁ < Φ₂ ∧ Φ₂ < Φ₃ ∧ Φ₃ < 2 * π) ∧
          (Φ₁ < π ∧ Φ₂ - Φ₁ < π ∧ Φ₃ - Φ₂ < π ∧ 2 * π - Φ₃ < π) ∧
          fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ 0 = 0 ∧
          ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
            (∃ m > 0, ∀ z : ℝ × ℝ, boxGauge (-δ) δ (-δ) δ z = 1 →
              m ≤ ‖fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃ z‖) ∧
            ∃ (γ : C(unitInterval, ℂ)) (hγ : ∀ s, γ s ≠ 0),
              (∀ s : unitInterval, γ s = fourBarAnchorAdj ρ Φ₁ Φ₂ Φ₃
                  (boxRadial (-δ) δ (-δ) δ (2 * Real.pi * ↑s))) ∧
              windingNumberC γ hγ = -1 := by
  -- Step 1: radii separation across the threshold `1/c`
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, ⟨r1, r2, r3, r4⟩, -, -⟩ :=
    dfv_fourBar_quad hc hpos h
  set ρ : Fin 4 → ℝ :=
    ![1 / κ ((i₁ : ℕ) : ZMod n), 1 / κ ((i₂ : ℕ) : ZMod n),
      1 / κ ((i₃ : ℕ) : ZMod n), 1 / κ ((i₄ : ℕ) : ZMod n)] with hρ
  have hρ0 : ρ 0 = 1 / κ ((i₁ : ℕ) : ZMod n) := rfl
  have hρ1 : ρ 1 = 1 / κ ((i₂ : ℕ) : ZMod n) := rfl
  have hρ2 : ρ 2 = 1 / κ ((i₃ : ℕ) : ZMod n) := rfl
  have hρ3 : ρ 3 = 1 / κ ((i₄ : ℕ) : ZMod n) := rfl
  -- Step 2: strictly convex tangential core
  obtain ⟨Φ₁, Φ₂, Φ₃, hord, hgap, hzero⟩ :=
    fourBar_core_exists ρ (T := 1 / c) (hρ0 ▸ r1) (hρ2 ▸ r3) (hρ1 ▸ r2)
      (hρ3 ▸ r4)
  -- Step 3: transversality is automatic at the tangential core
  have h01 : ρ 0 < ρ 1 := by rw [hρ0, hρ1]; exact r1.trans r2
  have h21 : ρ 2 < ρ 1 := by rw [hρ2, hρ1]; exact r3.trans r2
  have hsin : 0 < Real.sin (Φ₂ - Φ₁) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hord.2.1]) hgap.2.1
  obtain ⟨δm, hδm, hmarg⟩ :=
    fourBarAnchorAdj_boundary_margin ρ Φ₁ Φ₂ Φ₃ h01.ne h21.ne' hsin.ne' hzero
  obtain ⟨δw, hδw, hwind⟩ :=
    fourBarAnchorAdj_boundary_winding ρ Φ₁ Φ₂ Φ₃ h01 h21 hsin hzero
  refine ⟨i₁, i₂, i₃, i₄, ⟨h12, h23, h34, h41⟩, ρ, ⟨hρ0, hρ1, hρ2, hρ3⟩,
    Φ₁, Φ₂, Φ₃, hord, hgap, hzero, min δm δw, lt_min hδm hδw,
    fun δ hδ hδle => ?_⟩
  exact ⟨hmarg δ hδ (hδle.trans (min_le_left _ _)),
    hwind δ hδ (hδle.trans (min_le_right _ _))⟩

end Gluck.Discrete
