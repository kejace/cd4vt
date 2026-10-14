/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Gluck.Discrete.CollaredContinuation
import Gluck.Discrete.Convexity
import Gluck.Discrete.Converse

/-!
# Route A′/B collar wiring: the conditional general-`n` converse

This file wires the abstract collared-continuation engine
(`compact_collared_continuation`, file `CollaredContinuation.lean`) to the
concrete general-`n` curvature-profile projection, producing the conditional
realizability theorem `realizesR2_of_collar`.

* `projImage_mem_nhds_of_jointSubmersion` — the analytic core: at a solution
  of `G = 0` where the joint derivative `(G', π')` is surjective, the
  parameter projection of any set absorbing all nearby solutions is a
  neighbourhood of the parameter.  This is the correct discharge of the
  local-openness hypothesis; the in-tree wall-crossing lemma
  `regularWallZero_entersInterior` moves inside a fibre at fixed parameter
  and can NOT open the parameter image.
* `collar_hlocal_of_openSolutionSet` — packages the above into hypothesis
  (4) of `compact_collared_continuation`.
* `collared_continuation_subset` — the set-level continuation engine, over a
  preconnected parameter *set* rather than a `PreconnectedSpace` type.
* `closureMapR3`, `collarInterior`, `isOpen_moderateArcZero`,
  `realizesR2_of_mem_collarInterior`, `realizesR2_of_collar` — the concrete
  wiring at general `n ≥ 3`.  The two open research cruxes stay NAMED
  HYPOTHESES: `hD`-compactness (crux A′, chamber compactness modulo collapse
  strata) and `hcollar` (crux B, global inward collar).  The theorem is
  honest: it does not settle Tabachnikov Problem 2; it reduces it to the two
  cruxes plus a pointwise interior regularity condition that the Lorentzian
  Closure Obstruction does not touch.

-/

namespace Gluck.Discrete

open Filter Set
open scoped Topology

/-! ## Joint submersion opens the parameter image -/

/-- **Joint submersion at a solution opens the parameter image.**  Let
`G : E → F` be a closure map and `π : E → K` a parameter map, both strictly
differentiable at a solution `x` of `G = 0`, with the *joint* derivative
`v ↦ (G' v, π' v)` surjective.  If `U` contains all solutions in some
neighbourhood `V` of `x`, then `π '' U` is a neighbourhood of `π x`.
This is the same inverse-function-theorem step as Mathlib's Lagrange
multiplier proof, repackaged as a statement about the parameter image. -/
theorem projImage_mem_nhds_of_jointSubmersion
    {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    {G : E → F} {π : E → K} {G' : E →L[ℝ] F} {π' : E →L[ℝ] K} {x : E}
    (hGx : G x = 0)
    (hG : HasStrictFDerivAt G G' x) (hπ : HasStrictFDerivAt π π' x)
    (hsurj : (G'.prod π').range = ⊤)
    {V : Set E} (hV : V ∈ 𝓝 x)
    {U : Set E} (hU : {y | G y = 0} ∩ V ⊆ U) :
    π '' U ∈ 𝓝 (π x) := by
  have hH : HasStrictFDerivAt (fun y => (G y, π y)) (G'.prod π') x := hG.prodMk hπ
  have hmap : Filter.map (fun y => (G y, π y)) (𝓝 x) = 𝓝 (G x, π x) :=
    hH.map_nhds_eq_of_surj hsurj
  have hHV : (fun y => (G y, π y)) '' V ∈ 𝓝 ((0 : F), π x) := by
    rw [← hGx, ← hmap]
    exact Filter.image_mem_map hV
  have hWnhds : (fun k : K => ((0 : F), k)) ⁻¹' ((fun y => (G y, π y)) '' V)
      ∈ 𝓝 (π x) :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hHV
  refine Filter.mem_of_superset hWnhds ?_
  rintro k hkW
  obtain ⟨y, hyV, hy⟩ := hkW
  have hyG : G y = 0 := (Prod.ext_iff.mp hy).1
  have hyπ : π y = k := (Prod.ext_iff.mp hy).2
  exact ⟨y, hU ⟨hyG, hyV⟩, hyπ⟩

/-- **Interior submersion ⇒ local openness.**  A set `U` of solutions of
`G = 0` that is relatively open among solutions and consists of joint-regular
points satisfies the local-openness hypothesis of
`compact_collared_continuation`. -/
theorem collar_hlocal_of_openSolutionSet
    {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    {G : E → F} {π : E → K} {U : Set E}
    (hsol : ∀ x ∈ U, G x = 0)
    (hopen : ∀ x ∈ U, ∃ V ∈ 𝓝 x, {y | G y = 0} ∩ V ⊆ U)
    (hreg : ∀ x ∈ U, ∃ (G' : E →L[ℝ] F) (π' : E →L[ℝ] K),
      HasStrictFDerivAt G G' x ∧ HasStrictFDerivAt π π' x ∧
      (G'.prod π').range = ⊤) :
    ∀ x ∈ U, π '' U ∈ 𝓝 (π x) := by
  intro x hx
  obtain ⟨V, hV, hVU⟩ := hopen x hx
  obtain ⟨G', π', hG, hπ, hsurj⟩ := hreg x hx
  exact projImage_mem_nhds_of_jointSubmersion (hsol x hx) hG hπ hsurj hV hVU

/-! ## The set-level continuation engine -/

/-- **Collared continuation over a preconnected parameter set.**  The engine
of `compact_collared_continuation` with the parameter chamber given as a
preconnected subset `S` of the parameter space rather than a
`PreconnectedSpace` instance; local openness is required only relative to
`S`.  Concludes `S ⊆ π '' U`. -/
theorem collared_continuation_subset
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K] [T2Space K]
    {D U : Set X} {π : X → K} {S : Set K}
    (hS : IsPreconnected S)
    (hD : IsCompact D) (hne : D.Nonempty) (hUD : U ⊆ D)
    (hπ : ContinuousOn π D) (hDS : π '' D ⊆ S)
    (hcollar : ∀ x ∈ D, ∃ y ∈ U, π y = π x)
    (hlocal : ∀ x ∈ U, π '' U ∈ 𝓝[S] (π x)) :
    S ⊆ π '' U := by
  have himage : π '' D = π '' U := (fiberPurification_iff_image_eq hUD).mp hcollar
  have hAS : π '' U ⊆ S := himage ▸ hDS
  have hclosed : IsClosed (π '' U) :=
    himage ▸ (hD.image_of_continuousOn hπ).isClosed
  haveI := Subtype.preconnectedSpace hS
  set A' : Set S := Subtype.val ⁻¹' (π '' U) with hA'
  have hclosed' : IsClosed A' := hclosed.preimage continuous_subtype_val
  have hopen' : IsOpen A' := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨k, hkS⟩ hk
    obtain ⟨x, hxU, hxk⟩ := hk
    have h1 : π '' U ∈ 𝓝[S] (π x) := hlocal x hxU
    rw [hxk] at h1
    exact preimage_coe_mem_nhds_subtype.mpr h1
  have hne' : A'.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hyU, -⟩ := hcollar x hx
    exact ⟨⟨π y, hAS ⟨y, hyU, rfl⟩⟩, ⟨y, hyU, rfl⟩⟩
  have huniv : A' = Set.univ := IsClopen.eq_univ ⟨hclosed', hopen'⟩ hne'
  intro k hkS
  have hmem : (⟨k, hkS⟩ : S) ∈ A' := huniv.symm ▸ Set.mem_univ _
  exact hmem

/-! ## The concrete general-`n` wiring -/

variable {n : ℕ}

/-- The joint Euclidean closure map: closure gap and total-turning defect.
`closureMapR3 p = 0` says exactly that the development of `p = (κ, ℓ)`
closes up with total turning `2π`. -/
noncomputable def closureMapR3 [NeZero n]
    (p : (ZMod n → ℝ) × (ZMod n → ℝ)) : ℂ × ℝ :=
  (closureGap p.1 p.2, turningSum p.1 p.2 - 2 * Real.pi)

/-- The strict-interior solution set over a profile chamber `S`: moderate-arc
closed configurations with total turning `2π` whose profile lies in `S`. -/
def collarInterior [NeZero n] (S : Set (ZMod n → ℝ)) :
    Set ((ZMod n → ℝ) × (ZMod n → ℝ)) :=
  {p | p.1 ∈ S ∧ ModerateArc 0 p.1 p.2 ∧ closureMapR3 p = 0}

/-- The Euclidean strict moderate-arc condition is open in the configuration
space `(κ, ℓ)`: it is a finite conjunction of strict inequalities among
continuous functions. -/
theorem isOpen_moderateArcZero [NeZero n] :
    IsOpen {p : (ZMod n → ℝ) × (ZMod n → ℝ) | ModerateArc 0 p.1 p.2} := by
  have heq : {p : (ZMod n → ℝ) × (ZMod n → ℝ) | ModerateArc 0 p.1 p.2} =
      ⋂ i : ZMod n,
        ({p : (ZMod n → ℝ) × (ZMod n → ℝ) | 0 < p.2 i} ∩
          {p : (ZMod n → ℝ) × (ZMod n → ℝ) | |p.1 i| * (p.2 (i - 1) / 2) < 1} ∩
          {p : (ZMod n → ℝ) × (ZMod n → ℝ) | |p.1 i| * (p.2 i / 2) < 1}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, ModerateArc,
      sK_zero, cK_zero, tK_zero]
    constructor
    · intro h i
      obtain ⟨h1, _, _, h4, h5⟩ := h i
      exact ⟨⟨h1, h4⟩, h5⟩
    · intro h i
      obtain ⟨⟨h1, h4⟩, h5⟩ := h i
      exact ⟨h1, by linarith, one_pos, h4, h5⟩
  rw [heq]
  refine isOpen_iInter_of_finite fun i => ?_
  have hℓ : Continuous fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => p.2 i :=
    (continuous_apply i).comp continuous_snd
  have hℓ' : Continuous fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => p.2 (i - 1) :=
    (continuous_apply (i - 1)).comp continuous_snd
  have hκ : Continuous fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => |p.1 i| :=
    ((continuous_apply i).comp continuous_fst).abs
  exact ((isOpen_lt continuous_const hℓ).inter
      (isOpen_lt (hκ.mul (hℓ'.div_const 2)) continuous_const)).inter
    (isOpen_lt (hκ.mul (hℓ.div_const 2)) continuous_const)

/-- **Membership in the collar interior gives realizability** (the
Positive-Convexity Collapse): a positive-profile strict-interior solution is
a `RealizesR2` witness — simplicity is free in the positive case. -/
theorem realizesR2_of_mem_collarInterior [NeZero n] (hn : 3 ≤ n)
    {S : Set (ZMod n → ℝ)} {p : (ZMod n → ℝ) × (ZMod n → ℝ)}
    (hp : p ∈ collarInterior S) (hpos : ∀ i, 0 < p.1 i) :
    RealizesR2 p.1 := by
  obtain ⟨-, hMA, hG⟩ := hp
  rw [closureMapR3, Prod.ext_iff] at hG
  have hE : closureGap p.1 p.2 = 0 := hG.1
  have hT : turningSum p.1 p.2 = 2 * Real.pi := by
    have h2 : turningSum p.1 p.2 - 2 * Real.pi = 0 := hG.2
    linarith
  exact ⟨p.2, hMA, hE, hT,
    isSimplePolygon_of_turningPositive hn hMA hpos hE hT⟩

/-- **Route A′/B collar wiring, conditional, general `n`.**  Over a
preconnected chamber `S` of positive profiles, IF the closed solution set
`D` is compact with profile image in `S` (crux A′, `hD`/`hDS`), IF every
closed solution admits a same-profile strict-interior representative (crux
B, `hcollar`), and IF the closure map is jointly regular at every interior
solution (pointwise — untouched by the Lorentzian Closure Obstruction), THEN
every profile in `S` is realizable.  Honest scope: this does NOT settle
Tabachnikov Problem 2 — `hD` and `hcollar` are the two open research cruxes,
here reduced to clean named hypotheses about an explicit subset of
`(ZMod n → ℝ)²`. -/
theorem realizesR2_of_collar [NeZero n] (hn : 3 ≤ n)
    {S : Set (ZMod n → ℝ)} (hS : IsPreconnected S)
    (hSpos : ∀ κ ∈ S, ∀ i, 0 < κ i)
    {D : Set ((ZMod n → ℝ) × (ZMod n → ℝ))}
    (hD : IsCompact D) (hDne : D.Nonempty)
    (hUD : collarInterior S ⊆ D)
    (hDS : Prod.fst '' D ⊆ S)
    (hcollar : ∀ p ∈ D, ∃ q ∈ collarInterior S, q.1 = p.1)
    (hreg : ∀ p ∈ collarInterior S,
      ∃ G' : ((ZMod n → ℝ) × (ZMod n → ℝ)) →L[ℝ] ℂ × ℝ,
        HasStrictFDerivAt closureMapR3 G' p ∧
        (G'.prod (ContinuousLinearMap.fst ℝ (ZMod n → ℝ) (ZMod n → ℝ))).range
          = ⊤) :
    ∀ κ ∈ S, RealizesR2 κ := by
  have hlocal : ∀ p ∈ collarInterior S,
      Prod.fst '' collarInterior S ∈ 𝓝[S] p.1 := by
    intro p hp
    obtain ⟨G', hG, hsurj⟩ := hreg p hp
    have h0 : Prod.fst ''
        ({y : (ZMod n → ℝ) × (ZMod n → ℝ) | closureMapR3 y = 0} ∩
          {q : (ZMod n → ℝ) × (ZMod n → ℝ) | ModerateArc 0 q.1 q.2})
        ∈ 𝓝 p.1 :=
      projImage_mem_nhds_of_jointSubmersion hp.2.2 hG hasStrictFDerivAt_fst
        hsurj (isOpen_moderateArcZero.mem_nhds hp.2.1) Set.Subset.rfl
    refine Filter.mem_of_superset
      (Filter.inter_mem (nhdsWithin_le_nhds h0) self_mem_nhdsWithin) ?_
    rintro k ⟨⟨y, ⟨hy0, hyMA⟩, rfl⟩, hkS⟩
    exact ⟨y, ⟨hkS, hyMA, hy0⟩, rfl⟩
  have himg : S ⊆ Prod.fst '' collarInterior S :=
    collared_continuation_subset hS hD hDne hUD continuous_fst.continuousOn
      hDS hcollar hlocal
  intro κ hκ
  obtain ⟨p, hp, hpκ⟩ := himg hκ
  have hpos : ∀ i, 0 < p.1 i := by rw [hpκ]; exact hSpos κ hκ
  have hreal := realizesR2_of_mem_collarInterior hn hp hpos
  rwa [hpκ] at hreal

/-! ## Nonemptiness of the collar interior from the regular polygon -/

/-- Whenever the constant profile `κ ≡ c > 0` lies in the chamber `S`, the
regular `n`-gon supplies a strict-interior solution — the nonemptiness input
of the collar wiring at general `n`. -/
theorem collarInterior_nonempty_of_const [NeZero n] (hn : 3 ≤ n)
    {S : Set (ZMod n → ℝ)} {c : ℝ} (hc : 0 < c)
    (hcS : (fun _ : ZMod n => c) ∈ S) :
    (collarInterior S).Nonempty := by
  obtain ⟨hMA, -, hsum, hclose⟩ := regularGon_closes hn hc
  refine ⟨⟨fun _ => c, fun _ => 2 / c * Real.sin (Real.pi / n)⟩, hcS, hMA, ?_⟩
  simp [closureMapR3, hclose, hsum]

/-! ## Strict differentiability of the closure map on the moderate-arc
domain

The `hreg` hypothesis of `realizesR2_of_collar` bundles strict
differentiability with joint surjectivity.  The differentiability half is in
fact a theorem on the whole strict moderate-arc domain: every constituent of
`closureMapR3` is a finite algebraic/arcsin/exponential combination of the
coordinates, and the strict walls keep every `arcsin` argument inside
`(-1, 1)`.  This reduces `hreg` to a pointwise rank condition on the
canonical derivative (`realizesR2_of_collar_of_fderivSurj`). -/

private lemma arcsinAtom_hasStrictFDerivAt [NeZero n] (i j : ZMod n)
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)}
    (hwall : |p.1 i| * (p.2 j / 2) < 1) (hpos : 0 < p.2 j) :
    ∃ f' : ((ZMod n → ℝ) × (ZMod n → ℝ)) →L[ℝ] ℝ,
      HasStrictFDerivAt
        (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) =>
          Real.arcsin (q.1 i * (q.2 j / 2))) f' p := by
  have hκ : HasStrictFDerivAt
      (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => q.1 i)
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℝ (ZMod n → ℝ) (ZMod n → ℝ))) p :=
    ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ (ZMod n → ℝ) (ZMod n → ℝ))).hasStrictFDerivAt
  have hℓ : HasStrictFDerivAt
      (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => q.2 j)
      ((ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.snd ℝ (ZMod n → ℝ) (ZMod n → ℝ))) p :=
    ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (ZMod n → ℝ) (ZMod n → ℝ))).hasStrictFDerivAt
  have hfe : (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) =>
        Real.arcsin (q.1 i * (q.2 j / 2)))
      = fun q => Real.arcsin (q.1 i * (q.2 j * 2⁻¹)) := by
    funext q
    rw [div_eq_mul_inv]
  have hbase : HasStrictFDerivAt
      (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => q.1 i * (q.2 j * 2⁻¹)) _ p :=
    HasStrictFDerivAt.mul hκ (HasStrictFDerivAt.mul_const hℓ 2⁻¹)
  have harg : |p.1 i * (p.2 j * 2⁻¹)| < 1 := by
    rw [← div_eq_mul_inv, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < p.2 j / 2)]
    exact hwall
  rw [abs_lt] at harg
  rw [hfe]
  exact ⟨_, HasStrictDerivAt.comp_hasStrictFDerivAt p
    (Real.hasStrictDerivAt_arcsin (by linarith) (by linarith)) hbase⟩

private lemma turningAngleFn_hasStrictFDerivAt [NeZero n]
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)} (hMA : ModerateArc 0 p.1 p.2)
    (i : ZMod n) :
    ∃ f' : ((ZMod n → ℝ) × (ZMod n → ℝ)) →L[ℝ] ℝ,
      HasStrictFDerivAt
        (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) =>
          turningAngle 0 q.1 q.2 i) f' p := by
  have hwl : |p.1 i| * (p.2 (i - 1) / 2) < 1 := by
    have := hMA.wall_left i; rwa [tK_zero] at this
  have hwr : |p.1 i| * (p.2 i / 2) < 1 := by
    have := hMA.wall_right i; rwa [tK_zero] at this
  obtain ⟨f₁, h₁⟩ := arcsinAtom_hasStrictFDerivAt i (i - 1) hwl
    (hMA.length_pos (i - 1))
  obtain ⟨f₂, h₂⟩ := arcsinAtom_hasStrictFDerivAt i i hwr (hMA.length_pos i)
  refine ⟨f₁ + f₂, ?_⟩
  have hfe : (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => turningAngle 0 q.1 q.2 i)
      = fun q => Real.arcsin (q.1 i * (q.2 (i - 1) / 2)) +
          Real.arcsin (q.1 i * (q.2 i / 2)) := by
    funext q
    simp [turningAngle]
  rw [hfe]
  exact HasStrictFDerivAt.add h₁ h₂

private lemma turningSumFn_hasStrictFDerivAt [NeZero n]
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)} (hMA : ModerateArc 0 p.1 p.2) :
    ∃ f' : ((ZMod n → ℝ) × (ZMod n → ℝ)) →L[ℝ] ℝ,
      HasStrictFDerivAt
        (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => turningSum q.1 q.2) f' p := by
  choose f hf using fun i : ZMod n => turningAngleFn_hasStrictFDerivAt hMA i
  refine ⟨∑ i : ZMod n, f i, ?_⟩
  have hfe : (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => turningSum q.1 q.2)
      = ∑ i : ZMod n, fun q : (ZMod n → ℝ) × (ZMod n → ℝ) =>
          turningAngle 0 q.1 q.2 i := by
    funext q
    simp [turningSum, Finset.sum_apply]
  rw [hfe]
  exact HasStrictFDerivAt.sum fun i _ => hf i

private lemma headingFn_hasStrictFDerivAt [NeZero n]
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)} (hMA : ModerateArc 0 p.1 p.2)
    (j : ℕ) :
    ∃ f' : ((ZMod n → ℝ) × (ZMod n → ℝ)) →L[ℝ] ℝ,
      HasStrictFDerivAt
        (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => heading q.1 q.2 j) f' p := by
  choose f hf using fun i : ZMod n => turningAngleFn_hasStrictFDerivAt hMA i
  refine ⟨∑ m ∈ Finset.range (j + 1), f (m : ZMod n), ?_⟩
  have hfe : (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => heading q.1 q.2 j)
      = ∑ m ∈ Finset.range (j + 1),
          fun q : (ZMod n → ℝ) × (ZMod n → ℝ) =>
            turningAngle 0 q.1 q.2 (m : ZMod n) := by
    funext q
    simp [heading, Finset.sum_apply]
  rw [hfe]
  exact HasStrictFDerivAt.sum fun m _ => hf (m : ZMod n)

private lemma edgeFn_hasStrictFDerivAt [NeZero n]
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)} (hMA : ModerateArc 0 p.1 p.2)
    (j : ℕ) :
    ∃ f' : ((ZMod n → ℝ) × (ZMod n → ℝ)) →L[ℝ] ℂ,
      HasStrictFDerivAt
        (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) =>
          (q.2 (j : ZMod n) : ℂ) *
            Complex.exp ((heading q.1 q.2 j : ℂ) * Complex.I)) f' p := by
  obtain ⟨h', hh⟩ := headingFn_hasStrictFDerivAt hMA j
  have hofReal : HasStrictFDerivAt
      (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => ((heading q.1 q.2 j : ℝ) : ℂ))
      (Complex.ofRealCLM.comp h') p := by
    have := Complex.ofRealCLM.hasStrictFDerivAt.comp p hh
    simpa [Function.comp] using this
  have hexp : HasStrictFDerivAt
      (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) =>
        Complex.exp ((heading q.1 q.2 j : ℂ) * Complex.I)) _ p :=
    HasStrictFDerivAt.cexp
      (HasStrictFDerivAt.mul_const hofReal Complex.I)
  have hlen : HasStrictFDerivAt
      (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => (q.2 (j : ZMod n) : ℂ))
      (Complex.ofRealCLM.comp
        ((ContinuousLinearMap.proj (j : ZMod n)).comp
          (ContinuousLinearMap.snd ℝ (ZMod n → ℝ) (ZMod n → ℝ)))) p := by
    have := Complex.ofRealCLM.hasStrictFDerivAt.comp p
      (((ContinuousLinearMap.proj (j : ZMod n)).comp
        (ContinuousLinearMap.snd ℝ (ZMod n → ℝ) (ZMod n → ℝ))).hasStrictFDerivAt
        (x := p))
    simpa [Function.comp] using this
  exact ⟨_, HasStrictFDerivAt.mul hlen hexp⟩

private lemma closureGapFn_hasStrictFDerivAt [NeZero n]
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)} (hMA : ModerateArc 0 p.1 p.2) :
    ∃ f' : ((ZMod n → ℝ) × (ZMod n → ℝ)) →L[ℝ] ℂ,
      HasStrictFDerivAt
        (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => closureGap q.1 q.2) f' p := by
  choose f hf using fun j : ℕ => edgeFn_hasStrictFDerivAt hMA j
  refine ⟨∑ j ∈ Finset.range n, f j, ?_⟩
  have hfe : (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) => closureGap q.1 q.2)
      = ∑ j ∈ Finset.range n,
          fun q : (ZMod n → ℝ) × (ZMod n → ℝ) =>
            (q.2 (j : ZMod n) : ℂ) *
              Complex.exp ((heading q.1 q.2 j : ℂ) * Complex.I) := by
    funext q
    simp [closureGap, vertexR2, Finset.sum_apply]
  rw [hfe]
  exact HasStrictFDerivAt.sum fun j _ => hf j

/-- **The joint closure map is strictly differentiable at every moderate-arc
configuration.**  The differentiability half of the interior-regularity
hypothesis of `realizesR2_of_collar` is a theorem; only the joint rank
condition remains pointwise. -/
theorem closureMapR3_hasStrictFDerivAt [NeZero n]
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)} (hMA : ModerateArc 0 p.1 p.2) :
    ∃ G' : ((ZMod n → ℝ) × (ZMod n → ℝ)) →L[ℝ] ℂ × ℝ,
      HasStrictFDerivAt closureMapR3 G' p := by
  obtain ⟨gE, hE⟩ := closureGapFn_hasStrictFDerivAt hMA
  obtain ⟨gT, hT⟩ := turningSumFn_hasStrictFDerivAt hMA
  have hTs : HasStrictFDerivAt
      (fun q : (ZMod n → ℝ) × (ZMod n → ℝ) =>
        turningSum q.1 q.2 - 2 * Real.pi) gT p :=
    HasStrictFDerivAt.sub_const (2 * Real.pi) hT
  exact ⟨gE.prod gT, HasStrictFDerivAt.prodMk hE hTs⟩

/-- Variant of `realizesR2_of_collar` with the regularity hypothesis reduced
to its honest core: joint surjectivity of the *canonical* derivative
`fderiv ℝ closureMapR3 p` with the profile projection, the strict
differentiability being supplied by `closureMapR3_hasStrictFDerivAt`. -/
theorem realizesR2_of_collar_of_fderivSurj [NeZero n] (hn : 3 ≤ n)
    {S : Set (ZMod n → ℝ)} (hS : IsPreconnected S)
    (hSpos : ∀ κ ∈ S, ∀ i, 0 < κ i)
    {D : Set ((ZMod n → ℝ) × (ZMod n → ℝ))}
    (hD : IsCompact D) (hDne : D.Nonempty)
    (hUD : collarInterior S ⊆ D)
    (hDS : Prod.fst '' D ⊆ S)
    (hcollar : ∀ p ∈ D, ∃ q ∈ collarInterior S, q.1 = p.1)
    (hreg : ∀ p ∈ collarInterior S,
      ((fderiv ℝ closureMapR3 p).prod
        (ContinuousLinearMap.fst ℝ (ZMod n → ℝ) (ZMod n → ℝ))).range = ⊤) :
    ∀ κ ∈ S, RealizesR2 κ := by
  refine realizesR2_of_collar hn hS hSpos hD hDne hUD hDS hcollar ?_
  intro p hp
  obtain ⟨G', hG⟩ := closureMapR3_hasStrictFDerivAt hp.2.1
  have hfd : fderiv ℝ closureMapR3 p = G' :=
    HasFDerivAt.fderiv (HasStrictFDerivAt.hasFDerivAt hG)
  exact ⟨G', hG, by rw [← hfd]; exact hreg p hp⟩

/-! ## Crux C: the fibre-rank reduction of interior regularity

The `hreg` hypothesis of `realizesR2_of_collar` pairs the closure derivative
with the profile projection `Prod.fst`; because the parameter map is a
projection, joint surjectivity collapses to surjectivity of the derivative
in the edge-length (fibre) directions alone.  This section proves the
collapse, computes the resulting length columns in closed form (the moment
form), records the honest constant-profile degeneracy, and performs the
regular-locus repair. -/

/-- **Joint surjectivity over a projection is fibre surjectivity.**  The
fibre-split lemma reducing the joint-regularity hypothesis of the collar
wiring to a condition on the length derivative alone (crux C). -/
theorem range_prod_fst_eq_top_iff
    {E₁ E₂ F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G' : (E₁ × E₂) →L[ℝ] F) :
    ((G'.prod (ContinuousLinearMap.fst ℝ E₁ E₂)).range = ⊤ ↔
      Function.Surjective fun b : E₂ => G' (0, b)) := by
  rw [LinearMap.range_eq_top]
  constructor
  · intro hsurj f
    obtain ⟨v, hv⟩ := hsurj (f, 0)
    have h1 : G' v = f := congrArg Prod.fst hv
    have h2 : v.1 = (0 : E₁) := congrArg Prod.snd hv
    refine ⟨v.2, ?_⟩
    show G' (0, v.2) = f
    rw [← h2]
    exact h1
  · rintro hsurj ⟨f, a⟩
    obtain ⟨b, hb⟩ := hsurj (f - G' (a, 0))
    have hb' : G' (0, b) = f - G' (a, 0) := hb
    refine ⟨(a, b), Prod.ext ?_ ?_⟩
    · show G' (a, b) = f
      have hsplit : ((a, b) : E₁ × E₂) = (a, 0) + (0, b) := by simp
      rw [hsplit, map_add, hb']
      abel
    · rfl

/-- **Crux C as a predicate**: a configuration has *full length rank* when
the derivative of the closure map in the edge-length directions alone is
surjective onto `ℂ × ℝ`. -/
def LengthRank [NeZero n] (p : (ZMod n → ℝ) × (ZMod n → ℝ)) : Prop :=
  Function.Surjective fun b : ZMod n → ℝ => fderiv ℝ closureMapR3 p (0, b)

/-- **Wiring theorem, fibre-rank form**: the regularity hypothesis of the
collar wiring reduced to crux C — full length rank at every interior
solution. -/
theorem realizesR2_of_collar_of_lengthSurj [NeZero n] (hn : 3 ≤ n)
    {S : Set (ZMod n → ℝ)} (hS : IsPreconnected S)
    (hSpos : ∀ κ ∈ S, ∀ i, 0 < κ i)
    {D : Set ((ZMod n → ℝ) × (ZMod n → ℝ))}
    (hD : IsCompact D) (hDne : D.Nonempty)
    (hUD : collarInterior S ⊆ D)
    (hDS : Prod.fst '' D ⊆ S)
    (hcollar : ∀ p ∈ D, ∃ q ∈ collarInterior S, q.1 = p.1)
    (hreg : ∀ p ∈ collarInterior S, LengthRank p) :
    ∀ κ ∈ S, RealizesR2 κ := by
  refine realizesR2_of_collar_of_fderivSurj hn hS hSpos hD hDne hUD hDS
    hcollar fun p hp => ?_
  exact (range_prod_fst_eq_top_iff (fderiv ℝ closureMapR3 p)).mpr (hreg p hp)

/-! ### The length columns in closed form

Throughout, the length derivative at `(κ, ℓ)` in the `k`-th coordinate
direction is computed along the affine path `t ↦ ℓ + t • Pi.single k 1`.
The two arcsine slopes are the coefficients `a_i` (incoming edge) and `b_i`
(outgoing edge) of the blueprint. -/

/-- The incoming arcsine slope `a_i = (κ_i/2) / √(1 - (κ_i ℓ_{i-1}/2)²)`:
the derivative of the turning angle `θ_i` with respect to the incoming edge
length `ℓ_{i-1}`.  Finite exactly on the strict moderate-arc walls. -/
noncomputable def collarA (κ ℓ : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  κ i / 2 / Real.sqrt (1 - (κ i * (ℓ (i - 1) / 2)) ^ 2)

/-- The outgoing arcsine slope `b_i = (κ_i/2) / √(1 - (κ_i ℓ_i/2)²)`: the
derivative of the turning angle `θ_i` with respect to the outgoing edge
length `ℓ_i`. -/
noncomputable def collarB (κ ℓ : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  κ i / 2 / Real.sqrt (1 - (κ i * (ℓ i / 2)) ^ 2)

private lemma arcsinAtom_path_hasDerivAt {κ ℓ : ZMod n → ℝ} (i j k : ZMod n)
    (hwall : |κ i| * (ℓ j / 2) < 1) (hpos : 0 < ℓ j) :
    HasDerivAt
      (fun t : ℝ =>
        Real.arcsin (κ i * ((ℓ + t • Pi.single k 1 : ZMod n → ℝ) j / 2)))
      ((if j = k then (1 : ℝ) else 0) * (κ i / 2) /
        Real.sqrt (1 - (κ i * (ℓ j / 2)) ^ 2)) 0 := by
  have habs : |κ i * (ℓ j / 2)| < 1 := by
    rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ℓ j / 2)]
  rw [abs_lt] at habs
  have hfe : (fun t : ℝ =>
        Real.arcsin (κ i * ((ℓ + t • Pi.single k 1 : ZMod n → ℝ) j / 2)))
      = fun t : ℝ =>
          Real.arcsin (κ i * ((ℓ j + t * (if j = k then (1 : ℝ) else 0)) / 2)) := by
    funext t
    simp [Pi.single_apply, smul_eq_mul]
  rw [hfe]
  have hu : HasDerivAt
      (fun t : ℝ => κ i * ((ℓ j + t * (if j = k then (1 : ℝ) else 0)) / 2))
      (κ i * ((if j = k then (1 : ℝ) else 0) / 2)) 0 :=
    (((hasDerivAt_mul_const (if j = k then (1 : ℝ) else 0)).const_add
      (ℓ j)).div_const 2).const_mul (κ i)
  have h0 : κ i * ((ℓ j + 0 * (if j = k then (1 : ℝ) else 0)) / 2)
      = κ i * (ℓ j / 2) := by ring
  have harc : HasDerivAt Real.arcsin
      (1 / Real.sqrt (1 - (κ i * (ℓ j / 2)) ^ 2))
      (κ i * ((ℓ j + 0 * (if j = k then (1 : ℝ) else 0)) / 2)) := by
    rw [h0]
    exact Real.hasDerivAt_arcsin (by linarith) (by linarith)
  have hcomp := harc.comp 0 hu
  have hval : (if j = k then (1 : ℝ) else 0) * (κ i / 2) /
        Real.sqrt (1 - (κ i * (ℓ j / 2)) ^ 2)
      = 1 / Real.sqrt (1 - (κ i * (ℓ j / 2)) ^ 2) *
        (κ i * ((if j = k then (1 : ℝ) else 0) / 2)) := by
    ring
  rw [hval]
  exact hcomp

private lemma turningAngle_path_hasDerivAt {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (k i : ZMod n) :
    HasDerivAt
      (fun t : ℝ => turningAngle 0 κ (ℓ + t • Pi.single k (1 : ℝ)) i)
      ((if i = k + 1 then collarA κ ℓ i else 0) +
        (if i = k then collarB κ ℓ i else 0)) 0 := by
  have hwl : |κ i| * (ℓ (i - 1) / 2) < 1 := by
    have := hMA.wall_left i; rwa [tK_zero] at this
  have hwr : |κ i| * (ℓ i / 2) < 1 := by
    have := hMA.wall_right i; rwa [tK_zero] at this
  have h₁ := arcsinAtom_path_hasDerivAt (κ := κ) (ℓ := ℓ) i (i - 1) k hwl
    (hMA.length_pos (i - 1))
  have h₂ := arcsinAtom_path_hasDerivAt (κ := κ) (ℓ := ℓ) i i k hwr
    (hMA.length_pos i)
  have hfe : (fun t : ℝ => turningAngle 0 κ (ℓ + t • Pi.single k (1 : ℝ)) i)
      = fun t : ℝ =>
          Real.arcsin (κ i * ((ℓ + t • Pi.single k 1 : ZMod n → ℝ) (i - 1) / 2)) +
            Real.arcsin (κ i * ((ℓ + t • Pi.single k 1 : ZMod n → ℝ) i / 2)) := by
    funext t
    simp [turningAngle]
  rw [hfe]
  have hval : (if i = k + 1 then collarA κ ℓ i else 0) +
        (if i = k then collarB κ ℓ i else 0)
      = (if i - 1 = k then (1 : ℝ) else 0) * (κ i / 2) /
          Real.sqrt (1 - (κ i * (ℓ (i - 1) / 2)) ^ 2)
        + (if i = k then (1 : ℝ) else 0) * (κ i / 2) /
          Real.sqrt (1 - (κ i * (ℓ i / 2)) ^ 2) := by
    simp only [collarA, collarB, sub_eq_iff_eq_add]
    split_ifs <;> ring
  rw [hval]
  exact h₁.add h₂

/-- **Total-turning length gradient** `∂T/∂ℓ_k = b_k + a_{k+1}`: the length
`ℓ_k` occurs in exactly two turning angles, outgoing at vertex `k` and
incoming at vertex `k+1`. -/
theorem turningSum_lengthDeriv [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (k : ZMod n) :
    HasDerivAt (fun t : ℝ => turningSum κ (ℓ + t • Pi.single k (1 : ℝ)))
      (collarB κ ℓ k + collarA κ ℓ (k + 1)) 0 := by
  have hfe : (fun t : ℝ => turningSum κ (ℓ + t • Pi.single k (1 : ℝ)))
      = ∑ i : ZMod n, fun t : ℝ =>
          turningAngle 0 κ (ℓ + t • Pi.single k (1 : ℝ)) i := by
    funext t
    simp [turningSum, Finset.sum_apply]
  rw [hfe]
  have hval : collarB κ ℓ k + collarA κ ℓ (k + 1)
      = ∑ i : ZMod n, ((if i = k + 1 then collarA κ ℓ i else 0) +
          (if i = k then collarB κ ℓ i else 0)) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (k + 1)
      (fun i => collarA κ ℓ i), Finset.sum_ite_eq' Finset.univ k
      (fun i => collarB κ ℓ i)]
    simp [add_comm]
  rw [hval]
  exact HasDerivAt.sum fun i _ => turningAngle_path_hasDerivAt hMA k i

private lemma sum_range_natCast_ite [NeZero n] {M : Type*} [AddCommMonoid M]
    (q : ZMod n) (f : ℕ → M) :
    (∑ m ∈ Finset.range n, if ((m : ZMod n)) = q then f m else 0) = f q.val := by
  have hcongr : ∀ m ∈ Finset.range n,
      (if ((m : ZMod n)) = q then f m else 0) = if m = q.val then f m else 0 := by
    intro m hm
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · simpa [ZMod.val_cast_of_lt (Finset.mem_range.mp hm)] using
        congrArg ZMod.val h
    · rw [h]
      exact ZMod.natCast_rightInverse q
  rw [Finset.sum_congr rfl hcongr,
    Finset.sum_ite_eq' (Finset.range n) q.val f]
  simp [ZMod.val_lt q]

private lemma sum_range_indicator [NeZero n] {M : Type*} [AddCommMonoid M]
    (q : ZMod n) (c : M) {j : ℕ} (hj : j < n) :
    (∑ m ∈ Finset.range (j + 1), if ((m : ZMod n)) = q then c else 0)
      = if q.val ≤ j then c else 0 := by
  have hcongr : ∀ m ∈ Finset.range (j + 1),
      (if ((m : ZMod n)) = q then c else 0) = if m = q.val then c else 0 := by
    intro m hm
    have hmn : m < n :=
      lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hj
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · simpa [ZMod.val_cast_of_lt hmn] using congrArg ZMod.val h
    · rw [h]
      exact ZMod.natCast_rightInverse q
  rw [Finset.sum_congr rfl hcongr,
    Finset.sum_ite_eq' (Finset.range (j + 1)) q.val (fun _ => c)]
  simp

private lemma sum_range_tail {M : Type*} [AddCommGroup M] (f : ℕ → M)
    {m N : ℕ} (hm : m ≤ N) :
    (∑ j ∈ Finset.range N, if m ≤ j then f j else 0)
      = ∑ j ∈ Finset.range N, f j - ∑ j ∈ Finset.range m, f j := by
  rw [← Finset.sum_Ico_eq_sub f hm]
  have hsub : Finset.Ico m N ⊆ Finset.range N := by
    intro x hx
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
  rw [← Finset.sum_subset hsub (fun x hx hnx => ?_)]
  · exact Finset.sum_congr rfl fun x hx => if_pos (Finset.mem_Ico.mp hx).1
  · rw [if_neg]
    intro hmx
    exact hnx (Finset.mem_Ico.mpr ⟨hmx, Finset.mem_range.mp hx⟩)

private lemma heading_path_hasDerivAt [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (k : ZMod n) {j : ℕ} (hj : j < n) :
    HasDerivAt (fun t : ℝ => heading κ (ℓ + t • Pi.single k (1 : ℝ)) j)
      ((if k.val ≤ j then collarB κ ℓ k else 0) +
        (if (k + 1).val ≤ j then collarA κ ℓ (k + 1) else 0)) 0 := by
  have hfe : (fun t : ℝ => heading κ (ℓ + t • Pi.single k (1 : ℝ)) j)
      = ∑ m ∈ Finset.range (j + 1), fun t : ℝ =>
          turningAngle 0 κ (ℓ + t • Pi.single k (1 : ℝ)) (m : ZMod n) := by
    funext t
    simp [heading, Finset.sum_apply]
  rw [hfe]
  have hval : (if k.val ≤ j then collarB κ ℓ k else 0) +
        (if (k + 1).val ≤ j then collarA κ ℓ (k + 1) else 0)
      = ∑ m ∈ Finset.range (j + 1),
          ((if ((m : ZMod n)) = k + 1 then collarA κ ℓ ((m : ZMod n)) else 0) +
            (if ((m : ZMod n)) = k then collarB κ ℓ ((m : ZMod n)) else 0)) := by
    have h1 : ∀ m ∈ Finset.range (j + 1),
        ((if ((m : ZMod n)) = k + 1 then collarA κ ℓ ((m : ZMod n)) else 0) +
            (if ((m : ZMod n)) = k then collarB κ ℓ ((m : ZMod n)) else 0))
          = ((if ((m : ZMod n)) = k + 1 then collarA κ ℓ (k + 1) else 0) +
              (if ((m : ZMod n)) = k then collarB κ ℓ k else 0)) := by
      intro m _
      congr 1
      · by_cases h : ((m : ZMod n)) = k + 1 <;> simp [h]
      · by_cases h : ((m : ZMod n)) = k <;> simp [h]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
      sum_range_indicator (k + 1) (collarA κ ℓ (k + 1)) hj,
      sum_range_indicator k (collarB κ ℓ k) hj]
    exact add_comm _ _
  rw [hval]
  exact HasDerivAt.sum fun m _ => turningAngle_path_hasDerivAt hMA k (m : ZMod n)

private lemma edge_path_hasDerivAt [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (k : ZMod n) {j : ℕ} (hj : j < n) :
    HasDerivAt
      (fun t : ℝ => ((ℓ + t • Pi.single k 1 : ZMod n → ℝ) ((j : ZMod n)) : ℂ) *
        Complex.exp ((heading κ (ℓ + t • Pi.single k (1 : ℝ)) j : ℂ) * Complex.I))
      (((if ((j : ZMod n)) = k then (1 : ℝ) else 0 : ℝ) : ℂ) *
          Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)
        + (ℓ ((j : ZMod n)) : ℂ) *
            (Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) *
              ((((if k.val ≤ j then collarB κ ℓ k else 0) +
                  (if (k + 1).val ≤ j then collarA κ ℓ (k + 1) else 0) : ℝ) : ℂ) *
                Complex.I))) 0 := by
  have hlen : HasDerivAt
      (fun t : ℝ => (ℓ + t • Pi.single k 1 : ZMod n → ℝ) ((j : ZMod n)))
      (if ((j : ZMod n)) = k then (1 : ℝ) else 0) 0 := by
    have hfe : (fun t : ℝ => (ℓ + t • Pi.single k 1 : ZMod n → ℝ) ((j : ZMod n)))
        = fun t : ℝ =>
            ℓ ((j : ZMod n)) + t * (if ((j : ZMod n)) = k then (1 : ℝ) else 0) := by
      funext t
      simp [Pi.single_apply, smul_eq_mul]
    rw [hfe]
    exact (hasDerivAt_mul_const _).const_add _
  have hlenC := hlen.ofReal_comp
  have hψC := (heading_path_hasDerivAt hMA k hj).ofReal_comp
  have hinner := hψC.mul_const Complex.I
  have hexp : HasDerivAt
      (fun t : ℝ =>
        Complex.exp ((heading κ (ℓ + t • Pi.single k (1 : ℝ)) j : ℂ) * Complex.I))
      (Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) *
        ((((if k.val ≤ j then collarB κ ℓ k else 0) +
            (if (k + 1).val ≤ j then collarA κ ℓ (k + 1) else 0) : ℝ) : ℂ) *
          Complex.I)) 0 := by
    have := hinner.cexp
    simpa using this
  have hmul := hlenC.mul hexp
  have h0 : (ℓ + (0 : ℝ) • Pi.single k 1 : ZMod n → ℝ) = ℓ := by simp
  simp only [h0] at hmul
  exact hmul

/-- **Closure-gap length gradient**
`∂E/∂ℓ_k = e^{iψ_k} + i (b_k S_k + a_{k+1} S_{k+1})` with the development
tails `S_m = E - v_m`; the `k = n-1` wrap is captured by `(k+1).val = 0` and
`S_0 = E`. -/
theorem closureGap_lengthDeriv [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (k : ZMod n) :
    HasDerivAt (fun t : ℝ => closureGap κ (ℓ + t • Pi.single k (1 : ℝ)))
      (Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I)
        + ((collarB κ ℓ k : ℂ) * Complex.I *
              (closureGap κ ℓ - vertexR2 κ ℓ k.val)
            + (collarA κ ℓ (k + 1) : ℂ) * Complex.I *
              (closureGap κ ℓ - vertexR2 κ ℓ (k + 1).val))) 0 := by
  have hfe : (fun t : ℝ => closureGap κ (ℓ + t • Pi.single k (1 : ℝ)))
      = ∑ j ∈ Finset.range n, fun t : ℝ =>
          ((ℓ + t • Pi.single k 1 : ZMod n → ℝ) ((j : ZMod n)) : ℂ) *
            Complex.exp
              ((heading κ (ℓ + t • Pi.single k (1 : ℝ)) j : ℂ) * Complex.I) := by
    funext t
    simp [closureGap, vertexR2, Finset.sum_apply]
  rw [hfe]
  have htail : ∀ q : ZMod n,
      (∑ j ∈ Finset.range n, if q.val ≤ j then
          (ℓ ((j : ZMod n)) : ℂ) * Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)
        else 0)
        = closureGap κ ℓ - vertexR2 κ ℓ q.val := by
    intro q
    rw [sum_range_tail (fun j => (ℓ ((j : ZMod n)) : ℂ) *
      Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)) (le_of_lt (ZMod.val_lt q))]
    rfl
  have hhead : (∑ j ∈ Finset.range n, if ((j : ZMod n)) = k then
        Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) else 0)
      = Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I) :=
    sum_range_natCast_ite k
      (fun j => Complex.exp ((heading κ ℓ j : ℂ) * Complex.I))
  have hcongr : ∀ j ∈ Finset.range n,
      (((if ((j : ZMod n)) = k then (1 : ℝ) else 0 : ℝ) : ℂ) *
          Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)
        + (ℓ ((j : ZMod n)) : ℂ) *
            (Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) *
              ((((if k.val ≤ j then collarB κ ℓ k else 0) +
                  (if (k + 1).val ≤ j then collarA κ ℓ (k + 1) else 0) : ℝ) : ℂ) *
                Complex.I)))
        = (if ((j : ZMod n)) = k then
              Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) else 0)
          + ((collarB κ ℓ k : ℂ) * Complex.I *
              (if k.val ≤ j then (ℓ ((j : ZMod n)) : ℂ) *
                Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) else 0)
            + (collarA κ ℓ (k + 1) : ℂ) * Complex.I *
              (if (k + 1).val ≤ j then (ℓ ((j : ZMod n)) : ℂ) *
                Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) else 0)) := by
    intro j _
    split_ifs <;> push_cast <;> ring
  have hval : (∑ j ∈ Finset.range n,
        (((if ((j : ZMod n)) = k then (1 : ℝ) else 0 : ℝ) : ℂ) *
            Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)
          + (ℓ ((j : ZMod n)) : ℂ) *
              (Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) *
                ((((if k.val ≤ j then collarB κ ℓ k else 0) +
                    (if (k + 1).val ≤ j then collarA κ ℓ (k + 1) else 0) : ℝ) : ℂ) *
                  Complex.I))))
      = Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I)
        + ((collarB κ ℓ k : ℂ) * Complex.I *
              (closureGap κ ℓ - vertexR2 κ ℓ k.val)
            + (collarA κ ℓ (k + 1) : ℂ) * Complex.I *
              (closureGap κ ℓ - vertexR2 κ ℓ (k + 1).val)) := by
    rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hhead,
      htail k, htail (k + 1)]
  rw [← hval]
  exact HasDerivAt.sum fun j hj =>
    edge_path_hasDerivAt hMA k (Finset.mem_range.mp hj)

/-- The `k`-th **moment point** of a configuration: the explicit
(derivative-free) value of the `k`-th length column of the closure map at a
closed configuration,
`(e^{iψ_k} - i (b_k v_k + a_{k+1} v_{k+1}), b_k + a_{k+1})`. -/
noncomputable def momentPoint [NeZero n] (κ ℓ : ZMod n → ℝ) (k : ZMod n) :
    ℂ × ℝ :=
  (Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I)
      - Complex.I * ((collarB κ ℓ k : ℂ) * vertexR2 κ ℓ k.val
          + (collarA κ ℓ (k + 1) : ℂ) * vertexR2 κ ℓ (k + 1).val),
    collarB κ ℓ k + collarA κ ℓ (k + 1))

/-- **The length columns at a closed configuration: moment form.**  At a
point of the collar interior the `k`-th length column of the canonical
derivative of the closure map is the `k`-th moment point. -/
theorem closureMapR3_lengthColumn [NeZero n]
    {S : Set (ZMod n → ℝ)} {p : (ZMod n → ℝ) × (ZMod n → ℝ)}
    (hp : p ∈ collarInterior S) (k : ZMod n) :
    fderiv ℝ closureMapR3 p ((0 : ZMod n → ℝ), Pi.single k (1 : ℝ))
      = momentPoint p.1 p.2 k := by
  obtain ⟨-, hMA, hG⟩ := hp
  rw [closureMapR3, Prod.ext_iff] at hG
  have hE0 : closureGap p.1 p.2 = 0 := hG.1
  obtain ⟨G', hG'⟩ := closureMapR3_hasStrictFDerivAt hMA
  have hfd : fderiv ℝ closureMapR3 p = G' := hG'.hasFDerivAt.fderiv
  have hγ : HasDerivAt (fun t : ℝ => (p.1, p.2 + t • Pi.single k (1 : ℝ)))
      (((0 : ZMod n → ℝ), Pi.single k (1 : ℝ))) 0 := by
    have h1 : HasDerivAt (fun t : ℝ =>
        t • (((0 : ZMod n → ℝ), Pi.single k (1 : ℝ)) :
          (ZMod n → ℝ) × (ZMod n → ℝ)))
        ((0 : ZMod n → ℝ), Pi.single k (1 : ℝ)) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const
        (((0 : ZMod n → ℝ), Pi.single k (1 : ℝ)) :
          (ZMod n → ℝ) × (ZMod n → ℝ))
    have hfe : (fun t : ℝ => (p.1, p.2 + t • Pi.single k (1 : ℝ)))
        = fun t : ℝ =>
            p + t • (((0 : ZMod n → ℝ), Pi.single k (1 : ℝ)) :
              (ZMod n → ℝ) × (ZMod n → ℝ)) := by
      funext t
      apply Prod.ext <;> simp
    rw [hfe]
    exact h1.const_add p
  have hcomp : HasDerivAt
      (fun t : ℝ => closureMapR3 (p.1, p.2 + t • Pi.single k (1 : ℝ)))
      (G' ((0 : ZMod n → ℝ), Pi.single k (1 : ℝ))) 0 := by
    have hpt : ((p.1, p.2 + (0 : ℝ) • Pi.single k (1 : ℝ)) :
        (ZMod n → ℝ) × (ZMod n → ℝ)) = p := by
      apply Prod.ext <;> simp
    have hF := hG'.hasFDerivAt
    rw [← hpt] at hF
    have := hF.comp_hasDerivAt 0 hγ
    exact this
  have hE := closureGap_lengthDeriv hMA k
  have hT := (turningSum_lengthDeriv hMA k).sub_const (2 * Real.pi)
  have hval : ((Complex.exp ((heading p.1 p.2 k.val : ℂ) * Complex.I)
        + ((collarB p.1 p.2 k : ℂ) * Complex.I *
              (closureGap p.1 p.2 - vertexR2 p.1 p.2 k.val)
            + (collarA p.1 p.2 (k + 1) : ℂ) * Complex.I *
              (closureGap p.1 p.2 - vertexR2 p.1 p.2 (k + 1).val)),
        collarB p.1 p.2 k + collarA p.1 p.2 (k + 1)) : ℂ × ℝ)
      = momentPoint p.1 p.2 k := by
    simp only [momentPoint, hE0]
    exact Prod.ext (by ring) rfl
  have hexp : HasDerivAt
      (fun t : ℝ => closureMapR3 (p.1, p.2 + t • Pi.single k (1 : ℝ)))
      (momentPoint p.1 p.2 k) 0 := by
    rw [← hval]
    exact hE.prodMk hT
  rw [hfd]
  exact hcomp.unique hexp

/-! ### The constant-profile degeneracy: crux C is a real restriction

At the regular `n`-gon every moment point takes the same value, so the
length derivative has rank one and the interior-regularity hypothesis of
`realizesR2_of_collar` is NOT satisfiable on any chamber containing a
constant profile.  This is the differential shadow of the inscribed-polygon
family: all polygons inscribed in a fixed circle share the constant Menger
profile. -/

/-- **All moment points coincide at the regular `n`-gon** — the honest
negative result behind the regular-locus repair: the constant profile is a
nonemptiness witness and simultaneously a regularity counterexample. -/
theorem momentPoint_const_eq [NeZero n] (hn : 3 ≤ n) {c : ℝ} (hc : 0 < c)
    (k k' : ZMod n) :
    momentPoint (fun _ : ZMod n => c)
        (fun _ => 2 / c * Real.sin (Real.pi / n)) k
      = momentPoint (fun _ : ZMod n => c)
          (fun _ => 2 / c * Real.sin (Real.pi / n)) k' := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hθpos : 0 < Real.pi / n := div_pos Real.pi_pos hnpos
  have hθle : Real.pi / n ≤ Real.pi / 3 := by gcongr
  have hθlt : Real.pi / n < Real.pi / 2 := by linarith [Real.pi_pos]
  have hc₀ : 0 < Real.cos (Real.pi / n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθlt⟩
  -- the collar coefficients collapse to the single value `γ = (c/2)/cos(π/n)`
  have hkey : c * (2 / c * Real.sin (Real.pi / n) / 2)
      = Real.sin (Real.pi / n) := by
    field_simp
  have hsq : Real.sqrt (1 - Real.sin (Real.pi / n) ^ 2)
      = Real.cos (Real.pi / n) := by
    rw [← Real.cos_sq']
    exact Real.sqrt_sq hc₀.le
  have hA : ∀ i : ZMod n,
      collarA (fun _ : ZMod n => c) (fun _ => 2 / c * Real.sin (Real.pi / n)) i
        = c / 2 / Real.cos (Real.pi / n) := by
    intro i
    simp only [collarA]
    rw [hkey, hsq]
  have hB : ∀ i : ZMod n,
      collarB (fun _ : ZMod n => c) (fun _ => 2 / c * Real.sin (Real.pi / n)) i
        = c / 2 / Real.cos (Real.pi / n) := by
    intro i
    simp only [collarB]
    rw [hkey, hsq]
  -- headings and vertices of the regular `n`-gon
  have hturn := (regularGon_closes hn hc).2.1
  have hhead : ∀ j : ℕ,
      heading (fun _ : ZMod n => c) (fun _ => 2 / c * Real.sin (Real.pi / n)) j
        = (j + 1) * (2 * Real.pi / n) := by
    intro j
    simp only [heading, hturn]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hζ : IsPrimitiveRoot (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  set ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) with hω
  have hω1 : ω ≠ 1 := hζ.ne_one (by omega)
  have hωsub : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
  have hωn : ω ^ n = 1 := hζ.pow_eq_one
  have hexp : ∀ j : ℕ,
      Complex.exp ((heading (fun _ : ZMod n => c)
          (fun _ => 2 / c * Real.sin (Real.pi / n)) j : ℂ) * Complex.I)
        = ω ^ (j + 1) := by
    intro j
    rw [hhead j, hω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hmod : ∀ m : ℕ, ω ^ (m % n) = ω ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m n]
    rw [pow_add, pow_mul, hωn, one_pow, one_mul]
  have hwrap : ∀ q : ZMod n, ω ^ ((q + 1 : ZMod n).val) = ω ^ (q.val + 1) := by
    intro q
    rw [ZMod.val_add, ZMod.val_one, hmod]
  have hLC : ∀ m : ℕ,
      vertexR2 (fun _ : ZMod n => c)
          (fun _ => 2 / c * Real.sin (Real.pi / n)) m
        = ((2 / c * Real.sin (Real.pi / n) : ℝ) : ℂ) *
            ∑ j ∈ Finset.range m, ω ^ (j + 1) := by
    intro m
    simp only [vertexR2]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hexp j]
  have hv' : ∀ m : ℕ,
      vertexR2 (fun _ : ZMod n => c)
          (fun _ => 2 / c * Real.sin (Real.pi / n)) m * (ω - 1)
        = ((2 / c * Real.sin (Real.pi / n) : ℝ) : ℂ) * ω * (ω ^ m - 1) := by
    intro m
    rw [hLC m]
    have h2 : (∑ j ∈ Finset.range m, ω ^ (j + 1))
        = ω * ∑ j ∈ Finset.range m, ω ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => pow_succ' ω j
    rw [h2]
    linear_combination ((2 / c * Real.sin (Real.pi / n) : ℝ) : ℂ) * ω *
      geom_sum_mul ω m
  -- the closure identity `iγL(1+ω) = ω - 1`, i.e. `tan(π/n) = γL`
  have hcos2 : Real.cos (2 * Real.pi / n)
      = 1 - 2 * Real.sin (Real.pi / n) ^ 2 := by
    rw [show 2 * Real.pi / n = 2 * (Real.pi / n) by ring, Real.cos_two_mul]
    linear_combination 2 * Real.sin_sq_add_cos_sq (Real.pi / n)
  have hsin2 : Real.sin (2 * Real.pi / n)
      = 2 * Real.sin (Real.pi / n) * Real.cos (Real.pi / n) := by
    rw [show 2 * Real.pi / n = 2 * (Real.pi / n) by ring, Real.sin_two_mul]
  have hω_eul : ω = ((Real.cos (2 * Real.pi / n) : ℝ) : ℂ)
      + ((Real.sin (2 * Real.pi / n) : ℝ) : ℂ) * Complex.I := by
    rw [hω, show 2 * (Real.pi : ℂ) * Complex.I / n
        = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hpyth : ((Real.sin (Real.pi / n) : ℝ) : ℂ) ^ 2
      + ((Real.cos (Real.pi / n) : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (Real.pi / n)
  have hc₀ne : ((Real.cos (Real.pi / n) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hc₀.ne'
  have hinv : ((Real.cos (Real.pi / n) : ℝ) : ℂ)⁻¹ *
      ((Real.cos (Real.pi / n) : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hc₀ne
  have hbr : Complex.I * ((c / 2 / Real.cos (Real.pi / n) : ℝ) : ℂ) *
        ((2 / c * Real.sin (Real.pi / n) : ℝ) : ℂ) * (1 + ω) = ω - 1 := by
    have hγL : ((c / 2 / Real.cos (Real.pi / n) : ℝ) : ℂ) *
        ((2 / c * Real.sin (Real.pi / n) : ℝ) : ℂ)
        = ((Real.sin (Real.pi / n) : ℝ) : ℂ) *
            ((Real.cos (Real.pi / n) : ℝ) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_mul,
        show (c / 2 / Real.cos (Real.pi / n)) * (2 / c * Real.sin (Real.pi / n))
          = Real.sin (Real.pi / n) * (Real.cos (Real.pi / n))⁻¹ by
            rw [mul_comm]
            field_simp]
      push_cast [-Complex.ofReal_sin, -Complex.ofReal_cos]
      ring
    rw [mul_assoc Complex.I, hγL, hω_eul, hcos2, hsin2]
    push_cast [-Complex.ofReal_sin, -Complex.ofReal_cos]
    linear_combination
      (-2 * Complex.I * ((Real.sin (Real.pi / n) : ℝ) : ℂ) *
          ((Real.cos (Real.pi / n) : ℝ) : ℂ)⁻¹) * hpyth
      + (2 * ((Real.sin (Real.pi / n) : ℝ) : ℂ) ^ 2 *
          ((Real.cos (Real.pi / n) : ℝ) : ℂ) *
          ((Real.cos (Real.pi / n) : ℝ) : ℂ)⁻¹) * Complex.I_sq
      + (-2 * ((Real.sin (Real.pi / n) : ℝ) : ℂ) ^ 2 +
          2 * Complex.I * ((Real.sin (Real.pi / n) : ℝ) : ℂ) *
            ((Real.cos (Real.pi / n) : ℝ) : ℂ)) * hinv
  -- first coordinates are constant after clearing the denominator `ω - 1`
  have hfst : ∀ q : ZMod n,
      (momentPoint (fun _ : ZMod n => c)
          (fun _ => 2 / c * Real.sin (Real.pi / n)) q).1 * (ω - 1)
        = 2 * Complex.I * ((c / 2 / Real.cos (Real.pi / n) : ℝ) : ℂ) *
            ((2 / c * Real.sin (Real.pi / n) : ℝ) : ℂ) * ω := by
    intro q
    simp only [momentPoint]
    rw [hexp q.val, hB q, hA (q + 1)]
    have h1 := hv' q.val
    have h2 : vertexR2 (fun _ : ZMod n => c)
        (fun _ => 2 / c * Real.sin (Real.pi / n)) ((q + 1 : ZMod n).val) *
          (ω - 1)
        = ((2 / c * Real.sin (Real.pi / n) : ℝ) : ℂ) * ω *
            (ω ^ (q.val + 1) - 1) := by
      rw [hv' ((q + 1 : ZMod n).val), hwrap q]
    linear_combination (-(ω ^ (q.val + 1))) * hbr
      - Complex.I * ((c / 2 / Real.cos (Real.pi / n) : ℝ) : ℂ) * h1
      - Complex.I * ((c / 2 / Real.cos (Real.pi / n) : ℝ) : ℂ) * h2
  have hsnd : ∀ q : ZMod n,
      (momentPoint (fun _ : ZMod n => c)
          (fun _ => 2 / c * Real.sin (Real.pi / n)) q).2
        = c / 2 / Real.cos (Real.pi / n) + c / 2 / Real.cos (Real.pi / n) := by
    intro q
    simp only [momentPoint]
    rw [hB q, hA (q + 1)]
  apply Prod.ext
  · exact mul_right_cancel₀ hωsub ((hfst k).trans (hfst k').symm)
  · exact (hsnd k).trans (hsnd k').symm

/-! ### The regular-locus repair -/

/-- **Moment rank**: the `n` moment points span the full target `ℂ × ℝ`.
This is the computable, derivative-free form of crux C
(`lengthRank_iff_momentRank`). -/
def MomentRank [NeZero n] (κ ℓ : ZMod n → ℝ) : Prop :=
  Submodule.span ℝ (Set.range (momentPoint κ ℓ)) = ⊤

private lemma finrank_complex_prod_real : Module.finrank ℝ (ℂ × ℝ) = 3 := by
  rw [Module.finrank_prod, Complex.finrank_real_complex, Module.finrank_self]

/-- **Moment rank is the computable form of crux C**: at a point of the
collar interior, the length derivative of the closure map is surjective iff
the moment points span `ℂ × ℝ`. -/
theorem lengthRank_iff_momentRank [NeZero n]
    {S : Set (ZMod n → ℝ)} {p : (ZMod n → ℝ) × (ZMod n → ℝ)}
    (hp : p ∈ collarInterior S) :
    LengthRank p ↔ MomentRank p.1 p.2 := by
  set F : (ZMod n → ℝ) →ₗ[ℝ] ℂ × ℝ :=
    LinearMap.comp (↑(fderiv ℝ closureMapR3 p))
      (LinearMap.inr ℝ (ZMod n → ℝ) (ZMod n → ℝ)) with hF
  have hrange : LinearMap.range F
      = Submodule.span ℝ (Set.range (momentPoint p.1 p.2)) := by
    rw [LinearMap.range_eq_map, ← (Pi.basisFun ℝ (ZMod n)).span_eq,
      Submodule.map_span, ← Set.range_comp]
    have hfun : ⇑F ∘ ⇑(Pi.basisFun ℝ (ZMod n)) = momentPoint p.1 p.2 := by
      funext i
      show F ((Pi.basisFun ℝ (ZMod n)) i) = momentPoint p.1 p.2 i
      rw [Pi.basisFun_apply]
      exact closureMapR3_lengthColumn hp i
    rw [hfun]
  have hFsurj : (fun b : ZMod n → ℝ => fderiv ℝ closureMapR3 p (0, b))
      = ⇑F := rfl
  show Function.Surjective (fun b : ZMod n → ℝ =>
      fderiv ℝ closureMapR3 p (0, b))
    ↔ Submodule.span ℝ (Set.range (momentPoint p.1 p.2)) = ⊤
  rw [hFsurj, ← LinearMap.range_eq_top, hrange]

/-- **The regular `n`-gon does not have moment rank**: the moment points all
coincide, so their span is at most one-dimensional in the three-dimensional
target.  Consequently the interior-regularity hypothesis of
`realizesR2_of_collar` is not satisfiable on any chamber containing a
constant profile. -/
theorem not_momentRank_const [NeZero n] (hn : 3 ≤ n) {c : ℝ} (hc : 0 < c) :
    ¬ MomentRank (fun _ : ZMod n => c)
      (fun _ => 2 / c * Real.sin (Real.pi / n)) := by
  classical
  intro h
  let v : ℂ × ℝ := momentPoint (fun _ : ZMod n => c)
    (fun _ => 2 / c * Real.sin (Real.pi / n)) 0
  have hrange : Set.range (momentPoint (fun _ : ZMod n => c)
      (fun _ => 2 / c * Real.sin (Real.pi / n)))
      ⊆ {v} := by
    rintro x ⟨q, rfl⟩
    exact Set.mem_singleton_iff.mpr (momentPoint_const_eq hn hc q 0)
  have hle : (⊤ : Submodule ℝ (ℂ × ℝ)) ≤ Submodule.span ℝ {v} := by
    rw [← h]
    exact Submodule.span_mono hrange
  have h1 : Module.finrank ℝ (ℂ × ℝ) ≤ 1 := by
    calc Module.finrank ℝ (ℂ × ℝ)
        = Module.finrank ℝ (⊤ : Submodule ℝ (ℂ × ℝ)) := (finrank_top ℝ _).symm
      _ ≤ Module.finrank ℝ (Submodule.span ℝ {v}) :=
          Submodule.finrank_mono hle
      _ ≤ 1 := by
          change Module.finrank ℝ (ℝ ∙ v) ≤ 1
          by_cases hv : v = 0
          · rw [Submodule.span_singleton_eq_bot.mpr hv, finrank_bot]
            exact Nat.zero_le 1
          · rw [finrank_span_singleton hv]
  rw [finrank_complex_prod_real] at h1
  omega

private lemma momentRank_iff_exists_triple [NeZero n] (κ ℓ : ZMod n → ℝ) :
    MomentRank κ ℓ ↔ ∃ g : Fin 3 → ZMod n,
      LinearIndependent ℝ fun s => momentPoint κ ℓ (g s) := by
  constructor
  · intro h
    obtain ⟨b, hbsub, hbspan, hbli⟩ :=
      exists_linearIndependent ℝ (Set.range (momentPoint κ ℓ))
    rw [show Submodule.span ℝ (Set.range (momentPoint κ ℓ)) = ⊤ from h]
      at hbspan
    have hfin : b.Finite := hbli.setFinite
    haveI := hfin.fintype
    have hbasis : Module.Basis b ℝ (ℂ × ℝ) :=
      Module.Basis.mk hbli (by rw [Subtype.range_coe]; exact hbspan.ge)
    have hcard : Fintype.card b = 3 := by
      rw [← Module.finrank_eq_card_basis hbasis]
      exact finrank_complex_prod_real
    have e := Fintype.equivFinOfCardEq hcard
    choose g hg using fun x : b => hbsub x.2
    refine ⟨fun s => g (e.symm s), ?_⟩
    have hfe : (fun s => momentPoint κ ℓ (g (e.symm s)))
        = Subtype.val ∘ e.symm := by
      funext s
      exact hg (e.symm s)
    rw [hfe]
    exact hbli.comp e.symm e.symm.injective
  · rintro ⟨g, hli⟩
    have hspan := hli.span_eq_top_of_card_eq_finrank (by simp)
    show Submodule.span ℝ (Set.range (momentPoint κ ℓ)) = ⊤
    rw [eq_top_iff, ← hspan]
    apply Submodule.span_mono
    rintro x ⟨s, rfl⟩
    exact ⟨g s, rfl⟩

private lemma continuousOn_momentPoint [NeZero n] (q : ZMod n) :
    ContinuousOn
      (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => momentPoint p.1 p.2 q)
      {p : (ZMod n → ℝ) × (ZMod n → ℝ) | ModerateArc 0 p.1 p.2} := by
  have hκ : ∀ i : ZMod n, Continuous
      fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => p.1 i :=
    fun i => (continuous_apply i).comp continuous_fst
  have hℓ : ∀ i : ZMod n, Continuous
      fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => p.2 i :=
    fun i => (continuous_apply i).comp continuous_snd
  have hheadC : ∀ m : ℕ, Continuous
      fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => heading p.1 p.2 m := by
    intro m
    have hfe : (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => heading p.1 p.2 m)
        = fun p => ∑ r ∈ Finset.range (m + 1),
            (Real.arcsin (p.1 ((r : ZMod n)) * (p.2 ((r : ZMod n) - 1) / 2)) +
              Real.arcsin (p.1 ((r : ZMod n)) * (p.2 ((r : ZMod n)) / 2))) := by
      funext p
      simp [heading, turningAngle]
    rw [hfe]
    exact continuous_finsetSum _ fun r _ =>
      (Real.continuous_arcsin.comp ((hκ _).mul ((hℓ _).div_const 2))).add
        (Real.continuous_arcsin.comp ((hκ _).mul ((hℓ _).div_const 2)))
  have hexpC : ∀ m : ℕ, Continuous
      fun p : (ZMod n → ℝ) × (ZMod n → ℝ) =>
        Complex.exp ((heading p.1 p.2 m : ℂ) * Complex.I) :=
    fun m => Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (hheadC m)).mul_const Complex.I)
  have hvertC : ∀ m : ℕ, Continuous
      fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => vertexR2 p.1 p.2 m := by
    intro m
    have hfe : (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => vertexR2 p.1 p.2 m)
        = fun p => ∑ r ∈ Finset.range m,
            ((p.2 ((r : ZMod n)) : ℂ) *
              Complex.exp ((heading p.1 p.2 r : ℂ) * Complex.I)) := by
      funext p
      simp [vertexR2]
    rw [hfe]
    exact continuous_finsetSum _ fun r _ =>
      (Complex.continuous_ofReal.comp (hℓ _)).mul (hexpC r)
  have hcoef : ∀ i j : ZMod n,
      (∀ p : (ZMod n → ℝ) × (ZMod n → ℝ), ModerateArc 0 p.1 p.2 →
        |p.1 i| * (p.2 j / 2) < 1) →
      ContinuousOn (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) =>
        p.1 i / 2 / Real.sqrt (1 - (p.1 i * (p.2 j / 2)) ^ 2))
      {p : (ZMod n → ℝ) × (ZMod n → ℝ) | ModerateArc 0 p.1 p.2} := by
    intro i j hwall
    refine ContinuousOn.div (((hκ i).div_const 2).continuousOn)
      ((Real.continuous_sqrt.comp (continuous_const.sub
        (((hκ i).mul ((hℓ j).div_const 2)).pow 2))).continuousOn) ?_
    intro p hp
    have hMA : ModerateArc 0 p.1 p.2 := hp
    have habs : |p.1 i * (p.2 j / 2)| < 1 := by
      rw [abs_mul, abs_of_pos (div_pos (hMA.length_pos j) two_pos)]
      exact hwall p hMA
    have hpos : 0 < 1 - (p.1 i * (p.2 j / 2)) ^ 2 := by
      have := (sq_lt_one_iff_abs_lt_one _).mpr habs
      linarith
    exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hAcont : ∀ i : ZMod n, ContinuousOn
      (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => collarA p.1 p.2 i)
      {p : (ZMod n → ℝ) × (ZMod n → ℝ) | ModerateArc 0 p.1 p.2} := by
    intro i
    exact hcoef i (i - 1) fun p hMA => by
      have := hMA.wall_left i
      rwa [tK_zero] at this
  have hBcont : ∀ i : ZMod n, ContinuousOn
      (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => collarB p.1 p.2 i)
      {p : (ZMod n → ℝ) × (ZMod n → ℝ) | ModerateArc 0 p.1 p.2} := by
    intro i
    exact hcoef i i fun p hMA => by
      have := hMA.wall_right i
      rwa [tK_zero] at this
  have hfe : (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => momentPoint p.1 p.2 q)
      = fun p : (ZMod n → ℝ) × (ZMod n → ℝ) =>
          ((Complex.exp ((heading p.1 p.2 q.val : ℂ) * Complex.I)
            - Complex.I * ((collarB p.1 p.2 q : ℂ) * vertexR2 p.1 p.2 q.val
                + (collarA p.1 p.2 (q + 1) : ℂ) *
                  vertexR2 p.1 p.2 ((q + 1 : ZMod n).val)),
            collarB p.1 p.2 q + collarA p.1 p.2 (q + 1)) : ℂ × ℝ) := by
    funext p
    rfl
  rw [hfe]
  refine ContinuousOn.prodMk (ContinuousOn.sub
    ((hexpC q.val).continuousOn) (ContinuousOn.mul continuousOn_const
      (ContinuousOn.add ?_ ?_))) (ContinuousOn.add (hBcont q) (hAcont (q + 1)))
  · exact ContinuousOn.mul
      (Complex.continuous_ofReal.comp_continuousOn (hBcont q))
      ((hvertC q.val).continuousOn)
  · exact ContinuousOn.mul
      (Complex.continuous_ofReal.comp_continuousOn (hAcont (q + 1)))
      ((hvertC _).continuousOn)

/-- **Moment rank is an open condition** on the strict moderate-arc domain:
spanning the three-dimensional target is the existence of a linearly
independent triple, an open condition on the continuously-varying moment
points. -/
theorem isOpen_momentRank [NeZero n] :
    IsOpen {p : (ZMod n → ℝ) × (ZMod n → ℝ) |
      ModerateArc 0 p.1 p.2 ∧ MomentRank p.1 p.2} := by
  have hset : {p : (ZMod n → ℝ) × (ZMod n → ℝ) |
      ModerateArc 0 p.1 p.2 ∧ MomentRank p.1 p.2}
      = ⋃ g : Fin 3 → ZMod n,
          ({p : (ZMod n → ℝ) × (ZMod n → ℝ) | ModerateArc 0 p.1 p.2} ∩
            (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) =>
              fun s : Fin 3 => momentPoint p.1 p.2 (g s)) ⁻¹'
              {v : Fin 3 → ℂ × ℝ | LinearIndependent ℝ v}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage]
    constructor
    · rintro ⟨hMA, hMR⟩
      obtain ⟨g, hg⟩ := (momentRank_iff_exists_triple p.1 p.2).mp hMR
      exact ⟨g, hMA, hg⟩
    · rintro ⟨g, hMA, hg⟩
      exact ⟨hMA, (momentRank_iff_exists_triple p.1 p.2).mpr ⟨g, hg⟩⟩
  rw [hset]
  refine isOpen_iUnion fun g => ?_
  refine ContinuousOn.isOpen_inter_preimage ?_ isOpen_moderateArcZero
    isOpen_setOf_linearIndependent
  rw [continuousOn_pi]
  exact fun s => continuousOn_momentPoint (g s)

/-- **The regular collar interior**: strict-interior solutions that
additionally have moment rank.  Crux C holds on it by construction. -/
def collarRegularInterior [NeZero n] (S : Set (ZMod n → ℝ)) :
    Set ((ZMod n → ℝ) × (ZMod n → ℝ)) :=
  {p | p ∈ collarInterior S ∧ MomentRank p.1 p.2}

/-- **Wiring theorem, regular-locus form.**  Over a preconnected chamber of
positive profiles, IF the closed solution set is compact with profile image
in the chamber (crux A′) and IF every closed solution admits a same-profile
representative in the *regular* collar interior (the strengthened crux B′),
THEN every profile in the chamber is realizable.  Interior regularity is no
longer a hypothesis: it holds on `collarRegularInterior` by construction
(`lengthRank_iff_momentRank`), and `momentPoint_const_eq` shows the
strengthening of the collar is a genuine requirement, not a technicality. -/
theorem realizesR2_of_collar_regular [NeZero n] (hn : 3 ≤ n)
    {S : Set (ZMod n → ℝ)} (hS : IsPreconnected S)
    (hSpos : ∀ κ ∈ S, ∀ i, 0 < κ i)
    {D : Set ((ZMod n → ℝ) × (ZMod n → ℝ))}
    (hD : IsCompact D) (hDne : D.Nonempty)
    (hUD : collarRegularInterior S ⊆ D)
    (hDS : Prod.fst '' D ⊆ S)
    (hcollar : ∀ p ∈ D, ∃ q ∈ collarRegularInterior S, q.1 = p.1) :
    ∀ κ ∈ S, RealizesR2 κ := by
  have hlocal : ∀ p ∈ collarRegularInterior S,
      Prod.fst '' collarRegularInterior S ∈ 𝓝[S] p.1 := by
    intro p hp
    obtain ⟨hpI, hpR⟩ := hp
    obtain ⟨G', hG⟩ := closureMapR3_hasStrictFDerivAt hpI.2.1
    have hfd : fderiv ℝ closureMapR3 p = G' := hG.hasFDerivAt.fderiv
    have hsurj : (G'.prod
        (ContinuousLinearMap.fst ℝ (ZMod n → ℝ) (ZMod n → ℝ))).range = ⊤ := by
      rw [← hfd]
      exact (range_prod_fst_eq_top_iff _).mpr
        ((lengthRank_iff_momentRank hpI).mpr hpR)
    have h0 : Prod.fst ''
        ({y : (ZMod n → ℝ) × (ZMod n → ℝ) | closureMapR3 y = 0} ∩
          {q : (ZMod n → ℝ) × (ZMod n → ℝ) |
            ModerateArc 0 q.1 q.2 ∧ MomentRank q.1 q.2})
        ∈ 𝓝 p.1 :=
      projImage_mem_nhds_of_jointSubmersion hpI.2.2 hG hasStrictFDerivAt_fst
        hsurj (isOpen_momentRank.mem_nhds ⟨hpI.2.1, hpR⟩) Set.Subset.rfl
    refine Filter.mem_of_superset
      (Filter.inter_mem (nhdsWithin_le_nhds h0) self_mem_nhdsWithin) ?_
    rintro κ' ⟨⟨y, ⟨hy0, hyMA, hyMR⟩, rfl⟩, hkS⟩
    exact ⟨y, ⟨⟨hkS, hyMA, hy0⟩, hyMR⟩, rfl⟩
  have himg : S ⊆ Prod.fst '' collarRegularInterior S :=
    collared_continuation_subset hS hD hDne hUD continuous_fst.continuousOn
      hDS hcollar hlocal
  intro κ hκ
  obtain ⟨p, hp, hpκ⟩ := himg hκ
  have hpos : ∀ i, 0 < p.1 i := by rw [hpκ]; exact hSpos κ hκ
  have hreal := realizesR2_of_mem_collarInterior hn hp.1 hpos
  rwa [hpκ] at hreal

/-! ## The moment centres: crux C as planar non-collinearity

For a positive profile every moment point has strictly positive third
coordinate `t_k = b_k + a_{k+1}`, so crux C only sees the normalised complex
points.  The moment centre of edge `k` makes that normalisation an explicit
two-term formula (`momentPoint_eq_momentCenter`).  This section proves that the
failure locus of crux C CONTAINS the full constant-curvature stratum: at ANY
constant-curvature closed configuration (every inscribed polygon, not just the
regular `n`-gon) all `n` moment centres collapse onto the circumcentre and moment
rank fails (`not_momentRank_of_const_curvature`). -/

/-- The incoming arcsine slope is positive at a positively curved vertex. -/
lemma collarA_pos {κ ℓ : ZMod n → ℝ} (hMA : ModerateArc 0 κ ℓ) {i : ZMod n}
    (hκ : 0 < κ i) : 0 < collarA κ ℓ i := by
  have hl := hMA.length_pos (i - 1)
  have hwall : |κ i| * (ℓ (i - 1) / 2) < 1 := by
    have := hMA.wall_left i
    simpa [tK_zero] using this
  have habs : |κ i * (ℓ (i - 1) / 2)| < 1 := by
    rw [abs_mul, abs_of_pos (div_pos hl two_pos)]
    exact hwall
  have hsq : 0 < 1 - (κ i * (ℓ (i - 1) / 2)) ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one _).mpr habs
    linarith
  change 0 < κ i / 2 / Real.sqrt (1 - (κ i * (ℓ (i - 1) / 2)) ^ 2)
  exact div_pos (half_pos hκ) (Real.sqrt_pos.mpr hsq)

/-- The outgoing arcsine slope is positive at a positively curved vertex. -/
lemma collarB_pos {κ ℓ : ZMod n → ℝ} (hMA : ModerateArc 0 κ ℓ) {i : ZMod n}
    (hκ : 0 < κ i) : 0 < collarB κ ℓ i := by
  have hl := hMA.length_pos i
  have hwall : |κ i| * (ℓ i / 2) < 1 := by
    have := hMA.wall_right i
    simpa [tK_zero] using this
  have habs : |κ i * (ℓ i / 2)| < 1 := by
    rw [abs_mul, abs_of_pos (div_pos hl two_pos)]
    exact hwall
  have hsq : 0 < 1 - (κ i * (ℓ i / 2)) ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one _).mpr habs
    linarith
  change 0 < κ i / 2 / Real.sqrt (1 - (κ i * (ℓ i / 2)) ^ 2)
  exact div_pos (half_pos hκ) (Real.sqrt_pos.mpr hsq)

/-- The development recursion with residue indexing: at a closed
configuration `v_{(k+1).val} = v_{k.val} + ℓ_k e^{iψ_k}`, the wrap case
`k = n-1` being supplied by `E = 0`. -/
private lemma vertexR2_next [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (k : ZMod n) :
    vertexR2 κ ℓ ((k + 1 : ZMod n)).val
      = vertexR2 κ ℓ k.val
        + (ℓ k : ℂ) * Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I) := by
  have hstep : vertexR2 κ ℓ (k.val + 1)
      = vertexR2 κ ℓ k.val
        + (ℓ k : ℂ) * Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I) := by
    have h := vertexR2_succ κ ℓ k.val
    rwa [ZMod.natCast_rightInverse k] at h
  have hcast : ((k.val + 1 : ℕ) : ZMod n) = k + 1 := by
    push_cast
    rw [ZMod.natCast_rightInverse k]
  rcases Nat.lt_or_ge (k.val + 1) n with hlt | hge
  · rw [show (k + 1 : ZMod n).val = k.val + 1 by
      rw [← hcast, ZMod.val_cast_of_lt hlt]]
    exact hstep
  · have heq : k.val + 1 = n := by
      have := ZMod.val_lt k
      omega
    have hk0 : (k + 1 : ZMod n) = 0 := by
      rw [← hcast, heq, ZMod.natCast_self]
    have hv0 : vertexR2 κ ℓ 0 = 0 := by simp [vertexR2]
    have hvn : vertexR2 κ ℓ (k.val + 1) = 0 := by
      rw [heq]
      exact hE
    rw [hk0, ZMod.val_zero, hv0, ← hstep, hvn]

/-- The **moment centre** of edge `k`:
`C_k = v_k + (ℓ_k a_{k+1} + i) / (b_k + a_{k+1}) · e^{iψ_k}`.  At a closed
configuration `momentPoint κ ℓ k = (b_k + a_{k+1}) • (-i C_k, 1)`
(`momentPoint_eq_momentCenter`), so for a positive profile crux C is the
planar statement that the `n` moment centres are not collinear. -/
noncomputable def momentCenter [NeZero n] (κ ℓ : ZMod n → ℝ) (k : ZMod n) : ℂ :=
  vertexR2 κ ℓ k.val
    + (((ℓ k * collarA κ ℓ (k + 1) : ℝ) : ℂ) + Complex.I)
        / ((collarB κ ℓ k + collarA κ ℓ (k + 1) : ℝ) : ℂ)
      * Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I)

/-- **The moment point is the moment centre, rotated and scaled**: at a
closed configuration with `t_k = b_k + a_{k+1} ≠ 0`,
`momentPoint κ ℓ k = t_k • (-i C_k, 1)`. -/
theorem momentPoint_eq_momentCenter [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) {k : ZMod n}
    (ht : collarB κ ℓ k + collarA κ ℓ (k + 1) ≠ 0) :
    momentPoint κ ℓ k
      = (collarB κ ℓ k + collarA κ ℓ (k + 1)) •
          ((-Complex.I * momentCenter κ ℓ k, (1 : ℝ)) : ℂ × ℝ) := by
  have htC : ((collarB κ ℓ k + collarA κ ℓ (k + 1) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ht
  rw [Prod.smul_mk, smul_eq_mul, mul_one]
  refine Prod.ext ?_ rfl
  change Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I)
      - Complex.I * ((collarB κ ℓ k : ℂ) * vertexR2 κ ℓ k.val
          + (collarA κ ℓ (k + 1) : ℂ) * vertexR2 κ ℓ ((k + 1 : ZMod n)).val)
      = (collarB κ ℓ k + collarA κ ℓ (k + 1)) • (-Complex.I * momentCenter κ ℓ k)
  rw [Complex.real_smul]
  simp only [momentCenter]
  rw [vertexR2_next hE k]
  push_cast at htC ⊢
  field_simp
  linear_combination
    Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I) * Complex.I_sq

/-- **The moment centre seen from the far endpoint**: at a closed
configuration with `t_k ≠ 0`,
`C_k = v_{k+1} + (i - ℓ_k b_k)/(b_k + a_{k+1}) · e^{iψ_k}`. -/
theorem momentCenter_eq_next [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) {k : ZMod n}
    (ht : collarB κ ℓ k + collarA κ ℓ (k + 1) ≠ 0) :
    momentCenter κ ℓ k
      = vertexR2 κ ℓ ((k + 1 : ZMod n)).val
        + (Complex.I - ((ℓ k * collarB κ ℓ k : ℝ) : ℂ))
            / ((collarB κ ℓ k + collarA κ ℓ (k + 1) : ℝ) : ℂ)
          * Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I) := by
  have htC : ((collarB κ ℓ k + collarA κ ℓ (k + 1) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ht
  simp only [momentCenter]
  rw [vertexR2_next hE k]
  push_cast at htC ⊢
  field_simp
  ring

/-! ### The sharp failure locus: constant curvature

For a constant profile `κ ≡ c` the two arcsine slopes across each edge
coincide, and both readings of the moment centre become
`C_k = v_k + (i/c)·e^{i(ψ_k - φ_k)} = v_{k+1} + (i/c)·e^{i(ψ_k + φ_k)}` with
`φ_k = arcsin(c ℓ_k / 2)`.  The turning law then chains all centres into a
single point: rank drops at EVERY inscribed polygon, not only at the regular
`n`-gon. -/

private lemma momentCenter_const_form1 [NeZero n] {c : ℝ} (hc : 0 < c)
    {ℓ : ZMod n → ℝ} (hMA : ModerateArc 0 (fun _ : ZMod n => c) ℓ)
    (k : ZMod n) :
    momentCenter (fun _ : ZMod n => c) ℓ k
      = vertexR2 (fun _ : ZMod n => c) ℓ k.val
        + Complex.I / (c : ℂ) *
          Complex.exp
            (((heading (fun _ : ZMod n => c) ℓ k.val
                - Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I) := by
  have hl : 0 < ℓ k := hMA.length_pos k
  have hwall : |c| * (ℓ k / 2) < 1 := by
    have := hMA.wall_right k
    simpa [tK_zero] using this
  have habs : |c * (ℓ k / 2)| < 1 := by
    rw [abs_mul, abs_of_pos (div_pos hl two_pos)]
    exact hwall
  have habs' := abs_lt.mp habs
  have hsq : 0 < 1 - (c * (ℓ k / 2)) ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one _).mpr habs
    linarith
  have hspos : 0 < Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) := Real.sqrt_pos.mpr hsq
  have hsin : Real.sin (Real.arcsin (c * (ℓ k / 2))) = c * (ℓ k / 2) :=
    Real.sin_arcsin (le_of_lt habs'.1) (le_of_lt habs'.2)
  have hcos : Real.cos (Real.arcsin (c * (ℓ k / 2)))
      = Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) := Real.cos_arcsin _
  have hB : collarB (fun _ : ZMod n => c) ℓ k
      = c / 2 / Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) := rfl
  have hA : collarA (fun _ : ZMod n => c) ℓ (k + 1)
      = c / 2 / Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) := by
    simp only [collarA, add_sub_cancel_right]
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsC : ((Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hspos.ne'
  set s : ℝ := Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) with hs
  have hcoeff :
      (((ℓ k * (c / 2 / s) : ℝ) : ℂ) + Complex.I)
          / ((c / 2 / s + c / 2 / s : ℝ) : ℂ)
        = Complex.I / (c : ℂ)
            * Complex.exp
                (((-Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, hsin, hcos]
    push_cast
    field_simp
    linear_combination (2 * (ℓ k : ℂ) * (c : ℂ)) * Complex.I_sq
  have hsplit : Complex.exp
        (((heading (fun _ : ZMod n => c) ℓ k.val
            - Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I)
      = Complex.exp
            ((heading (fun _ : ZMod n => c) ℓ k.val : ℂ) * Complex.I) *
          Complex.exp
            (((-Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [momentCenter, hA, hB]
  rw [hcoeff, hsplit]
  ring

private lemma momentCenter_const_form2 [NeZero n] {c : ℝ} (hc : 0 < c)
    {ℓ : ZMod n → ℝ} (hMA : ModerateArc 0 (fun _ : ZMod n => c) ℓ)
    (hE : closureGap (fun _ : ZMod n => c) ℓ = 0) (k : ZMod n) :
    momentCenter (fun _ : ZMod n => c) ℓ k
      = vertexR2 (fun _ : ZMod n => c) ℓ ((k + 1 : ZMod n)).val
        + Complex.I / (c : ℂ) *
          Complex.exp
            (((heading (fun _ : ZMod n => c) ℓ k.val
                + Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I) := by
  have ht : collarB (fun _ : ZMod n => c) ℓ k
      + collarA (fun _ : ZMod n => c) ℓ (k + 1) ≠ 0 :=
    (add_pos (collarB_pos hMA hc) (collarA_pos hMA hc)).ne'
  have hl : 0 < ℓ k := hMA.length_pos k
  have hwall : |c| * (ℓ k / 2) < 1 := by
    have := hMA.wall_right k
    simpa [tK_zero] using this
  have habs : |c * (ℓ k / 2)| < 1 := by
    rw [abs_mul, abs_of_pos (div_pos hl two_pos)]
    exact hwall
  have habs' := abs_lt.mp habs
  have hsq : 0 < 1 - (c * (ℓ k / 2)) ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one _).mpr habs
    linarith
  have hspos : 0 < Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) := Real.sqrt_pos.mpr hsq
  have hsin : Real.sin (Real.arcsin (c * (ℓ k / 2))) = c * (ℓ k / 2) :=
    Real.sin_arcsin (le_of_lt habs'.1) (le_of_lt habs'.2)
  have hcos : Real.cos (Real.arcsin (c * (ℓ k / 2)))
      = Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) := Real.cos_arcsin _
  have hB : collarB (fun _ : ZMod n => c) ℓ k
      = c / 2 / Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) := rfl
  have hA : collarA (fun _ : ZMod n => c) ℓ (k + 1)
      = c / 2 / Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) := by
    simp only [collarA, add_sub_cancel_right]
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsC : ((Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hspos.ne'
  set s : ℝ := Real.sqrt (1 - (c * (ℓ k / 2)) ^ 2) with hs
  have hcoeff :
      (Complex.I - ((ℓ k * (c / 2 / s) : ℝ) : ℂ))
          / ((c / 2 / s + c / 2 / s : ℝ) : ℂ)
        = Complex.I / (c : ℂ)
            * Complex.exp
                (((Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      hsin, hcos]
    push_cast
    field_simp
    linear_combination (-2 * (ℓ k : ℂ) * (c : ℂ)) * Complex.I_sq
  have hsplit : Complex.exp
        (((heading (fun _ : ZMod n => c) ℓ k.val
            + Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I)
      = Complex.exp
            ((heading (fun _ : ZMod n => c) ℓ k.val : ℂ) * Complex.I) *
          Complex.exp
            (((Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [momentCenter_eq_next hE ht, hA, hB, hcoeff, hsplit]
  ring

private lemma momentCenter_const_succ [NeZero n] {c : ℝ} (hc : 0 < c)
    {ℓ : ZMod n → ℝ} (hMA : ModerateArc 0 (fun _ : ZMod n => c) ℓ)
    (hE : closureGap (fun _ : ZMod n => c) ℓ = 0)
    (hT : turningSum (fun _ : ZMod n => c) ℓ = 2 * Real.pi) (k : ZMod n) :
    momentCenter (fun _ : ZMod n => c) ℓ (k + 1)
      = momentCenter (fun _ : ZMod n => c) ℓ k := by
  rw [momentCenter_const_form1 hc hMA (k + 1),
    momentCenter_const_form2 hc hMA hE k]
  have hcast : ((k.val + 1 : ℕ) : ZMod n) = k + 1 := by
    push_cast
    rw [ZMod.natCast_rightInverse k]
  have hkey : Complex.exp
        (((heading (fun _ : ZMod n => c) ℓ (k + 1 : ZMod n).val
            - Real.arcsin (c * (ℓ (k + 1) / 2)) : ℝ) : ℂ) * Complex.I)
      = Complex.exp
          (((heading (fun _ : ZMod n => c) ℓ k.val
              + Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I) := by
    rcases Nat.lt_or_ge (k.val + 1) n with hlt | hge
    · -- no wrap: the two real exponents are literally equal
      have hval : (k + 1 : ZMod n).val = k.val + 1 := by
        rw [← hcast, ZMod.val_cast_of_lt hlt]
      have hheads : heading (fun _ : ZMod n => c) ℓ (k.val + 1)
          = heading (fun _ : ZMod n => c) ℓ k.val
            + turningAngle 0 (fun _ : ZMod n => c) ℓ (k + 1) := by
        change (∑ m ∈ Finset.range (k.val + 1 + 1),
            turningAngle 0 (fun _ : ZMod n => c) ℓ (m : ZMod n)) = _
        rw [Finset.sum_range_succ, hcast]
        rfl
      have hturn : turningAngle 0 (fun _ : ZMod n => c) ℓ (k + 1)
          = Real.arcsin (c * (ℓ k / 2))
            + Real.arcsin (c * (ℓ (k + 1) / 2)) := by
        simp only [turningAngle, tK_zero, add_sub_cancel_right]
      rw [hval, hheads, hturn]
      congr 1
      push_cast
      ring
    · -- wrap `k = n-1`: the exponents differ by the full turning `2π`
      have heq : k.val + 1 = n := by
        have := ZMod.val_lt k
        omega
      have hk0 : (k + 1 : ZMod n) = 0 := by
        rw [← hcast, heq, ZMod.natCast_self]
      have hkneg : k = -1 := eq_neg_of_add_eq_zero_left hk0
      have hψ0 : heading (fun _ : ZMod n => c) ℓ 0
          = Real.arcsin (c * (ℓ k / 2)) + Real.arcsin (c * (ℓ 0 / 2)) := by
        change (∑ m ∈ Finset.range 1,
            turningAngle 0 (fun _ : ZMod n => c) ℓ (m : ZMod n)) = _
        rw [Finset.sum_range_one]
        simp only [Nat.cast_zero, turningAngle, tK_zero, zero_sub, ← hkneg]
      have hψtop : heading (fun _ : ZMod n => c) ℓ k.val = 2 * Real.pi := by
        change (∑ m ∈ Finset.range (k.val + 1),
            turningAngle 0 (fun _ : ZMod n => c) ℓ (m : ZMod n)) = _
        rw [heq]
        have hbr := sum_range_natCast_add
          (turningAngle 0 (fun _ : ZMod n => c) ℓ) 0
        simp only [Nat.zero_add] at hbr
        rw [hbr]
        exact hT
      rw [hk0, ZMod.val_zero, hψ0, hψtop]
      have harg : ((Real.arcsin (c * (ℓ k / 2)) + Real.arcsin (c * (ℓ 0 / 2))
            - Real.arcsin (c * (ℓ 0 / 2)) : ℝ) : ℂ) * Complex.I
          = ((Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      have harg2 : ((2 * Real.pi + Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ)
            * Complex.I
          = ((Real.arcsin (c * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I
            + 2 * (Real.pi : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, harg2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [hkey]

/-- **All moment centres coincide at a constant-curvature profile**: for
`κ ≡ c > 0` with ARBITRARY strict moderate-arc edge lengths, `E = 0` and
`T = 2π`, the moment centre is independent of the edge.  This shows the
crux-C failure locus CONTAINS the entire inscribed-polygon stratum, which is
strictly larger than the regular-`n`-gon locus of `momentPoint_const_eq`.
Geometrically, at a constant-curvature configuration all `n` osculating circles
are one circle and every centre is its circumcentre. -/
theorem momentCenter_const_curvature [NeZero n] {c : ℝ} (hc : 0 < c)
    {ℓ : ZMod n → ℝ} (hMA : ModerateArc 0 (fun _ : ZMod n => c) ℓ)
    (hE : closureGap (fun _ : ZMod n => c) ℓ = 0)
    (hT : turningSum (fun _ : ZMod n => c) ℓ = 2 * Real.pi)
    (k k' : ZMod n) :
    momentCenter (fun _ : ZMod n => c) ℓ k
      = momentCenter (fun _ : ZMod n => c) ℓ k' := by
  have hall : ∀ j : ℕ, momentCenter (fun _ : ZMod n => c) ℓ (j : ZMod n)
      = momentCenter (fun _ : ZMod n => c) ℓ 0 := by
    intro j
    induction j with
    | zero => rw [Nat.cast_zero]
    | succ j ih =>
      have hj : ((j + 1 : ℕ) : ZMod n) = (j : ZMod n) + 1 := by
        push_cast
        ring
      rw [hj, momentCenter_const_succ hc hMA hE hT (j : ZMod n)]
      exact ih
  calc momentCenter (fun _ : ZMod n => c) ℓ k
      = momentCenter (fun _ : ZMod n => c) ℓ ((k.val : ℕ) : ZMod n) := by
        rw [ZMod.natCast_rightInverse k]
    _ = momentCenter (fun _ : ZMod n => c) ℓ 0 := hall k.val
    _ = momentCenter (fun _ : ZMod n => c) ℓ ((k'.val : ℕ) : ZMod n) :=
        (hall k'.val).symm
    _ = momentCenter (fun _ : ZMod n => c) ℓ k' := by
        rw [ZMod.natCast_rightInverse k']

/-- **Crux C is planar non-collinearity of the moment centres**: at a closed
configuration whose slope sums `t_k = b_k + a_{k+1}` are all positive
(automatic for a positive profile), moment rank holds iff the `n` moment
centres are not collinear in `ℂ ≅ ℝ²`. -/
theorem momentRank_iff_not_collinear [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0)
    (htpos : ∀ k : ZMod n, 0 < collarB κ ℓ k + collarA κ ℓ (k + 1)) :
    MomentRank κ ℓ ↔ ¬ Collinear ℝ (Set.range (momentCenter κ ℓ)) := by
  constructor
  · -- moment rank ⇒ the centres cannot be collinear
    intro hMR hcol
    obtain ⟨v, hv⟩ :=
      (collinear_iff_of_mem (Set.mem_range_self (0 : ZMod n))).mp hcol
    set A : ℂ × ℝ := (-Complex.I * momentCenter κ ℓ 0, (1 : ℝ)) with hA
    set B : ℂ × ℝ := (-Complex.I * v, (0 : ℝ)) with hB
    have hsub : Set.range (momentPoint κ ℓ)
        ⊆ ↑(Submodule.span ℝ ({A, B} : Set (ℂ × ℝ))) := by
      rintro x ⟨q, rfl⟩
      obtain ⟨r, hr⟩ := hv (momentCenter κ ℓ q) (Set.mem_range_self q)
      rw [momentPoint_eq_momentCenter hE (htpos q).ne']
      refine Submodule.smul_mem _ _ ?_
      have hval : ((-Complex.I * momentCenter κ ℓ q, (1 : ℝ)) : ℂ × ℝ)
          = A + r • B := by
        rw [hA, hB, Prod.smul_mk, Prod.mk_add_mk, hr]
        refine Prod.ext ?_ (by simp)
        change -Complex.I * (r • v +ᵥ momentCenter κ ℓ 0)
            = -Complex.I * momentCenter κ ℓ 0 + r • (-Complex.I * v)
        rw [vadd_eq_add, Complex.real_smul, Complex.real_smul]
        ring
      rw [hval]
      exact Submodule.add_mem _
        (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
    have hle : (⊤ : Submodule ℝ (ℂ × ℝ))
        ≤ Submodule.span ℝ ({A, B} : Set (ℂ × ℝ)) := by
      rw [← hMR]
      exact Submodule.span_le.mpr hsub
    have hcard : Module.finrank ℝ
        (Submodule.span ℝ ({A, B} : Set (ℂ × ℝ))) ≤ 2 := by
      refine le_trans (finrank_span_le_card _) ?_
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    have h3 : Module.finrank ℝ (ℂ × ℝ) ≤ 2 := by
      calc Module.finrank ℝ (ℂ × ℝ)
          = Module.finrank ℝ (⊤ : Submodule ℝ (ℂ × ℝ)) :=
            (finrank_top ℝ _).symm
        _ ≤ Module.finrank ℝ (Submodule.span ℝ ({A, B} : Set (ℂ × ℝ))) :=
            Submodule.finrank_mono hle
        _ ≤ 2 := hcard
    rw [finrank_complex_prod_real] at h3
    omega
  · -- non-collinear centres ⇒ full moment rank
    intro hncol
    set V := Submodule.span ℝ (Set.range (momentPoint κ ℓ)) with hVdef
    have hι : ∀ q : ZMod n,
        ((-Complex.I * momentCenter κ ℓ q, (1 : ℝ)) : ℂ × ℝ) ∈ V := by
      intro q
      have hmem : momentPoint κ ℓ q ∈ V := Submodule.subset_span ⟨q, rfl⟩
      have h2 := V.smul_mem (collarB κ ℓ q + collarA κ ℓ (q + 1))⁻¹ hmem
      rw [momentPoint_eq_momentCenter hE (htpos q).ne', smul_smul,
        inv_mul_cancel₀ (htpos q).ne', one_smul] at h2
      exact h2
    have hdiff : ∀ q q' : ZMod n,
        ((-Complex.I * (momentCenter κ ℓ q - momentCenter κ ℓ q'), (0 : ℝ))
          : ℂ × ℝ) ∈ V := by
      intro q q'
      have h3 : ((-Complex.I * (momentCenter κ ℓ q - momentCenter κ ℓ q'),
            (0 : ℝ)) : ℂ × ℝ)
          = ((-Complex.I * momentCenter κ ℓ q, (1 : ℝ)) : ℂ × ℝ)
            - ((-Complex.I * momentCenter κ ℓ q', (1 : ℝ)) : ℂ × ℝ) := by
        rw [Prod.mk_sub_mk, sub_self]
        exact Prod.ext (by ring) rfl
      rw [h3]
      exact V.sub_mem (hι q) (hι q')
    -- the difference set of the centres lands in `V` through `z ↦ (-iz, 0)`
    have hWle : vectorSpan ℝ (Set.range (momentCenter κ ℓ))
        ≤ Submodule.comap
          ((LinearMap.inl ℝ ℂ ℝ).comp (LinearMap.mulLeft ℝ (-Complex.I))) V := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro z hz
      rw [Set.mem_vsub] at hz
      obtain ⟨p, ⟨q, rfl⟩, p', ⟨q', rfl⟩, rfl⟩ := hz
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, LinearMap.inl_apply, vsub_eq_sub]
      exact hdiff q q'
    -- non-collinearity makes the centre differences span all of `ℂ`
    have htop : vectorSpan ℝ (Set.range (momentCenter κ ℓ)) = ⊤ := by
      have hle2 : Module.finrank ℝ
          (vectorSpan ℝ (Set.range (momentCenter κ ℓ))) ≤ 2 := by
        simpa [Complex.finrank_real_complex] using
          (vectorSpan ℝ (Set.range (momentCenter κ ℓ))).finrank_le
      have hgt : ¬ Module.finrank ℝ
          (vectorSpan ℝ (Set.range (momentCenter κ ℓ))) ≤ 1 :=
        fun h1 => hncol (collinear_iff_finrank_le_one.mpr h1)
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [Complex.finrank_real_complex]
      omega
    have hfst : ∀ w : ℂ, ((w, (0 : ℝ)) : ℂ × ℝ) ∈ V := by
      intro w
      have hz : Complex.I * w ∈ vectorSpan ℝ (Set.range (momentCenter κ ℓ)) := by
        rw [htop]
        exact Submodule.mem_top
      have h2 := hWle hz
      rw [Submodule.mem_comap, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.inl_apply] at h2
      have hw : -Complex.I * (Complex.I * w) = w := by
        rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
      rwa [hw] at h2
    have hsnd : (((0 : ℂ), (1 : ℝ)) : ℂ × ℝ) ∈ V := by
      have h2 := V.sub_mem (hι 0) (hfst (-Complex.I * momentCenter κ ℓ 0))
      rwa [Prod.mk_sub_mk, sub_self, sub_zero] at h2
    have hVtop : V = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨w, t⟩ -
      have h2 := V.add_mem (hfst w) (V.smul_mem t hsnd)
      simpa using h2
    exact hVtop

/-- **Constant curvature has no moment rank**: at ANY closed strict
moderate-arc configuration with constant profile `κ ≡ c > 0` and total
turning `2π` — every inscribed polygon, arbitrary edge lengths — the moment
points all lie on the line `ℝ·(-i C, 1)`, so they cannot span the
three-dimensional target.  `not_momentRank_const` is the special case
`ℓ ≡ (2/c)·sin(π/n)` of the regular `n`-gon. -/
theorem not_momentRank_of_const_curvature [NeZero n] {c : ℝ} (hc : 0 < c)
    {ℓ : ZMod n → ℝ} (hMA : ModerateArc 0 (fun _ : ZMod n => c) ℓ)
    (hE : closureGap (fun _ : ZMod n => c) ℓ = 0)
    (hT : turningSum (fun _ : ZMod n => c) ℓ = 2 * Real.pi) :
    ¬ MomentRank (fun _ : ZMod n => c) ℓ := by
  intro h
  have htpos : ∀ q : ZMod n, 0 < collarB (fun _ : ZMod n => c) ℓ q
      + collarA (fun _ : ZMod n => c) ℓ (q + 1) :=
    fun q => add_pos (collarB_pos hMA hc) (collarA_pos hMA hc)
  have hrange : Set.range (momentPoint (fun _ : ZMod n => c) ℓ)
      ⊆ ↑(Submodule.span ℝ
          ({(-Complex.I * momentCenter (fun _ : ZMod n => c) ℓ 0, (1 : ℝ))}
            : Set (ℂ × ℝ))) := by
    rintro x ⟨q, rfl⟩
    rw [momentPoint_eq_momentCenter hE (htpos q).ne',
      momentCenter_const_curvature hc hMA hE hT q 0]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_singleton _))
  have hle : (⊤ : Submodule ℝ (ℂ × ℝ)) ≤ Submodule.span ℝ
      ({(-Complex.I * momentCenter (fun _ : ZMod n => c) ℓ 0, (1 : ℝ))}
        : Set (ℂ × ℝ)) := by
    rw [← h]
    exact Submodule.span_le.mpr hrange
  have h1 : Module.finrank ℝ (ℂ × ℝ) ≤ 1 := by
    calc Module.finrank ℝ (ℂ × ℝ)
        = Module.finrank ℝ (⊤ : Submodule ℝ (ℂ × ℝ)) := (finrank_top ℝ _).symm
      _ ≤ Module.finrank ℝ (Submodule.span ℝ
            ({(-Complex.I * momentCenter (fun _ : ZMod n => c) ℓ 0, (1 : ℝ))}
              : Set (ℂ × ℝ))) := Submodule.finrank_mono hle
      _ ≤ 1 := by
          simpa using finrank_span_le_card
            ({(-Complex.I * momentCenter (fun _ : ZMod n => c) ℓ 0, (1 : ℝ))}
              : Set (ℂ × ℝ))
  rw [finrank_complex_prod_real] at h1
  omega

/-! ## The converse at the rank-one stratum

`momentCenter_const_curvature` says constant curvature collapses all moment
centres.  This section proves the converse: at a closed positive strict
moderate-arc configuration with total turning `2π`, coincident moment centres
force a constant profile (`const_curvature_of_momentCenter_const`), so the
RANK-ONE part of the crux-C failure locus is exactly the inscribed-polygon
stratum (`momentCenter_const_iff`).  The rank-two case — centres collinear but
not all equal — remains open; see the blueprint remark on the failure locus. -/

/-- `cos (arcsin x) > 0` whenever `|x| < 1`. -/
lemma cos_arcsin_pos_of_abs_lt {x : ℝ} (hx : |x| < 1) :
    0 < Real.cos (Real.arcsin x) := by
  rw [Real.cos_arcsin]
  have hsq : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one _).mpr hx
  exact Real.sqrt_pos.mpr (by linarith)

private lemma abs_arcsin_lt_pi_div_two {x : ℝ} (hx : |x| < 1) :
    |Real.arcsin x| < Real.pi / 2 := by
  rw [abs_lt] at hx ⊢
  exact ⟨Real.neg_pi_div_two_lt_arcsin.2 hx.1, Real.arcsin_lt_pi_div_two.2 hx.2⟩

/-- The strict left wall at vertex `k + 1` in product-with-half-length form. -/
lemma abs_mul_half_lt_one_left {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (k : ZMod n) : |κ (k + 1) * (ℓ k / 2)| < 1 := by
  have h := hMA.wall_left (k + 1)
  rw [tK_zero, add_sub_cancel_right] at h
  rw [abs_mul, abs_of_pos (div_pos (hMA.length_pos k) two_pos)]
  exact h

/-- The strict right wall at vertex `k` in product-with-half-length form. -/
lemma abs_mul_half_lt_one_right {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (k : ZMod n) : |κ k * (ℓ k / 2)| < 1 := by
  have h := hMA.wall_right k
  rw [tK_zero] at h
  rw [abs_mul, abs_of_pos (div_pos (hMA.length_pos k) two_pos)]
  exact h

/-- **The outgoing slope is a tangent**: `ℓ_k b_k = tan φ⁺_k` with
`φ⁺_k = arcsin (κ_k ℓ_k / 2)`. -/
theorem length_mul_collarB (κ ℓ : ZMod n → ℝ) (k : ZMod n) :
    ℓ k * collarB κ ℓ k = Real.tan (Real.arcsin (κ k * (ℓ k / 2))) := by
  rw [Real.tan_arcsin]
  change ℓ k * (κ k / 2 / Real.sqrt (1 - (κ k * (ℓ k / 2)) ^ 2)) = _
  ring

/-- **The incoming slope is a tangent too**: `ℓ_k a_{k+1} = tan φ⁻_{k+1}` with
`φ⁻_{k+1} = arcsin (κ_{k+1} ℓ_k / 2)`. -/
theorem length_mul_collarA (κ ℓ : ZMod n → ℝ) (k : ZMod n) :
    ℓ k * collarA κ ℓ (k + 1)
      = Real.tan (Real.arcsin (κ (k + 1) * (ℓ k / 2))) := by
  rw [Real.tan_arcsin]
  change ℓ k * (κ (k + 1) / 2
      / Real.sqrt (1 - (κ (k + 1) * (ℓ (k + 1 - 1) / 2)) ^ 2)) = _
  rw [add_sub_cancel_right]
  ring

/-- **Polar form of `tan φ + i`**: for `cos φ ≠ 0`,
`tan φ + i = i·e^{-iφ}/cos φ`.  Project-local: the polar reading of a real
tangent that rotates the moment centre onto its osculating ray. -/
theorem tan_add_I_eq {φ : ℝ} (hφ : Real.cos φ ≠ 0) :
    ((Real.tan φ : ℝ) : ℂ) + Complex.I
      = Complex.I * Complex.exp (-(φ : ℂ) * Complex.I) / (Real.cos φ : ℂ) := by
  have hφC : ((Real.cos φ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hφ
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.tan_eq_sin_div_cos]
  push_cast [-Complex.ofReal_sin, -Complex.ofReal_cos]
  field_simp
  linear_combination (Real.sin φ : ℂ) * Complex.I_sq

/-- **Polar form of `i - tan φ`**: for `cos φ ≠ 0`,
`i - tan φ = i·e^{iφ}/cos φ`. -/
theorem I_sub_tan_eq {φ : ℝ} (hφ : Real.cos φ ≠ 0) :
    Complex.I - ((Real.tan φ : ℝ) : ℂ)
      = Complex.I * Complex.exp ((φ : ℂ) * Complex.I) / (Real.cos φ : ℂ) := by
  have hφC : ((Real.cos φ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hφ
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.tan_eq_sin_div_cos]
  push_cast [-Complex.ofReal_sin, -Complex.ofReal_cos]
  field_simp
  linear_combination -(Real.sin φ : ℂ) * Complex.I_sq

/-- **The two polar readings of a moment centre** at a closed strict
moderate-arc configuration with positive slope sums:
`C_k − v_k = i/(t_k cos φ⁻_{k+1})·e^{i(ψ_k − φ⁻_{k+1})}` and
`C_{k−1} − v_k = i/(t_{k−1} cos φ⁺_{k−1})·e^{i(ψ_{k−1} + φ⁺_{k−1})}`,
both prefactors strictly positive. -/
theorem momentCenter_sub_vertex_polar [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (hE : closureGap κ ℓ = 0) (k : ZMod n)
    (ht : 0 < collarB κ ℓ k + collarA κ ℓ (k + 1))
    (ht' : 0 < collarB κ ℓ (k - 1) + collarA κ ℓ k) :
    momentCenter κ ℓ k - vertexR2 κ ℓ k.val
      = Complex.I / (((collarB κ ℓ k + collarA κ ℓ (k + 1))
            * Real.cos (Real.arcsin (κ (k + 1) * (ℓ k / 2))) : ℝ) : ℂ)
        * Complex.exp (((heading κ ℓ k.val
            - Real.arcsin (κ (k + 1) * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I)
    ∧ momentCenter κ ℓ (k - 1) - vertexR2 κ ℓ k.val
      = Complex.I / (((collarB κ ℓ (k - 1) + collarA κ ℓ k)
            * Real.cos (Real.arcsin (κ (k - 1) * (ℓ (k - 1) / 2))) : ℝ) : ℂ)
        * Complex.exp (((heading κ ℓ (k - 1).val
            + Real.arcsin (κ (k - 1) * (ℓ (k - 1) / 2)) : ℝ) : ℂ) * Complex.I) := by
  have hw1 := abs_mul_half_lt_one_left hMA k
  have hw2 := abs_mul_half_lt_one_right hMA (k - 1)
  have hc1 := cos_arcsin_pos_of_abs_lt hw1
  have hc2 := cos_arcsin_pos_of_abs_lt hw2
  have htC : ((collarB κ ℓ k + collarA κ ℓ (k + 1) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ht.ne'
  have ht'C : ((collarB κ ℓ (k - 1) + collarA κ ℓ k : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ht'.ne'
  have hc1C : ((Real.cos (Real.arcsin (κ (k + 1) * (ℓ k / 2))) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hc1.ne'
  have hc2C :
      ((Real.cos (Real.arcsin (κ (k - 1) * (ℓ (k - 1) / 2))) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hc2.ne'
  constructor
  · have hstart : momentCenter κ ℓ k - vertexR2 κ ℓ k.val
        = (((ℓ k * collarA κ ℓ (k + 1) : ℝ) : ℂ) + Complex.I)
            / ((collarB κ ℓ k + collarA κ ℓ (k + 1) : ℝ) : ℂ)
          * Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I) := by
      simp only [momentCenter]
      ring
    rw [hstart, length_mul_collarA κ ℓ k, tan_add_I_eq hc1.ne']
    have hsplit : Complex.exp (((heading κ ℓ k.val
          - Real.arcsin (κ (k + 1) * (ℓ k / 2)) : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I)
          * Complex.exp
              (-(Real.arcsin (κ (k + 1) * (ℓ k / 2)) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    push_cast at htC hc1C ⊢
    field_simp
  · have hkk : (k - 1 + 1 : ZMod n) = k := by ring
    have ht'' : collarB κ ℓ (k - 1) + collarA κ ℓ (k - 1 + 1) ≠ 0 := by
      rw [hkk]
      exact ht'.ne'
    have hnext := momentCenter_eq_next hE (k := k - 1) ht''
    rw [hkk] at hnext
    have hstart : momentCenter κ ℓ (k - 1) - vertexR2 κ ℓ k.val
        = (Complex.I - ((ℓ (k - 1) * collarB κ ℓ (k - 1) : ℝ) : ℂ))
            / ((collarB κ ℓ (k - 1) + collarA κ ℓ k : ℝ) : ℂ)
          * Complex.exp ((heading κ ℓ (k - 1).val : ℂ) * Complex.I) := by
      rw [hnext]
      ring
    rw [hstart, length_mul_collarB κ ℓ (k - 1), I_sub_tan_eq hc2.ne']
    have hsplit : Complex.exp (((heading κ ℓ (k - 1).val
          + Real.arcsin (κ (k - 1) * (ℓ (k - 1) / 2)) : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((heading κ ℓ (k - 1).val : ℂ) * Complex.I)
          * Complex.exp
              ((Real.arcsin (κ (k - 1) * (ℓ (k - 1) / 2)) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    push_cast at ht'C hc2C ⊢
    field_simp

/-- **Coincident neighbouring centres force an angle identity**:
`C_{k−1} = C_k` implies `θ_k = φ⁺_{k−1} + φ⁻_{k+1}`. -/
theorem turningAngle_eq_of_momentCenter_eq [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) {k : ZMod n}
    (ht : 0 < collarB κ ℓ k + collarA κ ℓ (k + 1))
    (ht' : 0 < collarB κ ℓ (k - 1) + collarA κ ℓ k)
    (hCC : momentCenter κ ℓ (k - 1) = momentCenter κ ℓ k) :
    turningAngle 0 κ ℓ k
      = Real.arcsin (κ (k - 1) * (ℓ (k - 1) / 2))
        + Real.arcsin (κ (k + 1) * (ℓ k / 2)) := by
  obtain ⟨h1, h2⟩ := momentCenter_sub_vertex_polar hMA hE k ht ht'
  have hw1 := abs_mul_half_lt_one_left hMA k
  have hw2 := abs_mul_half_lt_one_right hMA (k - 1)
  have hc1 := cos_arcsin_pos_of_abs_lt hw1
  have hc2 := cos_arcsin_pos_of_abs_lt hw2
  have hr1 : (0 : ℝ) < (collarB κ ℓ k + collarA κ ℓ (k + 1))
      * Real.cos (Real.arcsin (κ (k + 1) * (ℓ k / 2))) := mul_pos ht hc1
  have hr2 : (0 : ℝ) < (collarB κ ℓ (k - 1) + collarA κ ℓ k)
      * Real.cos (Real.arcsin (κ (k - 1) * (ℓ (k - 1) / 2))) := mul_pos ht' hc2
  have hθabs := abs_lt.mp (abs_turningAngle_lt_pi hMA k)
  have hφm_abs := abs_lt.mp (abs_arcsin_lt_pi_div_two hw1)
  have hφp_abs := abs_lt.mp (abs_arcsin_lt_pi_div_two hw2)
  set φm : ℝ := Real.arcsin (κ (k + 1) * (ℓ k / 2)) with hφm
  set φp : ℝ := Real.arcsin (κ (k - 1) * (ℓ (k - 1) / 2)) with hφp
  -- the heading advance across vertex `k`, wrap case supplied by `hT`
  have hcast : (((k - 1).val + 1 : ℕ) : ZMod n) = k := by
    push_cast
    rw [ZMod.natCast_rightInverse (k - 1)]
    ring
  have hψ : heading κ ℓ k.val
        = heading κ ℓ (k - 1).val + turningAngle 0 κ ℓ k
      ∨ heading κ ℓ k.val
        = heading κ ℓ (k - 1).val + turningAngle 0 κ ℓ k - 2 * Real.pi := by
    rcases Nat.lt_or_ge ((k - 1).val + 1) n with hlt | hge
    · left
      have hval : k.val = (k - 1).val + 1 := by
        conv_lhs => rw [← hcast]
        rw [ZMod.val_cast_of_lt hlt]
      rw [hval]
      change (∑ m ∈ Finset.range ((k - 1).val + 1 + 1),
          turningAngle 0 κ ℓ (m : ZMod n)) = _
      rw [Finset.sum_range_succ, hcast]
      rfl
    · right
      have heq : (k - 1).val + 1 = n := by
        have := ZMod.val_lt (k - 1)
        omega
      have hk0 : k = 0 := by
        rw [← hcast, heq, ZMod.natCast_self]
      have hψtop : heading κ ℓ (k - 1).val = 2 * Real.pi := by
        change (∑ m ∈ Finset.range ((k - 1).val + 1),
            turningAngle 0 κ ℓ (m : ZMod n)) = _
        rw [heq]
        have hbr := sum_range_natCast_add (turningAngle 0 κ ℓ) 0
        simp only [Nat.zero_add] at hbr
        rw [hbr]
        exact hT
      have hψ0 : heading κ ℓ k.val = turningAngle 0 κ ℓ k := by
        rw [hk0, ZMod.val_zero]
        change (∑ m ∈ Finset.range 1, turningAngle 0 κ ℓ (m : ZMod n)) = _
        rw [Finset.sum_range_one, Nat.cast_zero]
      rw [hψ0, hψtop]
      ring
  -- equate the two polar readings and cancel the common positive prefactor
  have hEq : momentCenter κ ℓ (k - 1) - vertexR2 κ ℓ k.val
      = momentCenter κ ℓ k - vertexR2 κ ℓ k.val := by rw [hCC]
  rw [h1, h2] at hEq
  have hn := congrArg norm hEq
  simp only [norm_mul, norm_div, Complex.norm_I, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_eq_abs, mul_one, one_div] at hn
  rw [abs_of_pos ht, abs_of_pos ht', abs_of_pos hc1, abs_of_pos hc2] at hn
  have hr : (collarB κ ℓ (k - 1) + collarA κ ℓ k) * Real.cos φp
      = (collarB κ ℓ k + collarA κ ℓ (k + 1)) * Real.cos φm := inv_inj.mp hn
  rw [hr] at hEq
  have hrC : (((collarB κ ℓ k + collarA κ ℓ (k + 1))
      * Real.cos φm : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr1.ne'
  have hexp := mul_left_cancel₀ (div_ne_zero Complex.I_ne_zero hrC) hEq
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  push_cast at hm
  have hreal : heading κ ℓ (k - 1).val + φp
      = heading κ ℓ k.val - φm + m * (2 * Real.pi) := by
    have himg : (((heading κ ℓ (k - 1).val + φp)
        - (heading κ ℓ k.val - φm + m * (2 * Real.pi)) : ℝ) : ℂ)
          * Complex.I = 0 := by
      push_cast
      linear_combination hm
    rcases mul_eq_zero.mp himg with h | h
    · have h0 := Complex.ofReal_eq_zero.mp h
      linarith
    · exact absurd h Complex.I_ne_zero
  obtain ⟨M, hM⟩ : ∃ M : ℤ,
      φp + φm - turningAngle 0 κ ℓ k = M * (2 * Real.pi) := by
    rcases hψ with hno | hwrap
    · refine ⟨m, ?_⟩
      rw [hno] at hreal
      linarith
    · refine ⟨m - 1, ?_⟩
      rw [hwrap] at hreal
      push_cast
      linarith
  have hM0 : M = 0 := by
    by_contra hne
    have h1le : (1 : ℝ) ≤ |(M : ℝ)| := by
      have : (1 : ℤ) ≤ |M| := Int.one_le_abs hne
      exact_mod_cast this
    have hpi := Real.pi_pos
    have habs : |φp + φm - turningAngle 0 κ ℓ k| < 2 * Real.pi := by
      rw [abs_lt]
      constructor <;> linarith [hθabs.1, hθabs.2, hφm_abs.1, hφm_abs.2,
        hφp_abs.1, hφp_abs.2]
    rw [hM, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.pi)] at habs
    nlinarith
  rw [hM0] at hM
  push_cast at hM
  linarith

/-- The **curvature jump across edge `k`**:
`g_k = arcsin (κ_{k+1} ℓ_k / 2) − arcsin (κ_k ℓ_k / 2)`, the difference of the
incoming and outgoing half-angles across the shared edge. -/
noncomputable def curvatureJump (κ ℓ : ZMod n → ℝ) (k : ZMod n) : ℝ :=
  Real.arcsin (κ (k + 1) * (ℓ k / 2)) - Real.arcsin (κ k * (ℓ k / 2))

private lemma curvatureJump_succ [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (hpos : ∀ i, 0 < κ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi)
    (hCC : ∀ k k' : ZMod n, momentCenter κ ℓ k = momentCenter κ ℓ k')
    (k : ZMod n) :
    curvatureJump κ ℓ (k + 1) = curvatureJump κ ℓ k := by
  have htpos : ∀ q : ZMod n, 0 < collarB κ ℓ q + collarA κ ℓ (q + 1) :=
    fun q => add_pos (collarB_pos hMA (hpos q)) (collarA_pos hMA (hpos (q + 1)))
  have ht' : 0 < collarB κ ℓ (k + 1 - 1) + collarA κ ℓ (k + 1) := by
    rw [show (k + 1 - 1 : ZMod n) = k by ring]
    exact htpos k
  have hkey := turningAngle_eq_of_momentCenter_eq hMA hE hT
    (htpos (k + 1)) ht' (hCC _ _)
  simp only [add_sub_cancel_right] at hkey
  have hθ : turningAngle 0 κ ℓ (k + 1)
      = Real.arcsin (κ (k + 1) * (ℓ k / 2))
        + Real.arcsin (κ (k + 1) * (ℓ (k + 1) / 2)) := by
    simp only [turningAngle, tK_zero, add_sub_cancel_right]
  rw [hθ] at hkey
  simp only [curvatureJump]
  linarith

/-- **Coincident centres make the curvature jump constant** on `ZMod n`. -/
theorem curvatureJump_const_of_momentCenter_const [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (hpos : ∀ i, 0 < κ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi)
    (hCC : ∀ k k' : ZMod n, momentCenter κ ℓ k = momentCenter κ ℓ k') :
    ∀ k k' : ZMod n, curvatureJump κ ℓ k = curvatureJump κ ℓ k' := by
  have hall : ∀ j : ℕ, curvatureJump κ ℓ (j : ZMod n) = curvatureJump κ ℓ 0 := by
    intro j
    induction j with
    | zero => rw [Nat.cast_zero]
    | succ j ih =>
      have hj : ((j + 1 : ℕ) : ZMod n) = (j : ZMod n) + 1 := by
        push_cast
        ring
      rw [hj, curvatureJump_succ hMA hpos hE hT hCC (j : ZMod n)]
      exact ih
  intro k k'
  calc curvatureJump κ ℓ k
      = curvatureJump κ ℓ ((k.val : ℕ) : ZMod n) := by
        rw [ZMod.natCast_rightInverse k]
    _ = curvatureJump κ ℓ 0 := hall k.val
    _ = curvatureJump κ ℓ ((k'.val : ℕ) : ZMod n) := (hall k'.val).symm
    _ = curvatureJump κ ℓ k' := by rw [ZMod.natCast_rightInverse k']

/-- **Coincident centres force constant curvature**: at a closed positive
strict moderate-arc configuration with total turning `2π`, if all `n` moment
centres coincide then the curvature profile is constant.  This is the converse
of `momentCenter_const_curvature`. -/
theorem const_curvature_of_momentCenter_const [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (hpos : ∀ i, 0 < κ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi)
    (hCC : ∀ k k' : ZMod n, momentCenter κ ℓ k = momentCenter κ ℓ k') :
    ∀ i j : ZMod n, κ i = κ j := by
  have hjump := curvatureJump_const_of_momentCenter_const hMA hpos hE hT hCC
  have hshift : ∑ x : ZMod n, κ (x + 1) = ∑ x : ZMod n, κ x :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _ (fun _ => rfl)
  have hsum0 : ∑ x : ZMod n, (κ (x + 1) - κ x) = 0 := by
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  have hmono : ∀ k : ZMod n, curvatureJump κ ℓ k < 0 → κ (k + 1) < κ k := by
    intro k hj
    have harc : Real.arcsin (κ (k + 1) * (ℓ k / 2))
        < Real.arcsin (κ k * (ℓ k / 2)) := by
      have h0 : Real.arcsin (κ (k + 1) * (ℓ k / 2))
          - Real.arcsin (κ k * (ℓ k / 2)) < 0 := hj
      linarith
    have hmul : κ (k + 1) * (ℓ k / 2) < κ k * (ℓ k / 2) := by
      by_contra hle
      exact absurd (Real.arcsin_le_arcsin (not_lt.mp hle)) (not_le.mpr harc)
    exact lt_of_mul_lt_mul_right hmul
      (div_pos (hMA.length_pos k) two_pos).le
  have hmono' : ∀ k : ZMod n, 0 < curvatureJump κ ℓ k → κ k < κ (k + 1) := by
    intro k hj
    have harc : Real.arcsin (κ k * (ℓ k / 2))
        < Real.arcsin (κ (k + 1) * (ℓ k / 2)) := by
      have h0 : 0 < Real.arcsin (κ (k + 1) * (ℓ k / 2))
          - Real.arcsin (κ k * (ℓ k / 2)) := hj
      linarith
    have hmul : κ k * (ℓ k / 2) < κ (k + 1) * (ℓ k / 2) := by
      by_contra hle
      exact absurd (Real.arcsin_le_arcsin (not_lt.mp hle)) (not_le.mpr harc)
    exact lt_of_mul_lt_mul_right hmul
      (div_pos (hMA.length_pos k) two_pos).le
  have hsucc : ∀ k : ZMod n, κ (k + 1) = κ k := by
    rcases lt_trichotomy (curvatureJump κ ℓ 0) 0 with hneg | hzero | hposg
    · exfalso
      have hlt : ∑ x : ZMod n, (κ (x + 1) - κ x) < 0 :=
        Finset.sum_neg
          (fun x _ => sub_neg.mpr (hmono x (by rw [hjump x 0]; exact hneg)))
          Finset.univ_nonempty
      linarith
    · intro k
      have hj : curvatureJump κ ℓ k = 0 := by
        rw [hjump k 0]
        exact hzero
      have harc : Real.arcsin (κ (k + 1) * (ℓ k / 2))
          = Real.arcsin (κ k * (ℓ k / 2)) := by
        have h0 : Real.arcsin (κ (k + 1) * (ℓ k / 2))
            - Real.arcsin (κ k * (ℓ k / 2)) = 0 := hj
        linarith
      have h1 := abs_lt.mp (abs_mul_half_lt_one_left hMA k)
      have h2 := abs_lt.mp (abs_mul_half_lt_one_right hMA k)
      have hx : κ (k + 1) * (ℓ k / 2) = κ k * (ℓ k / 2) :=
        (Real.arcsin_inj h1.1.le h1.2.le h2.1.le h2.2.le).mp harc
      exact mul_right_cancel₀ (div_pos (hMA.length_pos k) two_pos).ne' hx
    · exfalso
      have hlt : 0 < ∑ x : ZMod n, (κ (x + 1) - κ x) :=
        Finset.sum_pos
          (fun x _ => sub_pos.mpr (hmono' x (by rw [hjump x 0]; exact hposg)))
          Finset.univ_nonempty
      linarith
  have hall : ∀ j : ℕ, κ ((j : ℕ) : ZMod n) = κ 0 := by
    intro j
    induction j with
    | zero => rw [Nat.cast_zero]
    | succ j ih =>
      have hj : ((j + 1 : ℕ) : ZMod n) = (j : ZMod n) + 1 := by
        push_cast
        ring
      rw [hj, hsucc]
      exact ih
  intro i j
  calc κ i = κ ((i.val : ℕ) : ZMod n) := by rw [ZMod.natCast_rightInverse i]
    _ = κ 0 := hall i.val
    _ = κ ((j.val : ℕ) : ZMod n) := (hall j.val).symm
    _ = κ j := by rw [ZMod.natCast_rightInverse j]

/-- **Exact characterisation of the rank-one stratum**: at a closed positive
strict moderate-arc configuration with total turning `2π`, all `n` moment
centres coincide iff the curvature profile is constant — the locus where the
moment points span only a line is exactly the inscribed-polygon stratum.  The
rank-two case (centres collinear but not all equal) remains open. -/
theorem momentCenter_const_iff [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (hpos : ∀ i, 0 < κ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) :
    (∀ k k' : ZMod n, momentCenter κ ℓ k = momentCenter κ ℓ k')
      ↔ ∀ i j : ZMod n, κ i = κ j := by
  constructor
  · exact const_curvature_of_momentCenter_const hMA hpos hE hT
  · intro hconst
    have hfun : κ = fun _ : ZMod n => κ 0 := funext fun i => hconst i 0
    rw [hfun] at hMA hE hT ⊢
    exact momentCenter_const_curvature (hpos 0) hMA hE hT

end Gluck.Discrete
