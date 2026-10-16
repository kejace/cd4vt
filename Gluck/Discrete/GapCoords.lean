/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.Convexity

/-!
# Edge-gap coordinates

The discrete layer so far is indexed by *vertices*: `turningAngle` lives at
vertex `i` and reads the two adjacent edges, and `ModerateArc 0` is a
per-vertex conjunction with overlapping constraints. This file installs the
complementary *edge*-indexed bookkeeping: each edge `e` carries one scalar

`β_e = arcsin (κ_e ℓ_e / 2) + arcsin (κ_{e+1} ℓ_e / 2)`,

the **gap** of that edge — the total turn performed while traversing `e`.

* `gapAngleAt`, `gapAngle` — the gap function of an edge and the gap of a
  configuration.
* `edgeCap`, `edgeWall` — the length cap `C_e = 2 / max (κ_e, κ_{e+1})` and the
  gap wall `U_e = π/2 + arcsin (min κ / max κ)`.
* `sum_gapAngle` — regrouping the `2n` arcsines by edge: `∑ β_e = T(κ, ℓ)`,
  so the gauge constraint `T = 2π` is affine in the gaps.
* `moderateArc_zero_iff_edge` — the strict moderate-arc domain is exactly the
  box `∀ e, 0 < ℓ_e < C_e` in edge coordinates.
* `gapAngleAt_strictMonoOn`, `gapAngleAt_zero`, `gapAngleAt_edgeCap`,
  `gapAngle_mem_Ioo`, `exists_unique_length_of_gap`, `gapLength` — on
  `[0, C_e]` the gap function is a strictly increasing continuous bijection
  onto `[0, U_e]`, with explicit inverse `gapLength`.
* `edgeCap_eq_radius`, `edgeWall_eq_radius` — cap and wall in the osculating
  radii `r_i = 1/κ_i` (the coordinate of the external four-gap notes; the
  inversion swaps `min` and `max`).
* `realizesR2_of_gapData`, `realizesR2_of_gapVector` — repackaging a gap
  vector strictly inside its walls with `∑ β = 2π` and vanishing closure into
  `RealizesR2 κ`, simplicity supplied by `isSimplePolygon_of_turningPositive`.
* `exists_le_both_neighbours`, `exists_of_high_neighbour` — the purely
  order-theoretic global step of the external zigzag argument.

**Scope.** This file is a change of variables plus a repackaging: it proves NO
new realization. It does not import, assume, or depend on any of the external
pipeline's local four-gap certificates (all under external audit);
`exists_of_high_neighbour` takes the consequence it needs as an explicit
hypothesis and is vacuous until an audited argument supplies it. Nothing here
bears on Tabachnikov's Problem 2.

-/

@[expose] public section

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

/-! ## The gap of an edge -/

/-- The gap function of edge `e`: the total turn contributed by an edge of
length `t` sitting between the two endpoint curvatures `κ e` and `κ (e+1)`.
Blueprint `def:gap_angle`. -/
noncomputable def gapAngleAt (κ : ZMod n → ℝ) (e : ZMod n) (t : ℝ) : ℝ :=
  Real.arcsin (κ e * (t / 2)) + Real.arcsin (κ (e + 1) * (t / 2))

/-- The gap of edge `e` in the configuration `(κ, ℓ)`: `β_e = γ_e (ℓ e)`.
Blueprint `def:gap_of_config`. -/
noncomputable def gapAngle (κ ℓ : ZMod n → ℝ) (e : ZMod n) : ℝ :=
  gapAngleAt κ e (ℓ e)

/-- The edge cap `C_e = 2 / max (κ e) (κ (e+1))`: the supremum of the lengths
edge `e` may take inside the strict moderate-arc domain
(`moderateArc_zero_iff_edge`). Blueprint `def:edge_cap`. -/
noncomputable def edgeCap (κ : ZMod n → ℝ) (e : ZMod n) : ℝ :=
  2 / max (κ e) (κ (e + 1))

/-- The edge wall `U_e = π/2 + arcsin (min κ / max κ)`: the supremum of the
gaps edge `e` may take (`gapAngleAt_edgeCap`). Blueprint `def:edge_wall`. -/
noncomputable def edgeWall (κ : ZMod n → ℝ) (e : ZMod n) : ℝ :=
  Real.pi / 2 + Real.arcsin (min (κ e) (κ (e + 1)) / max (κ e) (κ (e + 1)))

/-- **The turning sum is the sum of the gaps.** Regrouping the `2n` arcsines
of `turningSum` by the edge they mention instead of the vertex that owns them:
`∑ e, β_e = T(κ, ℓ)`. This is what makes the gauge constraint `T = 2π` affine
in edge-gap coordinates. Blueprint `lem:gap_sum`. -/
lemma sum_gapAngle [NeZero n] (κ ℓ : ZMod n → ℝ) :
    ∑ e : ZMod n, gapAngle κ ℓ e = turningSum κ ℓ := by
  unfold turningSum turningAngle gapAngle gapAngleAt
  simp only [tK_zero]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_comm]
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _
    (fun x => by simp [add_sub_cancel_right])

/-! ## The strict domain in edge coordinates -/

/-- Cap positivity: for positive endpoint curvatures the edge cap is positive
and clamps both arcsine arguments at or below `1`, with equality in at least
one of the two. Blueprint `lem:edge_cap_pos`. -/
lemma edgeCap_pos {κ : ZMod n → ℝ} {e : ZMod n} (h : 0 < κ e)
    (h' : 0 < κ (e + 1)) :
    0 < edgeCap κ e ∧ κ e * (edgeCap κ e / 2) ≤ 1 ∧
      κ (e + 1) * (edgeCap κ e / 2) ≤ 1 ∧
      (κ e * (edgeCap κ e / 2) = 1 ∨ κ (e + 1) * (edgeCap κ e / 2) = 1) := by
  have hmax : 0 < max (κ e) (κ (e + 1)) := lt_max_iff.2 (Or.inl h)
  have hhalf : edgeCap κ e / 2 = (max (κ e) (κ (e + 1)))⁻¹ := by
    rw [edgeCap]
    field_simp
  refine ⟨div_pos two_pos hmax, ?_, ?_, ?_⟩
  · rw [hhalf, ← div_eq_mul_inv, div_le_one hmax]
    exact le_max_left _ _
  · rw [hhalf, ← div_eq_mul_inv, div_le_one hmax]
    exact le_max_right _ _
  · rcases le_total (κ e) (κ (e + 1)) with hle | hle
    · exact Or.inr (by rw [hhalf, max_eq_right hle, mul_inv_cancel₀ h'.ne'])
    · exact Or.inl (by rw [hhalf, max_eq_left hle, mul_inv_cancel₀ h.ne'])

/-- Below the cap of the edge `e`, both endpoint walls of that edge hold: any
`c` with `0 < c ≤ max (κ e) (κ (e+1))` satisfies `c * (t/2) < 1`. -/
private lemma mul_half_lt_one_of_lt_edgeCap {κ : ZMod n → ℝ} {e : ZMod n}
    {c t : ℝ} (hc : 0 < c) (hle : c ≤ max (κ e) (κ (e + 1))) (ht : 0 ≤ t)
    (h : t < edgeCap κ e) : c * (t / 2) < 1 := by
  have hM : 0 < max (κ e) (κ (e + 1)) := lt_of_lt_of_le hc hle
  rw [edgeCap, lt_div_iff₀ hM] at h
  nlinarith [mul_le_mul_of_nonneg_right hle ht]

/-- Both endpoint walls of edge `e` put its length below the cap. -/
private lemma lt_edgeCap_of_walls {κ : ZMod n → ℝ} {e : ZMod n} {t : ℝ}
    (hmax : 0 < max (κ e) (κ (e + 1)))
    (h1 : κ e * (t / 2) < 1) (h2 : κ (e + 1) * (t / 2) < 1) :
    t < edgeCap κ e := by
  rw [edgeCap, lt_div_iff₀ hmax]
  rcases le_total (κ e) (κ (e + 1)) with hle | hle
  · rw [max_eq_right hle]
    nlinarith
  · rw [max_eq_left hle]
    nlinarith

/-- **The moderate-arc domain is a box in `ℓ`.** For positive curvature the
per-vertex strict moderate-arc conjunction collapses to the single two-sided
per-edge bound `0 < ℓ_e < C_e`. Blueprint `lem:moderate_arc_edge`. -/
lemma moderateArc_zero_iff_edge {κ ℓ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i) :
    ModerateArc 0 κ ℓ ↔ ∀ e : ZMod n, 0 < ℓ e ∧ ℓ e < edgeCap κ e := by
  rw [moderateArc_zero_iff]
  constructor
  · intro h e
    have hmax : 0 < max (κ e) (κ (e + 1)) := lt_max_iff.2 (Or.inl (hκ e))
    obtain ⟨hpos, -, hr⟩ := h e
    obtain ⟨-, hl', -⟩ := h (e + 1)
    rw [abs_of_pos (hκ e)] at hr
    rw [abs_of_pos (hκ (e + 1)), add_sub_cancel_right] at hl'
    exact ⟨hpos, lt_edgeCap_of_walls hmax hr hl'⟩
  · intro h i
    have hpos : 0 < ℓ i := (h i).1
    have hpos' : 0 < ℓ (i - 1) := (h (i - 1)).1
    refine ⟨hpos, ?_, ?_⟩
    · rw [abs_of_pos (hκ i)]
      exact mul_half_lt_one_of_lt_edgeCap (hκ i)
        (by rw [sub_add_cancel]; exact le_max_right _ _) hpos'.le (h (i - 1)).2
    · rw [abs_of_pos (hκ i)]
      exact mul_half_lt_one_of_lt_edgeCap (hκ i) (le_max_left _ _) hpos.le
        (h i).2

/-! ## The gap function is a bijection onto `(0, U_e)` -/

/-- One arcsine summand of the gap function is strictly increasing below the
clamp. -/
private lemma arcsin_summand_lt {c s t C : ℝ} (hc : 0 < c)
    (hclamp : c * (C / 2) ≤ 1) (hs : 0 ≤ s) (hst : s < t) (htC : t ≤ C) :
    Real.arcsin (c * (s / 2)) < Real.arcsin (c * (t / 2)) := by
  refine Real.arcsin_lt_arcsin (by nlinarith) (by nlinarith) (by nlinarith)

/-- **The gap function is strictly increasing up to the cap.** Blueprint
`lem:gap_strict_mono`. -/
lemma gapAngleAt_strictMonoOn {κ : ZMod n → ℝ} {e : ZMod n} (h : 0 < κ e)
    (h' : 0 < κ (e + 1)) :
    StrictMonoOn (gapAngleAt κ e) (Set.Icc 0 (edgeCap κ e)) := by
  obtain ⟨-, hcl1, hcl2, -⟩ := edgeCap_pos h h'
  intro s hs t ht hst
  exact add_lt_add (arcsin_summand_lt h hcl1 hs.1 hst ht.2)
    (arcsin_summand_lt h' hcl2 hs.1 hst ht.2)

/-- The gap function is continuous (in the clamped-arcsin convention, on all
of `ℝ`). -/
private lemma gapAngleAt_continuous (κ : ZMod n → ℝ) (e : ZMod n) :
    Continuous (gapAngleAt κ e) := by
  unfold gapAngleAt
  fun_prop

/-- The gap function vanishes at zero length. Blueprint
`lem:gap_wall_value_zero`. -/
lemma gapAngleAt_zero (κ : ZMod n → ℝ) (e : ZMod n) : gapAngleAt κ e 0 = 0 := by
  simp [gapAngleAt]

/-- **The gap function reaches the wall at the cap**: `γ_e(C_e) = U_e`. At the
cap, the arcsine at the larger curvature is exactly `π/2` and the other reads
the ratio `min κ / max κ`. Blueprint `lem:gap_wall_value_cap`. -/
lemma gapAngleAt_edgeCap {κ : ZMod n → ℝ} {e : ZMod n} (h : 0 < κ e)
    (h' : 0 < κ (e + 1)) : gapAngleAt κ e (edgeCap κ e) = edgeWall κ e := by
  rcases le_total (κ e) (κ (e + 1)) with hle | hle
  · rw [gapAngleAt, edgeCap, edgeWall, max_eq_right hle, min_eq_left hle]
    have h1 : κ e * (2 / κ (e + 1) / 2) = κ e / κ (e + 1) := by
      field_simp
    have h2 : κ (e + 1) * (2 / κ (e + 1) / 2) = 1 := by
      field_simp
    rw [h1, h2, Real.arcsin_one]
    ring
  · rw [gapAngleAt, edgeCap, edgeWall, max_eq_left hle, min_eq_right hle]
    have h1 : κ e * (2 / κ e / 2) = 1 := by
      field_simp
    have h2 : κ (e + 1) * (2 / κ e / 2) = κ (e + 1) / κ e := by
      field_simp
    rw [h1, h2, Real.arcsin_one]

/-- **Admissible lengths give admissible gaps**: `0 < ℓ_e < C_e` implies
`0 < β_e < U_e`. Blueprint `lem:gap_mem_Ioo`. -/
lemma gapAngle_mem_Ioo {κ ℓ : ZMod n → ℝ} {e : ZMod n} (h : 0 < κ e)
    (h' : 0 < κ (e + 1)) (h0 : 0 < ℓ e) (hcap : ℓ e < edgeCap κ e) :
    0 < gapAngle κ ℓ e ∧ gapAngle κ ℓ e < edgeWall κ e := by
  have hC : 0 < edgeCap κ e := (edgeCap_pos h h').1
  have hmono := gapAngleAt_strictMonoOn h h'
  unfold gapAngle
  constructor
  · have := hmono (Set.left_mem_Icc.2 hC.le) ⟨h0.le, hcap.le⟩ h0
    rwa [gapAngleAt_zero] at this
  · have := hmono ⟨h0.le, hcap.le⟩ (Set.right_mem_Icc.2 hC.le) hcap
    rwa [gapAngleAt_edgeCap h h'] at this

/-- **Every admissible gap is attained, uniquely**: for `0 < β < U_e` there is
a unique `t ∈ (0, C_e)` with `γ_e(t) = β`. Existence is the intermediate value
theorem on `[0, C_e]`; uniqueness is strict monotonicity. Blueprint
`lem:gap_surjective`. -/
lemma exists_unique_length_of_gap {κ : ZMod n → ℝ} {e : ZMod n} (h : 0 < κ e)
    (h' : 0 < κ (e + 1)) {β : ℝ} (hβ0 : 0 < β) (hβU : β < edgeWall κ e) :
    ∃! t, t ∈ Set.Ioo 0 (edgeCap κ e) ∧ gapAngleAt κ e t = β := by
  have hC : (0 : ℝ) ≤ edgeCap κ e := (edgeCap_pos h h').1.le
  have hsub := intermediate_value_Ioo hC
    ((gapAngleAt_continuous κ e).continuousOn
      (s := Set.Icc 0 (edgeCap κ e)))
  rw [gapAngleAt_zero, gapAngleAt_edgeCap h h'] at hsub
  obtain ⟨t, ht, hval⟩ := hsub ⟨hβ0, hβU⟩
  refine ⟨t, ⟨ht, hval⟩, ?_⟩
  rintro s ⟨hs, hsval⟩
  exact (gapAngleAt_strictMonoOn h h').injOn (Set.Ioo_subset_Icc_self hs)
    (Set.Ioo_subset_Icc_self ht) (hsval.trans hval.symm)

/-- **The inverse: length of a prescribed gap.** For positive endpoint
curvatures and `0 < β < U_e` this is the unique length in `(0, C_e)` whose gap
is `β` (`exists_unique_length_of_gap`); junk value `0` otherwise. Blueprint
`def:gap_length`. -/
noncomputable def gapLength (κ : ZMod n → ℝ) (e : ZMod n) (β : ℝ) : ℝ :=
  if h : 0 < κ e ∧ 0 < κ (e + 1) ∧ 0 < β ∧ β < edgeWall κ e then
    (exists_unique_length_of_gap h.1 h.2.1 h.2.2.1 h.2.2.2).exists.choose
  else 0

/-- The inverse inverts: `γ_e (gapLength κ e β) = β` on the admissible range.
Blueprint `lem:gap_length_spec`. -/
lemma gapLength_spec {κ : ZMod n → ℝ} {e : ZMod n} {β : ℝ} (h : 0 < κ e)
    (h' : 0 < κ (e + 1)) (hβ0 : 0 < β) (hβU : β < edgeWall κ e) :
    gapAngleAt κ e (gapLength κ e β) = β := by
  rw [gapLength, dif_pos ⟨h, h', hβ0, hβU⟩]
  exact (exists_unique_length_of_gap h h' hβ0 hβU).exists.choose_spec.2

/-- The inverse lands strictly inside the cap:
`0 < gapLength κ e β < C_e` on the admissible range. Blueprint
`lem:gap_length_mem`. -/
lemma gapLength_mem_Ioo {κ : ZMod n → ℝ} {e : ZMod n} {β : ℝ} (h : 0 < κ e)
    (h' : 0 < κ (e + 1)) (hβ0 : 0 < β) (hβU : β < edgeWall κ e) :
    0 < gapLength κ e β ∧ gapLength κ e β < edgeCap κ e := by
  rw [gapLength, dif_pos ⟨h, h', hβ0, hβU⟩]
  exact ⟨(exists_unique_length_of_gap h h' hβ0 hβU).exists.choose_spec.1.1,
    (exists_unique_length_of_gap h h' hβ0 hβU).exists.choose_spec.1.2⟩

/-! ## Radius form of the cap and the wall

The external four-gap notes work with the osculating radii `r_i = 1/κ_i`;
inversion is order-reversing on `(0, ∞)`, so it swaps `min` and `max` and
leaves the wall ratio unchanged. -/

/-- Radius form of the cap: `C_e = 2 min (r_e, r_{e+1})` for `r_i = 1/κ_i`.
Blueprint `lem:gap_radius_cap`. -/
lemma edgeCap_eq_radius {κ : ZMod n → ℝ} {e : ZMod n} (h : 0 < κ e)
    (h' : 0 < κ (e + 1)) :
    edgeCap κ e = 2 * min (1 / κ e) (1 / κ (e + 1)) := by
  rcases le_total (κ e) (κ (e + 1)) with hle | hle
  · rw [edgeCap, max_eq_right hle,
      min_eq_right (one_div_le_one_div_of_le h hle)]
    ring
  · rw [edgeCap, max_eq_left hle,
      min_eq_left (one_div_le_one_div_of_le h' hle)]
    ring

/-- Radius form of the wall:
`U_e = π/2 + arcsin (min (r_e, r_{e+1}) / max (r_e, r_{e+1}))` for
`r_i = 1/κ_i`. The ratio is unchanged by the inversion. Blueprint
`lem:gap_radius_wall`. -/
lemma edgeWall_eq_radius {κ : ZMod n → ℝ} {e : ZMod n} (h : 0 < κ e)
    (h' : 0 < κ (e + 1)) :
    edgeWall κ e = Real.pi / 2 +
      Real.arcsin (min (1 / κ e) (1 / κ (e + 1)) /
        max (1 / κ e) (1 / κ (e + 1))) := by
  rcases le_total (κ e) (κ (e + 1)) with hle | hle
  · rw [edgeWall, max_eq_right hle, min_eq_left hle,
      min_eq_right (one_div_le_one_div_of_le h hle),
      max_eq_left (one_div_le_one_div_of_le h hle)]
    have harg : (1 : ℝ) / κ (e + 1) / (1 / κ e) = κ e / κ (e + 1) := by
      field_simp [h.ne', h'.ne']
    rw [harg]
  · rw [edgeWall, max_eq_left hle, min_eq_right hle,
      min_eq_left (one_div_le_one_div_of_le h' hle),
      max_eq_right (one_div_le_one_div_of_le h' hle)]
    have harg : (1 : ℝ) / κ e / (1 / κ (e + 1)) = κ (e + 1) / κ e := by
      field_simp [h.ne', h'.ne']
    rw [harg]

/-! ## Repackaging a gap vector as a realization -/

/-- **Realizability from edge-coordinate data.** Lengths strictly inside the
edge caps, vanishing closure, and total gap `2π` package into `RealizesR2 κ`,
with simplicity supplied by `isSimplePolygon_of_turningPositive`. This proves
no new realization: it is a change of variables. Blueprint
`thm:realizes_of_gap_data`. -/
theorem realizesR2_of_gapData [NeZero n] {κ ℓ : ZMod n → ℝ} (hn : 3 ≤ n)
    (hκ : ∀ i, 0 < κ i) (hℓ : ∀ e : ZMod n, 0 < ℓ e ∧ ℓ e < edgeCap κ e)
    (hE : closureGap κ ℓ = 0)
    (hsum : ∑ e : ZMod n, gapAngle κ ℓ e = 2 * Real.pi) :
    RealizesR2 κ := by
  have hMA : ModerateArc 0 κ ℓ := (moderateArc_zero_iff_edge hκ).2 hℓ
  have hT : turningSum κ ℓ = 2 * Real.pi := by
    rw [← sum_gapAngle]
    exact hsum
  exact ⟨ℓ, hMA, hE, hT, isSimplePolygon_of_turningPositive hn hMA hκ hE hT⟩

/-- **Realizability from a gap vector.** The hypothesis triple — strict gaps
below their walls, total gap `2π`, closure zero at the induced lengths — is
verbatim the conclusion the external four-gap pipeline's realization arguments
end at; this theorem is the interface at which such an argument, once audited,
would deliver `RealizesR2` without further geometry. **The hypotheses are
never discharged in-tree**: no external certificate is imported or assumed.
Blueprint `thm:realizes_of_gap_vector`. -/
theorem realizesR2_of_gapVector [NeZero n] {κ : ZMod n → ℝ} (hn : 3 ≤ n)
    (hκ : ∀ i, 0 < κ i) {β : ZMod n → ℝ}
    (hβ : ∀ k : ZMod n, 0 < β k ∧ β k < edgeWall κ k)
    (hsum : ∑ k : ZMod n, β k = 2 * Real.pi)
    (hE : closureGap κ (fun e => gapLength κ e (β e)) = 0) :
    RealizesR2 κ := by
  have hmem : ∀ e : ZMod n, 0 < gapLength κ e (β e) ∧
      gapLength κ e (β e) < edgeCap κ e := fun e =>
    gapLength_mem_Ioo (hκ e) (hκ (e + 1)) (hβ e).1 (hβ e).2
  refine realizesR2_of_gapData hn hκ hmem hE ?_
  rw [Finset.sum_congr rfl fun e _ =>
    show gapAngle κ (fun e' => gapLength κ e' (β e')) e = β e from
      gapLength_spec (hκ e) (hκ (e + 1)) (hβ e).1 (hβ e).2]
  exact hsum

/-! ## The global step of the zigzag argument

Purely order-theoretic — no curvature, no closure, no geometry. The local
consequence feeding `exists_of_high_neighbour` is an explicit hypothesis,
precisely so that this file takes on none of the risk of the unaudited
external local certificates. -/

/-- **A cyclic family cannot beat both neighbours everywhere**: some index has
`H (i+1) ≤ H i` and `H (i+1) ≤ H (i+2)` — take `i + 1` at a global minimum.
Blueprint `lem:high_neighbour_cyclic`. -/
lemma exists_le_both_neighbours {m : ℕ} [NeZero m] (H : ZMod m → ℝ) :
    ∃ i : ZMod m, H (i + 1) ≤ H i ∧ H (i + 1) ≤ H (i + 2) := by
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_min_image Finset.univ H Finset.univ_nonempty
  have h1 : j - 1 + 1 = j := sub_add_cancel j 1
  have h2 : j - 1 + 2 = j + 1 := by ring
  exact ⟨j - 1, by rw [h1]; exact hj _ (Finset.mem_univ _),
    by rw [h1, h2]; exact hj _ (Finset.mem_univ _)⟩

/-- **Global step of the zigzag argument.** If failure of `P` at `i` forces
the middle value `H (i+1)` strictly above one of its neighbours, then `P`
holds somewhere. In the intended application `H` is the cyclic word of radius
maxima and `P i` says the `i`-th four-gap carrier has strictly opposite
endpoint defects; **the high-neighbour hypothesis is supplied only by an
unaudited external analysis and is never discharged in-tree**, so this lemma
is vacuous until such an argument is audited. Blueprint
`lem:high_neighbour_global`. -/
lemma exists_of_high_neighbour {m : ℕ} [NeZero m] {H : ZMod m → ℝ}
    {P : ZMod m → Prop}
    (hloc : ∀ i : ZMod m, ¬P i → H i < H (i + 1) ∨ H (i + 2) < H (i + 1)) :
    ∃ i, P i := by
  by_contra hall
  rw [not_exists] at hall
  obtain ⟨i, h1, h2⟩ := exists_le_both_neighbours H
  rcases hloc i (hall i) with hlt | hlt
  · exact absurd h1 (not_le.2 hlt)
  · exact absurd h2 (not_le.2 hlt)

end Gluck.Discrete
