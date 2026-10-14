/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Convexity
import Mathlib.Topology.Order.IntermediateValue

/-!
# The closing engine (Euclidean, positive) — Section 1: the Umlauf rescaling retraction

For a positive profile `κ` and a positive base `ℓ⁰` the total turning
`t ↦ turningSum κ (t · ℓ⁰)` is strictly increasing (`turningSum_smul_lt`),
continuous with value `0` at `t = 0` (`turningSum_smul_tendsto_zero`), and hence,
given a *ceiling* `t₁` at which the moderate-arc data already turns by `≥ 2π`,
attains the value `2π` at a unique admissible scale `t⋆ ∈ (0, t₁]`
(`exists_umlauf_scale`). This solves the scalar turning equation of the discrete
closing engine; the ceiling hypothesis (constructing a *balanced base*) and the
2-dimensional position equation are Sections 2–3, left at architecture level.

Blueprint: `blueprint/src/chapters/Gluck_Discrete_Closing.tex`, `sec:umlauf`.
-/

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

/-! ## Project-local Mathlib supplement — Umlauf rescaling retraction -/

/-- Strict monotonicity of `arcsin` packaged for the turning-angle arguments:
each argument is positive at the smaller scale and below the moderate-arc wall
at the larger scale, so both lie in `[-1, 1]` and `arcsin` strictly increases. -/
private lemma arcsin_arg_lt {xs xt : ℝ} (hpos : 0 < xs) (hlt : xs < xt)
    (hlt1 : xt < 1) : Real.arcsin xs < Real.arcsin xt :=
  Real.arcsin_lt_arcsin (by linarith) hlt hlt1.le

/-- Each Euclidean turning angle is strictly increasing under uniform scaling of
a positive base by `s < t`, provided the larger scale is moderate-arc. -/
private lemma turningAngle_scale_lt {κ ℓ₀ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (hℓ : ∀ i, 0 < ℓ₀ i) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hMA : ModerateArc 0 κ (fun i => t * ℓ₀ i)) (i : ZMod n) :
    turningAngle 0 κ (fun i => s * ℓ₀ i) i
      < turningAngle 0 κ (fun i => t * ℓ₀ i) i := by
  rw [moderateArc_zero_iff] at hMA
  obtain ⟨_, hw1, hw2⟩ := hMA i
  rw [abs_of_pos (hκ i)] at hw1 hw2
  simp only [turningAngle, tK_zero]
  apply add_lt_add
  · refine arcsin_arg_lt (mul_pos (hκ i) (div_pos (mul_pos hs (hℓ _)) two_pos))
      (mul_lt_mul_of_pos_left ?_ (hκ i)) hw1
    nlinarith [hℓ (i - 1)]
  · refine arcsin_arg_lt (mul_pos (hκ i) (div_pos (mul_pos hs (hℓ _)) two_pos))
      (mul_lt_mul_of_pos_left ?_ (hκ i)) hw2
    nlinarith [hℓ i]

/-- **`lem:turning_scale_mono`.** For a positive profile `κ` and positive base
`ℓ⁰`, the total turning `turningSum κ (t · ℓ⁰)` is strictly increasing in the
scale `t` on the moderate-arc range: if `0 < s < t` and the larger scale is
moderate-arc, then the turning sum at `s` is strictly below that at `t`.
Termwise strict via `turningAngle_scale_lt`. -/
theorem turningSum_smul_lt [NeZero n] {κ ℓ₀ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (hℓ : ∀ i, 0 < ℓ₀ i) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hMA : ModerateArc 0 κ (fun i => t * ℓ₀ i)) :
    turningSum κ (fun i => s * ℓ₀ i) < turningSum κ (fun i => t * ℓ₀ i) := by
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty ?_
  intro i _
  exact turningAngle_scale_lt hκ hℓ hs hst hMA i

/-- Moderate-arcness is inherited by smaller scales: if `t · ℓ⁰` is moderate-arc
and `0 < s ≤ t`, then `s · ℓ⁰` is moderate-arc (every `arcsin` argument only
shrinks). -/
private lemma moderateArc_scale_le {κ ℓ₀ : ZMod n → ℝ} (hℓ : ∀ i, 0 < ℓ₀ i)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hMA : ModerateArc 0 κ (fun i => t * ℓ₀ i)) :
    ModerateArc 0 κ (fun i => s * ℓ₀ i) := by
  rw [moderateArc_zero_iff] at hMA ⊢
  intro i
  obtain ⟨_, hw1, hw2⟩ := hMA i
  refine ⟨mul_pos hs (hℓ i), ?_, ?_⟩
  · have hle : |κ i| * (s * ℓ₀ (i - 1) / 2) ≤ |κ i| * (t * ℓ₀ (i - 1) / 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hℓ (i - 1)]) (abs_nonneg _)
    linarith
  · have hle : |κ i| * (s * ℓ₀ i / 2) ≤ |κ i| * (t * ℓ₀ i / 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hℓ i]) (abs_nonneg _)
    linarith

/-- **`lem:turning_scale_zero`.** For a positive profile `κ` and positive base
`ℓ⁰` the scaling map `t ↦ turningSum κ (t · ℓ⁰)` is (globally) continuous and
vanishes at `t = 0`. Global continuity is the cleanest form and subsumes the
`t → 0⁺` limit; each summand is `arcsin` of a linear-in-`t` argument. -/
theorem turningSum_smul_tendsto_zero [NeZero n] {κ ℓ₀ : ZMod n → ℝ} :
    Continuous (fun t : ℝ => turningSum κ (fun i => t * ℓ₀ i)) ∧
      turningSum κ (fun i => (0 : ℝ) * ℓ₀ i) = 0 := by
  refine ⟨?_, ?_⟩
  · have hEq : (fun t : ℝ => turningSum κ (fun i => t * ℓ₀ i))
        = fun t : ℝ => ∑ i : ZMod n,
          (Real.arcsin (κ i * (t * ℓ₀ (i - 1) / 2))
            + Real.arcsin (κ i * (t * ℓ₀ i / 2))) := by
      funext t
      simp only [turningSum, turningAngle, tK_zero]
    rw [hEq]
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (Real.continuous_arcsin.comp (by fun_prop)).add
      (Real.continuous_arcsin.comp (by fun_prop))
  · simp [turningSum, turningAngle, tK_zero]

/-- **`lem:exists_umlauf_scale`.** Given `n ≥ 3` (`[NeZero n]`), a positive
profile `κ`, a positive base `ℓ⁰`, and a *ceiling* `t₁ > 0` at which the data is
moderate-arc and already turns by `≥ 2π`, there is an admissible scale
`t⋆ ∈ (0, t₁]` at which `t⋆ · ℓ⁰` is moderate-arc and turns by exactly `2π`.
Monotone IVT: the continuous strictly-increasing `g t = turningSum κ (t · ℓ⁰)`
runs from `g 0 = 0 < 2π` to `g t₁ ≥ 2π`, so hits `2π`; the hitting scale is
positive and `≤ t₁`, hence moderate-arc by `moderateArc_scale_le`. -/
theorem exists_umlauf_scale [NeZero n] {κ ℓ₀ : ZMod n → ℝ}
    (_hκ : ∀ i, 0 < κ i) (hℓ : ∀ i, 0 < ℓ₀ i) {t₁ : ℝ} (ht₁ : 0 < t₁)
    (hMA₁ : ModerateArc 0 κ (fun i => t₁ * ℓ₀ i))
    (hcap : 2 * Real.pi ≤ turningSum κ (fun i => t₁ * ℓ₀ i)) :
    ∃ t ∈ Set.Ioc 0 t₁, ModerateArc 0 κ (fun i => t * ℓ₀ i) ∧
      turningSum κ (fun i => t * ℓ₀ i) = 2 * Real.pi := by
  obtain ⟨hcont, hzero⟩ :=
    turningSum_smul_tendsto_zero (n := n) (κ := κ) (ℓ₀ := ℓ₀)
  set g : ℝ → ℝ := fun t => turningSum κ (fun i => t * ℓ₀ i) with hg
  have hg0 : g 0 = 0 := hzero
  have hmem : 2 * Real.pi ∈ Set.Icc (g 0) (g t₁) := by
    rw [hg0]
    exact ⟨by positivity, hcap⟩
  obtain ⟨t, htmem, hgt⟩ :=
    intermediate_value_Icc ht₁.le hcont.continuousOn hmem
  obtain ⟨ht0, ht1⟩ := htmem
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, hg0] at hgt
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      linarith
  refine ⟨t, ⟨htpos, ht1⟩, moderateArc_scale_le hℓ htpos ht1 hMA₁, hgt⟩

/-- Uniqueness of the Umlauf scale (the `unique` clause of
`lem:exists_umlauf_scale`): two positive moderate-arc scales of a positive base
with equal total turning coincide. Immediate from strict monotonicity
(`turningSum_smul_lt`) via trichotomy. -/
theorem umlauf_scale_unique [NeZero n] {κ ℓ₀ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (hℓ : ∀ i, 0 < ℓ₀ i) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hMAs : ModerateArc 0 κ (fun i => s * ℓ₀ i))
    (hMAt : ModerateArc 0 κ (fun i => t * ℓ₀ i))
    (hST : turningSum κ (fun i => s * ℓ₀ i)
      = turningSum κ (fun i => t * ℓ₀ i)) : s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact absurd hST (ne_of_lt (turningSum_smul_lt hκ hℓ hs h hMAt))
  · exact h
  · exact absurd hST.symm (ne_of_lt (turningSum_smul_lt hκ hℓ ht h hMAs))

/-! ## Section 4 — single-edge turning tune (`sec:edge_tune`)

Unlike the *ray* retraction of Section 1 (which scales all edges together and is
obstructed), the turning sum is monotone in *one* edge with the others held
fixed — the discrete `∂θ/∂ℓ_k > 0` fact — and this single-edge dependence is not
obstructed. The edge value `ℓ_k` enters `turningAngle 0 κ ℓ i` at exactly the
two vertices `i = k` (right summand) and `i = k+1` (left summand). We record the
strict monotonicity (`turningSum_update_lt`) and its IVT tune to `2π`
(`exists_edge_turning_scale`), the route-shared inner solve. -/

/-- `Function.update` is monotone in its value slot: if `a ≤ b` then the updated
base is pointwise `≤` (the two functions agree off `k`, and at `k` we have
`a ≤ b`). -/
private lemma update_mono {ℓ : ZMod n → ℝ} {k : ZMod n} {a b : ℝ} (hab : a ≤ b)
    (j : ZMod n) : Function.update ℓ k a j ≤ Function.update ℓ k b j := by
  by_cases h : j = k
  · subst h; simp [Function.update_self, hab]
  · simp [Function.update_of_ne h]

/-- Each Euclidean turning angle is monotone under raising a single edge value:
both `arcsin` arguments only grow (`κ i > 0`, and `update ℓ k a ≤ update ℓ k b`
pointwise), and `arcsin` is monotone (`Real.arcsin_le_arcsin`). -/
private lemma turningAngle_update_le {κ ℓ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i)
    {k : ZMod n} {a b : ℝ} (hab : a ≤ b) (i : ZMod n) :
    turningAngle 0 κ (Function.update ℓ k a) i
      ≤ turningAngle 0 κ (Function.update ℓ k b) i := by
  simp only [turningAngle, tK_zero]
  apply add_le_add
  · exact Real.arcsin_le_arcsin
      (mul_le_mul_of_nonneg_left
        (by linarith [update_mono (ℓ := ℓ) (k := k) hab (i - 1)]) (hκ i).le)
  · exact Real.arcsin_le_arcsin
      (mul_le_mul_of_nonneg_left
        (by linarith [update_mono (ℓ := ℓ) (k := k) hab i]) (hκ i).le)

/-- **`lem:turningSum_edge_mono`.** For a positive profile `κ`, raising a single
edge `ℓ_k` from `a` to `b` (`0 < a < b`, moderate-arc at the larger value)
strictly increases the total turning. Termwise `≤` everywhere
(`turningAngle_update_le`) with one strict term at the vertex `i = k` (via
`arcsin_arg_lt`, its argument below the wall at `b`); `Finset.sum_lt_sum`. -/
theorem turningSum_update_lt [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (k : ZMod n) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hMA : ModerateArc 0 κ (Function.update ℓ k b)) :
    turningSum κ (Function.update ℓ k a) < turningSum κ (Function.update ℓ k b) := by
  apply Finset.sum_lt_sum
  · intro i _
    exact turningAngle_update_le hκ hab.le i
  · refine ⟨k, Finset.mem_univ k, ?_⟩
    simp only [turningAngle, tK_zero]
    apply add_lt_add_of_le_of_lt
    · exact Real.arcsin_le_arcsin
        (mul_le_mul_of_nonneg_left
          (by linarith [update_mono (ℓ := ℓ) (k := k) hab.le (k - 1)]) (hκ k).le)
    · simp only [Function.update_self]
      refine arcsin_arg_lt (mul_pos (hκ k) (div_pos ha two_pos))
        (mul_lt_mul_of_pos_left (by linarith) (hκ k)) ?_
      have hw := (moderateArc_zero_iff.mp hMA k).2.2
      rw [Function.update_self, abs_of_pos (hκ k)] at hw
      exact hw

/-- Moderate-arcness is inherited by smaller single-edge values: if
`update ℓ k b` is moderate-arc and `0 < a ≤ b`, then `update ℓ k a` is
moderate-arc (every `arcsin` argument only shrinks; the updated `k`-th edge
stays positive because `a > 0`). -/
private lemma moderateArc_update_le {κ ℓ : ZMod n → ℝ} {k : ZMod n}
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hMA : ModerateArc 0 κ (Function.update ℓ k b)) :
    ModerateArc 0 κ (Function.update ℓ k a) := by
  rw [moderateArc_zero_iff] at hMA ⊢
  intro i
  obtain ⟨hpos, hw1, hw2⟩ := hMA i
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : i = k
    · subst h; rw [Function.update_self]; exact ha
    · rw [Function.update_of_ne h]; rw [Function.update_of_ne h] at hpos; exact hpos
  · have hb : |κ i| * (Function.update ℓ k a (i - 1) / 2)
        ≤ |κ i| * (Function.update ℓ k b (i - 1) / 2) :=
      mul_le_mul_of_nonneg_left
        (by linarith [update_mono (ℓ := ℓ) (k := k) hab (i - 1)]) (abs_nonneg _)
    linarith
  · have hb : |κ i| * (Function.update ℓ k a i / 2)
        ≤ |κ i| * (Function.update ℓ k b i / 2) :=
      mul_le_mul_of_nonneg_left
        (by linarith [update_mono (ℓ := ℓ) (k := k) hab i]) (abs_nonneg _)
    linarith

/-- Continuity of the single-edge value slot: `a ↦ Function.update ℓ k a m` is
continuous (it is `id` when `m = k`, constant otherwise). -/
private lemma continuous_update_apply {ℓ : ZMod n → ℝ} (k m : ZMod n) :
    Continuous (fun a : ℝ => Function.update ℓ k a m) := by
  by_cases h : m = k
  · subst h; simp only [Function.update_self]; exact continuous_id
  · simp only [Function.update_of_ne h]; exact continuous_const

/-- The single-edge turning map `a ↦ turningSum κ (update ℓ k a)` is continuous:
each summand is `arcsin` of an argument linear in the (continuous) updated edge
value. -/
private lemma continuous_turningSum_update [NeZero n] {κ ℓ : ZMod n → ℝ}
    (k : ZMod n) :
    Continuous (fun a : ℝ => turningSum κ (Function.update ℓ k a)) := by
  have hEq : (fun a : ℝ => turningSum κ (Function.update ℓ k a))
      = fun a : ℝ => ∑ i : ZMod n,
        (Real.arcsin (κ i * (Function.update ℓ k a (i - 1) / 2))
          + Real.arcsin (κ i * (Function.update ℓ k a i / 2))) := by
    funext a
    simp only [turningSum, turningAngle, tK_zero]
  rw [hEq]
  refine continuous_finsetSum _ (fun i _ => ?_)
  refine (Real.continuous_arcsin.comp ?_).add (Real.continuous_arcsin.comp ?_)
  · exact continuous_const.mul ((continuous_update_apply k (i - 1)).div_const 2)
  · exact continuous_const.mul ((continuous_update_apply k i).div_const 2)

/-- **`lem:exists_edge_turning_scale`.** Given `n ≥ 3` (`[NeZero n]`), a positive
profile `κ`, a base `ℓ`, a tuned edge `k`, and `0 < lo < hi` with the larger
value moderate-arc and `turningSum (update ℓ k lo) < 2π ≤ turningSum
(update ℓ k hi)`, there is `a ∈ (lo, hi]` at which `update ℓ k a` is moderate-arc
and turns by exactly `2π`. Monotone IVT: `g a = turningSum κ (update ℓ k a)` is
continuous (`continuous_turningSum_update`) with `g lo < 2π ≤ g hi`, so
`intermediate_value_Icc` hits `2π`; the hitting value exceeds `lo` (since
`g lo < 2π`) and is `≤ hi`, hence moderate-arc by `moderateArc_update_le`. -/
theorem exists_edge_turning_scale [NeZero n] {κ ℓ : ZMod n → ℝ}
    (_hκ : ∀ i, 0 < κ i) (k : ZMod n) {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hMA : ModerateArc 0 κ (Function.update ℓ k hi))
    (hlt : turningSum κ (Function.update ℓ k lo) < 2 * Real.pi)
    (hge : 2 * Real.pi ≤ turningSum κ (Function.update ℓ k hi)) :
    ∃ a ∈ Set.Ioc lo hi, ModerateArc 0 κ (Function.update ℓ k a) ∧
      turningSum κ (Function.update ℓ k a) = 2 * Real.pi := by
  set g : ℝ → ℝ := fun a => turningSum κ (Function.update ℓ k a) with hg
  have hcont : Continuous g := continuous_turningSum_update k
  have hmem : 2 * Real.pi ∈ Set.Icc (g lo) (g hi) := ⟨hlt.le, hge⟩
  obtain ⟨a, hamem, hga⟩ :=
    intermediate_value_Icc hlohi.le hcont.continuousOn hmem
  obtain ⟨hloa, hahi⟩ := hamem
  have hloa' : lo < a := by
    rcases hloa.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hga
      exact absurd hga (ne_of_lt hlt)
  refine ⟨a, ⟨hloa', hahi⟩,
    moderateArc_update_le (hlo.trans hloa') hahi hMA, hga⟩

/-- Uniqueness of the single-edge turning tune (the `unique` clause of
`lem:exists_edge_turning_scale`): two positive moderate-arc single-edge values of
a base with equal total turning coincide. Immediate from the strict monotonicity
of `turningSum_update_lt` via trichotomy. -/
theorem edge_turning_scale_unique [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (k : ZMod n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hMAa : ModerateArc 0 κ (Function.update ℓ k a))
    (hMAb : ModerateArc 0 κ (Function.update ℓ k b))
    (hAB : turningSum κ (Function.update ℓ k a)
      = turningSum κ (Function.update ℓ k b)) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hAB (ne_of_lt (turningSum_update_lt hκ k ha h hMAb))
  · exact h
  · exact absurd hAB.symm (ne_of_lt (turningSum_update_lt hκ k hb h hMAa))

/-! ## Section 4b — subset-scaling turning tune (`sec:subset_tune`)

The block generalization of the single-edge tune: a designated subset `S` of
edges is scaled by a common factor `t` with the other edges held fixed, and the
turning sum is tuned to `2π` in `t`. The proofs are verbatim mirrors of §4
(termwise comparison, one strict term at any `e₀ ∈ S`, IVT). Block-constant
families, wall-relative families, and the adjacent-block slices of any anchor
variant all consume exactly this solve. -/

/-- **`def:scale_on`.** Subset edge scaling: scale the edges in `S` by `t`,
holding the others fixed. For `t > 0` and `ℓ` positive this is again a positive
edge vector; the single-edge update of `sec:edge_tune` is (up to
reparameterizing the scale by the absolute edge value) the case `S = {k}`. -/
def scaleOn (ℓ : ZMod n → ℝ) (S : Finset (ZMod n)) (t : ℝ) : ZMod n → ℝ :=
  fun e => if e ∈ S then t * ℓ e else ℓ e

/-- `scaleOn` at a scaled edge (`e ∈ S`) is `t * ℓ e`. -/
private lemma scaleOn_apply_mem {ℓ : ZMod n → ℝ} {S : Finset (ZMod n)} {t : ℝ}
    {e : ZMod n} (he : e ∈ S) : scaleOn ℓ S t e = t * ℓ e := if_pos he

/-- Scaling by `1` is the identity: `scaleOn ℓ S 1 = ℓ` (the `t = 1` anchor of
every block family). -/
@[simp] theorem scaleOn_one (ℓ : ZMod n → ℝ) (S : Finset (ZMod n)) :
    scaleOn ℓ S 1 = ℓ := by
  funext e
  simp [scaleOn]

/-- `scaleOn` is pointwise monotone in the scale over a positive base: the
scaled edges grow with `t` (`ℓ e > 0`), the unscaled ones are unchanged. -/
private lemma scaleOn_mono {ℓ : ZMod n → ℝ} (hℓ : ∀ e, 0 < ℓ e)
    {S : Finset (ZMod n)} {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) (e : ZMod n) :
    scaleOn ℓ S t₁ e ≤ scaleOn ℓ S t₂ e := by
  by_cases he : e ∈ S
  · simp only [scaleOn_apply_mem he]
    exact mul_le_mul_of_nonneg_right h (hℓ e).le
  · simp only [scaleOn, if_neg he]
    exact le_rfl

/-- `scaleOn` of a positive base at a positive scale is positive. -/
private lemma scaleOn_pos {ℓ : ZMod n → ℝ} (hℓ : ∀ e, 0 < ℓ e)
    {S : Finset (ZMod n)} {t : ℝ} (ht : 0 < t) (e : ZMod n) :
    0 < scaleOn ℓ S t e := by
  by_cases he : e ∈ S
  · rw [scaleOn_apply_mem he]; exact mul_pos ht (hℓ e)
  · rw [scaleOn, if_neg he]; exact hℓ e

/-- Each Euclidean turning angle is monotone under raising the subset scale:
both `arcsin` arguments only grow (`κ i > 0`, `scaleOn` pointwise monotone),
and `arcsin` is monotone (`Real.arcsin_le_arcsin`). Mirror of
`turningAngle_update_le`. -/
private lemma turningAngle_scaleOn_le {κ ℓ : ZMod n → ℝ} (hκ : ∀ i, 0 < κ i)
    (hℓ : ∀ e, 0 < ℓ e) {S : Finset (ZMod n)} {t₁ t₂ : ℝ} (h : t₁ ≤ t₂)
    (i : ZMod n) :
    turningAngle 0 κ (scaleOn ℓ S t₁) i ≤ turningAngle 0 κ (scaleOn ℓ S t₂) i := by
  simp only [turningAngle, tK_zero]
  apply add_le_add
  · exact Real.arcsin_le_arcsin
      (mul_le_mul_of_nonneg_left
        (by linarith [scaleOn_mono hℓ (S := S) h (i - 1)]) (hκ i).le)
  · exact Real.arcsin_le_arcsin
      (mul_le_mul_of_nonneg_left
        (by linarith [scaleOn_mono hℓ (S := S) h i]) (hκ i).le)

/-- **`lem:turningSum_scaleOn_mono`.** For a positive profile `κ` and positive
base `ℓ`, raising the common scale of a *nonempty* edge subset `S` from `t₁` to
`t₂` (`0 < t₁ < t₂`, moderate-arc at the larger scale) strictly increases the
total turning. Termwise `≤` everywhere (`turningAngle_scaleOn_le`) with one
strict term at any `e₀ ∈ S` (right summand of the vertex `i = e₀`, via
`arcsin_arg_lt` with its argument below the wall at `t₂`); `Finset.sum_lt_sum`.
Mirror of `turningSum_update_lt`. -/
theorem turningSum_scaleOn_lt [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (hℓ : ∀ e, 0 < ℓ e) {S : Finset (ZMod n)}
    (hS : S.Nonempty) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht : t₁ < t₂)
    (hMA : ModerateArc 0 κ (scaleOn ℓ S t₂)) :
    turningSum κ (scaleOn ℓ S t₁) < turningSum κ (scaleOn ℓ S t₂) := by
  apply Finset.sum_lt_sum
  · intro i _
    exact turningAngle_scaleOn_le hκ hℓ ht.le i
  · obtain ⟨e₀, he₀⟩ := hS
    refine ⟨e₀, Finset.mem_univ e₀, ?_⟩
    simp only [turningAngle, tK_zero]
    apply add_lt_add_of_le_of_lt
    · exact Real.arcsin_le_arcsin
        (mul_le_mul_of_nonneg_left
          (by linarith [scaleOn_mono hℓ (S := S) ht.le (e₀ - 1)]) (hκ e₀).le)
    · have hw := (moderateArc_zero_iff.mp hMA e₀).2.2
      rw [abs_of_pos (hκ e₀)] at hw
      simp only [scaleOn_apply_mem he₀] at hw ⊢
      refine arcsin_arg_lt
        (mul_pos (hκ e₀) (div_pos (mul_pos ht₁ (hℓ e₀)) two_pos))
        (mul_lt_mul_of_pos_left (by nlinarith [hℓ e₀]) (hκ e₀)) hw

/-- Moderate-arcness is inherited by smaller subset scales: if `scaleOn ℓ S t₂`
is moderate-arc and `0 < t₁ ≤ t₂`, then `scaleOn ℓ S t₁` is moderate-arc (every
`arcsin` argument only shrinks; positivity from `t₁ > 0`). Mirror of
`moderateArc_update_le`. -/
private lemma moderateArc_scaleOn_le {κ ℓ : ZMod n → ℝ} (hℓ : ∀ e, 0 < ℓ e)
    {S : Finset (ZMod n)} {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h : t₁ ≤ t₂)
    (hMA : ModerateArc 0 κ (scaleOn ℓ S t₂)) :
    ModerateArc 0 κ (scaleOn ℓ S t₁) := by
  rw [moderateArc_zero_iff] at hMA ⊢
  intro i
  obtain ⟨_, hw1, hw2⟩ := hMA i
  refine ⟨scaleOn_pos hℓ ht₁ i, ?_, ?_⟩
  · have hb : |κ i| * (scaleOn ℓ S t₁ (i - 1) / 2)
        ≤ |κ i| * (scaleOn ℓ S t₂ (i - 1) / 2) :=
      mul_le_mul_of_nonneg_left
        (by linarith [scaleOn_mono hℓ (S := S) h (i - 1)]) (abs_nonneg _)
    linarith
  · have hb : |κ i| * (scaleOn ℓ S t₁ i / 2)
        ≤ |κ i| * (scaleOn ℓ S t₂ i / 2) :=
      mul_le_mul_of_nonneg_left
        (by linarith [scaleOn_mono hℓ (S := S) h i]) (abs_nonneg _)
    linarith

/-- Continuity of the subset scale slot: `t ↦ scaleOn ℓ S t e` is continuous
(it is `t ↦ t * ℓ e` when `e ∈ S`, constant otherwise). Mirror of
`continuous_update_apply`. -/
private lemma continuous_scaleOn_apply {ℓ : ZMod n → ℝ} (S : Finset (ZMod n))
    (e : ZMod n) : Continuous (fun t : ℝ => scaleOn ℓ S t e) := by
  by_cases he : e ∈ S
  · simp only [scaleOn_apply_mem he]
    exact continuous_id.mul continuous_const
  · simp only [scaleOn, if_neg he]
    exact continuous_const

/-- The subset-scaling turning map `t ↦ turningSum κ (scaleOn ℓ S t)` is
continuous: each summand is `arcsin` of an argument linear in the (continuous)
subset scale. Mirror of `continuous_turningSum_update`. -/
private lemma continuous_turningSum_scaleOn [NeZero n] {κ ℓ : ZMod n → ℝ}
    (S : Finset (ZMod n)) :
    Continuous (fun t : ℝ => turningSum κ (scaleOn ℓ S t)) := by
  have hEq : (fun t : ℝ => turningSum κ (scaleOn ℓ S t))
      = fun t : ℝ => ∑ i : ZMod n,
        (Real.arcsin (κ i * (scaleOn ℓ S t (i - 1) / 2))
          + Real.arcsin (κ i * (scaleOn ℓ S t i / 2))) := by
    funext t
    simp only [turningSum, turningAngle, tK_zero]
  rw [hEq]
  refine continuous_finsetSum _ (fun i _ => ?_)
  refine (Real.continuous_arcsin.comp ?_).add (Real.continuous_arcsin.comp ?_)
  · exact continuous_const.mul ((continuous_scaleOn_apply S (i - 1)).div_const 2)
  · exact continuous_const.mul ((continuous_scaleOn_apply S i).div_const 2)

/-- **`lem:exists_scaleOn_turning_scale`.** Given `n ≥ 3` (`[NeZero n]`), a
positive profile `κ`, a positive base `ℓ`, an edge subset `S`, and
`0 < lo < hi` with the larger scale moderate-arc and
`turningSum (scaleOn ℓ S lo) < 2π ≤ turningSum (scaleOn ℓ S hi)`, there is
`t ∈ (lo, hi]` at which `scaleOn ℓ S t` is moderate-arc and turns by exactly
`2π`. Monotone IVT: `g t = turningSum κ (scaleOn ℓ S t)` is continuous
(`continuous_turningSum_scaleOn`) with `g lo < 2π ≤ g hi`, so
`intermediate_value_Icc` hits `2π`; the hitting scale exceeds `lo` (since
`g lo < 2π`) and is `≤ hi`, hence moderate-arc by `moderateArc_scaleOn_le`.
Mirror of `exists_edge_turning_scale`. -/
theorem exists_scaleOn_turning_scale [NeZero n] {κ ℓ : ZMod n → ℝ}
    (_hκ : ∀ i, 0 < κ i) (hℓ : ∀ e, 0 < ℓ e) (S : Finset (ZMod n))
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hMA : ModerateArc 0 κ (scaleOn ℓ S hi))
    (hlt : turningSum κ (scaleOn ℓ S lo) < 2 * Real.pi)
    (hge : 2 * Real.pi ≤ turningSum κ (scaleOn ℓ S hi)) :
    ∃ t ∈ Set.Ioc lo hi, ModerateArc 0 κ (scaleOn ℓ S t) ∧
      turningSum κ (scaleOn ℓ S t) = 2 * Real.pi := by
  set g : ℝ → ℝ := fun t => turningSum κ (scaleOn ℓ S t) with hg
  have hcont : Continuous g := continuous_turningSum_scaleOn S
  have hmem : 2 * Real.pi ∈ Set.Icc (g lo) (g hi) := ⟨hlt.le, hge⟩
  obtain ⟨t, htmem, hgt⟩ :=
    intermediate_value_Icc hlohi.le hcont.continuousOn hmem
  obtain ⟨hlot, hthi⟩ := htmem
  have hlot' : lo < t := by
    rcases hlot.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hgt
      exact absurd hgt (ne_of_lt hlt)
  refine ⟨t, ⟨hlot', hthi⟩,
    moderateArc_scaleOn_le hℓ (hlo.trans hlot') hthi hMA, hgt⟩

/-- **`lem:scaleOn_turning_scale_unique`.** Uniqueness of the subset-scaling
turning scale: two positive moderate-arc scales of a positive base over the
same nonempty subset with equal total turning coincide. Immediate from the
strict monotonicity of `turningSum_scaleOn_lt` via trichotomy. Mirror of
`edge_turning_scale_unique`. -/
theorem scaleOn_turning_scale_unique [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i, 0 < κ i) (hℓ : ∀ e, 0 < ℓ e) {S : Finset (ZMod n)}
    (hS : S.Nonempty) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hMA₁ : ModerateArc 0 κ (scaleOn ℓ S t₁))
    (hMA₂ : ModerateArc 0 κ (scaleOn ℓ S t₂))
    (hT : turningSum κ (scaleOn ℓ S t₁) = turningSum κ (scaleOn ℓ S t₂)) :
    t₁ = t₂ := by
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · exact absurd hT (ne_of_lt (turningSum_scaleOn_lt hκ hℓ hS ht₁ h hMA₂))
  · exact h
  · exact absurd hT.symm (ne_of_lt (turningSum_scaleOn_lt hκ hℓ hS ht₂ h hMA₁))

/-! ## Section 3 — the central-symmetry closing anchor (`sec:closure`)

The crux-independent `t = 0` anchor of the central-symmetry continuation (discrete
DeTurck–Gluck Prop 9.1): a centrally symmetric moderate-arc profile with total
turning `2π` closes. We phrase central symmetry as **half-period** `m = n/2`:
`n = 2m` and both `κ` and `ℓ` satisfy `x_{i+m} = x_i` (indices in `ZMod n`, so
`m` is the class `(m : ZMod n)`). The chain is: the turning angle is
half-periodic (`turningAngle_add_half`); hence a half-period block of turning
angles sums to `π` (`turningAngle_block_sum_half`); hence the heading advances by
exactly `π` over a half-period (`heading_add_half`); hence each opposite edge is
the negation of its mate and the development closes (`central_symmetry_closes`).

Blueprint: `blueprint/src/chapters/Gluck_Discrete_Closing.tex`, `sec:closure`. -/

/-- **`lem:turningangle_period`.** Under the half-period symmetry
`κ_{i+m} = κ_i`, `ℓ_{i+m} = ℓ_i` (all `i : ZMod n`, `n = 2m`, `m` the class
`(m : ZMod n)`), the Euclidean turning angle is invariant under the index shift
by `m`: `turningAngle 0 κ ℓ (i + m) = turningAngle 0 κ ℓ i`. Direct from the
turning-angle law (`K = 0`, `tK 0 = id`): both `κ` and `ℓ` are half-periodic,
and `(i + m) - 1 = (i - 1) + m` so the left edge length is unchanged too. -/
theorem turningAngle_add_half {m : ℕ} {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (m : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (m : ZMod n)) = ℓ i) (i : ZMod n) :
    turningAngle 0 κ ℓ (i + (m : ZMod n)) = turningAngle 0 κ ℓ i := by
  simp only [turningAngle, tK_zero]
  rw [hκ i, hℓ i,
    show (i + (m : ZMod n)) - 1 = (i - 1) + (m : ZMod n) from by ring, hℓ (i - 1)]

/-- **`lem:half_block_sum`.** Under the half-period symmetry and
`turningSum κ ℓ = 2π` (`n = 2m`), every half-period block of turning angles sums
to `π`: for all `a : ℕ`,
`∑_{i ∈ range m} turningAngle 0 κ ℓ ((a+i : ℕ) : ZMod n) = π`.
Two consecutive `m`-blocks starting at `a` are equal by `turningAngle_add_half`,
and their concatenation is a full period summing to `turningSum = 2π`
(`sum_range_natCast_add`); hence each block is `π`. -/
theorem turningAngle_block_sum_half [NeZero n] {m : ℕ} (hn : n = 2 * m)
    {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (m : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (m : ZMod n)) = ℓ i)
    (hT : turningSum κ ℓ = 2 * Real.pi) (a : ℕ) :
    ∑ i ∈ Finset.range m, turningAngle 0 κ ℓ ((a + i : ℕ) : ZMod n) = Real.pi := by
  have hnn : Finset.range n = Finset.range (m + m) := by rw [hn, two_mul]
  have hfull : ∑ k ∈ Finset.range n, turningAngle 0 κ ℓ ((a + k : ℕ) : ZMod n)
      = 2 * Real.pi := by
    rw [sum_range_natCast_add (turningAngle 0 κ ℓ) a]; exact hT
  rw [hnn, Finset.sum_range_add] at hfull
  have hsecond : ∑ k ∈ Finset.range m,
        turningAngle 0 κ ℓ ((a + (m + k) : ℕ) : ZMod n)
      = ∑ k ∈ Finset.range m, turningAngle 0 κ ℓ ((a + k : ℕ) : ZMod n) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hcast : ((a + (m + k) : ℕ) : ZMod n)
        = ((a + k : ℕ) : ZMod n) + (m : ZMod n) := by push_cast; ring
    rw [hcast, turningAngle_add_half hκ hℓ]
  rw [hsecond] at hfull
  linarith

/-- **`lem:heading_add_half`.** Under the half-period symmetry and
`turningSum κ ℓ = 2π` (`n = 2m`), the heading advances by exactly `π` over a
half-period: for all `j : ℕ`, `heading κ ℓ (j + m) = heading κ ℓ j + π`.
Split `range (j + m + 1) = range ((j+1) + m)` (`Finset.sum_range_add`); the
trailing `m`-block is `π` by `turningAngle_block_sum_half` at `a = j + 1`. -/
theorem heading_add_half [NeZero n] {m : ℕ} (hn : n = 2 * m) {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (m : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (m : ZMod n)) = ℓ i)
    (hT : turningSum κ ℓ = 2 * Real.pi) (j : ℕ) :
    heading κ ℓ (j + m) = heading κ ℓ j + Real.pi := by
  unfold heading
  rw [show j + m + 1 = (j + 1) + m from by ring,
    Finset.sum_range_add (fun i => turningAngle 0 κ ℓ (i : ZMod n)) (j + 1) m]
  congr 1
  exact turningAngle_block_sum_half hn hκ hℓ hT (j + 1)

/-- **`lem:central_symmetry_closes`.** The crux-independent central-symmetry
closing anchor (discrete DeTurck–Gluck Prop 9.1): a centrally symmetric
(half-period `n = 2m`, `κ_{i+m} = κ_i`, `ℓ_{i+m} = ℓ_i`) profile with total
turning `2π` closes, `closureGap κ ℓ = 0`. Split `range n = range (m+m)`; over
each half-period the edge length is unchanged and the heading advances by `π`
(`heading_add_half`), so `e^{i ψ_{j+m}} = -e^{i ψ_j}` (`Complex.exp_pi_mul_I`)
and the opposite edge vectors cancel term by term. -/
theorem central_symmetry_closes [NeZero n] {m : ℕ} (hn : n = 2 * m)
    {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (m : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (m : ZMod n)) = ℓ i)
    (hT : turningSum κ ℓ = 2 * Real.pi) :
    closureGap κ ℓ = 0 := by
  have hnn : Finset.range n = Finset.range (m + m) := by rw [hn, two_mul]
  simp only [closureGap, vertexR2]
  rw [hnn, Finset.sum_range_add, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  have hℓeq : ((m + j : ℕ) : ZMod n) = ((j : ℕ) : ZMod n) + (m : ZMod n) := by
    push_cast; ring
  have hheq : heading κ ℓ (m + j) = heading κ ℓ j + Real.pi := by
    rw [Nat.add_comm m j]; exact heading_add_half hn hκ hℓ hT j
  rw [hℓeq, hℓ, hheq]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

end Gluck.Discrete
