/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.GapCoords
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Carrier selection for strictly zigzag words

The selection half of the fully alternating all-even pair-carrier theorem
(§§1–3 of `research/notes/FULLY_ALTERNATING_ALL_EVEN_PAIR_CARRIER_THEOREM.md`, audited in
`notes/aristotle/ARISTOTLE_ZIGZAG_CHAIN_AUDIT_REPORT.md`, verdicts A1, B1–B3 all CONFIRMED):
for a strictly zigzag positive radius word, written in the interleaved form
`H_0, L_0, …, H_{m-1}, L_{m-1}` with `L_i < H_i` and `L_i < H_{i+1}`, *some*
consecutive-minimum carrier `H_i - L_i - H_{i+1} - L_{i+1} - H_{i+2}`
satisfies one of the external pipeline's two local certificates.

* `ZigzagPair`, `zigzagRatioA`, `zigzagRatioB`, `zigzagRatio_mem_Ioo` — the
  interleaved word and its carrier ratios `a_i = L_i/H_i`, `b_i = L_i/H_{i+1}`
  in `(0,1)`.
* `crossShared`, `crossOuter`, `arcsin_add_arcsin_lt_pi_div_two_iff`,
  `crossShared_lt_one_iff`, `crossOuter_lt_one_iff` — the cross sums
  `S_i = b_i² + a_{i+1}²`, `O_i = a_i² + b_{i+1}²`, and the quarter-turn
  criterion `arcsin u + arcsin v < π/2 ⟺ u² + v² < 1` showing they *are* the
  pipeline's angular conditions (audit verdict A1), not surrogates.
* `selectorT`, `selectorT_lt_selectorT_left`, `selectorT_lt_selectorT_right`
  — the selector `𝒯(u,v) = arctan (u√(1-v²)/(1+uv))`, strictly increasing in
  its first and strictly decreasing in its second argument on `(0,1)`.
* `mixed_monotone_disjunction`, `common_numerator_lt_iff`,
  `zigzagSelectorPlus`, `zigzagSelectorMinus`,
  `highNeighbour_of_selectorPlus_pos`, `highNeighbour_of_selectorMinus_pos` —
  a strict corner selector `K_i^± > 0` forces `H_i < H_{i+1}` or
  `H_{i+2} < H_{i+1}`.
* `exists_opposite_defects`, `exists_carrier_certificate` — the global
  pigeonhole through the in-tree `exists_of_high_neighbour` and the terminal
  selection theorem.

**Scope.** Nothing here realizes anything. The local certificates enter as
named hypotheses of `exists_carrier_certificate`.  The common-allocation
geometry and its ambient opening are connected in `ZigzagCommonBranch`; the
opposite-endpoint and conditioned-wall interfaces remain to be discharged.
Moreover the audit's verdict E1 refutes the extension of this architecture to
general strict-DFV words with monotone runs, so this chapter does not bear on
Tabachnikov's Problem 2.

-/

@[expose] public section

namespace Gluck.Discrete

open scoped Real

variable {m : ℕ}

/-! ## Zigzag pairs and their carrier ratios -/

/-- A **zigzag pair** on `ZMod m`: the interleaved presentation
`H_0, L_0, H_1, L_1, …` of a strictly zigzag positive word of even length
`2m` by its maxima `H` and minima `L`, i.e. `0 < L_i`, `L_i < H_i`,
`L_i < H_{i+1}` for all `i`. Positivity of `H` follows. Blueprint
`def:zc_pair`. -/
def ZigzagPair (H L : ZMod m → ℝ) : Prop :=
  ∀ i : ZMod m, 0 < L i ∧ L i < H i ∧ L i < H (i + 1)

/-- The first carrier ratio `a_i = L_i / H_i` of a zigzag pair. Blueprint
`def:zc_ratios`. -/
noncomputable def zigzagRatioA (H L : ZMod m → ℝ) (i : ZMod m) : ℝ :=
  L i / H i

/-- The second carrier ratio `b_i = L_i / H_{i+1}`: the `i`-th minimum over
the high it shares with the next carrier. Blueprint `def:zc_ratio_b`. -/
noncomputable def zigzagRatioB (H L : ZMod m → ℝ) (i : ZMod m) : ℝ :=
  L i / H (i + 1)

/-- For a zigzag pair both carrier ratios lie strictly between `0` and `1`.
Blueprint `lem:zc_ratio_mem`. -/
theorem zigzagRatio_mem_Ioo {H L : ZMod m → ℝ} (h : ZigzagPair H L)
    (i : ZMod m) :
    zigzagRatioA H L i ∈ Set.Ioo (0 : ℝ) 1 ∧
      zigzagRatioB H L i ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨hL, hHa, hHb⟩ := h i
  have hHa0 : 0 < H i := hL.trans hHa
  have hHb0 : 0 < H (i + 1) := hL.trans hHb
  exact ⟨⟨div_pos hL hHa0, (div_lt_one hHa0).2 hHa⟩,
    ⟨div_pos hL hHb0, (div_lt_one hHb0).2 hHb⟩⟩

/-- The **shared-high cross sum** `S_i = b_i² + a_{i+1}²`: the two ratios of
the carrier's two minima to the high `H_{i+1}` they share. Blueprint
`def:zc_cross`. -/
noncomputable def crossShared (H L : ZMod m → ℝ) (i : ZMod m) : ℝ :=
  zigzagRatioB H L i ^ 2 + zigzagRatioA H L (i + 1) ^ 2

/-- The **outer-high cross sum** `O_i = a_i² + b_{i+1}²`: the two ratios of
the carrier's two minima to its two outer highs `H_i`, `H_{i+2}`. Blueprint
`def:zc_cross_outer`. -/
noncomputable def crossOuter (H L : ZMod m → ℝ) (i : ZMod m) : ℝ :=
  zigzagRatioA H L i ^ 2 + zigzagRatioB H L (i + 1) ^ 2

/-- **The quarter-turn criterion** (audit verdict A1): for `0 ≤ u < 1` and
`0 ≤ v < 1`, `arcsin u + arcsin v < π/2 ↔ u² + v² < 1`. This is why the
cross sums `S_i`, `O_i` *are* the external pipeline's angular conditions and
not surrogates for them. Blueprint `lem:zc_arcsin_sum`. -/
theorem arcsin_add_arcsin_lt_pi_div_two_iff {u v : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (hv0 : 0 ≤ v) (_hv1 : v < 1) :
    Real.arcsin u + Real.arcsin v < π / 2 ↔ u ^ 2 + v ^ 2 < 1 := by
  have hstep : Real.arcsin u + Real.arcsin v < π / 2 ↔
      Real.arcsin u < Real.arcsin (Real.sqrt (1 - v ^ 2)) := by
    rw [← Real.arccos_eq_arcsin hv0, Real.arccos_eq_pi_div_two_sub_arcsin]
    constructor <;> intro h <;> linarith
  have hmem_u : u ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hu1.le⟩
  have hmem_s : Real.sqrt (1 - v ^ 2) ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_trans (by norm_num) (Real.sqrt_nonneg _),
      Real.sqrt_le_one.2 (by nlinarith [sq_nonneg v])⟩
  rw [hstep, Real.strictMonoOn_arcsin.lt_iff_lt hmem_u hmem_s,
    Real.lt_sqrt hu0]
  constructor <;> intro h <;> linarith

/-- The shared-high cross sum condition `S_i < 1` is exactly the pipeline's
angular condition `arcsin b_i + arcsin a_{i+1} < π/2`. Blueprint
`lem:zc_cross_shared_iff`. -/
theorem crossShared_lt_one_iff {H L : ZMod m → ℝ} (h : ZigzagPair H L)
    (i : ZMod m) :
    crossShared H L i < 1 ↔
      Real.arcsin (zigzagRatioB H L i) +
        Real.arcsin (zigzagRatioA H L (i + 1)) < π / 2 := by
  have hb := (zigzagRatio_mem_Ioo h i).2
  have ha := (zigzagRatio_mem_Ioo h (i + 1)).1
  simp only [crossShared]
  exact (arcsin_add_arcsin_lt_pi_div_two_iff hb.1.le hb.2 ha.1.le ha.2).symm

/-- The outer-high twin of `crossShared_lt_one_iff`: `O_i < 1` is exactly
`arcsin a_i + arcsin b_{i+1} < π/2`. Blueprint `lem:zc_cross_shared_iff`
(second clause). -/
theorem crossOuter_lt_one_iff {H L : ZMod m → ℝ} (h : ZigzagPair H L)
    (i : ZMod m) :
    crossOuter H L i < 1 ↔
      Real.arcsin (zigzagRatioA H L i) +
        Real.arcsin (zigzagRatioB H L (i + 1)) < π / 2 := by
  have ha := (zigzagRatio_mem_Ioo h i).1
  have hb := (zigzagRatio_mem_Ioo h (i + 1)).2
  simp only [crossOuter]
  exact (arcsin_add_arcsin_lt_pi_div_two_iff ha.1.le ha.2 hb.1.le hb.2).symm

/-! ## The corner selector and its monotonicity -/

/-- The **selector function** `𝒯(u, v) = arctan (u √(1 - v²) / (1 + uv))` of
the external pair-carrier note, eq. (8). Blueprint `def:zc_selector_T`. -/
noncomputable def selectorT (u v : ℝ) : ℝ :=
  Real.arctan (u * Real.sqrt (1 - v ^ 2) / (1 + u * v))

/-- `𝒯` is strictly increasing in its first argument on `(0,1)`. Blueprint
`lem:zc_T_mono_left`. -/
theorem selectorT_lt_selectorT_left {u₁ u₂ v : ℝ}
    (hu₁ : u₁ ∈ Set.Ioo (0 : ℝ) 1) (hu₂ : u₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hv : v ∈ Set.Ioo (0 : ℝ) 1) (h : u₁ < u₂) :
    selectorT u₁ v < selectorT u₂ v := by
  have hs : 0 < Real.sqrt (1 - v ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [hv.1, hv.2])
  have hd₁ : 0 < 1 + u₁ * v := add_pos one_pos (mul_pos hu₁.1 hv.1)
  have hd₂ : 0 < 1 + u₂ * v := add_pos one_pos (mul_pos hu₂.1 hv.1)
  apply Real.arctan_strictMono
  rw [div_lt_div_iff₀ hd₁ hd₂]
  nlinarith [mul_lt_mul_of_pos_right h hs,
    mul_pos (mul_pos hu₁.1 hu₂.1) (mul_pos hv.1 hs)]

/-- `𝒯` is strictly decreasing in its second argument on `(0,1)`: the
difference of the squared cleared numerators factors exactly as
`B² - A² = (v₂ - v₁) (2u(1 + v₁v₂) + (1 + u²)(v₁ + v₂))`. Blueprint
`lem:zc_T_anti_right`. -/
theorem selectorT_lt_selectorT_right {u v₁ v₂ : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) (hv₁ : v₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hv₂ : v₂ ∈ Set.Ioo (0 : ℝ) 1) (h : v₁ < v₂) :
    selectorT u v₂ < selectorT u v₁ := by
  have hq₁ : Real.sqrt (1 - v₁ ^ 2) ^ 2 = 1 - v₁ ^ 2 :=
    Real.sq_sqrt (by nlinarith [hv₁.1, hv₁.2])
  have hq₂ : Real.sqrt (1 - v₂ ^ 2) ^ 2 = 1 - v₂ ^ 2 :=
    Real.sq_sqrt (by nlinarith [hv₂.1, hv₂.2])
  have hd₁ : 0 < 1 + u * v₁ := add_pos one_pos (mul_pos hu.1 hv₁.1)
  have hd₂ : 0 < 1 + u * v₂ := add_pos one_pos (mul_pos hu.1 hv₂.1)
  apply Real.arctan_strictMono
  rw [div_lt_div_iff₀ hd₂ hd₁]
  have hAB : Real.sqrt (1 - v₂ ^ 2) * (1 + u * v₁) <
      Real.sqrt (1 - v₁ ^ 2) * (1 + u * v₂) := by
    have hB0 : 0 ≤ Real.sqrt (1 - v₁ ^ 2) * (1 + u * v₂) := by positivity
    refine lt_of_pow_lt_pow_left₀ 2 hB0 ?_
    have e₂ : (Real.sqrt (1 - v₂ ^ 2) * (1 + u * v₁)) ^ 2 =
        (1 - v₂ ^ 2) * (1 + u * v₁) ^ 2 := by rw [mul_pow, hq₂]
    have e₁ : (Real.sqrt (1 - v₁ ^ 2) * (1 + u * v₂)) ^ 2 =
        (1 - v₁ ^ 2) * (1 + u * v₂) ^ 2 := by rw [mul_pow, hq₁]
    rw [e₂, e₁]
    nlinarith [mul_pos (sub_pos.2 h)
      (show (0 : ℝ) < 2 * u * (1 + v₁ * v₂) + (1 + u ^ 2) * (v₁ + v₂) by
        nlinarith [hu.1, hv₁.1, hv₂.1, mul_pos hv₁.1 hv₂.1])]
  calc u * Real.sqrt (1 - v₂ ^ 2) * (1 + u * v₁)
      = u * (Real.sqrt (1 - v₂ ^ 2) * (1 + u * v₁)) := by ring
    _ < u * (Real.sqrt (1 - v₁ ^ 2) * (1 + u * v₂)) :=
        mul_lt_mul_of_pos_left hAB hu.1
    _ = u * Real.sqrt (1 - v₁ ^ 2) * (1 + u * v₂) := by ring

/-- **Mixed monotonicity excludes both weak comparisons** (`D`-restricted
adaptation of the audit's order-lemma kernel
`mixed_monotone_strict_disjunction`): if `f` is strictly increasing in its
first and strictly decreasing in its second argument on `D`, and
`f b d < f a c` with all four points in `D`, then `b < a` or `c < d`.
Blueprint `lem:zc_mixed_disjunction`. -/
theorem mixed_monotone_disjunction {D : Set ℝ} {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hinc : ∀ x ∈ D, ∀ y ∈ D, ∀ v ∈ D, x < y → f x v < f y v)
    (hdec : ∀ u ∈ D, ∀ x ∈ D, ∀ y ∈ D, x < y → f u y < f u x)
    (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hd : d ∈ D)
    (h : f b d < f a c) : b < a ∨ c < d := by
  by_contra hn
  obtain ⟨hab, hdc⟩ := not_or.1 hn
  replace hab : a ≤ b := not_lt.1 hab
  replace hdc : d ≤ c := not_lt.1 hdc
  have h₁ : f a c ≤ f b c := by
    rcases hab.eq_or_lt with rfl | hab'
    · exact le_rfl
    · exact (hinc a ha b hb c hc hab').le
  have h₂ : f b c ≤ f b d := by
    rcases hdc.eq_or_lt with rfl | hdc'
    · exact le_rfl
    · exact (hdec b hb d hd c hc hdc').le
  exact absurd h (not_lt.2 (h₁.trans h₂))

/-- **Common-numerator order translation** (audit order-lemma kernel
`common_numerator_ratio_gt_iff`): for `L, H₀, H₁ > 0`,
`L/H₁ < L/H₀ ↔ H₀ < H₁`. Blueprint `lem:zc_common_numerator`. -/
theorem common_numerator_lt_iff {L H₀ H₁ : ℝ} (hL : 0 < L) (hH₀ : 0 < H₀)
    (hH₁ : 0 < H₁) : L / H₁ < L / H₀ ↔ H₀ < H₁ := by
  rw [div_lt_div_iff₀ hH₁ hH₀]
  constructor <;> intro h <;> nlinarith

/-- The **balanced corner selector**
`K_i⁺ = 𝒯(a_i, a_{i+1}) - 𝒯(b_i, b_{i+1})` of carrier `i` (external note,
eq. (9)). Blueprint `def:zc_corner_selectors`. -/
noncomputable def zigzagSelectorPlus (H L : ZMod m → ℝ) (i : ZMod m) : ℝ :=
  selectorT (zigzagRatioA H L i) (zigzagRatioA H L (i + 1)) -
    selectorT (zigzagRatioB H L i) (zigzagRatioB H L (i + 1))

/-- The **reversed corner selector**
`K_i⁻ = 𝒯(b_{i+1}, b_i) - 𝒯(a_{i+1}, a_i)` of carrier `i` (external note,
eq. (10)). Blueprint `def:zc_corner_selector_minus`. -/
noncomputable def zigzagSelectorMinus (H L : ZMod m → ℝ) (i : ZMod m) : ℝ :=
  selectorT (zigzagRatioB H L (i + 1)) (zigzagRatioB H L i) -
    selectorT (zigzagRatioA H L (i + 1)) (zigzagRatioA H L i)

/-! ## From a strict corner selector to a high-neighbour inequality -/

/-- A strictly positive `K_i⁺` forces the shared high `H_{i+1}` strictly
above one of its neighbours: `H_i < H_{i+1}` or `H_{i+2} < H_{i+1}`
(external note, (14)–(15)). Blueprint `lem:zc_high_neighbour_plus`. -/
theorem highNeighbour_of_selectorPlus_pos {H L : ZMod m → ℝ}
    (hzz : ZigzagPair H L) {i : ZMod m}
    (hK : 0 < zigzagSelectorPlus H L i) :
    H i < H (i + 1) ∨ H (i + 2) < H (i + 1) := by
  obtain ⟨hLi, hHi, hHi1⟩ := hzz i
  obtain ⟨hLi1, -, hHi2⟩ := hzz (i + 1)
  have hHi0 : 0 < H i := hLi.trans hHi
  have hHi10 : 0 < H (i + 1) := hLi.trans hHi1
  have hHi20 : 0 < H (i + 1 + 1) := hLi1.trans hHi2
  have hmem := zigzagRatio_mem_Ioo hzz i
  have hmem1 := zigzagRatio_mem_Ioo hzz (i + 1)
  have hlt : selectorT (zigzagRatioB H L i) (zigzagRatioB H L (i + 1)) <
      selectorT (zigzagRatioA H L i) (zigzagRatioA H L (i + 1)) := by
    have := hK
    unfold zigzagSelectorPlus at this
    linarith
  have hdisj := mixed_monotone_disjunction (D := Set.Ioo (0 : ℝ) 1)
    (f := selectorT)
    (fun x hx y hy v hv hxy => selectorT_lt_selectorT_left hx hy hv hxy)
    (fun w hw x hx y hy hxy => selectorT_lt_selectorT_right hw hx hy hxy)
    hmem.1 hmem.2 hmem1.1 hmem1.2 hlt
  have h11 : i + 1 + 1 = i + 2 := by ring
  rcases hdisj with h1 | h1
  · left
    simp only [zigzagRatioA, zigzagRatioB] at h1
    exact (common_numerator_lt_iff hLi hHi0 hHi10).1 h1
  · right
    simp only [zigzagRatioA, zigzagRatioB] at h1
    have := (common_numerator_lt_iff hLi1 hHi20 hHi10).1 h1
    rwa [h11] at this

/-- A strictly positive `K_i⁻` forces the same high-neighbour disjunction
`H_i < H_{i+1}` or `H_{i+2} < H_{i+1}` (external note, (16)); the direction
of the comparison between the two minima has disappeared. Blueprint
`lem:zc_high_neighbour_minus`. -/
theorem highNeighbour_of_selectorMinus_pos {H L : ZMod m → ℝ}
    (hzz : ZigzagPair H L) {i : ZMod m}
    (hK : 0 < zigzagSelectorMinus H L i) :
    H i < H (i + 1) ∨ H (i + 2) < H (i + 1) := by
  obtain ⟨hLi, hHi, hHi1⟩ := hzz i
  obtain ⟨hLi1, -, hHi2⟩ := hzz (i + 1)
  have hHi0 : 0 < H i := hLi.trans hHi
  have hHi10 : 0 < H (i + 1) := hLi.trans hHi1
  have hHi20 : 0 < H (i + 1 + 1) := hLi1.trans hHi2
  have hmem := zigzagRatio_mem_Ioo hzz i
  have hmem1 := zigzagRatio_mem_Ioo hzz (i + 1)
  have hlt : selectorT (zigzagRatioA H L (i + 1)) (zigzagRatioA H L i) <
      selectorT (zigzagRatioB H L (i + 1)) (zigzagRatioB H L i) := by
    have := hK
    unfold zigzagSelectorMinus at this
    linarith
  have hdisj := mixed_monotone_disjunction (D := Set.Ioo (0 : ℝ) 1)
    (f := selectorT)
    (fun x hx y hy v hv hxy => selectorT_lt_selectorT_left hx hy hv hxy)
    (fun w hw x hx y hy hxy => selectorT_lt_selectorT_right hw hx hy hxy)
    hmem1.2 hmem1.1 hmem.2 hmem.1 hlt
  have h11 : i + 1 + 1 = i + 2 := by ring
  rcases hdisj with h1 | h1
  · right
    simp only [zigzagRatioA, zigzagRatioB] at h1
    have := (common_numerator_lt_iff hLi1 hHi20 hHi10).1 h1
    rwa [h11] at this
  · left
    simp only [zigzagRatioA, zigzagRatioB] at h1
    exact (common_numerator_lt_iff hLi hHi0 hHi10).1 h1

/-! ## The global step and the selection theorem -/

/-- **Some carrier has opposite endpoint defects** (external note, §3). If
the *conditioned wall estimate* holds — at every carrier `i` without the
property `Opp`, `L_i ≤ L_{i+1}` forces `0 < K_i⁺` and `L_{i+1} ≤ L_i` forces
`0 < K_i⁻` — then `Opp` holds somewhere.

The conditioned wall estimate is a HYPOTHESIS standing for the external
outer-heavy cyclic lemma (`research/notes/ALTERNATING_N6_OUTER_HEAVY_CYCLIC_LEMMA.md`
§§1–3, audited genuinely one-carrier local, verdicts B1–B3); it is
discharged nowhere in-tree. Blueprint `thm:zc_exists_opposite`. -/
theorem exists_opposite_defects [NeZero m] {H L : ZMod m → ℝ}
    (hzz : ZigzagPair H L) {Opp : ZMod m → Prop}
    (hwall : ∀ i, ¬Opp i →
      (L i ≤ L (i + 1) → 0 < zigzagSelectorPlus H L i) ∧
      (L (i + 1) ≤ L i → 0 < zigzagSelectorMinus H L i)) :
    ∃ i, Opp i := by
  refine exists_of_high_neighbour (H := H) fun i hOpp => ?_
  rcases le_total (L i) (L (i + 1)) with hle | hle
  · exact highNeighbour_of_selectorPlus_pos hzz ((hwall i hOpp).1 hle)
  · exact highNeighbour_of_selectorMinus_pos hzz ((hwall i hOpp).2 hle)

/-- **Carrier selection for a strictly zigzag word** (external note, §§1–3):
for a zigzag pair on `ZMod m` and predicates `Alloc`, `Opp` satisfying the
three interface hypotheses, some carrier satisfies `Alloc` or `Opp`.

The theorem is deliberately interface-shaped.  `halloc` is consumed by the
in-tree common-allocation construction in `ZigzagCommonBranch`;
`hendpoint` represents the shared-heavy / outer-light endpoint-sign branch;
and `hwall` is the conditioned wall estimate in the outer-heavy regime.  The
latter two interfaces remain open.  Moreover the audit's verdict E1 refutes
the extension of this architecture to general strict-DFV words with monotone
runs, so this selection theorem does not approach Tabachnikov's Problem 2.
Blueprint `thm:zc_exists_certificate`. -/
theorem exists_carrier_certificate [NeZero m] {H L : ZMod m → ℝ}
    (hzz : ZigzagPair H L) {Alloc Opp : ZMod m → Prop}
    (halloc : ∀ i, crossShared H L i < 1 → crossOuter H L i < 1 → Alloc i)
    (hendpoint : ∀ i, 1 ≤ crossShared H L i → crossOuter H L i < 1 → Opp i)
    (hwall : (∀ i, 1 ≤ crossOuter H L i) → ∀ i, ¬Opp i →
      (L i ≤ L (i + 1) → 0 < zigzagSelectorPlus H L i) ∧
      (L (i + 1) ≤ L i → 0 < zigzagSelectorMinus H L i)) :
    ∃ i, Alloc i ∨ Opp i := by
  by_cases hout : ∀ i, 1 ≤ crossOuter H L i
  · obtain ⟨i, hi⟩ := exists_opposite_defects hzz (hwall hout)
    exact ⟨i, Or.inr hi⟩
  · obtain ⟨i, hi⟩ := not_forall.1 hout
    have hi' : crossOuter H L i < 1 := not_le.1 hi
    by_cases hS : crossShared H L i < 1
    · exact ⟨i, Or.inl (halloc i hS hi')⟩
    · exact ⟨i, Or.inr (hendpoint i (not_lt.1 hS) hi')⟩

end Gluck.Discrete
