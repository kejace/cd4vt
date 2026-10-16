/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.BlockResultant
public import Gluck.Discrete.FourArcRectangle
public import Gluck.Discrete.GapCoords
public import Gluck.Discrete.MirandaPerturbation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Opening dormant edges: the analytic half of branch (iv)

Branch (iv) of the four-gap programme opens finitely many *dormant* edges —
edges of length `0` in a closure certificate configuration — to small positive
lengths, the active gaps absorbing the turn they consume.  This file proves the
analytic half of that step: the developed closure `closureGap` is continuous in
the LENGTH vector (unconditionally, with no positivity or `ModerateArc`
hypothesis — valid in particular at the degenerate vectors with vanishing
entries that the `ε = 0` slice consists of), and the assembly of that
continuity with either Miranda face signs or nonzero boundary winding into
conditional realizability statements.

**Honest ceiling.**  Nothing in this file constructs the opened family
`L (ε, z)` and nothing here produces the `ε = 0` face signs or winding.
`realizesR2_of_dormant_opening`, its winding analogue, and the support-form
corollary are therefore genuine implications with named hypotheses, NOT
realizations.  The continuity lemmas and the persistence of nonzero boundary
winding through every sufficiently small positive slice are unconditional
once their displayed family hypotheses are supplied.

Blueprint: `chapters/Gluck_Discrete_DormantOpening.tex`.
-/

@[expose] public section

open Real Complex

namespace Gluck.Discrete

variable {n : ℕ}

/-! ## The developed closure is continuous in the lengths -/

/-- `lem:do_heading_continuous` — every heading `ψ_j` is continuous as a
function of the full length vector `ℓ : ZMod n → ℝ`.  Unconditional: no
positivity, no `ModerateArc`; `arcsin` is globally continuous. -/
theorem continuous_heading_lengths (κ : ZMod n → ℝ) (j : ℕ) :
    Continuous fun ℓ : ZMod n → ℝ => heading κ ℓ j := by
  unfold heading turningAngle
  simp only [tK_zero]
  refine continuous_finsetSum _ fun m _ => Continuous.add ?_ ?_ <;>
    exact Real.continuous_arcsin.comp
      (continuous_const.mul ((continuous_apply _).div_const 2))

/-- `lem:do_closure_continuous` — the developed closure `E(ℓ) = closureGap κ ℓ`
is continuous as a function of the full length vector `ℓ : ZMod n → ℝ`.

**Unconditional** — no positivity, no `ModerateArc`; valid at length vectors
with zero entries, in particular on the degenerate `ε = 0` slice of a
dormant-opening family.  This is the file's reusable payload: the project
previously re-derived this continuity ad hoc wherever it was needed. -/
theorem continuous_closureGap_lengths (κ : ZMod n → ℝ) :
    Continuous fun ℓ : ZMod n → ℝ => closureGap κ ℓ := by
  unfold closureGap vertexR2
  refine continuous_finsetSum _ fun j _ =>
    (Complex.continuous_ofReal.comp (continuous_apply _)).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_heading_lengths κ j)).mul
          continuous_const))

/-! ## Smoothness inside the strict walls -/

/-- Inside its two strict arcsine walls, a turning angle is `C¹` in the
entire length vector. -/
theorem contDiffAt_turningAngle_lengths [NeZero n]
    {κ ℓ : ZMod n → ℝ} (i : ZMod n)
    (hw1 : |κ i * (ℓ (i - 1) / 2)| < 1)
    (hw2 : |κ i * (ℓ i / 2)| < 1) :
    ContDiffAt ℝ 1 (fun L : ZMod n → ℝ => turningAngle 0 κ L i) ℓ := by
  rw [abs_lt] at hw1 hw2
  have hlin1 : ContDiffAt ℝ 1
      (fun L : ZMod n → ℝ => κ i * (L (i - 1) / 2)) ℓ := by
    fun_prop
  have hlin2 : ContDiffAt ℝ 1
      (fun L : ZMod n → ℝ => κ i * (L i / 2)) ℓ := by
    fun_prop
  have ha1 := (Real.contDiffAt_arcsin (ne_of_gt hw1.1)
    (ne_of_lt hw1.2)).comp ℓ hlin1
  have ha2 := (Real.contDiffAt_arcsin (ne_of_gt hw2.1)
    (ne_of_lt hw2.2)).comp ℓ hlin2
  simpa only [Function.comp_apply, turningAngle, tK_zero] using ha1.add ha2

/-- Inside its strict arcsine walls, a turning angle is `C¹` jointly in the
curvature and length vectors. -/
theorem contDiffAt_turningAngle_profile_lengths [NeZero n]
    {κ ℓ : ZMod n → ℝ} (i : ZMod n)
    (hw1 : |κ i * (ℓ (i - 1) / 2)| < 1)
    (hw2 : |κ i * (ℓ i / 2)| < 1) :
    ContDiffAt ℝ 1
      (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) ↦
        turningAngle 0 p.1 p.2 i) (κ, ℓ) := by
  rw [abs_lt] at hw1 hw2
  have hlin1 : ContDiffAt ℝ 1
      (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) ↦
        p.1 i * (p.2 (i - 1) / 2)) (κ, ℓ) := by
    fun_prop
  have hlin2 : ContDiffAt ℝ 1
      (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) ↦
        p.1 i * (p.2 i / 2)) (κ, ℓ) := by
    fun_prop
  have ha1 := (Real.contDiffAt_arcsin (ne_of_gt hw1.1)
    (ne_of_lt hw1.2)).comp (κ, ℓ) hlin1
  have ha2 := (Real.contDiffAt_arcsin (ne_of_gt hw2.1)
    (ne_of_lt hw2.2)).comp (κ, ℓ) hlin2
  simpa only [Function.comp_apply, turningAngle, tK_zero] using ha1.add ha2

/-- If all preceding turning angles lie inside their strict walls, their
cumulative heading is `C¹` in the length vector. -/
theorem contDiffAt_heading_lengths [NeZero n]
    {κ ℓ : ZMod n → ℝ} (j : ℕ)
    (hw : ∀ m ∈ Finset.range (j + 1),
      |κ (m : ZMod n) * (ℓ ((m : ZMod n) - 1) / 2)| < 1 ∧
        |κ (m : ZMod n) * (ℓ (m : ZMod n) / 2)| < 1) :
    ContDiffAt ℝ 1 (fun L : ZMod n → ℝ => heading κ L j) ℓ := by
  unfold heading
  exact ContDiffAt.sum fun m hm =>
    contDiffAt_turningAngle_lengths (m : ZMod n) (hw m hm).1 (hw m hm).2

/-- Throughout the strict arcsine walls, the total turning is `C¹` in the
full length vector. -/
theorem contDiffAt_turningSum_lengths [NeZero n]
    {κ ℓ : ZMod n → ℝ}
    (hw : ∀ i : ZMod n,
      |κ i * (ℓ (i - 1) / 2)| < 1 ∧ |κ i * (ℓ i / 2)| < 1) :
    ContDiffAt ℝ 1 (fun L : ZMod n → ℝ => turningSum κ L) ℓ := by
  unfold turningSum
  exact ContDiffAt.sum fun i _ =>
    contDiffAt_turningAngle_lengths i (hw i).1 (hw i).2

/-- Throughout the strict arcsine walls, the developed closure is `C¹` in
the full length vector. -/
theorem contDiffAt_closureGap_lengths [NeZero n]
    {κ ℓ : ZMod n → ℝ}
    (hw : ∀ i : ZMod n,
      |κ i * (ℓ (i - 1) / 2)| < 1 ∧ |κ i * (ℓ i / 2)| < 1) :
    ContDiffAt ℝ 1 (fun L : ZMod n → ℝ => closureGap κ L) ℓ := by
  unfold closureGap vertexR2
  apply ContDiffAt.sum
  intro j hj
  have hheading : ContDiffAt ℝ 1
      (fun L : ZMod n → ℝ => heading κ L j) ℓ := by
    apply contDiffAt_heading_lengths j
    intro m hm
    exact hw (m : ZMod n)
  have hlength : ContDiffAt ℝ 1
      (fun L : ZMod n → ℝ => (L (j : ZMod n) : ℂ)) ℓ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp ℓ (by fun_prop)
  have hheadingC : ContDiffAt ℝ 1
      (fun L : ZMod n → ℝ => (heading κ L j : ℂ)) ℓ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp ℓ hheading
  exact hlength.mul ((hheadingC.mul contDiffAt_const).cexp)

/-! ## The opening theorem -/

/-- A jointly continuous two-component certificate map with strict compact
face signs can open a dormant length family.  The map need not be a fixed
complex rotation of the closure: it is enough that each of its positive-slice
zeros forces the literal developed closure to vanish.  This accommodates the
`|I|`-corrected map used by a balanced seam rectangle. -/
theorem realizesR2_of_dormant_opening_via_map [NeZero n]
    {kappa : ZMod n → ℝ} (hn : 3 ≤ n) (hkappa : ∀ i, 0 < kappa i)
    {a₁ a₂ b₁ b₂ ε₀ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (hε₀ : 0 < ε₀) {L : ℝ → ℝ × ℝ → ZMod n → ℝ}
    {Φ : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    (hΦ : ContinuousOn Φ
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)))
    (hleft : ∀ y ∈ Set.Icc b₁ b₂, (Φ (0, (a₁, y))).1 < 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂, 0 < (Φ (0, (a₂, y))).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂, (Φ (0, (x, b₁))).2 < 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂, 0 < (Φ (0, (x, b₂))).2)
    (hzero : ∀ ε ∈ Set.Ioo 0 ε₀, ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
      Φ (ε, z) = 0 → closureGap kappa (L ε z) = 0)
    (hadm : ∀ ε ∈ Set.Ioo 0 ε₀, ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
      ∀ e : ZMod n, 0 < L ε z e ∧ L ε z e < edgeCap kappa e)
    (hsum : ∀ ε ∈ Set.Ioo 0 ε₀, ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
      ∑ e : ZMod n, gapAngle kappa (L ε z) e = 2 * Real.pi) :
    RealizesR2 kappa := by
  obtain ⟨ε₁, hε₁0, hε₁ε₀, hall⟩ :=
    exists_pos_forall_lt_exists_zero ha hb hε₀ hΦ hleft hright hbot htop
  have hmem : ε₁ / 2 ∈ Set.Ioo 0 ε₁ :=
    ⟨half_pos hε₁0, half_lt_self hε₁0⟩
  have hmem₀ : ε₁ / 2 ∈ Set.Ioo 0 ε₀ :=
    ⟨half_pos hε₁0, (half_lt_self hε₁0).trans_le hε₁ε₀⟩
  obtain ⟨z, hz, hΦzero⟩ := hall _ hmem
  exact realizesR2_of_gapData hn hkappa (hadm _ hmem₀ z hz)
    (hzero _ hmem₀ z hz hΦzero) (hsum _ hmem₀ z hz)

/-- `thm:do_opening` — opening dormant edges produces a closure: if the length
family `L` is jointly continuous on `[0, ε₀] × Q` and the rotated developed
closure of the `ε = 0` slice has strict Poincaré–Miranda face signs on the
rectangle `Q`, then for every sufficiently small `ε > 0` some `z ∈ Q` has
vanishing closure gap `closureGap κ (L ε z) = 0`.

Conditional: the face signs and the family are HYPOTHESES — nothing here
constructs them. -/
theorem exists_pos_forall_lt_closureGap_eq_zero (κ : ZMod n → ℝ)
    {a₁ a₂ b₁ b₂ ε₀ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hε₀ : 0 < ε₀)
    {L : ℝ → ℝ × ℝ → ZMod n → ℝ}
    (hL : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => L p.1 p.2)
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)))
    {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hu0 : ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, u z ≠ 0)
    (hleft : ∀ y ∈ Set.Icc b₁ b₂,
      (rotateBy (u (a₁, y)) (closureGap κ (L 0 (a₁, y)))).1 < 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂,
      0 < (rotateBy (u (a₂, y)) (closureGap κ (L 0 (a₂, y)))).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂,
      (rotateBy (u (x, b₁)) (closureGap κ (L 0 (x, b₁)))).2 < 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂,
      0 < (rotateBy (u (x, b₂)) (closureGap κ (L 0 (x, b₂)))).2) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Set.Ioo 0 ε₁,
      ∃ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, closureGap κ (L ε z) = 0 := by
  have hΦ : ContinuousOn
      (fun p : ℝ × (ℝ × ℝ) => rotateBy (u p.2) (closureGap κ (L p.1 p.2)))
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)) := by
    refine continuous_rotateBy.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
    · exact hu.comp continuous_snd.continuousOn fun p hp => hp.2
    · exact (continuous_closureGap_lengths κ).comp_continuousOn hL
  obtain ⟨ε₁, hε₁0, hε₁ε₀, hall⟩ :=
    exists_pos_forall_lt_exists_zero ha hb hε₀ hΦ hleft hright hbot htop
  refine ⟨ε₁, hε₁0, hε₁ε₀, fun ε hε => ?_⟩
  obtain ⟨z, hz, hΦ0⟩ := hall ε hε
  exact ⟨z, hz, (rotateBy_eq_zero_iff (hu0 z hz) _).1 hΦ0⟩

/-- `thm:do_opening_realizes` — opening dormant edges realizes the profile:
in the situation of `exists_pos_forall_lt_closureGap_eq_zero`, if in addition
`3 ≤ n`, `κ` is positive, and for every `ε ∈ (0, ε₀)` and `z ∈ Q` the lengths
`L ε z` lie strictly inside the edge caps with total gap `2π`, then
`RealizesR2 κ`.

Conditional: every geometric input — the family, the face signs, the
admissibility, the gap sum — is a named HYPOTHESIS; this theorem is an
implication, not a realization. -/
theorem realizesR2_of_dormant_opening [NeZero n] {κ : ZMod n → ℝ} (hn : 3 ≤ n)
    (hκ : ∀ i, 0 < κ i)
    {a₁ a₂ b₁ b₂ ε₀ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hε₀ : 0 < ε₀)
    {L : ℝ → ℝ × ℝ → ZMod n → ℝ}
    (hL : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => L p.1 p.2)
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)))
    {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hu0 : ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, u z ≠ 0)
    (hleft : ∀ y ∈ Set.Icc b₁ b₂,
      (rotateBy (u (a₁, y)) (closureGap κ (L 0 (a₁, y)))).1 < 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂,
      0 < (rotateBy (u (a₂, y)) (closureGap κ (L 0 (a₂, y)))).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂,
      (rotateBy (u (x, b₁)) (closureGap κ (L 0 (x, b₁)))).2 < 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂,
      0 < (rotateBy (u (x, b₂)) (closureGap κ (L 0 (x, b₂)))).2)
    (hadm : ∀ ε ∈ Set.Ioo 0 ε₀, ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
      ∀ e : ZMod n, 0 < L ε z e ∧ L ε z e < edgeCap κ e)
    (hsum : ∀ ε ∈ Set.Ioo 0 ε₀, ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
      ∑ e : ZMod n, gapAngle κ (L ε z) e = 2 * Real.pi) :
    RealizesR2 κ := by
  obtain ⟨ε₁, hε₁0, hε₁ε₀, hall⟩ :=
    exists_pos_forall_lt_closureGap_eq_zero κ ha hb hε₀ hL hu hu0
      hleft hright hbot htop
  have hmem : ε₁ / 2 ∈ Set.Ioo 0 ε₁ := ⟨half_pos hε₁0, half_lt_self hε₁0⟩
  have hmem0 : ε₁ / 2 ∈ Set.Ioo 0 ε₀ :=
    ⟨half_pos hε₁0, lt_of_lt_of_le (half_lt_self hε₁0) hε₁ε₀⟩
  obtain ⟨z, hz, hE⟩ := hall _ hmem
  exact realizesR2_of_gapData hn hκ (hadm _ hmem0 z hz) hE (hsum _ hmem0 z hz)

/-- Nonzero winding of a compactified closure loop persists after every
sufficiently small positive dormant opening. -/
theorem exists_pos_forall_lt_closureGap_eq_zero_of_boundary_winding
    (κ : ZMod n → ℝ)
    {a₁ a₂ b₁ b₂ ε₀ : ℝ} (ha : a₁ < a₂) (hb : b₁ < b₂) (hε₀ : 0 < ε₀)
    {L : ℝ → ℝ × ℝ → ZMod n → ℝ}
    (hL : ContinuousOn (fun p : ℝ × (ℝ × ℝ) ↦ L p.1 p.2)
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)))
    (gamma : C(unitInterval, ℂ)) (hgamma : ∀ t, gamma t ≠ 0)
    (hgammaEq : ∀ t, gamma t =
      closureGap κ (L 0 (fourArcRectangleBoundary a₁ a₂ b₁ b₂ t)))
    (hwind : Gluck.windingNumberC gamma hgamma ≠ 0) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Set.Ioo 0 ε₁,
      ∃ z ∈ Set.Ioo a₁ a₂ ×ˢ Set.Ioo b₁ b₂,
        closureGap κ (L ε z) = 0 := by
  have hΦ : ContinuousOn
      (fun p : ℝ × (ℝ × ℝ) ↦ closureGap κ (L p.1 p.2))
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)) :=
    (continuous_closureGap_lengths κ).comp_continuousOn hL
  exact exists_pos_forall_lt_exists_zero_of_fourArcRectangleBoundary_winding
    ha hb hε₀ hΦ gamma hgamma hgammaEq hwind

/-- A winding-certified dormant-opening family with strict caps and total
gap `2π` realizes its positive curvature profile. -/
theorem realizesR2_of_dormant_opening_winding [NeZero n] {κ : ZMod n → ℝ}
    (hn : 3 ≤ n) (hκ : ∀ i, 0 < κ i)
    {a₁ a₂ b₁ b₂ ε₀ : ℝ} (ha : a₁ < a₂) (hb : b₁ < b₂) (hε₀ : 0 < ε₀)
    {L : ℝ → ℝ × ℝ → ZMod n → ℝ}
    (hL : ContinuousOn (fun p : ℝ × (ℝ × ℝ) ↦ L p.1 p.2)
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)))
    (gamma : C(unitInterval, ℂ)) (hgamma : ∀ t, gamma t ≠ 0)
    (hgammaEq : ∀ t, gamma t =
      closureGap κ (L 0 (fourArcRectangleBoundary a₁ a₂ b₁ b₂ t)))
    (hwind : Gluck.windingNumberC gamma hgamma ≠ 0)
    (hadm : ∀ ε ∈ Set.Ioo 0 ε₀,
      ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
        ∀ e : ZMod n, 0 < L ε z e ∧ L ε z e < edgeCap κ e)
    (hsum : ∀ ε ∈ Set.Ioo 0 ε₀,
      ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
        ∑ e : ZMod n, gapAngle κ (L ε z) e = 2 * Real.pi) :
    RealizesR2 κ := by
  obtain ⟨ε₁, hε₁, hε₁ε₀, hall⟩ :=
    exists_pos_forall_lt_closureGap_eq_zero_of_boundary_winding κ ha hb hε₀
      hL gamma hgamma hgammaEq hwind
  have hmem : ε₁ / 2 ∈ Set.Ioo 0 ε₁ := ⟨half_pos hε₁, half_lt_self hε₁⟩
  have hmem0 : ε₁ / 2 ∈ Set.Ioo 0 ε₀ :=
    ⟨half_pos hε₁, (half_lt_self hε₁).trans_le hε₁ε₀⟩
  obtain ⟨z, hz, hE⟩ := hall _ hmem
  have hzClosed : z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂ :=
    ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  exact realizesR2_of_gapData hn hκ (hadm _ hmem0 z hzClosed) hE
    (hsum _ hmem0 z hzClosed)

/-! ## The interface with branch (i) -/

/-- `thm:do_opening_support` — opening a four-edge-supported degeneracy: the
face signs may be stated on the sum over an arbitrary support set `S` alone,
because `L 0 z` vanishes off `S` and `closureGap_eq_sum_of_subset` collapses
the closure to that sum.  The intended application is `|S| = 4` — branch (i)
hands its certificate over as a statement about a quadrilateral, and no
`n`-gon closure has to be evaluated to check it.

Conditional, exactly as `realizesR2_of_dormant_opening`. -/
theorem realizesR2_of_dormant_opening_of_support [NeZero n] {κ : ZMod n → ℝ}
    (hn : 3 ≤ n) (hκ : ∀ i, 0 < κ i)
    {a₁ a₂ b₁ b₂ ε₀ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hε₀ : 0 < ε₀)
    {L : ℝ → ℝ × ℝ → ZMod n → ℝ}
    (hL : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => L p.1 p.2)
      (Set.Icc 0 ε₀ ×ˢ (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)))
    {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hu0 : ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, u z ≠ 0)
    {S : Finset ℕ} (hS : S ⊆ Finset.range n)
    (hsupp : ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
      ∀ j ∈ Finset.range n, j ∉ S → L 0 z (j : ZMod n) = 0)
    (hleft : ∀ y ∈ Set.Icc b₁ b₂,
      (rotateBy (u (a₁, y)) (∑ j ∈ S, (L 0 (a₁, y) (j : ZMod n) : ℂ) *
        Complex.exp ((heading κ (L 0 (a₁, y)) j : ℂ) * Complex.I))).1 < 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂,
      0 < (rotateBy (u (a₂, y)) (∑ j ∈ S, (L 0 (a₂, y) (j : ZMod n) : ℂ) *
        Complex.exp ((heading κ (L 0 (a₂, y)) j : ℂ) * Complex.I))).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂,
      (rotateBy (u (x, b₁)) (∑ j ∈ S, (L 0 (x, b₁) (j : ZMod n) : ℂ) *
        Complex.exp ((heading κ (L 0 (x, b₁)) j : ℂ) * Complex.I))).2 < 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂,
      0 < (rotateBy (u (x, b₂)) (∑ j ∈ S, (L 0 (x, b₂) (j : ZMod n) : ℂ) *
        Complex.exp ((heading κ (L 0 (x, b₂)) j : ℂ) * Complex.I))).2)
    (hadm : ∀ ε ∈ Set.Ioo 0 ε₀, ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
      ∀ e : ZMod n, 0 < L ε z e ∧ L ε z e < edgeCap κ e)
    (hsum : ∀ ε ∈ Set.Ioo 0 ε₀, ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
      ∑ e : ZMod n, gapAngle κ (L ε z) e = 2 * Real.pi) :
    RealizesR2 κ := by
  have hrw : ∀ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂,
      (∑ j ∈ S, (L 0 z (j : ZMod n) : ℂ) *
        Complex.exp ((heading κ (L 0 z) j : ℂ) * Complex.I))
        = closureGap κ (L 0 z) := fun z hz =>
    (closureGap_eq_sum_of_subset κ (L 0 z) hS (hsupp z hz)).symm
  refine realizesR2_of_dormant_opening hn hκ ha hb hε₀ hL hu hu0
    (fun y hy => ?_) (fun y hy => ?_) (fun x hx => ?_) (fun x hx => ?_)
    hadm hsum
  · rw [← hrw (a₁, y) ⟨⟨le_refl _, ha⟩, hy⟩]; exact hleft y hy
  · rw [← hrw (a₂, y) ⟨⟨ha, le_refl _⟩, hy⟩]; exact hright y hy
  · rw [← hrw (x, b₁) ⟨hx, ⟨le_refl _, hb⟩⟩]; exact hbot x hx
  · rw [← hrw (x, b₂) ⟨hx, ⟨hb, le_refl _⟩⟩]; exact htop x hx

end Gluck.Discrete
