/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import ForMathlib.Analysis.Complex.PoincareMiranda

/-!
# Poincaré–Miranda under perturbation

The topological half of branch (iv) of the four-gap chain — the *dormant-gap
opening lemma* — isolated from all geometry.  Blueprint chapter:
`chap:discrete_miranda_perturbation`.

**This file is unconditional planar topology.**  It mentions no curvature, no
gap, no closure and no certificate.  Its content: strict Poincaré–Miranda
face signs on a compact rectangle become a uniform margin
(`exists_face_margin`); a uniform margin survives a uniform perturbation
(`exists_zero_of_close_to_miranda`); and in a jointly continuous
one-parameter family the strict face signs of the `ε = 0` slice persist to
all sufficiently small `ε > 0`, producing zeros there
(`exists_pos_forall_lt_exists_zero`).  A trivial dictionary (`rotateBy`,
`rotateBy_eq_zero_iff`, `continuous_rotateBy`) passes between a single
complex closure with a nonvanishing rotating multiplier and the two real
Miranda components.

**Honest ceiling.**  This file does NOT produce the `ε = 0` face signs — it
consumes them.  Those signs are branch (i)'s output
(`exists_two_block_closure` and the balanced two-block assembly), available
there only conditionally on the external endpoint-defect certificate; the
opened family itself is branch (iv)'s remaining geometric work
(`chap:discrete_dormant_opening`).  Nothing in this file is a realization
theorem.
-/

@[expose] public section

open Set

namespace Gluck.Discrete

/-! ## Rotating a complex number into Miranda components -/

/-- `def:mp_rotate` — the two real Miranda components of a complex closure
`E`, read in the frame rotated by the multiplier `u`. -/
def rotateBy (u E : ℂ) : ℝ × ℝ := ((u * E).re, (u * E).im)

/-- `lem:mp_rotate_zero_iff` — for a nonvanishing multiplier, a rotated zero
is a zero. -/
theorem rotateBy_eq_zero_iff {u : ℂ} (hu : u ≠ 0) (E : ℂ) :
    rotateBy u E = 0 ↔ E = 0 := by
  constructor
  · intro h
    simp only [rotateBy, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h
    have huE : u * E = 0 := Complex.ext (by simpa using h.1) (by simpa using h.2)
    exact (mul_eq_zero.mp huE).resolve_left hu
  · intro h
    simp [rotateBy, h]

/-- `lem:mp_rotate_continuous` — joint continuity of the rotated
components. -/
theorem continuous_rotateBy : Continuous fun p : ℂ × ℂ => rotateBy p.1 p.2 :=
  (Complex.continuous_re.comp (continuous_fst.mul continuous_snd)).prodMk
    (Complex.continuous_im.comp (continuous_fst.mul continuous_snd))

/-! ## Strict face signs become a uniform margin -/

/-- A continuous function strictly negative on a nonempty compact interval is
bounded away from zero: `g ≤ -δ` for some `δ > 0`. -/
private lemma exists_neg_margin {c d : ℝ} (hcd : c ≤ d) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc c d)) (hneg : ∀ y ∈ Set.Icc c d, g y < 0) :
    ∃ δ > 0, ∀ y ∈ Set.Icc c d, g y ≤ -δ := by
  obtain ⟨y₀, hy₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hcd) hg
  refine ⟨-g y₀, by linarith [hneg y₀ hy₀], fun y hy => ?_⟩
  rw [neg_neg]
  exact hmax hy

/-- A continuous function strictly positive on a nonempty compact interval is
bounded away from zero: `δ ≤ g` for some `δ > 0`. -/
private lemma exists_pos_margin {c d : ℝ} (hcd : c ≤ d) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc c d)) (hpos : ∀ y ∈ Set.Icc c d, 0 < g y) :
    ∃ δ > 0, ∀ y ∈ Set.Icc c d, δ ≤ g y := by
  obtain ⟨y₀, hy₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hcd) hg
  exact ⟨g y₀, hpos y₀ hy₀, fun y hy => hmin hy⟩

/-- `lem:mp_face_margin` — strict Poincaré–Miranda face signs of a continuous
map on a compact rectangle admit a uniform margin `δ > 0`. -/
theorem exists_face_margin {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    {F : ℝ × ℝ → ℝ × ℝ}
    (hF : ContinuousOn F (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hleft : ∀ y ∈ Set.Icc b₁ b₂, (F (a₁, y)).1 < 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂, 0 < (F (a₂, y)).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂, (F (x, b₁)).2 < 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂, 0 < (F (x, b₂)).2) :
    ∃ δ > 0, (∀ y ∈ Set.Icc b₁ b₂, (F (a₁, y)).1 ≤ -δ) ∧
      (∀ y ∈ Set.Icc b₁ b₂, δ ≤ (F (a₂, y)).1) ∧
      (∀ x ∈ Set.Icc a₁ a₂, (F (x, b₁)).2 ≤ -δ) ∧
      (∀ x ∈ Set.Icc a₁ a₂, δ ≤ (F (x, b₂)).2) := by
  have hL : ContinuousOn (fun y => (F (a₁, y)).1) (Set.Icc b₁ b₂) :=
    continuous_fst.comp_continuousOn
      (hF.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun y hy => Set.mk_mem_prod (Set.left_mem_Icc.2 ha) hy))
  have hR : ContinuousOn (fun y => (F (a₂, y)).1) (Set.Icc b₁ b₂) :=
    continuous_fst.comp_continuousOn
      (hF.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun y hy => Set.mk_mem_prod (Set.right_mem_Icc.2 ha) hy))
  have hB : ContinuousOn (fun x => (F (x, b₁)).2) (Set.Icc a₁ a₂) :=
    continuous_snd.comp_continuousOn
      (hF.comp ((continuous_id.prodMk continuous_const).continuousOn)
        (fun x hx => Set.mk_mem_prod hx (Set.left_mem_Icc.2 hb)))
  have hT : ContinuousOn (fun x => (F (x, b₂)).2) (Set.Icc a₁ a₂) :=
    continuous_snd.comp_continuousOn
      (hF.comp ((continuous_id.prodMk continuous_const).continuousOn)
        (fun x hx => Set.mk_mem_prod hx (Set.right_mem_Icc.2 hb)))
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_neg_margin hb hL hleft
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_pos_margin hb hR hright
  obtain ⟨δ₃, hδ₃, h₃⟩ := exists_neg_margin ha hB hbot
  obtain ⟨δ₄, hδ₄, h₄⟩ := exists_pos_margin ha hT htop
  have hm₁ : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₁ :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hm₂ : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₂ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hm₃ : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₃ :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hm₄ : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₄ :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨min (min δ₁ δ₂) (min δ₃ δ₄), lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄),
    fun y hy => ?_, fun y hy => le_trans hm₂ (h₂ y hy),
    fun x hx => ?_, fun x hx => le_trans hm₄ (h₄ x hx)⟩
  · linarith [h₁ y hy]
  · linarith [h₃ x hx]

/-- The two coordinatewise distances are bounded by the product (sup) distance
on `ℝ × ℝ`. -/
private lemma abs_sub_lt_of_dist_lt {q r : ℝ × ℝ} {δ : ℝ} (h : dist q r < δ) :
    |q.1 - r.1| < δ ∧ |q.2 - r.2| < δ := by
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at h
  exact h

/-- `thm:mp_stable` — Poincaré–Miranda is stable under uniform perturbation:
a map with face margins `δ` forces a zero of every continuous map uniformly
`δ`-close to it on the rectangle.  Only the margins of `F` enter — `F` itself
need not be continuous. -/
theorem exists_zero_of_close_to_miranda {a₁ a₂ b₁ b₂ δ : ℝ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) {F G : ℝ × ℝ → ℝ × ℝ}
    (hmargL : ∀ y ∈ Set.Icc b₁ b₂, (F (a₁, y)).1 ≤ -δ)
    (hmargR : ∀ y ∈ Set.Icc b₁ b₂, δ ≤ (F (a₂, y)).1)
    (hmargB : ∀ x ∈ Set.Icc a₁ a₂, (F (x, b₁)).2 ≤ -δ)
    (hmargT : ∀ x ∈ Set.Icc a₁ a₂, δ ≤ (F (x, b₂)).2)
    (hG : ContinuousOn G (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂))
    (hclose : ∀ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, dist (G p) (F p) < δ) :
    ∃ p ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, G p = 0 := by
  have haL : a₁ ∈ Set.Icc a₁ a₂ := Set.left_mem_Icc.2 ha
  have haR : a₂ ∈ Set.Icc a₁ a₂ := Set.right_mem_Icc.2 ha
  have hbB : b₁ ∈ Set.Icc b₁ b₂ := Set.left_mem_Icc.2 hb
  have hbT : b₂ ∈ Set.Icc b₁ b₂ := Set.right_mem_Icc.2 hb
  refine poincare_miranda ha hb G hG ?_ ?_ ?_ ?_
  · intro y hy
    have h1 := (abs_sub_lt_of_dist_lt
      (hclose (a₁, y) (Set.mk_mem_prod haL hy))).1
    have h2 := abs_lt.1 h1
    linarith [hmargL y hy]
  · intro y hy
    have h1 := (abs_sub_lt_of_dist_lt
      (hclose (a₂, y) (Set.mk_mem_prod haR hy))).1
    have h2 := abs_lt.1 h1
    linarith [hmargR y hy]
  · intro x hx
    have h1 := (abs_sub_lt_of_dist_lt
      (hclose (x, b₁) (Set.mk_mem_prod hx hbB))).2
    have h2 := abs_lt.1 h1
    linarith [hmargB x hx]
  · intro x hx
    have h1 := (abs_sub_lt_of_dist_lt
      (hclose (x, b₂) (Set.mk_mem_prod hx hbT))).2
    have h2 := abs_lt.1 h1
    linarith [hmargT x hx]

/-! ## The parameterized form -/

/-- The bad-set argument on one face: a jointly continuous scalar family on
`[0,ε₀] × [c,d]` whose `ε = 0` slice is strictly negative stays strictly
negative for all `ε` below some `η > 0`.  The bad set
`S = {(ε,y) : 0 ≤ g (ε,y)}` is compact; if nonempty, its `ε`-minimum is
positive by the slice sign. -/
private lemma exists_eta_of_slice_neg {ε₀ c d : ℝ} (hε₀ : 0 < ε₀) (_hcd : c ≤ d)
    {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc 0 ε₀ ×ˢ Set.Icc c d))
    (h0 : ∀ y ∈ Set.Icc c d, g (0, y) < 0) :
    ∃ η, 0 < η ∧ η ≤ ε₀ ∧
      ∀ ε ∈ Set.Ico 0 η, ∀ y ∈ Set.Icc c d, g (ε, y) < 0 := by
  set K : Set (ℝ × ℝ) := Set.Icc 0 ε₀ ×ˢ Set.Icc c d with hKdef
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  set S : Set (ℝ × ℝ) := K ∩ g ⁻¹' Set.Ici 0 with hSdef
  have hSclosed : IsClosed S :=
    hg.preimage_isClosed_of_isClosed hKcomp.isClosed isClosed_Ici
  have hScomp : IsCompact S :=
    hKcomp.of_isClosed_subset hSclosed Set.inter_subset_left
  rcases S.eq_empty_or_nonempty with hemp | hne
  · refine ⟨ε₀, hε₀, le_refl _, fun ε hε y hy => ?_⟩
    by_contra hcon
    have hmem : (ε, y) ∈ S :=
      ⟨Set.mk_mem_prod ⟨hε.1, hε.2.le⟩ hy, not_lt.1 hcon⟩
    rw [hemp] at hmem
    exact hmem
  · obtain ⟨p₀, hp₀S, hmin⟩ :=
      hScomp.exists_isMinOn hne continuous_fst.continuousOn
    have hp₀K : p₀ ∈ K := hp₀S.1
    have hp₀g : 0 ≤ g p₀ := hp₀S.2
    have hη_pos : 0 < p₀.1 := by
      rcases eq_or_lt_of_le hp₀K.1.1 with h | h
      · exfalso
        have hpe : p₀ = ((0 : ℝ), p₀.2) := Prod.ext h.symm rfl
        rw [hpe] at hp₀g
        linarith [h0 p₀.2 hp₀K.2]
      · exact h
    refine ⟨p₀.1, hη_pos, hp₀K.1.2, fun ε hε y hy => ?_⟩
    by_contra hcon
    have hmem : (ε, y) ∈ S :=
      ⟨Set.mk_mem_prod ⟨hε.1, hε.2.le.trans hp₀K.1.2⟩ hy, not_lt.1 hcon⟩
    exact absurd (hmin hmem) (not_le.2 hε.2)

/-- `thm:mp_family` — opening a degenerate Miranda rectangle: if a jointly
continuous family `Φ` on `[0,ε₀] × Q` has strict Poincaré–Miranda face signs
at the slice `ε = 0`, then there is `ε₁ ∈ (0, ε₀]` such that `Φ (ε, ·)` has a
zero in `Q` for every `ε ∈ (0, ε₁)`.  Unconditional; the number of parameters
being opened is invisible here. -/
theorem exists_pos_forall_lt_exists_zero {a₁ a₂ b₁ b₂ ε₀ : ℝ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hε₀ : 0 < ε₀)
    {Φ : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    (hΦ : ContinuousOn Φ (Set.Icc 0 ε₀ ×ˢ (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂)))
    (hleft : ∀ y ∈ Set.Icc b₁ b₂, (Φ (0, (a₁, y))).1 < 0)
    (hright : ∀ y ∈ Set.Icc b₁ b₂, 0 < (Φ (0, (a₂, y))).1)
    (hbot : ∀ x ∈ Set.Icc a₁ a₂, (Φ (0, (x, b₁))).2 < 0)
    (htop : ∀ x ∈ Set.Icc a₁ a₂, 0 < (Φ (0, (x, b₂))).2) :
    ∃ ε₁, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ ε ∈ Set.Ioo 0 ε₁,
      ∃ z ∈ Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂, Φ (ε, z) = 0 := by
  -- the four face families, jointly continuous on `[0,ε₀] ×ˢ` the face
  have hgL : ContinuousOn (fun p : ℝ × ℝ => (Φ (p.1, (a₁, p.2))).1)
      (Set.Icc 0 ε₀ ×ˢ Set.Icc b₁ b₂) :=
    continuous_fst.comp_continuousOn
      (hΦ.comp ((continuous_fst.prodMk
          (continuous_const.prodMk continuous_snd)).continuousOn)
        (fun p hp => Set.mk_mem_prod hp.1
          (Set.mk_mem_prod (Set.left_mem_Icc.2 ha) hp.2)))
  have hgR : ContinuousOn (fun p : ℝ × ℝ => (Φ (p.1, (a₂, p.2))).1)
      (Set.Icc 0 ε₀ ×ˢ Set.Icc b₁ b₂) :=
    continuous_fst.comp_continuousOn
      (hΦ.comp ((continuous_fst.prodMk
          (continuous_const.prodMk continuous_snd)).continuousOn)
        (fun p hp => Set.mk_mem_prod hp.1
          (Set.mk_mem_prod (Set.right_mem_Icc.2 ha) hp.2)))
  have hgB : ContinuousOn (fun p : ℝ × ℝ => (Φ (p.1, (p.2, b₁))).2)
      (Set.Icc 0 ε₀ ×ˢ Set.Icc a₁ a₂) :=
    continuous_snd.comp_continuousOn
      (hΦ.comp ((continuous_fst.prodMk
          (continuous_snd.prodMk continuous_const)).continuousOn)
        (fun p hp => Set.mk_mem_prod hp.1
          (Set.mk_mem_prod hp.2 (Set.left_mem_Icc.2 hb))))
  have hgT : ContinuousOn (fun p : ℝ × ℝ => (Φ (p.1, (p.2, b₂))).2)
      (Set.Icc 0 ε₀ ×ˢ Set.Icc a₁ a₂) :=
    continuous_snd.comp_continuousOn
      (hΦ.comp ((continuous_fst.prodMk
          (continuous_snd.prodMk continuous_const)).continuousOn)
        (fun p hp => Set.mk_mem_prod hp.1
          (Set.mk_mem_prod hp.2 (Set.right_mem_Icc.2 hb))))
  obtain ⟨η₁, hη₁pos, hη₁le, hη₁⟩ :=
    exists_eta_of_slice_neg hε₀ hb hgL hleft
  obtain ⟨η₂, hη₂pos, hη₂le, hη₂⟩ :=
    exists_eta_of_slice_neg hε₀ hb hgR.neg
      (fun y hy => neg_lt_zero.2 (hright y hy))
  obtain ⟨η₃, hη₃pos, hη₃le, hη₃⟩ :=
    exists_eta_of_slice_neg hε₀ ha hgB hbot
  obtain ⟨η₄, hη₄pos, hη₄le, hη₄⟩ :=
    exists_eta_of_slice_neg hε₀ ha hgT.neg
      (fun x hx => neg_lt_zero.2 (htop x hx))
  have hm₁ : min (min η₁ η₂) (min η₃ η₄) ≤ η₁ :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hm₂ : min (min η₁ η₂) (min η₃ η₄) ≤ η₂ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hm₃ : min (min η₁ η₂) (min η₃ η₄) ≤ η₃ :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hm₄ : min (min η₁ η₂) (min η₃ η₄) ≤ η₄ :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨min (min η₁ η₂) (min η₃ η₄),
    lt_min (lt_min hη₁pos hη₂pos) (lt_min hη₃pos hη₄pos),
    hm₁.trans hη₁le, fun ε hε => ?_⟩
  have hεIcc : ε ∈ Set.Icc 0 ε₀ :=
    ⟨hε.1.le, (hε.2.le.trans hm₁).trans hη₁le⟩
  have hΦε : ContinuousOn (fun z : ℝ × ℝ => Φ (ε, z))
      (Set.Icc a₁ a₂ ×ˢ Set.Icc b₁ b₂) :=
    hΦ.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun z hz => Set.mk_mem_prod hεIcc hz)
  refine poincare_miranda ha hb _ hΦε ?_ ?_ ?_ ?_
  · intro y hy
    exact (hη₁ ε ⟨hε.1.le, lt_of_lt_of_le hε.2 hm₁⟩ y hy).le
  · intro y hy
    have := hη₂ ε ⟨hε.1.le, lt_of_lt_of_le hε.2 hm₂⟩ y hy
    change -((Φ (ε, a₂, y)).1) < 0 at this
    linarith
  · intro x hx
    exact (hη₃ ε ⟨hε.1.le, lt_of_lt_of_le hε.2 hm₃⟩ x hx).le
  · intro x hx
    have := hη₄ ε ⟨hε.1.le, lt_of_lt_of_le hε.2 hm₄⟩ x hx
    change -((Φ (ε, x, b₂)).2) < 0 at this
    linarith

end Gluck.Discrete
