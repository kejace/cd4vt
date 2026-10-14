/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.CollaredConverse
import Gluck.Discrete.DormantOpening
import Gluck.Discrete.WallCrossing

/-!
# Opening a regular dormant anchor

A closed moderate-arc anchor may have zero ambient edge lengths while all of
its arcsine walls remain strict.  This file turns the ordinary submersion
criterion at such an anchor into a strict-positive realization.

The first consumer accepts an explicit kernel direction pointing into every
collapsed length face.  The second accepts the more convenient equivalent
input used by sparse four-edge anchors: every controller target can be
produced by a correction supported away from the collapsed coordinates.
-/

namespace Gluck.Discrete

open Set

variable {n : ℕ}

private lemma endpoint_wall_of_nonneg_lt_edgeCap [NeZero n]
    {kappa : ZMod n → ℝ} {e : ZMod n} {c t : ℝ}
    (hc : 0 < c) (hle : c ≤ max (kappa e) (kappa (e + 1)))
    (ht : 0 ≤ t) (hcap : t < edgeCap kappa e) :
    c * (t / 2) < 1 := by
  have hM : 0 < max (kappa e) (kappa (e + 1)) := hc.trans_le hle
  rw [edgeCap, lt_div_iff₀ hM] at hcap
  nlinarith [mul_le_mul_of_nonneg_right hle ht]

/-- Nonnegative sub-cap lengths satisfy every strict arcsine wall. -/
lemma strict_arc_walls_of_nonneg_lt_edgeCap [NeZero n]
    {kappa ell : ZMod n → ℝ} (hkappa : ∀ i, 0 < kappa i)
    (hell : ∀ i, 0 ≤ ell i ∧ ell i < edgeCap kappa i) :
    ∀ i, |kappa i * (ell (i - 1) / 2)| < 1 ∧
      |kappa i * (ell i / 2)| < 1 := by
  intro i
  constructor
  · have hraw := endpoint_wall_of_nonneg_lt_edgeCap
      (e := i - 1) (c := kappa i) (t := ell (i - 1)) (hkappa i)
      (by simp) (hell (i - 1)).1 (hell (i - 1)).2
    rw [abs_of_nonneg
      (mul_nonneg (hkappa i).le (div_nonneg (hell (i - 1)).1 zero_le_two))]
    exact hraw
  · have hraw := endpoint_wall_of_nonneg_lt_edgeCap
      (e := i) (c := kappa i) (t := ell i) (hkappa i)
      (le_max_left (kappa i) (kappa (i + 1))) (hell i).1 (hell i).2
    rw [abs_of_nonneg
      (mul_nonneg (hkappa i).le (div_nonneg (hell i).1 zero_le_two))]
    exact hraw

/-- The length-only closure controller is strictly differentiable even at
zero length coordinates, provided every arcsine wall is strict. -/
theorem lengthClosureMap_hasStrictFDerivAt_of_nonneg_lt_edgeCap [NeZero n]
    {kappa ell : ZMod n → ℝ} (hkappa : ∀ i, 0 < kappa i)
    (hell : ∀ i, 0 ≤ ell i ∧ ell i < edgeCap kappa i) :
    HasStrictFDerivAt (fun L ↦ closureMapR3 (kappa, L))
      (fderiv ℝ (fun L ↦ closureMapR3 (kappa, L)) ell) ell := by
  have hw := strict_arc_walls_of_nonneg_lt_edgeCap hkappa hell
  have hE := contDiffAt_closureGap_lengths (κ := kappa) (ℓ := ell) hw
  have hT := contDiffAt_turningSum_lengths (κ := kappa) (ℓ := ell) hw
  have hC : ContDiffAt ℝ 1
      (fun L ↦ (closureGap kappa L, turningSum kappa L - 2 * Real.pi)) ell :=
    hE.prodMk (hT.sub contDiffAt_const)
  simpa only [closureMapR3] using hC.hasStrictFDerivAt one_ne_zero

/-- A regular closed anchor with nonnegative lengths opens whenever one
kernel direction points into every collapsed length face. -/
theorem realizesR2_of_regular_dormant_anchor [NeZero n]
    (hn : 3 ≤ n) {kappa ell v : ZMod n → ℝ}
    (hkappa : ∀ i, 0 < kappa i)
    (hell : ∀ i, 0 ≤ ell i ∧ ell i < edgeCap kappa i)
    (hzero : closureMapR3 (kappa, ell) = 0)
    {F' : (ZMod n → ℝ) →L[ℝ] ℂ × ℝ}
    (hF : HasStrictFDerivAt (fun L ↦ closureMapR3 (kappa, L)) F' ell)
    (hsurj : F'.range = ⊤) (hv : v ∈ F'.ker)
    (hvinward : ∀ i, ell i = 0 → 0 < v i) :
    RealizesR2 kappa := by
  let w : (ZMod n ⊕ ZMod n) → (ZMod n → ℝ) → ℝ
    | Sum.inl i => fun L ↦ L i
    | Sum.inr i => fun L ↦ edgeCap kappa i - L i
  let w' : (ZMod n ⊕ ZMod n) → (ZMod n → ℝ) →L[ℝ] ℝ
    | Sum.inl i => ContinuousLinearMap.proj i
    | Sum.inr i => -(ContinuousLinearMap.proj i)
  have hw : ∀ i, HasFDerivAt (w i) (w' i) ell := by
    intro i
    rcases i with i | i
    · simpa [w, w'] using (hasFDerivAt_apply (𝕜 := ℝ) i ell)
    · simpa [w, w'] using
        (hasFDerivAt_apply (𝕜 := ℝ) i ell).const_sub (edgeCap kappa i)
  have hclosed : ∀ i, 0 ≤ w i ell := by
    intro i
    rcases i with i | i
    · simpa [w] using (hell i).1
    · simpa [w] using (sub_nonneg.mpr (hell i).2.le)
  have hinward : ∀ i, w i ell = 0 → 0 < w' i v := by
    intro i
    rcases i with i | i
    · intro hi
      simpa [w, w'] using hvinward i (by simpa [w] using hi)
    · intro hi
      have hi' : edgeCap kappa i - ell i = 0 := by simpa [w] using hi
      exfalso
      linarith [(hell i).2]
  obtain ⟨gamma, eps, heps, _hgamma0, _hgammaDeriv, _hgammaLim, hgood⟩ :=
    regularActiveWallZero_entersStrictDomain
      (ι := ZMod n ⊕ ZMod n) hF hsurj hv hw hclosed hinward
  have ht : eps / 2 ∈ Set.Ioo (0 : ℝ) eps :=
    ⟨half_pos heps, half_lt_self heps⟩
  obtain ⟨hlevel, hwalls⟩ := hgood (eps / 2) ht.1 ht.2
  have hbounds : ∀ i, 0 < gamma (eps / 2) i ∧
      gamma (eps / 2) i < edgeCap kappa i := by
    intro i
    have hlow := hwalls (Sum.inl i)
    have hupp := hwalls (Sum.inr i)
    change 0 < gamma (eps / 2) i at hlow
    change 0 < edgeCap kappa i - gamma (eps / 2) i at hupp
    exact ⟨hlow, sub_pos.mp hupp⟩
  have hMA : ModerateArc 0 kappa (gamma (eps / 2)) :=
    (moderateArc_zero_iff_edge hkappa).2 hbounds
  have hzero' : closureMapR3 (kappa, gamma (eps / 2)) = 0 :=
    hlevel.trans hzero
  exact realizesR2_of_mem_collarInterior hn
    (S := Set.univ) ⟨Set.mem_univ _, hMA, hzero'⟩ hkappa

/-- It is enough that the controller derivative be surjective using
corrections supported away from the collapsed length coordinates. -/
theorem realizesR2_of_regular_dormant_anchor_of_active_surj [NeZero n]
    (hn : 3 ≤ n) {kappa ell : ZMod n → ℝ}
    (hkappa : ∀ i, 0 < kappa i)
    (hell : ∀ i, 0 ≤ ell i ∧ ell i < edgeCap kappa i)
    (hzero : closureMapR3 (kappa, ell) = 0)
    (hactive : ∀ y : ℂ × ℝ, ∃ b : ZMod n → ℝ,
      fderiv ℝ (fun L ↦ closureMapR3 (kappa, L)) ell b = y ∧
        ∀ i, ell i = 0 → b i = 0) :
    RealizesR2 kappa := by
  let F' := fderiv ℝ (fun L ↦ closureMapR3 (kappa, L)) ell
  have hF : HasStrictFDerivAt (fun L ↦ closureMapR3 (kappa, L)) F' ell :=
    lengthClosureMap_hasStrictFDerivAt_of_nonneg_lt_edgeCap hkappa hell
  have hsurj : F'.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨b, hb, _⟩ := hactive y
    exact ⟨b, by simpa [F'] using hb⟩
  let d : ZMod n → ℝ := fun i ↦ if ell i = 0 then 1 else 0
  obtain ⟨b, hb, hbzero⟩ := hactive (-F' d)
  let v := d + b
  have hv : v ∈ F'.ker := by
    rw [LinearMap.mem_ker]
    change F' (d + b) = 0
    rw [map_add]
    change F' b = -F' d at hb
    rw [hb, add_neg_cancel]
  have hvinward : ∀ i, ell i = 0 → 0 < v i := by
    intro i hi
    change 0 < d i + b i
    rw [show d i = 1 by simp [d, hi], hbzero i hi]
    norm_num
  exact realizesR2_of_regular_dormant_anchor hn hkappa hell hzero
    hF hsurj hv hvinward

end Gluck.Discrete
