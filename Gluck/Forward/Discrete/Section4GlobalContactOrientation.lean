/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4ContactReversal

/-!
# Global orientation of enclosing-disk contacts

This module proves the polygonal Jordan–Umlaufsatz bridge needed in
Dahlberg’s Section 4. For a simple polygon contained in a positive-radius
disk, every boundary contact with a nonzero local turn has the same strict
orientation. The proof is source-free: a Hopf secant grid computes the total
principal edge turn as `2π` or `-2π` at any exposed disk contact, and the
single global sum rules out opposite signs at two contacts.
-/

namespace Gluck.Forward

open Gluck.Discrete

private theorem principalTurn_mem_Ioo_of_cross_pos_global {u w : ℂ}
    (hcross : 0 < crossR2 0 u w) :
    principalTurn u w ∈ Set.Ioo 0 Real.pi := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    simp [crossR2] at hcross
  have him : 0 < (w / u).im := by
    rw [Complex.div_im]
    have hnum : 0 < w.im * u.re - w.re * u.im := by
      have h := hcross
      simp [crossR2] at h
      nlinarith
    rw [← sub_div]
    exact div_pos hnum (Complex.normSq_pos.mpr hu0)
  refine ⟨?_, ?_⟩
  · unfold principalTurn
    refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le) ?_
    intro hzero
    exact (ne_of_gt him) ((Complex.arg_eq_zero_iff.mp hzero.symm).2)
  · unfold principalTurn
    exact Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt him))

private theorem principalTurn_add_split_of_cross_pos_global {u w : ℂ}
    (hcross : 0 < crossR2 0 u w) :
    principalTurn u w =
      principalTurn u (u + w) + principalTurn (u + w) w := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    simp [crossR2] at hcross
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    simp [crossR2] at hcross
  have huw0 : u + w ≠ 0 := by
    intro h
    have hwu : w = -u := by linear_combination h
    rw [hwu] at hcross
    simp [crossR2] at hcross
    nlinarith
  have hcross₁ : 0 < crossR2 0 u (u + w) := by
    have heq : crossR2 0 u (u + w) = crossR2 0 u w := by
      unfold crossR2
      simp
      ring
    rw [heq]
    exact hcross
  have hcross₂ : 0 < crossR2 0 (u + w) w := by
    have heq : crossR2 0 (u + w) w = crossR2 0 u w := by
      unfold crossR2
      simp
      ring
    rw [heq]
    exact hcross
  have hα := principalTurn_mem_Ioo_of_cross_pos_global hcross
  have hβ := principalTurn_mem_Ioo_of_cross_pos_global hcross₁
  have hγ := principalTurn_mem_Ioo_of_cross_pos_global hcross₂
  have hprod : ((u + w) / u) * (w / (u + w)) = w / u := by
    field_simp
  have hcoe : (principalTurn u w : Real.Angle) =
      ((principalTurn u (u + w) + principalTurn (u + w) w : ℝ) :
        Real.Angle) := by
    unfold principalTurn
    rw [← hprod, Complex.arg_mul_coe_angle
      (div_ne_zero huw0 hu0) (div_ne_zero hw0 huw0)]
    simp [Real.Angle.coe_add]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hcoe
  have hklo : (-1 : ℝ) < (k : ℝ) := by
    by_contra h
    have hle : (k : ℝ) ≤ -1 := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hle
      (show 0 ≤ 2 * Real.pi by positivity)
    linarith [hα.1, hα.2, hβ.1, hβ.2, hγ.1, hγ.2]
  have hkhi : (k : ℝ) < 1 := by
    by_contra h
    have hle : (1 : ℝ) ≤ k := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hle
      (show 0 ≤ 2 * Real.pi by positivity)
    linarith [hα.1, hα.2, hβ.1, hβ.2, hγ.1, hγ.2]
  have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
  have hkhi' : k < (1 : ℤ) := by exact_mod_cast hkhi
  have hkzero : k = 0 := by omega
  rw [hkzero, Int.cast_zero, mul_zero] at hk
  linarith

private theorem principalTurn_swap_eq_neg_of_cross_ne_zero {u w : ℂ}
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hcross : crossR2 0 u w ≠ 0) :
    principalTurn w u = -principalTurn u w := by
  have hratio : u / w = (w / u)⁻¹ := by
    field_simp
  have hargNe : (w / u).arg ≠ Real.pi := by
    intro harg
    have him : (w / u).im = 0 := (Complex.arg_eq_pi_iff.mp harg).2
    rw [Complex.div_im] at him
    have hnorm : Complex.normSq u ≠ 0 := (Complex.normSq_pos.mpr hu0).ne'
    field_simp [hnorm] at him
    apply hcross
    unfold crossR2
    simp only [sub_zero]
    nlinarith
  unfold principalTurn
  rw [hratio, Complex.arg_inv, if_neg hargNe]

private theorem principalTurn_add_split_of_cross_neg_global {u w : ℂ}
    (hcross : crossR2 0 u w < 0) :
    principalTurn u w =
      principalTurn u (u + w) + principalTurn (u + w) w := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    simp [crossR2] at hcross
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    simp [crossR2] at hcross
  have huw0 : u + w ≠ 0 := by
    intro h
    have hwu : w = -u := by linear_combination h
    rw [hwu] at hcross
    simp [crossR2] at hcross
    nlinarith
  have hswap : 0 < crossR2 0 w u := by
    unfold crossR2 at hcross ⊢
    simp only [sub_zero] at hcross ⊢
    linarith
  have hsplit := principalTurn_add_split_of_cross_pos_global hswap
  have hsplit' : principalTurn w u =
      principalTurn w (u + w) + principalTurn (u + w) u := by
    simpa [add_comm] using hsplit
  have hmain := principalTurn_swap_eq_neg_of_cross_ne_zero
    hw0 hu0 (by linarith : crossR2 0 w u ≠ 0)
  have hleftCross : crossR2 0 w (u + w) ≠ 0 := by
    unfold crossR2 at hswap ⊢
    simp only [Complex.add_re, Complex.add_im, sub_zero] at hswap ⊢
    nlinarith
  have hleft := principalTurn_swap_eq_neg_of_cross_ne_zero
    hw0 huw0 hleftCross
  have hrightCross : crossR2 0 (u + w) u ≠ 0 := by
    unfold crossR2 at hswap ⊢
    simp only [Complex.add_re, Complex.add_im, sub_zero] at hswap ⊢
    nlinarith
  have hright := principalTurn_swap_eq_neg_of_cross_ne_zero
    huw0 hu0 hrightCross
  linarith

private theorem principalTurn_add_split_of_cross_eq_zero_global {u w : ℂ}
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) (huw0 : u + w ≠ 0)
    (hcross : crossR2 0 u w = 0) :
    principalTurn u w =
      principalTurn u (u + w) + principalTurn (u + w) w := by
  let q : ℂ := w / u
  have hq0 : q ≠ 0 := div_ne_zero hw0 hu0
  have hqim : q.im = 0 := by
    dsimp [q]
    rw [Complex.div_im]
    have hnorm : Complex.normSq u ≠ 0 := (Complex.normSq_pos.mpr hu0).ne'
    field_simp [hnorm]
    unfold crossR2 at hcross
    simp only [sub_zero] at hcross
    nlinarith
  have hqEq : q = (q.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hqim
  have hwq : w = q * u := by
    dsimp [q]
    field_simp
  have h1q0 : (1 : ℂ) + q ≠ 0 := by
    intro h
    apply huw0
    rw [hwq]
    calc
      u + q * u = ((1 : ℂ) + q) * u := by ring
      _ = 0 := by rw [h, zero_mul]
  have hα : w / u = q := rfl
  have hβ : (u + w) / u = 1 + q := by
    rw [hwq]
    field_simp
  have hγ : w / (u + w) = q / (1 + q) := by
    rw [hwq]
    field_simp
  have hqre0 : q.re ≠ 0 := by
    intro h
    apply hq0
    apply Complex.ext
    · simpa using h
    · simpa using hqim
  have h1qre0 : 1 + q.re ≠ 0 := by
    intro h
    apply h1q0
    rw [hqEq]
    apply Complex.ext <;> simp [h]
  unfold principalTurn
  rw [hα, hβ, hγ, hqEq]
  have hone : (1 : ℂ) + (q.re : ℂ) = ((1 + q.re : ℝ) : ℂ) := by
    norm_num
  have hdiv : (q.re : ℂ) / ((1 + q.re : ℝ) : ℂ) =
      ((q.re / (1 + q.re) : ℝ) : ℂ) := by
    norm_num
  rw [hone, hdiv]
  rcases lt_or_gt_of_ne hqre0 with hqneg | hqpos
  · rw [Complex.arg_ofReal_of_neg hqneg]
    rcases lt_or_gt_of_ne h1qre0 with h1neg | h1pos
    · have hratio : 0 ≤ q.re / (1 + q.re) :=
        (div_pos_of_neg_of_neg hqneg h1neg).le
      rw [Complex.arg_ofReal_of_neg h1neg,
        Complex.arg_ofReal_of_nonneg hratio]
      ring
    · have hratio : q.re / (1 + q.re) < 0 :=
        div_neg_of_neg_of_pos hqneg h1pos
      rw [Complex.arg_ofReal_of_nonneg h1pos.le,
        Complex.arg_ofReal_of_neg hratio]
      ring
  · have h1pos : 0 ≤ 1 + q.re := by linarith
    have hratio : 0 ≤ q.re / (1 + q.re) := by positivity
    rw [Complex.arg_ofReal_of_nonneg hqpos.le,
      Complex.arg_ofReal_of_nonneg h1pos,
      Complex.arg_ofReal_of_nonneg hratio]
    ring

private theorem principalTurn_add_split_global {u w : ℂ}
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) (huw0 : u + w ≠ 0) :
    principalTurn u w =
      principalTurn u (u + w) + principalTurn (u + w) w := by
  rcases lt_trichotomy (crossR2 0 u w) 0 with hneg | hzero | hpos
  · exact principalTurn_add_split_of_cross_neg_global hneg
  · exact principalTurn_add_split_of_cross_eq_zero_global
      hu0 hw0 huw0 hzero
  · exact principalTurn_add_split_of_cross_pos_global hpos

private theorem principalTurn_cyclicEdge_split_global {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) (i : ℕ) :
    principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1)) =
      principalTurn (cyclicSecant v i (i + 1))
          (cyclicSecant v i (i + 2)) +
        principalTurn (cyclicSecant v i (i + 2))
          (cyclicSecant v (i + 1) (i + 2)) := by
  have hu0 : cyclicEdge v i ≠ 0 := cyclicEdge_ne_zero hsimple i
  have hw0 : cyclicEdge v (i + 1) ≠ 0 := cyclicEdge_ne_zero hsimple (i + 1)
  have hsum : cyclicEdge v i + cyclicEdge v (i + 1) =
      cyclicSecant v i (i + 2) := by
    unfold cyclicEdge cyclicSecant
    rw [show i + 1 + 1 = i + 2 by omega]
    ring
  have hsum0 : cyclicEdge v i + cyclicEdge v (i + 1) ≠ 0 := by
    rw [hsum]
    unfold cyclicSecant
    rw [sub_ne_zero]
    have htwo : (2 : ZMod n) = 1 + 1 := by norm_num
    simpa [cyclicVertex, Nat.cast_add, htwo, add_assoc] using
      (isSimplePolygon_two_step_ne hsimple (i : ZMod n)).symm
  have hsplit := principalTurn_add_split_global hu0 hw0 hsum0
  rw [hsum] at hsplit
  simpa [cyclicSecant, cyclicEdge,
    show i + 1 + 1 = i + 2 by omega] using hsplit

private theorem sum_range_sub_succ_global (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (f i - f (i + 1)) = f 0 - f m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem hopf_column_transport_global
    (T : ℕ → ℝ) (H V : ℕ → ℕ → ℝ)
    (htriangle : ∀ i, T i = H i (i + 1) + V i (i + 2))
    {m : ℕ} (hm : 1 ≤ m)
    (hsquare : ∀ i, i + 1 < m →
      H i m + V i (m + 1) = V i m + H (i + 1) m) :
    (∑ i ∈ Finset.range (m - 1), V i m) + T (m - 1) =
      H 0 m + ∑ i ∈ Finset.range m, V i (m + 1) := by
  have hsquare_sum :
      (∑ i ∈ Finset.range (m - 1), V i m) =
        ∑ i ∈ Finset.range (m - 1),
          (H i m + V i (m + 1) - H (i + 1) m) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hs := hsquare i (by omega)
    linarith
  have htelescope :
      (∑ i ∈ Finset.range (m - 1),
        (H i m - H (i + 1) m)) = H 0 m - H (m - 1) m := by
    simpa using sum_range_sub_succ_global (fun i => H i m) (m - 1)
  have hlast : m - 1 + 1 = m := by omega
  have hlast2 : m - 1 + 2 = m + 1 := by omega
  have htri := htriangle (m - 1)
  rw [hlast, hlast2] at htri
  rw [hsquare_sum]
  rw [show (∑ i ∈ Finset.range (m - 1),
        (H i m + V i (m + 1) - H (i + 1) m)) =
      (∑ i ∈ Finset.range (m - 1), (H i m - H (i + 1) m)) +
        ∑ i ∈ Finset.range (m - 1), V i (m + 1) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  rw [htelescope]
  conv_rhs =>
    rw [← hlast, Finset.sum_range_succ]
  simp only [hlast]
  linarith

private theorem hopf_grid_sum_global
    (T : ℕ → ℝ) (H V : ℕ → ℕ → ℝ)
    (htriangle : ∀ i, T i = H i (i + 1) + V i (i + 2))
    (m : ℕ)
    (hsquare : ∀ i j, i + 1 < j → j ≤ m + 1 →
      H i j + V i (j + 1) = V i j + H (i + 1) j) :
    (∑ i ∈ Finset.range (m + 1), T i) =
      (∑ j ∈ Finset.Ico 1 (m + 2), H 0 j) +
        ∑ i ∈ Finset.range (m + 1), V i (m + 2) := by
  induction m with
  | zero =>
      simpa using htriangle 0
  | succ m ih =>
      have hsquare_prev : ∀ i j, i + 1 < j → j ≤ m + 1 →
          H i j + V i (j + 1) = V i j + H (i + 1) j := by
        intro i j hij hj
        exact hsquare i j hij (by omega)
      rw [Finset.sum_range_succ, ih hsquare_prev]
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 2)]
      have htransport := hopf_column_transport_global T H V htriangle
        (m := m + 2) (by omega)
        (fun i hi => hsquare i (m + 2) hi (by omega))
      have ht :
          (∑ i ∈ Finset.range (m + 1), V i (m + 2)) + T (m + 1) =
            H 0 (m + 2) +
              ∑ i ∈ Finset.range (m + 2), V i (m + 1 + 2) := by
        have hsub : m + 2 - 1 = m + 1 := by omega
        have hadd : m + 2 + 1 = m + 1 + 2 := by omega
        rw [hsub, hadd] at htransport
        exact htransport
      linarith

private theorem zmod_natCast_ne_of_lt_global {n : ℕ} [NeZero n]
    {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (a : ZMod n) ≠ (b : ZMod n) := by
  rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]
  exact hab

private theorem lifted_edges_disjoint_global {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) {i j : ℕ}
    (hjn : j + 1 < n) (hij : i + 1 < j) :
    Disjoint
      (segment ℝ (cyclicVertex v i) (cyclicVertex v (i + 1)))
      (segment ℝ (cyclicVertex v j) (cyclicVertex v (j + 1))) := by
  have hij0 : (i : ZMod n) ≠ (j : ZMod n) :=
    zmod_natCast_ne_of_lt_global (by omega) (by omega) (by omega)
  have hi1jNat : ((i + 1 : ℕ) : ZMod n) ≠ (j : ZMod n) :=
    zmod_natCast_ne_of_lt_global (by omega) (by omega) (by omega)
  have hi1j : (i : ZMod n) + 1 ≠ (j : ZMod n) := by
    simpa [Nat.cast_add] using hi1jNat
  have hj1iNat : ((j + 1 : ℕ) : ZMod n) ≠ (i : ZMod n) :=
    zmod_natCast_ne_of_lt_global hjn (by omega) (by omega)
  have hj1i : (j : ZMod n) + 1 ≠ (i : ZMod n) := by
    simpa [Nat.cast_add] using hj1iNat
  rw [Set.disjoint_iff_inter_eq_empty]
  simpa [cyclicVertex, Nat.cast_add] using
    hsimple.2.2 (i : ZMod n) (j : ZMod n) hij0 hi1j hj1i

private theorem lifted_edge_closing_disjoint_global {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) {i : ℕ}
    (hi : 1 ≤ i) (hin : i + 1 < n - 1) :
    Disjoint
      (segment ℝ (cyclicVertex v i) (cyclicVertex v (i + 1)))
      (segment ℝ (cyclicVertex v (n - 1)) (cyclicVertex v n)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hlast : n - 1 < n := by omega
  have hiLast : (i : ZMod n) ≠ ((n - 1 : ℕ) : ZMod n) :=
    zmod_natCast_ne_of_lt_global (by omega) hlast (by omega)
  have hi1LastNat : ((i + 1 : ℕ) : ZMod n) ≠
      ((n - 1 : ℕ) : ZMod n) :=
    zmod_natCast_ne_of_lt_global (by omega) hlast (by omega)
  have hi1Last : (i : ZMod n) + 1 ≠ ((n - 1 : ℕ) : ZMod n) := by
    simpa [Nat.cast_add] using hi1LastNat
  have hzeroi : (0 : ZMod n) ≠ (i : ZMod n) := by
    simpa using
      (zmod_natCast_ne_of_lt_global (a := 0) (b := i) hnpos
        (by omega) (by omega))
  have hlastSucc : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    calc
      ((n - 1 : ℕ) : ZMod n) + 1 = ((n - 1 + 1 : ℕ) : ZMod n) := by
        push_cast
        ring
      _ = (n : ℕ) := by congr 1; omega
      _ = 0 := ZMod.natCast_self n
  have hlastSuccI : ((n - 1 : ℕ) : ZMod n) + 1 ≠ (i : ZMod n) := by
    rw [hlastSucc]
    exact hzeroi
  rw [Set.disjoint_iff_inter_eq_empty]
  have hraw := hsimple.2.2 (i : ZMod n) ((n - 1 : ℕ) : ZMod n)
    hiLast hi1Last hlastSuccI
  rw [hlastSucc] at hraw
  simpa [cyclicVertex, Nat.cast_add] using hraw

private theorem hopf_open_chain_sum_global {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hn3 : 3 ≤ n) (hsimple : IsSimplePolygon v) :
    (∑ i ∈ Finset.range (n - 2),
        principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1))) =
      (∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j) (cyclicSecant v 0 (j + 1))) +
      ∑ i ∈ Finset.range (n - 2),
        principalTurn (cyclicSecant v i (n - 1))
          (cyclicSecant v (i + 1) (n - 1)) := by
  let T : ℕ → ℝ := fun i =>
    principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1))
  let H : ℕ → ℕ → ℝ := fun i j =>
    principalTurn (cyclicSecant v i j) (cyclicSecant v i (j + 1))
  let V : ℕ → ℕ → ℝ := fun i j =>
    principalTurn (cyclicSecant v i j) (cyclicSecant v (i + 1) j)
  have htriangle : ∀ i, T i = H i (i + 1) + V i (i + 2) := by
    intro i
    simpa [T, H, V] using principalTurn_cyclicEdge_split_global hsimple i
  have hsquare : ∀ i j, i + 1 < j → j ≤ n - 3 + 1 →
      H i j + V i (j + 1) = V i j + H (i + 1) j := by
    intro i j hij hj
    have hdisj := lifted_edges_disjoint_global hsimple
      (i := i) (j := j) (by omega) hij
    simpa [H, V, cyclicSecant] using
      principalTurn_secant_square_of_disjoint_segments hdisj
  have hgrid := hopf_grid_sum_global T H V htriangle (n - 3) hsquare
  have hsub1 : n - 3 + 1 = n - 2 := by omega
  have hsub2 : n - 3 + 2 = n - 1 := by omega
  rw [hsub1, hsub2] at hgrid
  simpa [T, H, V] using hgrid

private theorem vertex_zero_ne_nat_global {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) :
    cyclicVertex v 0 ≠ cyclicVertex v j := by
  by_cases hj : j = 1
  · subst j
    simpa [cyclicVertex] using hsimple.1 (0 : ZMod n)
  by_cases hjlast : j + 1 = n
  · have hsucc : (j : ZMod n) + 1 = 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add, hjlast, ZMod.natCast_self]
    have hne := hsimple.1 (j : ZMod n)
    rw [hsucc] at hne
    simpa [cyclicVertex] using hne.symm
  · have hj0z : (0 : ZMod n) ≠ (j : ZMod n) := by
      have h := zmod_natCast_ne_of_lt_global (n := n) (a := 0) (b := j)
        (by omega) hjn (Nat.ne_of_lt (by omega))
      simpa using h
    have h1jz : (0 : ZMod n) + 1 ≠ (j : ZMod n) := by
      have hraw := zmod_natCast_ne_of_lt_global (n := n) (a := 1) (b := j)
        (by omega) hjn (by omega)
      have h : (1 : ZMod n) ≠ (j : ZMod n) := by
        simpa using hraw
      simpa using h
    have hj10z : (j : ZMod n) + 1 ≠ 0 := by
      have hj1n : j + 1 < n := by omega
      have hraw := zmod_natCast_ne_of_lt_global (n := n) (a := j + 1) (b := 0)
        hj1n (by omega) (by omega)
      have h : ((j + 1 : ℕ) : ZMod n) ≠ (0 : ZMod n) := by
        simpa using hraw
      simpa [Nat.cast_add] using h
    have hdisj := hsimple.2.2 (0 : ZMod n) (j : ZMod n)
      hj0z h1jz hj10z
    intro heq
    simp only [cyclicVertex, Nat.cast_zero] at heq
    have hmem : v 0 ∈
        segment ℝ (v 0) (v (0 + 1)) ∩
          segment ℝ (v (j : ZMod n)) (v ((j : ZMod n) + 1)) := by
      constructor
      · exact left_mem_segment ℝ _ _
      · rw [← heq]
        exact left_mem_segment ℝ _ _
    rw [hdisj] at hmem
    exact hmem

private theorem principalTurn_eq_sub_arg_of_upper_rightCut_global {u w : ℂ}
    (hu : 0 ≤ u.im) (hur : u.im = 0 → 0 < u.re)
    (hw : 0 ≤ w.im) (hwr : w.im = 0 → 0 < w.re) :
    principalTurn u w = Complex.arg w - Complex.arg u := by
  have hu0 : u ≠ 0 := by
    intro h
    have him : u.im = 0 := by rw [h, Complex.zero_im]
    have hre := hur him
    rw [h, Complex.zero_re] at hre
    exact lt_irrefl 0 hre
  have hw0 : w ≠ 0 := by
    intro h
    have him : w.im = 0 := by rw [h, Complex.zero_im]
    have hre := hwr him
    rw [h, Complex.zero_re] at hre
    exact lt_irrefl 0 hre
  have hcoe : (principalTurn u w : Real.Angle) =
      ((Complex.arg w - Complex.arg u : ℝ) : Real.Angle) := by
    unfold principalTurn
    simpa [Real.Angle.coe_sub] using
      Complex.arg_div_coe_angle hw0 hu0
  have huarg0 : 0 ≤ Complex.arg u := Complex.arg_nonneg_iff.mpr hu
  have hwarg0 : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.mpr hw
  have huargπ : Complex.arg u < Real.pi := by
    rw [Complex.arg_lt_pi_iff]
    by_cases him : u.im = 0
    · exact Or.inl (hur him).le
    · exact Or.inr him
  have hdiff : Complex.arg w - Complex.arg u ∈
      Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · linarith
    · linarith [Complex.arg_le_pi w]
  have hp : principalTurn u w ∈ Set.Ioc (-Real.pi) Real.pi :=
    Complex.arg_mem_Ioc (w / u)
  have hreal := congrArg Real.Angle.toReal hcoe
  rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hp,
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hdiff] at hreal
  exact hreal

private theorem principalTurn_neg_left_add_arg_sub_of_upper_rightCut_pos
    {u z : ℂ}
    (hu : 0 ≤ u.im) (hur : u.im = 0 → 0 < u.re)
    (hz : 0 ≤ z.im) (hzr : z.im = 0 → 0 < z.re)
    (hcross : 0 < crossR2 0 u z) :
    principalTurn (-z) u + (Complex.arg z - Complex.arg u) = Real.pi := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp [crossR2] at hcross
  have hqim : (u / z).im < 0 := by
    rw [Complex.div_im]
    rw [← sub_div]
    apply div_neg_of_neg_of_pos
    · have h := hcross
      simp [crossR2] at h
      linarith
    · exact Complex.normSq_pos.mpr hz0
  have hneg := Complex.arg_neg_eq_arg_add_pi_of_im_neg hqim
  have hzu := principalTurn_eq_sub_arg_of_upper_rightCut_global
    hz hzr hu hur
  unfold principalTurn at hzu ⊢
  rw [div_neg, hneg, hzu]
  ring

private theorem principalTurn_neg_left_add_arg_sub_of_upper_rightCut_neg
    {u z : ℂ}
    (hu : 0 ≤ u.im) (hur : u.im = 0 → 0 < u.re)
    (hz : 0 ≤ z.im) (hzr : z.im = 0 → 0 < z.re)
    (hcross : crossR2 0 u z < 0) :
    principalTurn (-z) u + (Complex.arg z - Complex.arg u) = -Real.pi := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp [crossR2] at hcross
  have hqim : 0 < (u / z).im := by
    rw [Complex.div_im]
    rw [← sub_div]
    apply div_pos
    · have h := hcross
      simp [crossR2] at h
      linarith
    · exact Complex.normSq_pos.mpr hz0
  have hneg := Complex.arg_neg_eq_arg_sub_pi_of_im_pos hqim
  have hzu := principalTurn_eq_sub_arg_of_upper_rightCut_global
    hz hzr hu hur
  unfold principalTurn at hzu ⊢
  rw [div_neg, hneg, hzu]
  ring

private theorem sum_Ico_succ_sub_global (f : ℕ → ℝ)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ j ∈ Finset.Ico a b, (f (j + 1) - f j)) = f b - f a := by
  have hsum (m : ℕ) :
      (∑ j ∈ Finset.range m, (f (j + 1) - f j)) = f m - f 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  rw [Finset.sum_Ico_eq_sub _ hab, hsum b, hsum a]
  ring

private theorem sum_principalTurn_upper_rightCut_global
    (U : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b)
    (him : ∀ j, a ≤ j → j ≤ b → 0 ≤ (U j).im)
    (hre : ∀ j, a ≤ j → j ≤ b → (U j).im = 0 → 0 < (U j).re) :
    (∑ j ∈ Finset.Ico a b, principalTurn (U j) (U (j + 1))) =
      Complex.arg (U b) - Complex.arg (U a) := by
  rw [← sum_Ico_succ_sub_global (fun j => Complex.arg (U j)) hab]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  apply principalTurn_eq_sub_arg_of_upper_rightCut_global
  · exact him j hj.1 (by omega)
  · exact hre j hj.1 (by omega)
  · exact him (j + 1) (by omega) (by omega)
  · exact hre (j + 1) (by omega) (by omega)

private theorem cyclicSecant_zero_upper_rightCut_global {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re)
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) :
    0 ≤ (cyclicSecant v 0 j).im ∧
      ((cyclicSecant v 0 j).im = 0 →
        0 < (cyclicSecant v 0 j).re) := by
  have him := hminIm (j : ZMod n)
  have hne := vertex_zero_ne_nat_global hsimple hn3 hj1 hjn
  constructor
  · simpa [cyclicSecant, cyclicVertex] using sub_nonneg.mpr him
  · intro hzero
    have himEq : (v 0).im = (v (j : ZMod n)).im := by
      simpa [cyclicSecant, cyclicVertex] using (sub_eq_zero.mp hzero).symm
    have hre := hminReOnTie (j : ZMod n) himEq
    have hsecne : cyclicSecant v 0 j ≠ 0 := by
      unfold cyclicSecant
      rw [sub_ne_zero]
      exact hne.symm
    have hreNonneg : 0 ≤ (cyclicSecant v 0 j).re := by
      simpa [cyclicSecant, cyclicVertex] using sub_nonneg.mpr hre
    exact lt_of_le_of_ne hreNonneg fun hreZero =>
      hsecne (Complex.ext hreZero.symm hzero)

private theorem top_sum_eq_arg_sub_global {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re) :
    (∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j)
          (cyclicSecant v 0 (j + 1))) =
      Complex.arg (cyclicSecant v 0 (n - 1)) -
        Complex.arg (cyclicSecant v 0 1) := by
  apply sum_principalTurn_upper_rightCut_global
  · omega
  · intro j hj1 hjlast
    exact (cyclicSecant_zero_upper_rightCut_global hsimple hn3 hminIm
      hminReOnTie hj1 (by omega)).1
  · intro j hj1 hjlast
    exact (cyclicSecant_zero_upper_rightCut_global hsimple hn3 hminIm
      hminReOnTie hj1 (by omega)).2

private theorem lower_sum_eq_top_sum_global {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) :
    (∑ r ∈ Finset.range (n - 2),
        principalTurn (cyclicSecant v (r + 1) n)
          (cyclicSecant v (r + 2) n)) =
      ∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j)
          (cyclicSecant v 0 (j + 1)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show n - 1 - 1 = n - 2 by omega]
  apply Finset.sum_congr rfl
  intro r hr
  have hfirst : cyclicSecant v (r + 1) n =
      -cyclicSecant v 0 (1 + r) := by
    unfold cyclicSecant cyclicVertex
    simp
    congr 1
    ring
  have hsecond : cyclicSecant v (r + 2) n =
      -cyclicSecant v 0 (1 + r + 1) := by
    unfold cyclicSecant cyclicVertex
    simp
    congr 1
    ring
  rw [hfirst, hsecond]
  have hneg : principalTurn (-cyclicSecant v 0 (1 + r))
      (-cyclicSecant v 0 (1 + r + 1)) =
      principalTurn (cyclicSecant v 0 (1 + r))
        (cyclicSecant v 0 (1 + r + 1)) := by
    unfold principalTurn
    congr 1
    ring
  exact hneg

private theorem cross_first_lastSecant_eq_vertex_cross {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hn3 : 3 ≤ n) :
    crossR2 0 (cyclicSecant v 0 1) (cyclicSecant v 0 (n - 1)) =
      crossR2 (v (-1)) (v 0) (v 1) := by
  have hlast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    simp
  rw [← hlast]
  unfold cyclicSecant cyclicVertex crossR2
  simp only [Nat.cast_zero, Nat.cast_one, Complex.zero_re, Complex.zero_im,
    Complex.sub_re, Complex.sub_im]
  ring

private theorem top_add_closing_eq_pi_of_cross_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (hcross : 0 < crossR2 (v (-1)) (v 0) (v 1))
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re) :
    (∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j)
          (cyclicSecant v 0 (j + 1))) +
        principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) =
      Real.pi := by
  let u := cyclicSecant v 0 1
  let z := cyclicSecant v 0 (n - 1)
  have hu := cyclicSecant_zero_upper_rightCut_global hsimple hn3 hminIm
    hminReOnTie (j := 1) (by omega) (by omega)
  have hz := cyclicSecant_zero_upper_rightCut_global hsimple hn3 hminIm
    hminReOnTie (j := n - 1) (by omega) (by omega)
  have hcross' : 0 < crossR2 0 u z := by
    simpa [u, z, cross_first_lastSecant_eq_vertex_cross hn3] using hcross
  have hcomp : principalTurn (-z) u +
      (Complex.arg z - Complex.arg u) = Real.pi :=
    principalTurn_neg_left_add_arg_sub_of_upper_rightCut_pos
      hu.1 hu.2 hz.1 hz.2 hcross'
  have htop := top_sum_eq_arg_sub_global hsimple hn3 hminIm hminReOnTie
  have hedge0 : cyclicEdge v 0 = u := by
    simp [u, cyclicEdge, cyclicSecant, cyclicVertex]
  have hedgeLast : cyclicEdge v (n - 1) = -z := by
    simp [z, cyclicEdge, cyclicSecant, cyclicVertex,
      show n - 1 + 1 = n by omega]
  rw [htop, hedge0, hedgeLast]
  linarith

private theorem top_add_closing_eq_neg_pi_of_cross_neg {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (hcross : crossR2 (v (-1)) (v 0) (v 1) < 0)
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re) :
    (∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j)
          (cyclicSecant v 0 (j + 1))) +
        principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) =
      -Real.pi := by
  let u := cyclicSecant v 0 1
  let z := cyclicSecant v 0 (n - 1)
  have hu := cyclicSecant_zero_upper_rightCut_global hsimple hn3 hminIm
    hminReOnTie (j := 1) (by omega) (by omega)
  have hz := cyclicSecant_zero_upper_rightCut_global hsimple hn3 hminIm
    hminReOnTie (j := n - 1) (by omega) (by omega)
  have hcross' : crossR2 0 u z < 0 := by
    simpa [u, z, cross_first_lastSecant_eq_vertex_cross hn3] using hcross
  have hcomp : principalTurn (-z) u +
      (Complex.arg z - Complex.arg u) = -Real.pi :=
    principalTurn_neg_left_add_arg_sub_of_upper_rightCut_neg
      hu.1 hu.2 hz.1 hz.2 hcross'
  have htop := top_sum_eq_arg_sub_global hsimple hn3 hminIm hminReOnTie
  have hedge0 : cyclicEdge v 0 = u := by
    simp [u, cyclicEdge, cyclicSecant, cyclicVertex]
  have hedgeLast : cyclicEdge v (n - 1) = -z := by
    simp [z, cyclicEdge, cyclicSecant, cyclicVertex,
      show n - 1 + 1 = n by omega]
  rw [htop, hedge0, hedgeLast]
  linarith

private theorem cyclicSecant_one_last_ne_global {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n) :
    cyclicSecant v 1 (n - 1) ≠ 0 := by
  have hshift := isSimplePolygon_shift hsimple (1 : ZMod n)
  have hne := vertex_zero_ne_nat_global hshift hn3
    (j := n - 2) (by omega) (by omega)
  have hidx : (1 : ZMod n) + ((n - 2 : ℕ) : ZMod n) =
      ((n - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 2 ≤ n),
      Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    ring
  unfold cyclicSecant
  rw [sub_ne_zero]
  apply Ne.symm
  simpa [cyclicVertex, shiftPolygon, hidx] using hne

private theorem hopf_closed_boundary_sum_global {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hn3 : 3 ≤ n) (hsimple : IsSimplePolygon v) :
    (∑ i ∈ Finset.range n,
        principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1))) =
      (∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j) (cyclicSecant v 0 (j + 1))) +
      2 * principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) +
      ∑ r ∈ Finset.range (n - 2),
        principalTurn (cyclicSecant v (r + 1) n)
          (cyclicSecant v (r + 2) n) := by
  have hopen := hopf_open_chain_sum_global hn3 hsimple
  let T : ℕ → ℝ := fun r =>
    principalTurn (cyclicEdge v (r + 1)) (cyclicEdge v (r + 2))
  let H : ℕ → ℕ → ℝ := fun r j =>
    principalTurn (cyclicSecant v (r + 1) (j + 1))
      (cyclicSecant v (r + 1) (j + 2))
  let V : ℕ → ℕ → ℝ := fun r j =>
    principalTurn (cyclicSecant v (r + 1) (j + 1))
      (cyclicSecant v (r + 2) (j + 1))
  have htriangle : ∀ r, T r = H r (r + 1) + V r (r + 2) := by
    intro r
    simpa [T, H, V, add_assoc] using
      principalTurn_cyclicEdge_split_global hsimple (r + 1)
  have hsquare : ∀ r, r + 1 < n - 2 →
      H r (n - 2) + V r (n - 2 + 1) =
        V r (n - 2) + H (r + 1) (n - 2) := by
    intro r hr
    have hdisj := lifted_edge_closing_disjoint_global hsimple
      (i := r + 1) (by omega) (by omega)
    have hnm1 : n - 2 + 1 = n - 1 := by omega
    have hnm2 : n - 2 + 2 = n := by omega
    have hlast : n - 1 + 1 = n := by omega
    simp only [H, V, hnm1, hnm2, hlast]
    simpa [cyclicSecant, add_assoc] using
      principalTurn_secant_square_of_disjoint_segments hdisj
  have htransport := hopf_column_transport_global T H V htriangle
    (m := n - 2) (by omega) hsquare
  have hsub : n - 2 - 1 = n - 3 := by omega
  have hnm1 : n - 2 + 1 = n - 1 := by omega
  have hnm2 : n - 2 + 2 = n := by omega
  have hn31 : n - 3 + 1 = n - 2 := by omega
  have hn32 : n - 3 + 2 = n - 1 := by omega
  have hlast : n - 1 + 1 = n := by omega
  rw [hsub, hnm1] at htransport
  have htransport' :
      (∑ r ∈ Finset.range (n - 3),
        principalTurn (cyclicSecant v (r + 1) (n - 1))
          (cyclicSecant v (r + 2) (n - 1))) +
          principalTurn (cyclicEdge v (n - 2)) (cyclicEdge v (n - 1)) =
        principalTurn (cyclicSecant v 1 (n - 1))
            (cyclicSecant v 1 n) +
          ∑ r ∈ Finset.range (n - 2),
            principalTurn (cyclicSecant v (r + 1) n)
              (cyclicSecant v (r + 2) n) := by
    simpa [T, H, V, add_assoc, hn31, hn32, hnm1, hnm2, hlast] using htransport
  have hsec0Last : cyclicSecant v 0 (n - 1) = -cyclicEdge v (n - 1) := by
    unfold cyclicSecant cyclicEdge
    have hp := cyclicVertex_periodic v 0
    simp only [zero_add] at hp
    rw [hlast, hp]
    ring
  have hsec1N : cyclicSecant v 1 n = -cyclicEdge v 0 := by
    unfold cyclicSecant cyclicEdge
    have hp := cyclicVertex_periodic v 0
    simp only [zero_add] at hp
    rw [hp]
    ring
  have hsecSum : cyclicSecant v 0 (n - 1) + cyclicSecant v 1 n =
      cyclicSecant v 1 (n - 1) := by
    unfold cyclicSecant
    have hp := cyclicVertex_periodic v 0
    simp only [zero_add] at hp
    rw [hp]
    ring
  have hedgeN : cyclicEdge v n = cyclicEdge v 0 := by
    simpa using cyclicEdge_periodic v 0
  have hconnector :
      principalTurn (cyclicSecant v 0 (n - 1))
          (cyclicSecant v 1 (n - 1)) +
        principalTurn (cyclicSecant v 1 (n - 1))
          (cyclicSecant v 1 n) =
        principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) := by
    have hu0 : cyclicSecant v 0 (n - 1) ≠ 0 := by
      rw [hsec0Last]
      exact neg_ne_zero.mpr (cyclicEdge_ne_zero hsimple (n - 1))
    have hw0 : cyclicSecant v 1 n ≠ 0 := by
      rw [hsec1N]
      exact neg_ne_zero.mpr (cyclicEdge_ne_zero hsimple 0)
    have hsum0 : cyclicSecant v 0 (n - 1) + cyclicSecant v 1 n ≠ 0 := by
      rw [hsecSum]
      exact cyclicSecant_one_last_ne_global hsimple hn3
    have hs := principalTurn_add_split_global hu0 hw0 hsum0
    rw [hsecSum] at hs
    have hleft : principalTurn (cyclicSecant v 0 (n - 1))
        (cyclicSecant v 1 n) =
          principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) := by
      rw [hsec0Last, hsec1N]
      unfold principalTurn
      congr 1
      ring
    rw [hleft] at hs
    linarith
  let F : ℕ → ℝ := fun i =>
    principalTurn (cyclicSecant v i (n - 1))
      (cyclicSecant v (i + 1) (n - 1))
  let G : ℕ → ℝ := fun i =>
    principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1))
  have hrightSplit :
      (∑ i ∈ Finset.range (n - 2), F i) =
        F 0 + ∑ r ∈ Finset.range (n - 3), F (r + 1) := by
    have hcount : n - 2 = n - 3 + 1 := by omega
    rw [hcount, Finset.sum_range_succ']
    abel
  have hopen' :
      (∑ i ∈ Finset.range (n - 2), G i) =
        (∑ j ∈ Finset.Ico 1 (n - 1),
          principalTurn (cyclicSecant v 0 j) (cyclicSecant v 0 (j + 1))) +
        ∑ i ∈ Finset.range (n - 2), F i := by
    simpa [F, G] using hopen
  have htransport'' :
      (∑ r ∈ Finset.range (n - 3), F (r + 1)) + G (n - 2) =
        principalTurn (cyclicSecant v 1 (n - 1))
            (cyclicSecant v 1 n) +
          ∑ r ∈ Finset.range (n - 2),
            principalTurn (cyclicSecant v (r + 1) n)
              (cyclicSecant v (r + 2) n) := by
    have hadd (r : ℕ) : r + 1 + 1 = r + 2 := by omega
    simpa [F, G, hadd, hnm1] using htransport'
  have hconnector' : F 0 +
      principalTurn (cyclicSecant v 1 (n - 1)) (cyclicSecant v 1 n) =
        principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) := by
    simpa [F] using hconnector
  have hlastTurn : G (n - 1) =
      principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) := by
    dsimp [G]
    rw [hlast, hedgeN]
  have hfullSplit :
      (∑ i ∈ Finset.range n, G i) =
        (∑ i ∈ Finset.range (n - 2), G i) + G (n - 2) + G (n - 1) := by
    have hcount : n = (n - 2) + 2 := by omega
    have htwo :
        (∑ i ∈ Finset.range ((n - 2) + 2), G i) =
          (∑ i ∈ Finset.range (n - 2), G i) +
            G (n - 2) + G (n - 2 + 1) := by
      rw [show n - 2 + 2 = (n - 2 + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
    calc
      (∑ i ∈ Finset.range n, G i) =
          ∑ i ∈ Finset.range ((n - 2) + 2), G i := by
            apply Finset.sum_congr (congrArg Finset.range hcount)
            intro i _
            rfl
      _ = (∑ i ∈ Finset.range (n - 2), G i) +
          G (n - 2) + G (n - 2 + 1) := htwo
      _ = (∑ i ∈ Finset.range (n - 2), G i) +
          G (n - 2) + G (n - 1) := by rw [hnm1]
  change (∑ i ∈ Finset.range n, G i) = _
  rw [hfullSplit, hlastTurn, hopen', hrightSplit]
  linarith

private theorem hopf_boundary_value_of_lex_min_cross_pos_global
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (hcross : 0 < crossR2 (v (-1)) (v 0) (v 1))
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re) :
    (∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j)
          (cyclicSecant v 0 (j + 1))) +
      2 * principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) +
      (∑ r ∈ Finset.range (n - 2),
        principalTurn (cyclicSecant v (r + 1) n)
          (cyclicSecant v (r + 2) n)) =
      2 * Real.pi := by
  have htop := top_add_closing_eq_pi_of_cross_pos hsimple hn3 hcross
    hminIm hminReOnTie
  have hlower := lower_sum_eq_top_sum_global v
  rw [hlower]
  linarith

private theorem hopf_boundary_value_of_lex_min_cross_neg_global
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (hcross : crossR2 (v (-1)) (v 0) (v 1) < 0)
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re) :
    (∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j)
          (cyclicSecant v 0 (j + 1))) +
      2 * principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) +
      (∑ r ∈ Finset.range (n - 2),
        principalTurn (cyclicSecant v (r + 1) n)
          (cyclicSecant v (r + 2) n)) =
      -(2 * Real.pi) := by
  have htop := top_add_closing_eq_neg_pi_of_cross_neg hsimple hn3 hcross
    hminIm hminReOnTie
  have hlower := lower_sum_eq_top_sum_global v
  rw [hlower]
  linarith

private theorem sum_cyclicEdgeTurn_eq_two_pi_of_lex_min_cross_pos_global
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (hcross : 0 < crossR2 (v (-1)) (v 0) (v 1))
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re) :
    (∑ i ∈ Finset.range n, cyclicEdgeTurn v i) = 2 * Real.pi := by
  calc
    (∑ i ∈ Finset.range n, cyclicEdgeTurn v i) =
        ∑ i ∈ Finset.range n,
          principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1)) := by rfl
    _ = (∑ j ∈ Finset.Ico 1 (n - 1),
          principalTurn (cyclicSecant v 0 j)
            (cyclicSecant v 0 (j + 1))) +
        2 * principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) +
        ∑ r ∈ Finset.range (n - 2),
          principalTurn (cyclicSecant v (r + 1) n)
            (cyclicSecant v (r + 2) n) :=
      hopf_closed_boundary_sum_global hn3 hsimple
    _ = 2 * Real.pi :=
      hopf_boundary_value_of_lex_min_cross_pos_global hsimple hn3 hcross
        hminIm hminReOnTie

private theorem sum_cyclicEdgeTurn_eq_neg_two_pi_of_lex_min_cross_neg_global
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (hcross : crossR2 (v (-1)) (v 0) (v 1) < 0)
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re) :
    (∑ i ∈ Finset.range n, cyclicEdgeTurn v i) = -(2 * Real.pi) := by
  calc
    (∑ i ∈ Finset.range n, cyclicEdgeTurn v i) =
        ∑ i ∈ Finset.range n,
          principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1)) := by rfl
    _ = (∑ j ∈ Finset.Ico 1 (n - 1),
          principalTurn (cyclicSecant v 0 j)
            (cyclicSecant v 0 (j + 1))) +
        2 * principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) +
        ∑ r ∈ Finset.range (n - 2),
          principalTurn (cyclicSecant v (r + 1) n)
            (cyclicSecant v (r + 2) n) :=
      hopf_closed_boundary_sum_global hn3 hsimple
    _ = -(2 * Real.pi) :=
      hopf_boundary_value_of_lex_min_cross_neg_global hsimple hn3 hcross
        hminIm hminReOnTie

private theorem principalTurn_mul_left_global {c u w : ℂ} (hc : c ≠ 0) :
    principalTurn (c * u) (c * w) = principalTurn u w := by
  unfold principalTurn
  congr 1
  field_simp

private theorem cyclicEdge_directIsometry_global {n : ℕ}
    (u a : ℂ) (v : ZMod n → ℂ) (k : ℕ) :
    cyclicEdge (fun i ↦ directIsometryR2 u a (v i)) k =
      u * cyclicEdge v k := by
  simp [cyclicEdge, cyclicVertex, directIsometryR2]
  ring

private theorem cyclicEdgeTurn_directIsometry_global {n : ℕ}
    {u : ℂ} (hu : u ≠ 0) (a : ℂ) (v : ZMod n → ℂ) (k : ℕ) :
    cyclicEdgeTurn (fun i ↦ directIsometryR2 u a (v i)) k =
      cyclicEdgeTurn v k := by
  unfold cyclicEdgeTurn
  rw [cyclicEdge_directIsometry_global, cyclicEdge_directIsometry_global]
  exact principalTurn_mul_left_global hu

private theorem sum_cyclicEdgeTurn_directIsometry_global {n : ℕ}
    {u : ℂ} (hu : u ≠ 0) (a : ℂ) (v : ZMod n → ℂ) :
    (∑ k ∈ Finset.range n,
        cyclicEdgeTurn (fun i ↦ directIsometryR2 u a (v i)) k) =
      ∑ k ∈ Finset.range n, cyclicEdgeTurn v k := by
  apply Finset.sum_congr rfl
  intro k _
  exact cyclicEdgeTurn_directIsometry_global hu a v k

private theorem disk_contact_zero_normalization_data_global {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hR : 0 < R) (hcontains : PolygonInClosedDiskR2 v O R)
    (hboundary : OnDiskBoundaryR2 v O R 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      let w : ZMod n → ℂ := fun i ↦ directIsometryR2 u (-u * O) (v i)
      w 0 = -Complex.I * (R : ℂ) ∧
      (∀ i, (w 0).im ≤ (w i).im) ∧
      (∀ i, (w 0).im = (w i).im → (w 0).re ≤ (w i).re) := by
  let ξ : ℂ := v 0 - O
  have hξnorm : ‖ξ‖ = R := by
    have hb : dist O (v 0) = R := Metric.mem_sphere'.mp hboundary
    rw [dist_eq_norm] at hb
    dsimp [ξ]
    rw [show v 0 - O = -(O - v 0) by ring, norm_neg, hb]
  have hξ0 : ξ ≠ 0 := by
    intro h
    have : ‖ξ‖ = 0 := by rw [h, norm_zero]
    linarith
  let u : ℂ := (-Complex.I * (R : ℂ)) / ξ
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hξnorm,
      div_self hR.ne']
  refine ⟨u, hu, ?_⟩
  let w : ZMod n → ℂ := fun i ↦ directIsometryR2 u (-u * O) (v i)
  have hcenter : directIsometryR2 u (-u * O) O = 0 := by
    unfold directIsometryR2
    ring
  have hw0 : w 0 = -Complex.I * (R : ℂ) := by
    dsimp [w, directIsometryR2, u]
    calc
      (-Complex.I * (R : ℂ)) / ξ * v 0 +
          -((-Complex.I * (R : ℂ)) / ξ) * O =
          ((-Complex.I * (R : ℂ)) / ξ) * (v 0 - O) := by ring
      _ = ((-Complex.I * (R : ℂ)) / ξ) * ξ := by rw [show v 0 - O = ξ by rfl]
      _ = -Complex.I * (R : ℂ) := div_mul_cancel₀ _ hξ0
  refine ⟨hw0, ?_, ?_⟩
  · intro i
    have hdist : dist 0 (w i) ≤ R := by
      have hi := Metric.mem_closedBall'.mp (hcontains i)
      have hiso := dist_directIsometryR2 hu (-u * O) O (v i)
      rw [hcenter] at hiso
      dsimp [w]
      rw [hiso]
      exact hi
    have hnorm : ‖w i‖ ≤ R := by simpa [dist_eq_norm] using hdist
    have habs := Complex.abs_im_le_norm (w i)
    rw [abs_le] at habs
    change (w 0).im ≤ (w i).im
    rw [hw0]
    simp only [Complex.mul_im, Complex.neg_re, Complex.I_re,
      Complex.ofReal_im, neg_zero, zero_mul, Complex.neg_im, Complex.I_im,
      Complex.ofReal_re]
    linarith
  · intro i htie
    change (w 0).im = (w i).im at htie
    change (w 0).re ≤ (w i).re
    have hdist : dist 0 (w i) ≤ R := by
      have hi := Metric.mem_closedBall'.mp (hcontains i)
      have hiso := dist_directIsometryR2 hu (-u * O) O (v i)
      rw [hcenter] at hiso
      dsimp [w]
      rw [hiso]
      exact hi
    have hnorm : ‖w i‖ ≤ R := by simpa [dist_eq_norm] using hdist
    have him : (w i).im = -R := by
      rw [hw0] at htie
      simpa using htie.symm
    have hsq := Complex.sq_norm_sub_sq_im (w i)
    have hnorm0 := norm_nonneg (w i)
    have hreSq := sq_nonneg (w i).re
    have hre0 : (w i).re = 0 := by
      nlinarith
    rw [hw0, hre0]
    simp

private theorem sum_cyclicEdgeTurn_eq_two_pi_of_disk_contact_zero_cross_pos_global
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hn3 : 3 ≤ n) (hsimple : IsSimplePolygon v)
    (hR : 0 < R) (hcontains : PolygonInClosedDiskR2 v O R)
    (hboundary : OnDiskBoundaryR2 v O R 0)
    (hcross : 0 < crossR2 (v (-1)) (v 0) (v 1)) :
    (∑ k ∈ Finset.range n, cyclicEdgeTurn v k) = 2 * Real.pi := by
  obtain ⟨u, hu, hw0, hminIm, hminReOnTie⟩ :=
    disk_contact_zero_normalization_data_global hR hcontains hboundary
  let w : ZMod n → ℂ := fun i ↦ directIsometryR2 u (-u * O) (v i)
  have hsimpleW : IsSimplePolygon w := by
    simpa [w] using isSimplePolygon_directIsometry hu (-u * O) hsimple
  have hcrossW : 0 < crossR2 (w (-1)) (w 0) (w 1) := by
    dsimp [w]
    rwa [crossR2_directIsometry hu]
  have hsumW :=
    sum_cyclicEdgeTurn_eq_two_pi_of_lex_min_cross_pos_global
      hsimpleW hn3 hcrossW hminIm hminReOnTie
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hu
    norm_num at hu
  have hinv := sum_cyclicEdgeTurn_directIsometry_global hu0 (-u * O) v
  rw [hinv] at hsumW
  exact hsumW

private theorem sum_cyclicEdgeTurn_eq_neg_two_pi_of_disk_contact_zero_cross_neg_global
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hn3 : 3 ≤ n) (hsimple : IsSimplePolygon v)
    (hR : 0 < R) (hcontains : PolygonInClosedDiskR2 v O R)
    (hboundary : OnDiskBoundaryR2 v O R 0)
    (hcross : crossR2 (v (-1)) (v 0) (v 1) < 0) :
    (∑ k ∈ Finset.range n, cyclicEdgeTurn v k) = -(2 * Real.pi) := by
  obtain ⟨u, hu, hw0, hminIm, hminReOnTie⟩ :=
    disk_contact_zero_normalization_data_global hR hcontains hboundary
  let w : ZMod n → ℂ := fun i ↦ directIsometryR2 u (-u * O) (v i)
  have hsimpleW : IsSimplePolygon w := by
    simpa [w] using isSimplePolygon_directIsometry hu (-u * O) hsimple
  have hcrossW : crossR2 (w (-1)) (w 0) (w 1) < 0 := by
    dsimp [w]
    rwa [crossR2_directIsometry hu]
  have hsumW :=
    sum_cyclicEdgeTurn_eq_neg_two_pi_of_lex_min_cross_neg_global
      hsimpleW hn3 hcrossW hminIm hminReOnTie
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hu
    norm_num at hu
  have hinv := sum_cyclicEdgeTurn_directIsometry_global hu0 (-u * O) v
  rw [hinv] at hsumW
  exact hsumW

private theorem sum_cyclicEdgeTurn_eq_two_pi_of_disk_contact_cross_pos_global
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hn3 : 3 ≤ n) (hsimple : IsSimplePolygon v)
    (hR : 0 < R) (hcontains : PolygonInClosedDiskR2 v O R)
    {a : ZMod n} (hboundary : OnDiskBoundaryR2 v O R a)
    (hcross : 0 < crossR2 (v (a - 1)) (v a) (v (a + 1))) :
    (∑ k ∈ Finset.range n, cyclicEdgeTurn v k) = 2 * Real.pi := by
  let w := shiftPolygon v a
  have hsimpleW : IsSimplePolygon w := by
    exact isSimplePolygon_shift hsimple a
  have hcontainsW : PolygonInClosedDiskR2 w O R := by
    intro i
    simpa [w, shiftPolygon] using hcontains (a + i)
  have hboundaryW : OnDiskBoundaryR2 w O R 0 := by
    simpa [w, shiftPolygon] using hboundary
  have hcrossW : 0 < crossR2 (w (-1)) (w 0) (w 1) := by
    simpa [w, shiftPolygon, sub_eq_add_neg] using hcross
  have hsumW :=
    sum_cyclicEdgeTurn_eq_two_pi_of_disk_contact_zero_cross_pos_global
      hn3 hsimpleW hR hcontainsW hboundaryW hcrossW
  rw [sum_cyclicEdgeTurn_shift v a] at hsumW
  exact hsumW

private theorem sum_cyclicEdgeTurn_eq_neg_two_pi_of_disk_contact_cross_neg_global
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hn3 : 3 ≤ n) (hsimple : IsSimplePolygon v)
    (hR : 0 < R) (hcontains : PolygonInClosedDiskR2 v O R)
    {a : ZMod n} (hboundary : OnDiskBoundaryR2 v O R a)
    (hcross : crossR2 (v (a - 1)) (v a) (v (a + 1)) < 0) :
    (∑ k ∈ Finset.range n, cyclicEdgeTurn v k) = -(2 * Real.pi) := by
  let w := shiftPolygon v a
  have hsimpleW : IsSimplePolygon w := by
    exact isSimplePolygon_shift hsimple a
  have hcontainsW : PolygonInClosedDiskR2 w O R := by
    intro i
    simpa [w, shiftPolygon] using hcontains (a + i)
  have hboundaryW : OnDiskBoundaryR2 w O R 0 := by
    simpa [w, shiftPolygon] using hboundary
  have hcrossW : crossR2 (w (-1)) (w 0) (w 1) < 0 := by
    simpa [w, shiftPolygon, sub_eq_add_neg] using hcross
  have hsumW :=
    sum_cyclicEdgeTurn_eq_neg_two_pi_of_disk_contact_zero_cross_neg_global
      hn3 hsimpleW hR hcontainsW hboundaryW hcrossW
  rw [sum_cyclicEdgeTurn_shift v a] at hsumW
  exact hsumW

/-- Boundary contacts of one positive-radius containing disk have one common
strict local orientation in every simple polygon whose contact turns are
nonzero. -/
theorem circleContactSet_cross_uniform_of_enclosingDisk
    {n : ℕ} [NeZero n] (hn3 : 3 ≤ n) {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ}
    (hsimple : IsSimplePolygon v)
    (hR : 0 < R) (hcontains : PolygonInClosedDiskR2 v O R)
    (hcontactNe : ∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
      crossR2 (v (i - 1)) (v i) (v (i + 1)) ≠ 0) :
    ((∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
        0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) ∨
      (∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
        crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0)) := by
  classical
  by_cases hex : ∃ a : ZMod n, OnDiskBoundaryR2 v O R a
  · obtain ⟨a, ha⟩ := hex
    have haNe := hcontactNe a ha
    rcases lt_or_gt_of_ne haNe with haNeg | haPos
    · right
      intro i hi
      have hiNe := hcontactNe i hi
      rcases lt_or_gt_of_ne hiNe with hiNeg | hiPos
      · exact hiNeg
      · have hsumNeg :=
          sum_cyclicEdgeTurn_eq_neg_two_pi_of_disk_contact_cross_neg_global
            hn3 hsimple hR hcontains ha haNeg
        have hsumPos :=
          sum_cyclicEdgeTurn_eq_two_pi_of_disk_contact_cross_pos_global
            hn3 hsimple hR hcontains hi hiPos
        exfalso
        nlinarith [Real.pi_pos]
    · left
      intro i hi
      have hiNe := hcontactNe i hi
      rcases lt_or_gt_of_ne hiNe with hiNeg | hiPos
      · have hsumPos :=
          sum_cyclicEdgeTurn_eq_two_pi_of_disk_contact_cross_pos_global
            hn3 hsimple hR hcontains ha haPos
        have hsumNeg :=
          sum_cyclicEdgeTurn_eq_neg_two_pi_of_disk_contact_cross_neg_global
            hn3 hsimple hR hcontains hi hiNeg
        exfalso
        nlinarith [Real.pi_pos]
      · exact hiPos
  · left
    intro i hi
    exact False.elim (hex ⟨i, hi⟩)

/-- All contacts of the minimal enclosing disk of a simple Dahlberg-regular
polygon have one common strict local orientation. -/
theorem circleContactSet_cross_uniform
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ}
    (hsimple : IsSimplePolygon v)
    (hregular : DahlbergRegular v)
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    ((∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
        0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) ∨
      (∀ i : ZMod n, OnDiskBoundaryR2 v O R i →
        crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0)) := by
  apply circleContactSet_cross_uniform_of_enclosingDisk
      (show 3 ≤ n by omega) hsimple
      (radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon hΔ hsimple)
      (polygonInClosedDiskR2_of_minimalEnclosingDiskR2 hΔ)
  intro i hi
  exact crossR2_ne_zero_of_minimalEnclosingDisk_boundary
    hsimple hregular hΔ hi

end Gluck.Forward
