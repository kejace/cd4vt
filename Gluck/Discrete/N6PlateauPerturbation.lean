/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.CollarOpenness
import Gluck.Discrete.RealizabilityClosure

/-!
# Perturbing six-vertex plateaus

Every positive six-profile with a fixed four-vertex window is a limit of
positive profiles with the same window and no adjacent equal values.  The
perturbation adds a small multiple of the canonical residue representative.

This is only a generic-density statement.  It does not pass realizability to
the limiting plateau profile.
-/

namespace Gluck.Discrete

open Filter Set
open scoped Topology

/-- Add a scalar multiple of each residue's canonical representative. -/
def n6IndexPerturbation (w : ZMod 6 → ℝ) (ε : ℝ) (i : ZMod 6) : ℝ :=
  w i + ε * i.val

private lemma eventually_add_mul_ne_add_mul_aux {a b c d : ℝ} (hcd : c ≠ d) :
    ∀ᶠ ε in 𝓝[≠] 0, a + ε * c ≠ b + ε * d := by
  by_cases hab : a = b
  · subst b
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [mem_compl_iff, mem_singleton_iff] at hε
    intro heq
    apply hcd
    apply mul_left_cancel₀ hε
    linarith
  · have hcont : ContinuousAt (fun ε : ℝ ↦ (a + ε * c) - (b + ε * d)) 0 := by
      fun_prop
    have hzero : (a + 0 * c) - (b + 0 * d) ≠ 0 := by
      simpa only [zero_mul, add_zero, sub_ne_zero] using hab
    have hne := hcont.eventually_ne hzero
    filter_upwards [hne.filter_mono nhdsWithin_le_nhds] with ε hε
    exact sub_ne_zero.mp hε

private lemma n6_val_ne_succ_val_aux (i : ZMod 6) :
    (i.val : ℝ) ≠ ((i + 1).val : ℝ) := by
  intro h
  have hval : i.val = (i + 1).val := by
    exact_mod_cast h
  have hi : i = i + 1 := ZMod.val_injective 6 hval
  have hzero := congrArg (fun z : ZMod 6 ↦ z - i) hi
  norm_num at hzero
  exact (show (0 : ZMod 6) ≠ 1 by decide) hzero

/-- The index perturbation is continuous in its scalar parameter. -/
theorem continuous_n6IndexPerturbation (w : ZMod 6 → ℝ) :
    Continuous (n6IndexPerturbation w) := by
  unfold n6IndexPerturbation
  fun_prop

/-- The index perturbation tends to its original profile at zero. -/
theorem tendsto_n6IndexPerturbation_zero (w : ZMod 6 → ℝ) :
    Tendsto (n6IndexPerturbation w) (𝓝 0) (𝓝 w) := by
  have hcont : ContinuousAt (n6IndexPerturbation w) 0 :=
    (continuous_n6IndexPerturbation w).continuousAt
  change Tendsto (n6IndexPerturbation w) (𝓝 0)
    (𝓝 (n6IndexPerturbation w 0)) at hcont
  convert hcont using 1
  congr 1
  funext i
  simp only [n6IndexPerturbation, zero_mul, add_zero]

/-- Every adjacent pair of an index perturbation is unequal for all
sufficiently small nonzero parameters. -/
theorem eventually_n6IndexPerturbation_ne_succ (w : ZMod 6 → ℝ) :
    ∀ᶠ ε in 𝓝[≠] 0, ∀ i, n6IndexPerturbation w ε i ≠
      n6IndexPerturbation w ε (i + 1) := by
  rw [Filter.eventually_all]
  intro i
  simpa only [n6IndexPerturbation] using eventually_add_mul_ne_add_mul_aux
    (a := w i) (b := w (i + 1)) (n6_val_ne_succ_val_aux i)

/-- A positive six-profile with a fixed four-vertex window lies in the
closure of the adjacent-unequal profiles satisfying the same conditions. -/
theorem mem_closure_positive_dfv_ne_succ {w : ZMod 6 → ℝ} {c : ℝ}
    (hpos : ∀ i, 0 < w i) (hdfv : DFV w c) :
    w ∈ closure {w' : ZMod 6 → ℝ |
      (∀ i, 0 < w' i) ∧ DFV w' c ∧ ∀ i, w' i ≠ w' (i + 1)} := by
  have hprofile : ∀ᶠ w' in 𝓝 w, (∀ i, 0 < w' i) ∧ DFV w' c := by
    filter_upwards [isOpen_positiveProfile.eventually_mem hpos, hdfv.eventually]
      with w' hw'pos hw'dfv
    exact ⟨hw'pos, hw'dfv⟩
  have hpull := (tendsto_n6IndexPerturbation_zero w).eventually hprofile
  have hpull' : ∀ᶠ ε : ℝ in 𝓝[≠] 0,
      (∀ i, 0 < n6IndexPerturbation w ε i) ∧ DFV (n6IndexPerturbation w ε) c :=
    hpull.filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ ε in 𝓝[≠] 0, n6IndexPerturbation w ε ∈
      {w' : ZMod 6 → ℝ | (∀ i, 0 < w' i) ∧ DFV w' c ∧ ∀ i, w' i ≠ w' (i + 1)} := by
    filter_upwards [hpull', eventually_n6IndexPerturbation_ne_succ w]
      with ε hstable hne
    exact ⟨hstable.1, hstable.2, hne⟩
  have hlimNE : Tendsto (n6IndexPerturbation w) (𝓝[≠] (0 : ℝ)) (𝓝 w) :=
    (tendsto_n6IndexPerturbation_zero w).mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto hlimNE hall

/-- Uniformly interior realizations of the adjacent-unequal stratum pass to a
positive six-profile with adjacent equalities. -/
theorem realizesR2_of_n6_ne_succ_uniform_margin {w : ZMod 6 → ℝ} {c a b eta : ℝ}
    (hpos : ∀ i, 0 < w i) (hdfv : DFV w c) (ha : 0 < a) (heta : 0 < eta)
    (hgeneric : ∀ w' : ZMod 6 → ℝ, (∀ i, 0 < w' i) → DFV w' c →
      (∀ i, w' i ≠ w' (i + 1)) → ∃ ell : ZMod 6 → ℝ,
        (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
        (∀ i, |w' i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
          |w' i| * (ell i / 2) ≤ 1 - eta) ∧
        closureGap w' ell = 0 ∧ turningSum w' ell = 2 * Real.pi) :
    RealizesR2 w := by
  letI : NeZero 6 := ⟨by norm_num⟩
  exact realizesR2_of_mem_closure_uniform_margin (n := 6) (by norm_num)
    hpos ha heta (mem_closure_positive_dfv_ne_succ hpos hdfv) fun w' hw' =>
      hgeneric w' hw'.1 hw'.2.1 hw'.2.2

end Gluck.Discrete
