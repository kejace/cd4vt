/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.ZigzagWords
public import Gluck.Discrete.ZigzagCarrier

/-!
# Quantitative cuts in monotone runs

This file formalizes the combinatorics of the monotone-run extension of the
zigzag argument.  Adjacent small-to-large ratios telescope to endpoint ratios;
a depth bound therefore forces a quantitatively small cut.  Finite cut menus
have a canonical componentwise-minimum selection which exactly detects the
common-allocation chamber.  A cyclic run decomposition connects these menus to
the original profile, locates the first incompatible stratum at `n ≥ 3m`, and
shows that complete-run products recover the ordinary extremal zigzag pair.

The depth result is conditional, and the product compression is algebraic: no
theorem here lifts a compressed carrier certificate through a multi-edge active
run.  That geometric lifting problem is the remaining universal gap.
-/

@[expose] public section

namespace Gluck.Discrete

open scoped BigOperators

/-- The small-to-large ratio on an oriented high-to-low run edge. -/
noncomputable def runRatio (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  x (i + 1) / x i

/-- A positive descending edge has ratio strictly between zero and one. -/
lemma runRatio_mem_Ioo (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) {i : ℕ}
    (hdesc : x (i + 1) < x i) : runRatio x i ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨div_pos (hpos (i + 1)) (hpos i), (div_lt_one (hpos i)).mpr hdesc⟩

/-- The small-to-large ratio on an oriented low-to-high run edge. -/
noncomputable def ascendingRatio (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  x i / x (i + 1)

/-- A positive ascending edge has ratio strictly between zero and one. -/
lemma ascendingRatio_mem_Ioo (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) {i : ℕ}
    (hasc : x i < x (i + 1)) : ascendingRatio x i ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨div_pos (hpos i) (hpos (i + 1)), (div_lt_one (hpos (i + 1))).mpr hasc⟩

/-- Adjacent ratios telescope to the endpoint ratio of a positive run. -/
private lemma prod_runRatio (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (p : ℕ) :
    ∏ i ∈ Finset.range p, runRatio x i = x p / x 0 := by
  induction p with
  | zero => simp [runRatio, (hpos 0).ne']
  | succ p ih =>
      rw [Finset.prod_range_succ, ih]
      simp only [runRatio]
      field_simp [(hpos 0).ne', (hpos p).ne']

/-- Ascending adjacent ratios telescope to the low-to-high endpoint ratio. -/
private lemma prod_ascendingRatio (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (p : ℕ) :
    ∏ i ∈ Finset.range p, ascendingRatio x i = x 0 / x p := by
  induction p with
  | zero => simp [ascendingRatio, (hpos 0).ne']
  | succ p ih =>
      rw [Finset.prod_range_succ, ih]
      simp only [ascendingRatio]
      field_simp [(hpos p).ne', (hpos (p + 1)).ne']

/-- If the endpoint ratio is below `τ ^ p`, some one of the `p` cut ratios is
below `τ`.  This is the multiplicative pigeonhole step behind the depth
criterion. -/
theorem exists_runRatio_lt_of_endpoint_lt_pow (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i)
    (p : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (hdepth : x p / x 0 < τ ^ p) :
    ∃ i < p, runRatio x i < τ := by
  by_contra hcut
  push Not at hcut
  have hprod :
      (∏ _i ∈ Finset.range p, τ) ≤ ∏ i ∈ Finset.range p, runRatio x i := by
    apply Finset.prod_le_prod₀
    · exact fun _i _hi ↦ hτ
    · exact fun i hi ↦ hcut i (Finset.mem_range.mp hi)
  have hendpoint : τ ^ p ≤ x p / x 0 := by
    rw [← prod_runRatio x hpos p]
    simpa using hprod
  exact (not_lt_of_ge hendpoint) hdepth

/-- The ascending analogue of `exists_runRatio_lt_of_endpoint_lt_pow`. -/
theorem exists_ascendingRatio_lt_of_endpoint_lt_pow
    (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (p : ℕ)
    {tau : ℝ} (htau : 0 ≤ tau) (hdepth : x 0 / x p < tau ^ p) :
    ∃ i < p, ascendingRatio x i < tau := by
  by_contra hcut
  push Not at hcut
  have hprod :
      (∏ _i ∈ Finset.range p, tau) ≤ ∏ i ∈ Finset.range p, ascendingRatio x i := by
    apply Finset.prod_le_prod₀
    · exact fun _i _hi ↦ htau
    · exact fun i hi ↦ hcut i (Finset.mem_range.1 hi)
  have hendpoint : tau ^ p ≤ x 0 / x p := by
    rw [← prod_ascendingRatio x hpos p]
    simpa using hprod
  exact (not_lt_of_ge hendpoint) hdepth

/-- Multiplicative pigeonhole in its abstract finite-product form. -/
theorem exists_lt_of_prod_lt_pow (q : ℕ → ℝ) (p : ℕ) {tau : ℝ}
    (htau : 0 ≤ tau)
    (hprod : (∏ i ∈ Finset.range p, q i) < tau ^ p) :
    ∃ i < p, q i < tau := by
  by_contra hcut
  push Not at hcut
  have hle : (∏ _i ∈ Finset.range p, tau) ≤ ∏ i ∈ Finset.range p, q i := by
    apply Finset.prod_le_prod₀
    · exact fun _i _hi ↦ htau
    · exact fun i hi ↦ hcut i (Finset.mem_range.1 hi)
  have : tau ^ p ≤ ∏ i ∈ Finset.range p, q i := by simpa using hle
  exact (not_lt_of_ge this) hprod

/-- Four independent run-depth bounds force cuts whose two cross sums are
strictly below one.  These are exactly the numerical hypotheses of the
common-allocation carrier certificate. -/
theorem exists_allocation_cuts_of_depth
    (A B C D : ℕ → ℝ) (pA pB pC pD : ℕ)
    (hApos : ∀ i, 0 < A i) (hBpos : ∀ i, 0 < B i)
    (hCpos : ∀ i, 0 < C i) (hDpos : ∀ i, 0 < D i)
    (hAdesc : ∀ i < pA, A (i + 1) < A i)
    (hBdesc : ∀ i < pB, B (i + 1) < B i)
    (hCdesc : ∀ i < pC, C (i + 1) < C i)
    (hDdesc : ∀ i < pD, D (i + 1) < D i)
    {α β γ δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hAdepth : A pA / A 0 < α ^ pA) (hBdepth : B pB / B 0 < β ^ pB)
    (hCdepth : C pC / C 0 < γ ^ pC) (hDdepth : D pD / D 0 < δ ^ pD)
    (hshared : β ^ 2 + γ ^ 2 ≤ 1) (houter : α ^ 2 + δ ^ 2 ≤ 1) :
    ∃ iA iB iC iD,
      iA < pA ∧ iB < pB ∧ iC < pC ∧ iD < pD ∧
      runRatio A iA ∈ Set.Ioo (0 : ℝ) 1 ∧
      runRatio B iB ∈ Set.Ioo (0 : ℝ) 1 ∧
      runRatio C iC ∈ Set.Ioo (0 : ℝ) 1 ∧
      runRatio D iD ∈ Set.Ioo (0 : ℝ) 1 ∧
      runRatio B iB ^ 2 + runRatio C iC ^ 2 < 1 ∧
      runRatio A iA ^ 2 + runRatio D iD ^ 2 < 1 := by
  obtain ⟨iA, hiA, hAcut⟩ :=
    exists_runRatio_lt_of_endpoint_lt_pow A hApos pA hα.le hAdepth
  obtain ⟨iB, hiB, hBcut⟩ :=
    exists_runRatio_lt_of_endpoint_lt_pow B hBpos pB hβ.le hBdepth
  obtain ⟨iC, hiC, hCcut⟩ :=
    exists_runRatio_lt_of_endpoint_lt_pow C hCpos pC hγ.le hCdepth
  obtain ⟨iD, hiD, hDcut⟩ :=
    exists_runRatio_lt_of_endpoint_lt_pow D hDpos pD hδ.le hDdepth
  have hAmem := runRatio_mem_Ioo A hApos (hAdesc iA hiA)
  have hBmem := runRatio_mem_Ioo B hBpos (hBdesc iB hiB)
  have hCmem := runRatio_mem_Ioo C hCpos (hCdesc iC hiC)
  have hDmem := runRatio_mem_Ioo D hDpos (hDdesc iD hiD)
  have hAsq : runRatio A iA ^ 2 < α ^ 2 :=
    (sq_lt_sq₀ hAmem.1.le hα.le).mpr hAcut
  have hBsq : runRatio B iB ^ 2 < β ^ 2 :=
    (sq_lt_sq₀ hBmem.1.le hβ.le).mpr hBcut
  have hCsq : runRatio C iC ^ 2 < γ ^ 2 :=
    (sq_lt_sq₀ hCmem.1.le hγ.le).mpr hCcut
  have hDsq : runRatio D iD ^ 2 < δ ^ 2 :=
    (sq_lt_sq₀ hDmem.1.le hδ.le).mpr hDcut
  refine ⟨iA, iB, iC, iD, hiA, hiB, hiC, hiD, hAmem, hBmem, hCmem, hDmem, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-! ## Canonical cut menus -/

/-- The finite menu of ratios available by placing one active cut in a
monotone run.  Multiplicities are irrelevant for cut existence, so the menu
is represented by a nonempty finset. -/
structure RunCutMenu where
  ratios : Finset ℝ
  nonempty : ratios.Nonempty
  ratio_mem_Ioo : ∀ q ∈ ratios, q ∈ Set.Ioo (0 : ℝ) 1

namespace RunCutMenu

/-- The smallest ratio offered by a run. -/
noncomputable def minRatio (M : RunCutMenu) : ℝ :=
  M.ratios.min' M.nonempty

/-- The minimum ratio is an available cut. -/
lemma minRatio_mem (M : RunCutMenu) : M.minRatio ∈ M.ratios := by
  exact Finset.min'_mem M.ratios M.nonempty

/-- The minimum ratio lies strictly between zero and one. -/
lemma minRatio_mem_Ioo (M : RunCutMenu) : M.minRatio ∈ Set.Ioo (0 : ℝ) 1 :=
  M.ratio_mem_Ioo M.minRatio M.minRatio_mem

/-- The minimum ratio is no larger than any available cut ratio. -/
lemma minRatio_le (M : RunCutMenu) {q : ℝ} (hq : q ∈ M.ratios) : M.minRatio ≤ q := by
  exact Finset.min'_le M.ratios q hq

/-- A run menu with a single available ratio. -/
noncomputable def singleton (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) : RunCutMenu where
  ratios := {q}
  nonempty := Finset.singleton_nonempty q
  ratio_mem_Ioo r hr := by simpa only [Finset.mem_singleton.mp hr] using hq

@[simp]
lemma minRatio_singleton (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (singleton q hq).minRatio = q := by
  simp only [minRatio, singleton, Finset.min'_singleton]

/-- The cut menu supplied by the edges of a positive descending run. -/
noncomputable def ofDescendingRun (x : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hpos : ∀ i, 0 < x i) (hdesc : ∀ i < p, x (i + 1) < x i) : RunCutMenu where
  ratios := (Finset.range p).image (runRatio x)
  nonempty := by
    classical
    exact ⟨runRatio x 0, Finset.mem_image.2 ⟨0, Finset.mem_range.2 hp, rfl⟩⟩
  ratio_mem_Ioo := by
    classical
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hq
    exact runRatio_mem_Ioo x hpos (hdesc i (Finset.mem_range.1 hi))

/-- Every element of a run menu is represented by an actual edge index. -/
lemma mem_ofDescendingRun_iff (x : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hpos : ∀ i, 0 < x i) (hdesc : ∀ i < p, x (i + 1) < x i) {q : ℝ} :
    q ∈ (ofDescendingRun x p hp hpos hdesc).ratios ↔
      ∃ i < p, runRatio x i = q := by
  classical
  simp only [ofDescendingRun, Finset.mem_image, Finset.mem_range]

/-- The minimum of a run menu is itself achieved by an actual cut. -/
lemma exists_eq_minRatio_ofDescendingRun (x : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hpos : ∀ i, 0 < x i) (hdesc : ∀ i < p, x (i + 1) < x i) :
    ∃ i < p, runRatio x i = (ofDescendingRun x p hp hpos hdesc).minRatio := by
  exact (mem_ofDescendingRun_iff x p hp hpos hdesc).1
    (ofDescendingRun x p hp hpos hdesc).minRatio_mem

/-- The endpoint-depth estimate bounds the canonical minimum of the run menu. -/
theorem minRatio_lt_of_endpoint_lt_pow (x : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hpos : ∀ i, 0 < x i) (hdesc : ∀ i < p, x (i + 1) < x i)
    {tau : ℝ} (htau : 0 ≤ tau) (hdepth : x p / x 0 < tau ^ p) :
    (ofDescendingRun x p hp hpos hdesc).minRatio < tau := by
  obtain ⟨i, hi, hratio⟩ :=
    exists_runRatio_lt_of_endpoint_lt_pow x hpos p htau hdepth
  apply lt_of_le_of_lt _ hratio
  apply minRatio_le
  exact (mem_ofDescendingRun_iff x p hp hpos hdesc).2 ⟨i, hi, rfl⟩

end RunCutMenu

/-! ## Cyclic run decompositions -/

/-- The two oriented run menus incident to every cyclic low: `down i` runs
from `H_i` to `L_i`, while `up i` runs from `L_i` to `H_(i+1)` and records
each low-to-high edge as its small-to-large ratio. -/
structure CyclicRunMenus (m : ℕ) where
  down : ZMod m → RunCutMenu
  up : ZMod m → RunCutMenu

/-- A cyclic decomposition into strict monotone runs, indexed by alternating
highs `H_i` and lows `L_i`.  The `down` run travels forward from `H_i` to
`L_i`; the `up` run then travels forward from `L_i` to `H_(i+1)`.  The edge
count identity records that these runs make one complete circuit. -/
structure CyclicMonotoneRuns {n m : ℕ} [NeZero n] [NeZero m]
    (w : ZMod n → ℝ) where
  high : ZMod m → ZMod n
  low : ZMod m → ZMod n
  downLength : ZMod m → ℕ
  upLength : ZMod m → ℕ
  downLength_pos : ∀ i, 0 < downLength i
  upLength_pos : ∀ i, 0 < upLength i
  down_end : ∀ i, high i + (downLength i : ZMod n) = low i
  up_end : ∀ i, low i + (upLength i : ZMod n) = high (i + 1)
  down_strict : ∀ i t, t < downLength i →
    w (high i + ((t + 1 : ℕ) : ZMod n)) < w (high i + (t : ZMod n))
  up_strict : ∀ i t, t < upLength i →
    w (low i + (t : ZMod n)) < w (low i + ((t + 1 : ℕ) : ZMod n))
  edge_count : ∑ i, (downLength i + upLength i) = n

namespace CyclicMonotoneRuns

/-- Build a cyclic strict-run decomposition from an alternating enumeration
of extrema with no same-type extremum in the corresponding open run. -/
def ofAlternatingExtrema
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (hne : ∀ j, w j ≠ w (j + 1))
    (high low : ZMod m → ZMod n) (downLength upLength : ZMod m → ℕ)
    (hdownPos : ∀ i, 0 < downLength i) (hupPos : ∀ i, 0 < upLength i)
    (hdownEnd : ∀ i, high i + (downLength i : ZMod n) = low i)
    (hupEnd : ∀ i, low i + (upLength i : ZMod n) = high (i + 1))
    (hhigh : ∀ i, IsStrictLocalMax w (high i))
    (hlow : ∀ i, IsStrictLocalMin w (low i))
    (hnoDown : ∀ i t, t + 1 < downLength i →
      ¬ IsStrictLocalMin w (high i + ((t + 1 : ℕ) : ZMod n)))
    (hnoUp : ∀ i t, t + 1 < upLength i →
      ¬ IsStrictLocalMax w (low i + ((t + 1 : ℕ) : ZMod n)))
    (hedges : ∑ i, (downLength i + upLength i) = n) :
    CyclicMonotoneRuns (n := n) (m := m) w where
  high := high
  low := low
  downLength := downLength
  upLength := upLength
  downLength_pos := hdownPos
  upLength_pos := hupPos
  down_end := hdownEnd
  up_end := hupEnd
  down_strict i t ht := by
    exact (descending_run w hne (hhigh i).2 t
      (fun s hs ↦ hnoDown i s (by omega))).1
  up_strict i t ht := by
    exact (ascending_run w hne (hlow i).2 t
      (fun s hs ↦ hnoUp i s (by omega))).1
  edge_count := hedges

private lemma add_cast_pred_eq_sub_one {n p : ℕ} [NeZero n]
    {a b : ZMod n} (hp : 0 < p) (h : a + (p : ZMod n) = b) :
    a + ((p - 1 : ℕ) : ZMod n) = b - 1 := by
  have hp1 : p - 1 + 1 = p := by omega
  have hcast : (((p - 1 : ℕ) : ZMod n) + 1) = (p : ZMod n) := by
    simpa [Nat.cast_add] using congrArg (fun k : ℕ ↦ (k : ZMod n)) hp1
  calc
    a + ((p - 1 : ℕ) : ZMod n) =
        a + (((p - 1 : ℕ) : ZMod n) + 1) - 1 := by ring
    _ = a + (p : ZMod n) - 1 := by rw [hcast]
    _ = b - 1 := by rw [h]

/-- Every indexed high of a cyclic strict-run decomposition is a strict local
maximum of the underlying word. -/
theorem high_isStrictLocalMax {n m : ℕ} [NeZero n] [NeZero m]
    {w : ZMod n → ℝ} (R : CyclicMonotoneRuns (n := n) (m := m) w)
    (i : ZMod m) : IsStrictLocalMax w (R.high i) := by
  have hupPos := R.upLength_pos (i - 1)
  have hupEnd :
      R.low (i - 1) + (R.upLength (i - 1) : ZMod n) = R.high i := by
    simpa only [sub_add_cancel] using R.up_end (i - 1)
  have hprevIndex :
      R.low (i - 1) + ((R.upLength (i - 1) - 1 : ℕ) : ZMod n) =
        R.high i - 1 :=
    add_cast_pred_eq_sub_one hupPos hupEnd
  have hupLast := R.up_strict (i - 1) (R.upLength (i - 1) - 1) (by omega)
  have hupLastIndex :
      R.low (i - 1) + (((R.upLength (i - 1) - 1) + 1 : ℕ) : ZMod n) =
        R.high i := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R.upLength (i - 1))]
    exact hupEnd
  constructor
  · rwa [hprevIndex, hupLastIndex] at hupLast
  · simpa [Nat.cast_add] using R.down_strict i 0 (R.downLength_pos i)

/-- Every indexed low of a cyclic strict-run decomposition is a strict local
minimum of the underlying word. -/
theorem low_isStrictLocalMin {n m : ℕ} [NeZero n] [NeZero m]
    {w : ZMod n → ℝ} (R : CyclicMonotoneRuns (n := n) (m := m) w)
    (i : ZMod m) : IsStrictLocalMin w (R.low i) := by
  have hdownPos := R.downLength_pos i
  have hprevIndex :
      R.high i + ((R.downLength i - 1 : ℕ) : ZMod n) = R.low i - 1 :=
    add_cast_pred_eq_sub_one hdownPos (R.down_end i)
  have hdownLast := R.down_strict i (R.downLength i - 1) (by omega)
  have hdownLastIndex :
      R.high i + (((R.downLength i - 1) + 1 : ℕ) : ZMod n) = R.low i := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R.downLength i)]
    exact R.down_end i
  constructor
  · rwa [hdownLastIndex, hprevIndex] at hdownLast
  · simpa [Nat.cast_add] using R.up_strict i 0 (R.upLength_pos i)

/-- A carrier center is ordinary-compatible when the ascending run into its
shared high and the descending run out of that high are both single edges. -/
def HasOrdinaryCenter {n m : ℕ} [NeZero n] [NeZero m]
    {w : ZMod n → ℝ} (R : CyclicMonotoneRuns (n := n) (m := m) w)
    (i : ZMod m) : Prop :=
  R.upLength i = 1 ∧ R.downLength (i + 1) = 1

/-- If every shared high has a run vertex on at least one incident side, then
there are at least three edges per high. -/
theorem three_mul_le_of_no_ordinaryCenter
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w)
    (hnone : ∀ i, ¬ R.HasOrdinaryCenter i) : 3 * m ≤ n := by
  have hpoint (j : ZMod m) :
      3 ≤ R.downLength j + R.upLength (j - 1) := by
    have hd := R.downLength_pos j
    have hu := R.upLength_pos (j - 1)
    have hbad := hnone (j - 1)
    have hidx : j - 1 + 1 = j := sub_add_cancel j 1
    unfold HasOrdinaryCenter at hbad
    rw [hidx] at hbad
    omega
  have hsum :
      (∑ _j : ZMod m, 3) ≤
        ∑ j : ZMod m, (R.downLength j + R.upLength (j - 1)) := by
    exact Finset.sum_le_sum fun j _hj ↦ hpoint j
  have hshift :
      (∑ j : ZMod m, R.upLength (j - 1)) = ∑ j : ZMod m, R.upLength j := by
    exact Fintype.sum_equiv (Equiv.subRight (1 : ZMod m)) _ _ (fun _ ↦ rfl)
  have hright :
      (∑ j : ZMod m, (R.downLength j + R.upLength (j - 1))) = n := by
    rw [Finset.sum_add_distrib, hshift, ← Finset.sum_add_distrib]
    exact R.edge_count
  rw [hright] at hsum
  simpa [ZMod.card, Nat.mul_comm] using hsum

/-- Below the sharp threshold `n = 3m`, some consecutive-low carrier retains
the ordinary shared-high/common-low incidence despite the other monotone
runs. -/
theorem exists_ordinaryCenter_of_lt_three_mul
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hn : n < 3 * m) :
    ∃ i, R.HasOrdinaryCenter i := by
  by_contra hnone
  push Not at hnone
  exact (not_lt_of_ge (R.three_mul_le_of_no_ordinaryCenter hnone)) hn

/-! ## The first sharp residue: six edges and four runs -/

/-- Type A in the six-edge/four-run classification: one run has length three
and the other three runs have length one. -/
def SixRunTypeA (a b c d : ℕ) : Prop :=
  (a = 3 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
  (a = 1 ∧ b = 3 ∧ c = 1 ∧ d = 1) ∨
  (a = 1 ∧ b = 1 ∧ c = 3 ∧ d = 1) ∨
  (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 3)

/-- Type B in the six-edge/four-run classification: the two length-two runs
are opposite in the cyclic list. -/
def SixRunTypeB (a b c d : ℕ) : Prop :=
  (a = 2 ∧ b = 1 ∧ c = 2 ∧ d = 1) ∨
  (a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 2)

/-- Type C in the six-edge/four-run classification: the two length-two runs
are adjacent in the cyclic list. -/
def SixRunTypeC (a b c d : ℕ) : Prop :=
  (a = 2 ∧ b = 2 ∧ c = 1 ∧ d = 1) ∨
  (a = 1 ∧ b = 2 ∧ c = 2 ∧ d = 1) ∨
  (a = 1 ∧ b = 1 ∧ c = 2 ∧ d = 2) ∨
  (a = 2 ∧ b = 1 ∧ c = 1 ∧ d = 2)

/-- The two orientations of Type C for which neither shared high is incident
to two single-edge runs. -/
def SixRunTypeCNoCenter (a b c d : ℕ) : Prop :=
  (a = 2 ∧ b = 2 ∧ c = 1 ∧ d = 1) ∨
  (a = 1 ∧ b = 1 ∧ c = 2 ∧ d = 2)

/-- Four natural numbers are positive and sum to six exactly when their cyclic
list has one of the three six-edge/four-run types. -/
theorem sixRunType_iff_pos_and_sum (a b c d : ℕ) :
    SixRunTypeA a b c d ∨ SixRunTypeB a b c d ∨ SixRunTypeC a b c d ↔
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a + b + c + d = 6 := by
  constructor
  · rintro (hA | hB | hC)
    · rcases hA with h | h | h | h <;> omega
    · rcases hB with h | h <;> omega
    · rcases hC with h | h | h | h <;> omega
  · rintro ⟨ha, hb, hc, hd, hsum⟩
    have ha_le : a ≤ 3 := by omega
    have hb_le : b ≤ 3 := by omega
    have hc_le : c ≤ 3 := by omega
    unfold SixRunTypeA SixRunTypeB SixRunTypeC
    interval_cases a <;> interval_cases b <;> interval_cases c <;> omega

/-- Among the classified tuples, excluding both ordinary centers leaves all
of Type B and exactly two orientations of Type C. -/
theorem sixRunType_of_no_ordinary_pattern {a b c d : ℕ}
    (hclass : SixRunTypeA a b c d ∨ SixRunTypeB a b c d ∨ SixRunTypeC a b c d)
    (hzero : ¬(b = 1 ∧ c = 1)) (hone : ¬(d = 1 ∧ a = 1)) :
    SixRunTypeB a b c d ∨ SixRunTypeCNoCenter a b c d := by
  rcases hclass with hA | hB | hC
  · unfold SixRunTypeA at hA
    rcases hA with h | h | h | h <;> omega
  · exact Or.inl hB
  · right
    unfold SixRunTypeC at hC
    unfold SixRunTypeCNoCenter
    rcases hC with h | h | h | h <;> omega

/-- A cyclic decomposition of a six-edge word with two highs and two lows has
one of the three explicit run-length types.  The tuple is ordered as
`down 0, up 0, down 1, up 1`. -/
theorem six_run_length_classification {w : ZMod 6 → ℝ}
    (R : CyclicMonotoneRuns (n := 6) (m := 2) w) :
    SixRunTypeA (R.downLength 0) (R.upLength 0)
        (R.downLength 1) (R.upLength 1) ∨
      SixRunTypeB (R.downLength 0) (R.upLength 0)
        (R.downLength 1) (R.upLength 1) ∨
      SixRunTypeC (R.downLength 0) (R.upLength 0)
        (R.downLength 1) (R.upLength 1) := by
  rw [sixRunType_iff_pos_and_sum]
  refine ⟨R.downLength_pos 0, R.upLength_pos 0,
    R.downLength_pos 1, R.upLength_pos 1, ?_⟩
  have hsum := R.edge_count
  rw [← sum_range_natCast_add
    (fun i : ZMod 2 ↦ R.downLength i + R.upLength i) 0] at hsum
  norm_num [Finset.sum_range_succ] at hsum ⊢
  omega

/-- At the sharp threshold `n = 3m = 6`, failure of both ordinary centers is
equivalent, at the level of run lengths, to the explicit Type B/exceptional
Type C residue. -/
theorem six_run_length_classification_of_no_ordinaryCenter {w : ZMod 6 → ℝ}
    (R : CyclicMonotoneRuns (n := 6) (m := 2) w)
    (hnone : ∀ i, ¬R.HasOrdinaryCenter i) :
    SixRunTypeB (R.downLength 0) (R.upLength 0)
        (R.downLength 1) (R.upLength 1) ∨
      SixRunTypeCNoCenter (R.downLength 0) (R.upLength 0)
        (R.downLength 1) (R.upLength 1) := by
  apply sixRunType_of_no_ordinary_pattern R.six_run_length_classification
  · simpa [HasOrdinaryCenter] using hnone (0 : ZMod 2)
  · have hidx : (1 : ZMod 2) + 1 = 0 := by decide
    simpa only [HasOrdinaryCenter, hidx] using hnone (1 : ZMod 2)

/-- The small-to-large ratio at an edge of a descending cyclic run. -/
noncomputable def downRatio {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (i : ZMod m) (t : ℕ) : ℝ :=
  w (R.high i + ((t + 1 : ℕ) : ZMod n)) /
    w (R.high i + (t : ZMod n))

/-- The small-to-large ratio at an edge of an ascending cyclic run. -/
noncomputable def upRatio {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (i : ZMod m) (t : ℕ) : ℝ :=
  w (R.low i + (t : ZMod n)) /
    w (R.low i + ((t + 1 : ℕ) : ZMod n))

/-- The last descending cut is the ratio of a low to its immediate
predecessor. -/
theorem downRatio_last {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (i : ZMod m) :
    R.downRatio i (R.downLength i - 1) = w (R.low i) / w (R.low i - 1) := by
  have hprev :
      R.high i + ((R.downLength i - 1 : ℕ) : ZMod n) = R.low i - 1 :=
    add_cast_pred_eq_sub_one (R.downLength_pos i) (R.down_end i)
  have hdownPos := R.downLength_pos i
  have hlast :
      R.high i + (((R.downLength i - 1) + 1 : ℕ) : ZMod n) = R.low i := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R.downLength i)]
    exact R.down_end i
  rw [downRatio, hlast, hprev]

/-- The first ascending cut is the ratio of a low to its immediate
successor. -/
theorem upRatio_zero {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (i : ZMod m) :
    R.upRatio i 0 = w (R.low i) / w (R.low i + 1) := by
  simp only [upRatio, Nat.cast_zero, add_zero, zero_add, Nat.cast_one]

/-- At a one-edge ascending run, its unique ratio uses the extremal low and
the shared high. -/
theorem upRatio_zero_of_length_one
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (i : ZMod m)
    (h : R.upLength i = 1) :
    R.upRatio i 0 = w (R.low i) / w (R.high (i + 1)) := by
  have hend : R.low i + 1 = R.high (i + 1) := by
    simpa only [h, Nat.cast_one] using R.up_end i
  rw [R.upRatio_zero i, hend]

/-- At a one-edge descending run, its unique ratio uses the shared high and
the extremal low. -/
theorem downRatio_zero_of_length_one
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (i : ZMod m)
    (h : R.downLength i = 1) :
    R.downRatio i 0 = w (R.low i) / w (R.high i) := by
  have hend : R.high i + 1 = R.low i := by
    simpa only [h, Nat.cast_one] using R.down_end i
  simp only [downRatio, Nat.cast_zero, add_zero, zero_add, Nat.cast_one, hend]

/-- Exact ratio incidence retained at an ordinary-compatible center.  The
middle two ratios share the denominator `H_(i+1)`; each outer/middle pair
shares its low numerator. -/
theorem ordinaryCenter_ratio_incidence
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) {i : ZMod m}
    (h : R.HasOrdinaryCenter i) :
    R.downRatio i (R.downLength i - 1) =
        w (R.low i) / w (R.low i - 1) ∧
      R.upRatio i 0 = w (R.low i) / w (R.high (i + 1)) ∧
      R.downRatio (i + 1) 0 = w (R.low (i + 1)) / w (R.high (i + 1)) ∧
      R.upRatio (i + 1) 0 = w (R.low (i + 1)) / w (R.low (i + 1) + 1) := by
  refine ⟨R.downRatio_last i, R.upRatio_zero_of_length_one i h.1, ?_,
    R.upRatio_zero (i + 1)⟩
  exact R.downRatio_zero_of_length_one (i + 1) h.2

/-- Every descending-run cut ratio lies strictly between zero and one. -/
lemma downRatio_mem_Ioo {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) {t : ℕ} (ht : t < R.downLength i) :
    R.downRatio i t ∈ Set.Ioo (0 : ℝ) 1 := by
  have hden : 0 < w (R.high i + (t : ZMod n)) := hpos _
  exact ⟨div_pos (hpos _) hden, (div_lt_one hden).2 (R.down_strict i t ht)⟩

/-- Every ascending-run cut ratio lies strictly between zero and one. -/
lemma upRatio_mem_Ioo {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) {t : ℕ} (ht : t < R.upLength i) :
    R.upRatio i t ∈ Set.Ioo (0 : ℝ) 1 := by
  have hden : 0 < w (R.low i + ((t + 1 : ℕ) : ZMod n)) := hpos _
  exact ⟨div_pos (hpos _) hden, (div_lt_one hden).2 (R.up_strict i t ht)⟩

/-- The product of all descending ratios in one run is its extremal endpoint
ratio. -/
theorem prod_downRatio_eq_endpoint
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) :
    (∏ t ∈ Finset.range (R.downLength i), R.downRatio i t) =
      w (R.low i) / w (R.high i) := by
  let x : ℕ → ℝ := fun t ↦ w (R.high i + (t : ZMod n))
  have hxpos : ∀ t, 0 < x t := fun t ↦ hpos _
  have hprod := prod_runRatio x hxpos (R.downLength i)
  simpa only [runRatio, downRatio, x, Nat.cast_zero, add_zero, R.down_end i] using hprod

/-- The product of all ascending ratios in one run is its extremal endpoint
ratio. -/
theorem prod_upRatio_eq_endpoint
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) :
    (∏ t ∈ Finset.range (R.upLength i), R.upRatio i t) =
      w (R.low i) / w (R.high (i + 1)) := by
  let x : ℕ → ℝ := fun t ↦ w (R.low i + (t : ZMod n))
  have hxpos : ∀ t, 0 < x t := fun t ↦ hpos _
  have hprod := prod_ascendingRatio x hxpos (R.upLength i)
  simpa only [ascendingRatio, upRatio, x, Nat.cast_zero, add_zero, R.up_end i] using hprod

/-- Although selecting one ratio from each run need not preserve product
balance, the products of all descending and all ascending run ratios agree
exactly.  This is the balance available to a richer all-edge carrier. -/
theorem prod_all_downRatio_eq_prod_all_upRatio
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j) :
    (∏ i : ZMod m, ∏ t ∈ Finset.range (R.downLength i), R.downRatio i t) =
      ∏ i : ZMod m, ∏ t ∈ Finset.range (R.upLength i), R.upRatio i t := by
  simp_rw [R.prod_downRatio_eq_endpoint hpos, R.prod_upRatio_eq_endpoint hpos,
    Finset.prod_div_distrib]
  congr 1
  have hshift : (∏ i : ZMod m, w (R.high (i + 1))) =
      ∏ i : ZMod m, w (R.high i) := by
    exact Fintype.prod_equiv (Equiv.addRight (1 : ZMod m)) _ _ (fun _ ↦ rfl)
  exact hshift.symm

/-- A low endpoint lies strictly below the high at the start of its
descending run. -/
theorem low_lt_high {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) : w (R.low i) < w (R.high i) := by
  have hnonempty : (Finset.range (R.downLength i)).Nonempty := by
    exact ⟨0, Finset.mem_range.2 (R.downLength_pos i)⟩
  have hprod :
      (∏ t ∈ Finset.range (R.downLength i), R.downRatio i t) < 1 := by
    have hlt :
        (∏ t ∈ Finset.range (R.downLength i), R.downRatio i t) <
          ∏ _t ∈ Finset.range (R.downLength i), (1 : ℝ) := by
      apply Finset.prod_lt_prod_of_nonempty₀
      · exact fun t ht ↦ (R.downRatio_mem_Ioo hpos i (Finset.mem_range.1 ht)).1
      · exact fun t ht ↦ (R.downRatio_mem_Ioo hpos i (Finset.mem_range.1 ht)).2
      · exact hnonempty
    simpa using hlt
  rw [R.prod_downRatio_eq_endpoint hpos i] at hprod
  exact (div_lt_one (hpos (R.high i))).1 hprod

/-- A low endpoint lies strictly below the high at the end of its ascending
run. -/
theorem low_lt_next_high {n m : ℕ} [NeZero n] [NeZero m]
    {w : ZMod n → ℝ} (R : CyclicMonotoneRuns (n := n) (m := m) w)
    (hpos : ∀ j, 0 < w j) (i : ZMod m) :
    w (R.low i) < w (R.high (i + 1)) := by
  have hnonempty : (Finset.range (R.upLength i)).Nonempty := by
    exact ⟨0, Finset.mem_range.2 (R.upLength_pos i)⟩
  have hprod :
      (∏ t ∈ Finset.range (R.upLength i), R.upRatio i t) < 1 := by
    have hlt :
        (∏ t ∈ Finset.range (R.upLength i), R.upRatio i t) <
          ∏ _t ∈ Finset.range (R.upLength i), (1 : ℝ) := by
      apply Finset.prod_lt_prod_of_nonempty₀
      · exact fun t ht ↦ (R.upRatio_mem_Ioo hpos i (Finset.mem_range.1 ht)).1
      · exact fun t ht ↦ (R.upRatio_mem_Ioo hpos i (Finset.mem_range.1 ht)).2
      · exact hnonempty
    simpa using hlt
  rw [R.prod_upRatio_eq_endpoint hpos i] at hprod
  exact (div_lt_one (hpos (R.high (i + 1)))).1 hprod

/-- The cyclic profile of extremal highs extracted from a run
decomposition. -/
def extremaHigh {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) : ZMod m → ℝ :=
  fun i ↦ w (R.high i)

/-- The cyclic profile of extremal lows extracted from a run decomposition. -/
def extremaLow {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) : ZMod m → ℝ :=
  fun i ↦ w (R.low i)

/-- Compressing every monotone run to its endpoints produces an ordinary
zigzag pair. -/
theorem extrema_zigzagPair {n m : ℕ} [NeZero n] [NeZero m]
    {w : ZMod n → ℝ} (R : CyclicMonotoneRuns (n := n) (m := m) w)
    (hpos : ∀ j, 0 < w j) : ZigzagPair R.extremaHigh R.extremaLow := by
  intro i
  exact ⟨hpos (R.low i), R.low_lt_high hpos i, R.low_lt_next_high hpos i⟩

/-- The product of a complete descending run is exactly the first zigzag
ratio of the compressed extremal word. -/
theorem prod_downRatio_eq_zigzagRatioA
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) :
    (∏ t ∈ Finset.range (R.downLength i), R.downRatio i t) =
      zigzagRatioA R.extremaHigh R.extremaLow i := by
  rw [R.prod_downRatio_eq_endpoint hpos i]
  rfl

/-- The product of a complete ascending run is exactly the second zigzag
ratio of the compressed extremal word. -/
theorem prod_upRatio_eq_zigzagRatioB
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) :
    (∏ t ∈ Finset.range (R.upLength i), R.upRatio i t) =
      zigzagRatioB R.extremaHigh R.extremaLow i := by
  rw [R.prod_upRatio_eq_endpoint hpos i]
  rfl

/-- The complete zigzag carrier-selection theorem applies verbatim to the
product-compressed extremal word.  This is an algebraic compression theorem,
not yet a geometric lifting theorem for the intervening run vertices. -/
theorem exists_compressed_carrier_certificate
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    {Alloc Opp : ZMod m → Prop}
    (halloc : ∀ i,
      crossShared R.extremaHigh R.extremaLow i < 1 →
      crossOuter R.extremaHigh R.extremaLow i < 1 → Alloc i)
    (hendpoint : ∀ i,
      1 ≤ crossShared R.extremaHigh R.extremaLow i →
      crossOuter R.extremaHigh R.extremaLow i < 1 → Opp i)
    (hwall : (∀ i, 1 ≤ crossOuter R.extremaHigh R.extremaLow i) →
      ∀ i, ¬ Opp i →
        (R.extremaLow i ≤ R.extremaLow (i + 1) →
          0 < zigzagSelectorPlus R.extremaHigh R.extremaLow i) ∧
        (R.extremaLow (i + 1) ≤ R.extremaLow i →
          0 < zigzagSelectorMinus R.extremaHigh R.extremaLow i)) :
    ∃ i, Alloc i ∨ Opp i := by
  exact exists_carrier_certificate (R.extrema_zigzagPair hpos)
    halloc hendpoint hwall

/-- The actual edge ratios of a descending cyclic run, as a finite cut menu. -/
noncomputable def downMenu {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) :
    RunCutMenu where
  ratios := (Finset.range (R.downLength i)).image (R.downRatio i)
  nonempty := by
    classical
    exact ⟨R.downRatio i 0, Finset.mem_image.2
      ⟨0, Finset.mem_range.2 (R.downLength_pos i), rfl⟩⟩
  ratio_mem_Ioo := by
    classical
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hq
    exact R.downRatio_mem_Ioo hpos i (Finset.mem_range.1 ht)

/-- The actual edge ratios of an ascending cyclic run, as a finite cut menu. -/
noncomputable def upMenu {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) :
    RunCutMenu where
  ratios := (Finset.range (R.upLength i)).image (R.upRatio i)
  nonempty := by
    classical
    exact ⟨R.upRatio i 0, Finset.mem_image.2
      ⟨0, Finset.mem_range.2 (R.upLength_pos i), rfl⟩⟩
  ratio_mem_Ioo := by
    classical
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hq
    exact R.upRatio_mem_Ioo hpos i (Finset.mem_range.1 ht)

/-- Forget the locations of a cyclic run decomposition and retain exactly
the finite ratio menus relevant to carrier cut selection. -/
noncomputable def menus {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j) :
    CyclicRunMenus m where
  down i := R.downMenu hpos i
  up i := R.upMenu hpos i

/-- A descending menu entry is represented by an actual edge of that run. -/
lemma mem_downMenu_iff {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) {q : ℝ} :
    q ∈ (R.downMenu hpos i).ratios ↔
      ∃ t < R.downLength i, R.downRatio i t = q := by
  classical
  simp only [downMenu, Finset.mem_image, Finset.mem_range]

/-- An ascending menu entry is represented by an actual edge of that run. -/
lemma mem_upMenu_iff {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) {q : ℝ} :
    q ∈ (R.upMenu hpos i).ratios ↔
      ∃ t < R.upLength i, R.upRatio i t = q := by
  classical
  simp only [upMenu, Finset.mem_image, Finset.mem_range]

/-- A depth bound between the endpoints of a cyclic descending run bounds
the canonical minimum cut in its menu. -/
theorem downMinRatio_lt_of_endpoint_lt_pow
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) {tau : ℝ} (htau : 0 ≤ tau)
    (hdepth : w (R.low i) / w (R.high i) < tau ^ R.downLength i) :
    (R.downMenu hpos i).minRatio < tau := by
  let x : ℕ → ℝ := fun t ↦ w (R.high i + (t : ZMod n))
  have hxpos : ∀ t, 0 < x t := fun t ↦ hpos _
  have hxzero : x 0 = w (R.high i) := by simp only [x, Nat.cast_zero, add_zero]
  have hxend : x (R.downLength i) = w (R.low i) := by
    simp only [x, R.down_end i]
  have hxdepth : x (R.downLength i) / x 0 < tau ^ R.downLength i := by
    rwa [hxend, hxzero]
  obtain ⟨t, ht, hratio⟩ :=
    exists_runRatio_lt_of_endpoint_lt_pow x hxpos (R.downLength i) htau hxdepth
  apply lt_of_le_of_lt _ hratio
  apply RunCutMenu.minRatio_le
  apply (R.mem_downMenu_iff hpos i).2
  exact ⟨t, ht, rfl⟩

/-- A depth bound between the endpoints of a cyclic ascending run bounds the
canonical minimum cut in its menu. -/
theorem upMinRatio_lt_of_endpoint_lt_pow
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) {tau : ℝ} (htau : 0 ≤ tau)
    (hdepth : w (R.low i) / w (R.high (i + 1)) < tau ^ R.upLength i) :
    (R.upMenu hpos i).minRatio < tau := by
  let x : ℕ → ℝ := fun t ↦ w (R.low i + (t : ZMod n))
  have hxpos : ∀ t, 0 < x t := fun t ↦ hpos _
  have hxzero : x 0 = w (R.low i) := by simp only [x, Nat.cast_zero, add_zero]
  have hxend : x (R.upLength i) = w (R.high (i + 1)) := by
    simp only [x, R.up_end i]
  have hxdepth : x 0 / x (R.upLength i) < tau ^ R.upLength i := by
    rwa [hxzero, hxend]
  obtain ⟨t, ht, hratio⟩ :=
    exists_ascendingRatio_lt_of_endpoint_lt_pow x hxpos (R.upLength i) htau hxdepth
  apply lt_of_le_of_lt _ hratio
  apply RunCutMenu.minRatio_le
  apply (R.mem_upMenu_iff hpos i).2
  exact ⟨t, ht, rfl⟩

end CyclicMonotoneRuns

/-! ## Simultaneous cut selections -/

/-- A simultaneous choice of one cut ratio in every monotone run. -/
structure RunCutSelection {m : ℕ} (M : CyclicRunMenus m) where
  down : ZMod m → ℝ
  up : ZMod m → ℝ
  down_mem : ∀ i, down i ∈ (M.down i).ratios
  up_mem : ∀ i, up i ∈ (M.up i).ratios

namespace RunCutSelection

/-- The shared-high cross sum of a selected consecutive-low carrier. -/
noncomputable def crossShared {m : ℕ} {M : CyclicRunMenus m}
    (s : RunCutSelection M) (i : ZMod m) : ℝ :=
  s.up i ^ 2 + s.down (i + 1) ^ 2

/-- The outer-high cross sum of a selected consecutive-low carrier. -/
noncomputable def crossOuter {m : ℕ} {M : CyclicRunMenus m}
    (s : RunCutSelection M) (i : ZMod m) : ℝ :=
  s.down i ^ 2 + s.up (i + 1) ^ 2

/-- The selected carrier lies in the common-allocation chamber. -/
def HasAllocationAt {m : ℕ} {M : CyclicRunMenus m}
    (s : RunCutSelection M) (i : ZMod m) : Prop :=
  s.crossShared i < 1 ∧ s.crossOuter i < 1

end RunCutSelection

namespace CyclicRunMenus

/-- Choose the smallest available ratio in every run. -/
noncomputable def minimum {m : ℕ} (M : CyclicRunMenus m) : RunCutSelection M where
  down i := (M.down i).minRatio
  up i := (M.up i).minRatio
  down_mem i := (M.down i).minRatio_mem
  up_mem i := (M.up i).minRatio_mem

/-- The cyclic system in which every descending run offers `a` and every
reverse-ascending run offers `b`. -/
noncomputable def uniform (m : ℕ) (a b : ℝ)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    CyclicRunMenus m where
  down _ := RunCutMenu.singleton a ha
  up _ := RunCutMenu.singleton b hb

@[simp]
lemma minimum_uniform_down {m : ℕ} {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) (i : ZMod m) :
    (uniform m a b ha hb).minimum.down i = a := by
  simp only [minimum, uniform, RunCutMenu.minRatio_singleton]

@[simp]
lemma minimum_uniform_up {m : ℕ} {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) (i : ZMod m) :
    (uniform m a b ha hb).minimum.up i = b := by
  simp only [minimum, uniform, RunCutMenu.minRatio_singleton]

end CyclicRunMenus

namespace RunCutSelection

/-- The minimum selection is pointwise no larger than every other selection. -/
lemma minimum_le {m : ℕ} {M : CyclicRunMenus m} (s : RunCutSelection M) (i : ZMod m) :
    (M.minimum).down i ≤ s.down i ∧ (M.minimum).up i ≤ s.up i := by
  exact ⟨(M.down i).minRatio_le (s.down_mem i),
    (M.up i).minRatio_le (s.up_mem i)⟩

/-- The minimum selection simultaneously minimizes every shared cross sum. -/
lemma minimum_crossShared_le {m : ℕ} {M : CyclicRunMenus m}
    (s : RunCutSelection M) (i : ZMod m) :
    M.minimum.crossShared i ≤ s.crossShared i := by
  have hu := (minimum_le s i).2
  have hd := (minimum_le s (i + 1)).1
  have humin := (M.up i).minRatio_mem_Ioo.1.le
  have hus := (M.up i).ratio_mem_Ioo (s.up i) (s.up_mem i)
  have hdmin := (M.down (i + 1)).minRatio_mem_Ioo.1.le
  have hds := (M.down (i + 1)).ratio_mem_Ioo (s.down (i + 1)) (s.down_mem (i + 1))
  exact add_le_add ((sq_le_sq₀ humin hus.1.le).2 hu)
    ((sq_le_sq₀ hdmin hds.1.le).2 hd)

/-- The minimum selection simultaneously minimizes every outer cross sum. -/
lemma minimum_crossOuter_le {m : ℕ} {M : CyclicRunMenus m}
    (s : RunCutSelection M) (i : ZMod m) :
    M.minimum.crossOuter i ≤ s.crossOuter i := by
  have hd := (minimum_le s i).1
  have hu := (minimum_le s (i + 1)).2
  have hdmin := (M.down i).minRatio_mem_Ioo.1.le
  have hds := (M.down i).ratio_mem_Ioo (s.down i) (s.down_mem i)
  have humin := (M.up (i + 1)).minRatio_mem_Ioo.1.le
  have hus := (M.up (i + 1)).ratio_mem_Ioo (s.up (i + 1)) (s.up_mem (i + 1))
  exact add_le_add ((sq_le_sq₀ hdmin hds.1.le).2 hd)
    ((sq_le_sq₀ humin hus.1.le).2 hu)

/-- Any allocation carrier available under arbitrary cuts is still an
allocation carrier under the single componentwise-minimum selection. -/
theorem minimum_hasAllocationAt {m : ℕ} {M : CyclicRunMenus m}
    {s : RunCutSelection M} {i : ZMod m} (h : s.HasAllocationAt i) :
    M.minimum.HasAllocationAt i := by
  exact ⟨lt_of_le_of_lt (minimum_crossShared_le s i) h.1,
    lt_of_le_of_lt (minimum_crossOuter_le s i) h.2⟩

/-- There is no global conflict among cut choices for the allocation branch:
some selection has an allocation carrier if and only if the canonical
minimum selection has one. -/
theorem exists_allocation_iff_minimum {m : ℕ} (M : CyclicRunMenus m) :
    (∃ s : RunCutSelection M, ∃ i, s.HasAllocationAt i) ↔
      ∃ i, M.minimum.HasAllocationAt i := by
  constructor
  · rintro ⟨s, i, hi⟩
    exact ⟨i, minimum_hasAllocationAt hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨M.minimum, i, hi⟩

/-- Equivalently, the minimum selection detects the exact residue in which
every possible cut selection misses the allocation chamber. -/
theorem no_allocation_iff_minimum {m : ℕ} (M : CyclicRunMenus m) :
    (∀ s : RunCutSelection M, ∀ i, ¬ s.HasAllocationAt i) ↔
      ∀ i, ¬ M.minimum.HasAllocationAt i := by
  constructor
  · exact fun h i hi ↦ h M.minimum i hi
  · exact fun h s i hi ↦ h i (minimum_hasAllocationAt hi)

/-- A uniform pair of run menus is completely allocation-obstructed as soon
as its (necessarily constant) cross sum is heavy. -/
theorem no_allocation_uniform_of_heavy {m : ℕ} {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hheavy : 1 ≤ a ^ 2 + b ^ 2) :
    ∀ s : RunCutSelection (CyclicRunMenus.uniform m a b ha hb),
      ∀ i, ¬ s.HasAllocationAt i := by
  rw [no_allocation_iff_minimum]
  intro i hi
  have hcross :
      (CyclicRunMenus.uniform m a b ha hb).minimum.crossOuter i =
        a ^ 2 + b ^ 2 := by
    simp only [crossOuter, CyclicRunMenus.minimum_uniform_down,
      CyclicRunMenus.minimum_uniform_up]
  exact (not_lt_of_ge hheavy) (hcross ▸ hi.2)

/-- Exact obstruction from the repeated word `(100,90,81)`: descending
menus contain only `9/10`, reverse-ascending menus only `81/100`, and no
choice of cuts reaches the common-allocation chamber. -/
theorem no_allocation_nine_tenths_eighty_one_hundredths :
    ∀ s : RunCutSelection (CyclicRunMenus.uniform 2 (9 / 10) (81 / 100)
      (by norm_num) (by norm_num)), ∀ i, ¬ s.HasAllocationAt i := by
  apply no_allocation_uniform_of_heavy
  norm_num

end RunCutSelection

namespace CyclicMonotoneRuns

/-- Four quantitative endpoint-depth bounds on the runs surrounding a
carrier put the canonical minimum selection in the allocation chamber. -/
theorem minimum_hasAllocationAt_of_endpoint_depth
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) {alpha beta gamma delta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hgamma : 0 < gamma) (hdelta : 0 < delta)
    (hAdepth : w (R.low i) / w (R.high i) < alpha ^ R.downLength i)
    (hBdepth : w (R.low i) / w (R.high (i + 1)) < beta ^ R.upLength i)
    (hCdepth : w (R.low (i + 1)) / w (R.high (i + 1)) <
      gamma ^ R.downLength (i + 1))
    (hDdepth : w (R.low (i + 1)) / w (R.high (i + 2)) <
      delta ^ R.upLength (i + 1))
    (hshared : beta ^ 2 + gamma ^ 2 ≤ 1)
    (houter : alpha ^ 2 + delta ^ 2 ≤ 1) :
    (R.menus hpos).minimum.HasAllocationAt i := by
  have ha : (R.menus hpos).minimum.down i < alpha := by
    simpa only [CyclicRunMenus.minimum, menus] using
      R.downMinRatio_lt_of_endpoint_lt_pow hpos i halpha.le hAdepth
  have hb : (R.menus hpos).minimum.up i < beta := by
    simpa only [CyclicRunMenus.minimum, menus] using
      R.upMinRatio_lt_of_endpoint_lt_pow hpos i hbeta.le hBdepth
  have hc : (R.menus hpos).minimum.down (i + 1) < gamma := by
    simpa only [CyclicRunMenus.minimum, menus] using
      R.downMinRatio_lt_of_endpoint_lt_pow hpos (i + 1) hgamma.le hCdepth
  have hDdepth' : w (R.low (i + 1)) / w (R.high (i + 1 + 1)) <
      delta ^ R.upLength (i + 1) := by
    have hidx : i + 1 + 1 = i + 2 := by ring
    rwa [hidx]
  have hd : (R.menus hpos).minimum.up (i + 1) < delta := by
    simpa only [CyclicRunMenus.minimum, menus] using
      R.upMinRatio_lt_of_endpoint_lt_pow hpos (i + 1) hdelta.le hDdepth'
  have haMem := (R.menus hpos).down i |>.ratio_mem_Ioo _
    ((R.menus hpos).minimum.down_mem i)
  have hbMem := (R.menus hpos).up i |>.ratio_mem_Ioo _
    ((R.menus hpos).minimum.up_mem i)
  have hcMem := (R.menus hpos).down (i + 1) |>.ratio_mem_Ioo _
    ((R.menus hpos).minimum.down_mem (i + 1))
  have hdMem := (R.menus hpos).up (i + 1) |>.ratio_mem_Ioo _
    ((R.menus hpos).minimum.up_mem (i + 1))
  have haSq := (sq_lt_sq₀ haMem.1.le halpha.le).2 ha
  have hbSq := (sq_lt_sq₀ hbMem.1.le hbeta.le).2 hb
  have hcSq := (sq_lt_sq₀ hcMem.1.le hgamma.le).2 hc
  have hdSq := (sq_lt_sq₀ hdMem.1.le hdelta.le).2 hd
  constructor
  · simp only [RunCutSelection.crossShared]
    nlinarith
  · simp only [RunCutSelection.crossOuter]
    nlinarith

/-- The endpoint-depth criterion produces an actual simultaneous selection
of one cut in every run and an allocation carrier at the prescribed index. -/
theorem exists_selection_hasAllocationAt_of_endpoint_depth
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w) (hpos : ∀ j, 0 < w j)
    (i : ZMod m) {alpha beta gamma delta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hgamma : 0 < gamma) (hdelta : 0 < delta)
    (hAdepth : w (R.low i) / w (R.high i) < alpha ^ R.downLength i)
    (hBdepth : w (R.low i) / w (R.high (i + 1)) < beta ^ R.upLength i)
    (hCdepth : w (R.low (i + 1)) / w (R.high (i + 1)) <
      gamma ^ R.downLength (i + 1))
    (hDdepth : w (R.low (i + 1)) / w (R.high (i + 2)) <
      delta ^ R.upLength (i + 1))
    (hshared : beta ^ 2 + gamma ^ 2 ≤ 1)
    (houter : alpha ^ 2 + delta ^ 2 ≤ 1) :
    ∃ s : RunCutSelection (R.menus hpos), s.HasAllocationAt i := by
  exact ⟨(R.menus hpos).minimum,
    R.minimum_hasAllocationAt_of_endpoint_depth hpos i halpha hbeta hgamma hdelta
      hAdepth hBdepth hCdepth hDdepth hshared houter⟩

end CyclicMonotoneRuns

/-! ## A product-balanced replacement for the high-neighbour argument -/

/-- Two positive cyclic families with equal products have a weak crossing:
`a i ≤ b i` followed by `b (i+1) ≤ a (i+1)`. -/
theorem exists_ratio_crossing_of_prod_eq {m : ℕ} [NeZero m]
    (a b : ZMod m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hprod : (∏ i, a i) = ∏ i, b i) :
    ∃ i, a i ≤ b i ∧ b (i + 1) ≤ a (i + 1) := by
  classical
  have hstart : ∃ j, a j ≤ b j := by
    by_contra hall
    push Not at hall
    have hlt : (∏ i, b i) < ∏ i, a i := by
      apply Finset.prod_lt_prod_of_nonempty₀
      · exact fun i _hi ↦ hb i
      · exact fun i _hi ↦ hall i
      · exact Finset.univ_nonempty
    rw [hprod] at hlt
    exact (lt_irrefl _ hlt)
  obtain ⟨j, hj⟩ := hstart
  by_contra hcross
  have hstep (i : ZMod m) (hi : a i ≤ b i) : a (i + 1) < b (i + 1) := by
    by_contra hnext
    exact hcross ⟨i, hi, le_of_not_gt hnext⟩
  have hiter : ∀ t : ℕ,
      a (j + ((t + 1 : ℕ) : ZMod m)) < b (j + ((t + 1 : ℕ) : ZMod m)) := by
    intro t
    induction t with
    | zero => simpa using hstep j hj
    | succ t ih =>
        have hs := hstep (j + ((t + 1 : ℕ) : ZMod m)) ih.le
        have hidx :
            j + ((t + 1 : ℕ) : ZMod m) + 1 =
              j + ((t + 2 : ℕ) : ZMod m) := by
          simp [Nat.cast_add]
          ring
        rw [hidx] at hs
        simpa only [Nat.cast_succ] using hs
  have hallStrict : ∀ i, a i < b i := by
    intro i
    let z : ZMod m := i - j - 1
    have hz : ((z.val : ℕ) : ZMod m) = z := ZMod.natCast_zmod_val z
    have hs := hiter z.val
    have hidx : j + ((z.val + 1 : ℕ) : ZMod m) = i := by
      rw [Nat.cast_add, hz]
      dsimp only [z]
      ring
    rw [hidx] at hs
    exact hs
  have hlt : (∏ i, a i) < ∏ i, b i := by
    apply Finset.prod_lt_prod_of_nonempty₀
    · exact fun i _hi ↦ ha i
    · exact fun i _hi ↦ hallStrict i
    · exact Finset.univ_nonempty
  rw [hprod] at hlt
  exact (lt_irrefl _ hlt)

/-- If failure of a local certificate forces the mixed selector disjunction,
product balance of the chosen flanking ratios forces a successful carrier.
This is a quantitative substitute for the common-numerator telescoping used
by an ordinary zigzag carrier. -/
theorem exists_of_balanced_ratio_selector {m : ℕ} [NeZero m]
    {a b : ZMod m → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hprod : (∏ i, a i) = ∏ i, b i) {P : ZMod m → Prop}
    (hloc : ∀ i, ¬P i → b i < a i ∨ a (i + 1) < b (i + 1)) :
    ∃ i, P i := by
  obtain ⟨i, hi, hnext⟩ := exists_ratio_crossing_of_prod_eq a b ha hb hprod
  by_contra hall
  push Not at hall
  rcases hloc i (hall i) with hbad | hbad
  · exact (not_lt_of_ge hi) hbad
  · exact (not_lt_of_ge hnext) hbad

namespace CyclicMonotoneRuns

/-- The whole-run analogue of the outer-heavy ratio crossing.  Although a
one-cut transversal need not be product-balanced, retaining every factor in
every run always supplies a descending/ascending crossing at two consecutive
lows. -/
theorem exists_completeRunRatioCrossing
    {n m : ℕ} [NeZero n] [NeZero m] {w : ZMod n → ℝ}
    (R : CyclicMonotoneRuns (n := n) (m := m) w)
    (hpos : ∀ j, 0 < w j) :
    ∃ i,
      (∏ t ∈ Finset.range (R.downLength i), R.downRatio i t) ≤
          ∏ t ∈ Finset.range (R.upLength i), R.upRatio i t ∧
        (∏ t ∈ Finset.range (R.upLength (i + 1)), R.upRatio (i + 1) t) ≤
          ∏ t ∈ Finset.range (R.downLength (i + 1)),
            R.downRatio (i + 1) t := by
  let a : ZMod m → ℝ := fun i ↦
    ∏ t ∈ Finset.range (R.downLength i), R.downRatio i t
  let b : ZMod m → ℝ := fun i ↦
    ∏ t ∈ Finset.range (R.upLength i), R.upRatio i t
  have ha : ∀ i, 0 < a i := by
    intro i
    apply Finset.prod_pos
    intro t ht
    exact (R.downRatio_mem_Ioo hpos i (Finset.mem_range.1 ht)).1
  have hb : ∀ i, 0 < b i := by
    intro i
    apply Finset.prod_pos
    intro t ht
    exact (R.upRatio_mem_Ioo hpos i (Finset.mem_range.1 ht)).1
  have hprod : (∏ i, a i) = ∏ i, b i := by
    exact R.prod_all_downRatio_eq_prod_all_upRatio hpos
  simpa only [a, b] using
    exists_ratio_crossing_of_prod_eq a b ha hb hprod

end CyclicMonotoneRuns

end Gluck.Discrete
