/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.CyclicComponents

/-!
# Strictly convex cyclic chord geometry

This module derives the arbitrary-chord separation and crossing geometry used
in Dahlberg's Lemmas 4 and 6 from strict support at the polygon edges.  Its
proof is finite and algebraic: a Plücker identity propagates the orientation
of consecutive triples to all cyclically ordered triples.
-/

namespace Gluck.Forward.CyclicChordGeometry

open scoped Pointwise Real

/-- Every vertex outside an oriented polygon edge lies strictly to its left. -/
def CyclicChordStrictConvexEdgeSupport {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 →
    0 < Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v j)

private theorem cyclicLift_succ {n : ℕ} (c : ZMod n) (k : ℕ) :
    cyclicLift c (k + 1) = cyclicLift c k + 1 := by
  unfold cyclicLift
  push_cast
  ring

private theorem crossR2_cyclic {A B C : ℂ} :
    Gluck.Discrete.crossR2 A B C = Gluck.Discrete.crossR2 B C A := by
  exact (Gluck.Discrete.crossR2_cycle A B C).symm

private theorem crossR2_swap {A B C : ℂ} :
    Gluck.Discrete.crossR2 A B C = -Gluck.Discrete.crossR2 A C B := by
  exact Gluck.Discrete.crossR2_swap A C B

private theorem crossR2_swap_first {A B C : ℂ} :
    Gluck.Discrete.crossR2 A B C = -Gluck.Discrete.crossR2 B A C := by
  calc
    Gluck.Discrete.crossR2 A B C = Gluck.Discrete.crossR2 B C A :=
      (Gluck.Discrete.crossR2_cycle A B C).symm
    _ = -Gluck.Discrete.crossR2 B A C := Gluck.Discrete.crossR2_swap B A C

/-- Positive oriented areas are transitive inside a common open half-plane
based at `A → U`. -/
theorem crossR2_trans_of_common_left {A U X Y Z : ℂ}
    (hUX : 0 < Gluck.Discrete.crossR2 A U X)
    (hUY : 0 < Gluck.Discrete.crossR2 A U Y)
    (hUZ : 0 < Gluck.Discrete.crossR2 A U Z)
    (hXY : 0 < Gluck.Discrete.crossR2 A X Y)
    (hYZ : 0 < Gluck.Discrete.crossR2 A Y Z) :
    0 < Gluck.Discrete.crossR2 A X Z := by
  have hid :
      Gluck.Discrete.crossR2 A U Y * Gluck.Discrete.crossR2 A X Z =
        Gluck.Discrete.crossR2 A U X * Gluck.Discrete.crossR2 A Y Z +
          Gluck.Discrete.crossR2 A U Z * Gluck.Discrete.crossR2 A X Y := by
    unfold Gluck.Discrete.crossR2
    ring
  have hprod :
      0 < Gluck.Discrete.crossR2 A U Y *
        Gluck.Discrete.crossR2 A X Z := by
    rw [hid]
    exact add_pos (mul_pos hUX hYZ) (mul_pos hUZ hXY)
  exact (mul_pos_iff.mp hprod).resolve_right
    (not_and_of_not_left _ (not_lt_of_ge hUY.le)) |>.2

private theorem cyclicLift_ne_of_lt {n : ℕ} [NeZero n]
    (c : ZMod n) {r s : ℕ} (hr : r < n) (hs : s < n) (hrs : r ≠ s) :
    cyclicLift c r ≠ cyclicLift c s := by
  intro h
  exact hrs (cyclicLift_injOn_range c (by simpa using hr) (by simpa using hs) h)

/-- Every cyclically ordered triple of vertices has positive orientation if
all polygon edges strictly support the remaining vertices on their left. -/
theorem crossR2_cyclicLift_order_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsupport : CyclicChordStrictConvexEdgeSupport v)
    (c : ZMod n) {p k q : ℕ}
    (hpk : p < k) (hkq : k < q) (hqn : q < n) :
    0 < Gluck.Discrete.crossR2
      (v (cyclicLift c p)) (v (cyclicLift c k)) (v (cyclicLift c q)) := by
  have hpn : p < n := by omega
  have hkn : k < n := by omega
  have hp1n : p + 1 < n := by omega
  have hp1k : p + 1 ≤ k := by omega
  let A := v (cyclicLift c p)
  let U := v (cyclicLift c (p + 1))
  have hanchor : ∀ j : ℕ, p + 1 < j → j < n →
      0 < Gluck.Discrete.crossR2 A U (v (cyclicLift c j)) := by
    intro j hp1j hjn
    have hjp : cyclicLift c j ≠ cyclicLift c p :=
      cyclicLift_ne_of_lt c hjn hpn (by omega)
    have hjp1 : cyclicLift c j ≠ cyclicLift c (p + 1) :=
      cyclicLift_ne_of_lt c hjn hp1n (by omega)
    have hs := hsupport (cyclicLift c p) (cyclicLift c j) hjp
      (by simpa [cyclicLift_succ] using hjp1)
    simpa [A, U, cyclicLift_succ] using hs
  have hconsecutive : ∀ j : ℕ, p < j → j + 1 < n →
      0 < Gluck.Discrete.crossR2 A
        (v (cyclicLift c j)) (v (cyclicLift c (j + 1))) := by
    intro j hpj hj1n
    have hjn : j < n := by omega
    have hpjNe : cyclicLift c p ≠ cyclicLift c j :=
      cyclicLift_ne_of_lt c hpn hjn (by omega)
    have hpj1Ne : cyclicLift c p ≠ cyclicLift c (j + 1) :=
      cyclicLift_ne_of_lt c hpn hj1n (by omega)
    have hs := hsupport (cyclicLift c j) (cyclicLift c p)
      hpjNe (by simpa [cyclicLift_succ] using hpj1Ne)
    rw [← crossR2_cyclic] at hs
    simpa [A, cyclicLift_succ] using hs
  by_cases hkp1 : k = p + 1
  · subst k
    exact hanchor q (by omega) hqn
  have hp1k' : p + 1 < k := lt_of_le_of_ne hp1k (Ne.symm hkp1)
  have hAk : 0 < Gluck.Discrete.crossR2 A U (v (cyclicLift c k)) :=
    hanchor k hp1k' hkn
  have hforall : ∀ r : ℕ, k + 1 ≤ r → r < n →
      0 < Gluck.Discrete.crossR2 A
        (v (cyclicLift c k)) (v (cyclicLift c r)) := by
    intro r hkr
    induction r, hkr using Nat.le_induction with
    | base =>
        intro hbase
        exact hconsecutive k hpk hbase
    | succ r hkr ih =>
        intro hrsucc
        have hrn : r < n := by omega
        have hpr : p + 1 < r := by omega
        have hpr1 : p + 1 < r + 1 := by omega
        exact crossR2_trans_of_common_left hAk
          (hanchor r hpr hrn) (hanchor (r + 1) hpr1 hrsucc)
          (ih hrn) (hconsecutive r (by omega) hrsucc)
  exact hforall q (by omega) hqn

private theorem cyclicLift_sub_val {n : ℕ} [NeZero n]
    (c x : ZMod n) : cyclicLift c (x - c).val = x := by
  unfold cyclicLift
  rw [ZMod.natCast_zmod_val]
  ring

/-- Strict edge support makes every triple of distinct vertices noncollinear. -/
theorem crossR2_ne_zero_of_strictConvexEdgeSupport
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsupport : CyclicChordStrictConvexEdgeSupport v) :
    ∀ a b d : ZMod n, a ≠ b → d ≠ a → d ≠ b →
      Gluck.Discrete.crossR2 (v a) (v b) (v d) ≠ 0 := by
  intro a b d hab hda hdb
  let rb : ℕ := (b - a).val
  let rd : ℕ := (d - a).val
  have hrbpos : 0 < rb := by
    exact ZMod.val_pos.mpr (sub_ne_zero.mpr hab.symm)
  have hrdpos : 0 < rd := by
    exact ZMod.val_pos.mpr (sub_ne_zero.mpr hda)
  have hrbn : rb < n := ZMod.val_lt _
  have hrdn : rd < n := ZMod.val_lt _
  have hliftb : cyclicLift a rb = b := cyclicLift_sub_val a b
  have hliftd : cyclicLift a rd = d := cyclicLift_sub_val a d
  have hrbne : rb ≠ rd := by
    intro h
    apply hdb
    rw [← hliftb, ← hliftd, h]
  rcases lt_or_gt_of_ne hrbne with hrbd | hdrb
  · have hpos := crossR2_cyclicLift_order_pos hsupport a
      (p := 0) (k := rb) (q := rd) (by omega) hrbd hrdn
    rw [show cyclicLift a 0 = a by simp [cyclicLift], hliftb, hliftd] at hpos
    exact hpos.ne'
  · have hpos := crossR2_cyclicLift_order_pos hsupport a
      (p := 0) (k := rd) (q := rb) (by omega) hdrb hrbn
    rw [show cyclicLift a 0 = a by simp [cyclicLift], hliftd, hliftb] at hpos
    have hneg : Gluck.Discrete.crossR2 (v a) (v b) (v d) < 0 := by
      rw [crossR2_swap]
      exact neg_lt_zero.mpr hpos
    exact hneg.ne

/-- Vertices strictly inside a lifted cyclic gap lie on the positive side of
the chord oriented from its right endpoint to its left endpoint. -/
theorem crossR2_gap_pos {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsupport : CyclicChordStrictConvexEdgeSupport v)
    (c : ZMod n) {p k q : ℕ}
    (hpk : p < k) (hkq : k < q) (hqn : q < n) :
    0 < Gluck.Discrete.crossR2
      (v (cyclicLift c q)) (v (cyclicLift c p)) (v (cyclicLift c k)) := by
  have h := crossR2_cyclicLift_order_pos hsupport c hpk hkq hqn
  calc
    0 < Gluck.Discrete.crossR2
        (v (cyclicLift c p)) (v (cyclicLift c k)) (v (cyclicLift c q)) := h
    _ = Gluck.Discrete.crossR2
        (v (cyclicLift c q)) (v (cyclicLift c p)) (v (cyclicLift c k)) := by
          rw [crossR2_cyclic, crossR2_cyclic]

/-- Vertices outside a closed lifted cyclic gap lie strictly on the opposite
side of its endpoint chord. -/
theorem crossR2_gap_neg_of_not_mem {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsupport : CyclicChordStrictConvexEdgeSupport v)
    (c : ZMod n) {p q : ℕ} (hpq : p < q) (hqn : q < n)
    {x : ZMod n} (hx : x ∉ mapCut c (Finset.Icc p q)) :
    Gluck.Discrete.crossR2
      (v (cyclicLift c q)) (v (cyclicLift c p)) (v x) < 0 := by
  let r : ℕ := (x - c).val
  have hrn : r < n := ZMod.val_lt _
  have hlift : cyclicLift c r = x := cyclicLift_sub_val c x
  have hrnot : r ∉ Finset.Icc p q := by
    intro hr
    apply hx
    exact Finset.mem_image.mpr ⟨r, hr, hlift⟩
  have hcases : r < p ∨ q < r := by
    rw [Finset.mem_Icc] at hrnot
    omega
  rcases hcases with hrp | hqr
  · have hpos := crossR2_cyclicLift_order_pos hsupport c
      (p := r) (k := p) (q := q) hrp hpq hqn
    rw [crossR2_cyclic, crossR2_cyclic] at hpos
    rw [← hlift, crossR2_swap]
    exact neg_lt_zero.mpr hpos
  · have hpos := crossR2_cyclicLift_order_pos hsupport c
      (p := p) (k := q) (q := r) hpq hqr hrn
    rw [← hlift, crossR2_swap_first]
    exact neg_lt_zero.mpr hpos

/-- The nonnegative side of a lifted gap chord contains no vertices outside
the endpoint-closed gap. -/
theorem mem_gap_of_crossR2_nonneg {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsupport : CyclicChordStrictConvexEdgeSupport v)
    (c : ZMod n) {p q : ℕ} (hpq : p < q) (hqn : q < n)
    {x : ZMod n}
    (hx : 0 ≤ Gluck.Discrete.crossR2
      (v (cyclicLift c q)) (v (cyclicLift c p)) (v x)) :
    x ∈ mapCut c (Finset.Icc p q) := by
  by_contra hnot
  exact (not_lt_of_ge hx)
    (crossR2_gap_neg_of_not_mem hsupport c hpq hqn hnot)

private theorem strictConvexEdgeSupport_cross_nonneg {n : ℕ}
    {v : ZMod n → ℂ} (hsupport : CyclicChordStrictConvexEdgeSupport v)
    (i x : ZMod n) :
    0 ≤ Gluck.Discrete.crossR2 (v i) (v (i + 1)) (v x) := by
  by_cases hxi : x = i
  · subst x
    simp [Gluck.Discrete.crossR2]
  by_cases hxi1 : x = i + 1
  · subst x
    simp [Gluck.Discrete.crossR2]
    nlinarith
  exact (hsupport i x hxi hxi1).le

private theorem lineMap_parameter_nonneg_of_left_support
    {P A B Y : ℂ} {s : ℝ}
    (hY : Y = (AffineMap.lineMap A B) s)
    (hPB : 0 < Gluck.Discrete.crossR2 P A B)
    (hPY : 0 ≤ Gluck.Discrete.crossR2 P A Y) :
    0 ≤ s := by
  subst Y
  rw [Gluck.Discrete.crossR2_lineMap] at hPY
  have hzero : Gluck.Discrete.crossR2 P A A = 0 := by
    simp [Gluck.Discrete.crossR2]
    ring
  rw [hzero] at hPY
  simp only [mul_zero, zero_add] at hPY
  nlinarith

private theorem lineMap_parameter_le_one_of_right_support
    {A B N Y : ℂ} {s : ℝ}
    (hY : Y = (AffineMap.lineMap A B) s)
    (hNA : 0 < Gluck.Discrete.crossR2 B N A)
    (hNY : 0 ≤ Gluck.Discrete.crossR2 B N Y) :
    s ≤ 1 := by
  subst Y
  rw [Gluck.Discrete.crossR2_lineMap] at hNY
  have hzero : Gluck.Discrete.crossR2 B N B = 0 := by
    simp [Gluck.Discrete.crossR2]
  rw [hzero] at hNY
  simp only [mul_zero, add_zero] at hNY
  nlinarith

private theorem exists_lineMap_crossing_of_cross_pos_neg
    {A B Z X : ℂ} (hAB : A ≠ B)
    (hZ : 0 < Gluck.Discrete.crossR2 A B Z)
    (hX : Gluck.Discrete.crossR2 A B X < 0) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ s : ℝ,
      (AffineMap.lineMap Z X) t = (AffineMap.lineMap A B) s := by
  let α := Gluck.Discrete.crossR2 A B Z
  let β := Gluck.Discrete.crossR2 A B X
  let t := α / (α - β)
  have hα : 0 < α := hZ
  have hβ : β < 0 := hX
  have hden : 0 < α - β := by linarith
  have ht0 : 0 < t := div_pos hα hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  let Y := (AffineMap.lineMap Z X) t
  have hcrossY : Gluck.Discrete.crossR2 A B Y = 0 := by
    dsimp [Y]
    rw [Gluck.Discrete.crossR2_lineMap]
    change (1 - t) * α + t * β = 0
    dsimp [t]
    field_simp [hden.ne']
    ring
  obtain ⟨s, hs⟩ := Gluck.Discrete.exists_lineMap_eq_of_crossR2_eq_zero hAB hcrossY
  exact ⟨t, ⟨ht0, ht1⟩, s, hs.symm⟩

/-- The open segment from an interior gap vertex to a vertex outside the
closed gap meets the endpoint chord. -/
theorem exists_gap_chord_crossing {n : ℕ} [NeZero n]
    {v : ZMod n → ℂ} (hsupport : CyclicChordStrictConvexEdgeSupport v)
    (c : ZMod n) {p k q : ℕ}
    (hpk : p < k) (hkq : k < q) (hqn : q < n)
    {x : ZMod n} (hx : x ∉ mapCut c (Finset.Icc p q)) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1,
      (AffineMap.lineMap (v (cyclicLift c k)) (v x)) t =
        (AffineMap.lineMap (v (cyclicLift c q)) (v (cyclicLift c p))) s := by
  have hZ := crossR2_gap_pos hsupport c hpk hkq hqn
  have hX := crossR2_gap_neg_of_not_mem hsupport c
    (lt_trans hpk hkq) hqn hx
  have hAB : v (cyclicLift c q) ≠ v (cyclicLift c p) := by
    intro hEq
    rw [hEq] at hZ
    simp [Gluck.Discrete.crossR2] at hZ
  obtain ⟨t, ht, s, hline⟩ :=
    exists_lineMap_crossing_of_cross_pos_neg hAB hZ hX
  let P := v (cyclicLift c (q - 1))
  let A := v (cyclicLift c q)
  let B := v (cyclicLift c p)
  let N := v (cyclicLift c (p + 1))
  let Z := v (cyclicLift c k)
  let Y := (AffineMap.lineMap Z (v x)) t
  have hPAB : 0 < Gluck.Discrete.crossR2 P A B := by
    have horder := crossR2_cyclicLift_order_pos hsupport c
      (p := p) (k := q - 1) (q := q) (by omega) (by omega) hqn
    calc
      0 < Gluck.Discrete.crossR2 B P A := by simpa [A, B, P] using horder
      _ = Gluck.Discrete.crossR2 P A B := crossR2_cyclic
  have hBNA : 0 < Gluck.Discrete.crossR2 B N A := by
    simpa [A, B, N] using
      (crossR2_cyclicLift_order_pos hsupport c
        (p := p) (k := p + 1) (q := q) (by omega) (by omega) hqn)
  have hpredSucc : cyclicLift c (q - 1) + 1 = cyclicLift c q := by
    have h := cyclicLift_succ c (q - 1)
    rw [show q - 1 + 1 = q by omega] at h
    exact h.symm
  have hsucc : cyclicLift c p + 1 = cyclicLift c (p + 1) :=
    (cyclicLift_succ c p).symm
  have hPZ : 0 ≤ Gluck.Discrete.crossR2 P A Z := by
    have h := strictConvexEdgeSupport_cross_nonneg hsupport
      (cyclicLift c (q - 1)) (cyclicLift c k)
    rw [hpredSucc] at h
    simpa [P, A, Z] using h
  have hPX : 0 ≤ Gluck.Discrete.crossR2 P A (v x) := by
    have h := strictConvexEdgeSupport_cross_nonneg hsupport
      (cyclicLift c (q - 1)) x
    rw [hpredSucc] at h
    simpa [P, A] using h
  have hBZ : 0 ≤ Gluck.Discrete.crossR2 B N Z := by
    have h := strictConvexEdgeSupport_cross_nonneg hsupport
      (cyclicLift c p) (cyclicLift c k)
    rw [hsucc] at h
    simpa [B, N, Z] using h
  have hBX : 0 ≤ Gluck.Discrete.crossR2 B N (v x) := by
    have h := strictConvexEdgeSupport_cross_nonneg hsupport
      (cyclicLift c p) x
    rw [hsucc] at h
    simpa [B, N] using h
  have hPY : 0 ≤ Gluck.Discrete.crossR2 P A Y := by
    dsimp [Y]
    rw [Gluck.Discrete.crossR2_lineMap]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht.2.le) hPZ)
      (mul_nonneg ht.1.le hPX)
  have hBY : 0 ≤ Gluck.Discrete.crossR2 B N Y := by
    dsimp [Y]
    rw [Gluck.Discrete.crossR2_lineMap]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht.2.le) hBZ)
      (mul_nonneg ht.1.le hBX)
  have hline' : Y = (AffineMap.lineMap A B) s := by
    simpa [Y, Z, A, B] using hline
  have hs0 : 0 ≤ s :=
    lineMap_parameter_nonneg_of_left_support hline' hPAB hPY
  have hs1 : s ≤ 1 :=
    lineMap_parameter_le_one_of_right_support hline' hBNA hBY
  exact ⟨t, ht, s, ⟨hs0, hs1⟩, by simpa [A, B, Z] using hline⟩

/-- The noncollinearity, side, and chord-crossing fields consumed by
Dahlberg's finite contact-set argument. -/
structure StrictConvexCyclicChordGeometryFields {n : ℕ} [NeZero n]
    (v : ZMod n → ℂ) : Prop where
  noncollinear : ∀ a b d : ZMod n,
    a ≠ b → d ≠ a → d ≠ b →
      Gluck.Discrete.crossR2 (v a) (v b) (v d) ≠ 0
  gap : ∀ (c : ZMod n) (p k q : ℕ),
    p < k → k < q → q < n →
    let a := cyclicLift c q
    let b := cyclicLift c p
    let z := cyclicLift c k
    let E := mapCut c (Finset.Icc p q)
    v a ≠ v b ∧
      0 < Gluck.Discrete.crossR2 (v a) (v b) (v z) ∧
      (∀ x : ZMod n,
        0 ≤ Gluck.Discrete.crossR2 (v a) (v b) (v x) → x ∈ E) ∧
      (∀ x : ZMod n, x ∉ E →
        ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1,
          (AffineMap.lineMap (v z) (v x)) t =
            (AffineMap.lineMap (v a) (v b)) s)

/-- Strict support at every polygon edge supplies all cyclic chord geometry
needed by Dahlberg's Lemmas 4 and 6. -/
theorem strictConvexCyclicChordGeometryFields_of_edgeSupport
    {n : ℕ} [NeZero n] {v : ZMod n → ℂ}
    (hsupport : CyclicChordStrictConvexEdgeSupport v) :
    StrictConvexCyclicChordGeometryFields v := by
  constructor
  · exact crossR2_ne_zero_of_strictConvexEdgeSupport hsupport
  · intro c p k q hpk hkq hqn
    dsimp
    have hgap := crossR2_gap_pos hsupport c hpk hkq hqn
    refine ⟨?_, hgap, ?_, ?_⟩
    · intro hEq
      rw [hEq] at hgap
      simp [Gluck.Discrete.crossR2] at hgap
    · intro x hx
      exact mem_gap_of_crossR2_nonneg hsupport c (lt_trans hpk hkq) hqn hx
    · intro x hx
      exact exists_gap_chord_crossing hsupport c hpk hkq hqn hx

end Gluck.Forward.CyclicChordGeometry
