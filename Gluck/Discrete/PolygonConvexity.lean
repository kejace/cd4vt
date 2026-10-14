/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Convexity
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Positive polygonal turning and global support

This file proves the positive polygonal Umlaufsatz needed by Dahlberg's convex
theorem.  For an arbitrary cyclic polygon we construct the canonical lifted
edge heading by adding the principal positive turn between successive edges.
A finite Hopf secant-grid argument, evaluated after shifting a lowest vertex
to index zero, proves that a simple positively oriented polygon accumulates
exactly `2π` of heading in one period.  The resulting heading reconstruction
then gives global strict edge support.
-/

namespace Gluck.Discrete

open scoped Pointwise Real

variable {n : ℕ}

/-- The natural-number lift of a cyclic polygon vertex. -/
def cyclicVertex (v : ZMod n → ℂ) (k : ℕ) : ℂ :=
  v (k : ZMod n)

/-- The outgoing edge in the natural-number lift. -/
def cyclicEdge (v : ZMod n → ℂ) (k : ℕ) : ℂ :=
  cyclicVertex v (k + 1) - cyclicVertex v k

/-- The secant between two vertices in the natural-number lift. -/
def cyclicSecant (v : ZMod n → ℂ) (i j : ℕ) : ℂ :=
  cyclicVertex v j - cyclicVertex v i

/-- The positive Euclidean length of a nondegenerate lifted edge. -/
noncomputable def cyclicEdgeLength (v : ZMod n → ℂ) (k : ℕ) : ℝ :=
  ‖cyclicEdge v k‖

/-- The principal signed turn from edge `k` to edge `k+1`. -/
noncomputable def cyclicEdgeTurn (v : ZMod n → ℂ) (k : ℕ) : ℝ :=
  Complex.arg (cyclicEdge v (k + 1) / cyclicEdge v k)

/-- The canonical lifted heading: start with the principal argument of edge
zero and add the principal turn at every successive vertex. -/
noncomputable def cyclicEdgeHeading (v : ZMod n → ℂ) : ℕ → ℝ
  | 0 => Complex.arg (cyclicEdge v 0)
  | k + 1 => cyclicEdgeHeading v k + cyclicEdgeTurn v k

/-- The exact remaining polygonal Umlaufsatz conclusion for one polygon. -/
def HasPositiveTurningNumberOne (v : ZMod n → ℂ) : Prop :=
  cyclicEdgeHeading v n = cyclicEdgeHeading v 0 + 2 * Real.pi

/-- The smallest source-free polygonal Umlaufsatz interface needed below:
simplicity and positive consecutive orientation force one total positive turn. -/
def PositivePolygonalUmlaufsatz : Prop :=
  ∀ (n : ℕ) [NeZero n] (v : ZMod n → ℂ),
    IsSimplePolygon v →
    (∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) →
    HasPositiveTurningNumberOne v

/-- Every cyclic vertex lies in every closed left edge half-plane. -/
def ConvexEdgeSupport (v : ZMod n → ℂ) : Prop :=
  ∀ i j : ZMod n, 0 ≤ crossR2 (v i) (v (i + 1)) (v j)

/-- Every vertex other than the endpoints lies in the open left half-plane of
each oriented edge.  This is the strict-convexity interface consumed by the
Dahlberg edge-envelope argument. -/
def StrictConvexEdgeSupport (v : ZMod n → ℂ) : Prop :=
  ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 →
    0 < crossR2 (v i) (v (i + 1)) (v j)

/-- The principal signed turn from a nonzero vector `u` to a nonzero vector
`w`. -/
noncomputable def principalTurn (u w : ℂ) : ℝ :=
  Complex.arg (w / u)

/-- In one open half-plane through the origin, the principal turn is the
ordinary difference of principal arguments. -/
private theorem principalTurn_eq_sub_arg_of_re_pos {u w : ℂ}
    (hu : 0 < u.re) (hw : 0 < w.re) :
    principalTurn u w = Complex.arg w - Complex.arg u := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hu
    exact lt_irrefl 0 hu
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    exact lt_irrefl 0 hw
  have hcoe : (principalTurn u w : Real.Angle) =
      ((Complex.arg w - Complex.arg u : ℝ) : Real.Angle) := by
    unfold principalTurn
    simpa [Real.Angle.coe_sub] using
      Complex.arg_div_coe_angle hw0 hu0
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hcoe
  have huarg := (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
  have hwarg := (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  rw [abs_lt] at huarg hwarg
  have hp := Complex.arg_mem_Ioc (w / u)
  change -Real.pi < principalTurn u w ∧ principalTurn u w ≤ Real.pi at hp
  have hklo : (-1 : ℝ) < (k : ℝ) := by
    nlinarith [Real.pi_pos]
  have hkhi : (k : ℝ) < 1 := by
    nlinarith [Real.pi_pos]
  have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
  have hkhi' : k < (1 : ℤ) := by exact_mod_cast hkhi
  have hkzero : k = 0 := by omega
  rw [hkzero, Int.cast_zero, mul_zero] at hk
  linarith

/-- A common nonzero complex factor does not change a principal turn. -/
private theorem principalTurn_mul_left {c u w : ℂ} (hc : c ≠ 0) :
    principalTurn (c * u) (c * w) = principalTurn u w := by
  unfold principalTurn
  congr 1
  field_simp

/-- Reversing both vectors preserves their principal relative turn. -/
private theorem principalTurn_neg (u w : ℂ) :
    principalTurn (-u) (-w) = principalTurn u w := by
  simpa using principalTurn_mul_left (c := (-1 : ℂ)) (u := u) (w := w)
    (by norm_num)

/-- Positive oriented area means that the principal vector turn lies strictly
between `0` and `π`. -/
private theorem principalTurn_mem_Ioo_of_cross_pos {u w : ℂ}
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

/-- Hopf's elementary triangle move: a positive turn splits exactly through
the diagonal vector `u + w`. -/
private theorem principalTurn_add_split_of_cross_pos {u w : ℂ}
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
  have hα := principalTurn_mem_Ioo_of_cross_pos hcross
  have hβ := principalTurn_mem_Ioo_of_cross_pos hcross₁
  have hγ := principalTurn_mem_Ioo_of_cross_pos hcross₂
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

/-- A Euclidean segment in `ℂ` is compact. -/
private theorem isCompact_segment_complex (A B : ℂ) :
    IsCompact (segment ℝ A B) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

/-- A separating common multiplier puts two secants in the open right
half-plane, where their principal turn is an ordinary argument difference. -/
private theorem principalTurn_eq_sub_arg_after_common_multiplier {c u w : ℂ}
    (hu : 0 < (c * u).re) (hw : 0 < (c * w).re) :
    principalTurn u w = Complex.arg (c * w) - Complex.arg (c * u) := by
  have hc0 : c ≠ 0 := by
    intro h
    subst c
    simp at hu
  rw [← principalTurn_mul_left hc0]
  exact principalTurn_eq_sub_arg_of_re_pos hu hw

/-- **Hopf's secant-square identity.** If the two closed segments `AB` and
`CD` are disjoint, the four principal secant turns around their parameter
square telescope exactly, rather than only modulo `2π`. -/
theorem principalTurn_secant_square_of_disjoint_segments
    {A B C D : ℂ}
    (hdisj : Disjoint (segment ℝ A B) (segment ℝ C D)) :
    principalTurn (C - A) (D - A) +
        principalTurn (D - A) (D - B) =
      principalTurn (C - A) (C - B) +
        principalTurn (C - B) (D - B) := by
  let Q : Set ℂ := segment ℝ C D - segment ℝ A B
  have hQconvex : Convex ℝ Q :=
    (convex_segment C D).sub (convex_segment A B)
  have hQcompact : IsCompact Q := by
    dsimp [Q]
    rw [sub_eq_add_neg]
    exact (isCompact_segment_complex C D).add
      (isCompact_segment_complex A B).neg
  have hzeroQ : (0 : ℂ) ∉ Q := by
    intro hzero
    rcases Set.mem_sub.mp hzero with ⟨c, hc, a, ha, hca⟩
    have hEq : c = a := sub_eq_zero.mp hca
    exact Set.disjoint_left.mp hdisj ha (hEq ▸ hc)
  obtain ⟨f, u, hfu, hsep⟩ :=
    RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
      hQconvex hQcompact.isClosed hzeroQ
  have hu : 0 < u := by
    simpa using hfu
  let c : ℂ := f 1
  have hf_apply (q : ℂ) : f q = q * c := by
    change f q = q * f 1
    calc
      f q = f (q • (1 : ℂ)) := by simp
      _ = q • f 1 := f.map_smul q 1
      _ = q * f 1 := by simp [smul_eq_mul]
  have hright {q : ℂ} (hq : q ∈ Q) : 0 < (c * q).re := by
    have h := hu.trans (hsep q hq)
    rw [hf_apply, mul_comm] at h
    exact h
  have hCA : C - A ∈ Q :=
    Set.sub_mem_sub (left_mem_segment ℝ C D) (left_mem_segment ℝ A B)
  have hDA : D - A ∈ Q :=
    Set.sub_mem_sub (right_mem_segment ℝ C D) (left_mem_segment ℝ A B)
  have hCB : C - B ∈ Q :=
    Set.sub_mem_sub (left_mem_segment ℝ C D) (right_mem_segment ℝ A B)
  have hDB : D - B ∈ Q :=
    Set.sub_mem_sub (right_mem_segment ℝ C D) (right_mem_segment ℝ A B)
  rw [principalTurn_eq_sub_arg_after_common_multiplier
      (hright hCA) (hright hDA),
    principalTurn_eq_sub_arg_after_common_multiplier
      (hright hDA) (hright hDB),
    principalTurn_eq_sub_arg_after_common_multiplier
      (hright hCA) (hright hCB),
    principalTurn_eq_sub_arg_after_common_multiplier
      (hright hCB) (hright hDB)]
  ring

/-! ## Finite Hopf-grid cancellation -/

/-- The elementary telescoping identity used along a row of the Hopf grid. -/
private theorem sum_range_sub_succ (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (f i - f (i + 1)) = f 0 - f m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- One-column Stokes move for an abstract triangular Hopf grid. -/
private theorem hopf_column_transport
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
    simpa using sum_range_sub_succ (fun i => H i m) (m - 1)
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

/-- Discrete Stokes cancellation on the triangular Hopf secant grid. -/
private theorem hopf_grid_sum
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
      have htransport := hopf_column_transport T H V htriangle
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

/-- Two natural representatives in the fundamental range remain distinct in
`ZMod n`. -/
private theorem zmod_natCast_ne_of_lt [NeZero n] {a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (a : ZMod n) ≠ (b : ZMod n) := by
  rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]
  exact hab

/-- Positive consecutive orientation is impossible with fewer than three
cyclic vertices. -/
private theorem three_le_of_positiveOrientation [NeZero n]
    {v : ZMod n → ℂ}
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    3 ≤ n := by
  by_contra hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  interval_cases n
  · have h := horient 0
    simp only [zero_sub, zero_add] at h
    have hm : (-1 : ZMod 1) = 0 := Subsingleton.elim _ _
    have hp : (1 : ZMod 1) = 0 := Subsingleton.elim _ _
    rw [hm, hp] at h
    simp [crossR2] at h
  · have h := horient 0
    simp only [zero_sub, zero_add] at h
    have hm : (-1 : ZMod 2) = 1 := by decide
    rw [hm] at h
    simp [crossR2] at h

/-- Translation of a vertex-triple cross product to its two outgoing edge
vectors. -/
private theorem crossR2_edge_vectors (A B C : ℂ) :
    crossR2 0 (B - A) (C - B) = crossR2 A B C := by
  unfold crossR2
  simp
  ring

/-- Natural-lift edges that do not share a cyclic endpoint are disjoint in a
simple polygon.  The final hypothesis covers both an ordinary later edge and
the closing edge of the chosen unwrapped period. -/
theorem IsSimplePolygon.natural_edges_disjoint_of_separated [NeZero n]
    {v : ZMod n → ℂ} (hsimple : IsSimplePolygon v) {i j : ℕ}
    (hij : i + 1 < j) (hjn : j < n) (hwrap : j + 1 < n ∨ 0 < i) :
    Disjoint
      (segment ℝ (cyclicVertex v i) (cyclicVertex v (i + 1)))
      (segment ℝ (cyclicVertex v j) (cyclicVertex v (j + 1))) := by
  have hi : i < n := by omega
  have hi1 : i + 1 < n := by omega
  have hij0 : (i : ZMod n) ≠ (j : ZMod n) :=
    zmod_natCast_ne_of_lt hi hjn (by omega)
  have hi1j : (i : ZMod n) + 1 ≠ (j : ZMod n) := by
    simpa [Nat.cast_add] using
      zmod_natCast_ne_of_lt hi1 hjn (by omega : i + 1 ≠ j)
  have hj1i : (j : ZMod n) + 1 ≠ (i : ZMod n) := by
    rcases hwrap with hj1n | hi0
    · simpa [Nat.cast_add] using
        zmod_natCast_ne_of_lt hj1n hi (by omega : j + 1 ≠ i)
    · intro heq
      by_cases hj1n : j + 1 < n
      · exact (zmod_natCast_ne_of_lt hj1n hi (by omega : j + 1 ≠ i))
          (by simpa [Nat.cast_add] using heq)
      · have hj1eq : ((j + 1 : ℕ) : ZMod n) = (i : ZMod n) := by
          simpa [Nat.cast_add] using heq
        have hj1 : j + 1 = n := by omega
        rw [hj1, ZMod.natCast_self] at hj1eq
        have hival := congrArg ZMod.val hj1eq.symm
        simp only [ZMod.val_natCast_of_lt hi, ZMod.val_zero] at hival
        omega
  rw [Set.disjoint_iff_inter_eq_empty]
  simpa [cyclicVertex, Nat.cast_add] using
    hsimple.2.2 (i : ZMod n) (j : ZMod n) hij0 hi1j hj1i

/-! ## A canonical lowest-vertex cut -/

/-- A finite cyclic polygon has a vertex lexicographically minimal in
`(im, re)`. -/
theorem exists_vertex_min_im_then_re [NeZero n] (v : ZMod n → ℂ) :
    ∃ a : ZMod n,
      (∀ i, (v a).im ≤ (v i).im) ∧
      (∀ i, (v a).im = (v i).im → (v a).re ≤ (v i).re) := by
  obtain ⟨a₀, ha₀⟩ := Finite.exists_min (fun i : ZMod n => (v i).im)
  let S : Finset (ZMod n) :=
    Finset.univ.filter fun i => (v i).im = (v a₀).im
  have hS : S.Nonempty := by
    refine ⟨a₀, ?_⟩
    simp [S]
  obtain ⟨a, haS, ha⟩ := S.exists_min_image (fun i => (v i).re) hS
  have haim : (v a).im = (v a₀).im := by
    simpa [S] using haS
  refine ⟨a, ?_, ?_⟩
  · intro i
    rw [haim]
    exact ha₀ i
  · intro i hi
    apply ha i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hi, haim]

/-- Cyclically translate a polygon's index set. -/
def shiftPolygon (v : ZMod n → ℂ) (a : ZMod n) : ZMod n → ℂ :=
  fun i => v (a + i)

/-- Cyclic index translation preserves polygon simplicity. -/
theorem isSimplePolygon_shift [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (a : ZMod n) :
    IsSimplePolygon (shiftPolygon v a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [shiftPolygon, add_assoc] using hsimple.1 (a + i)
  · intro i
    simpa [shiftPolygon, add_assoc] using hsimple.2.1 (a + i)
  · intro i j hij hi1j hj1i
    have h₀ : a + i ≠ a + j := by
      intro h
      exact hij (add_left_cancel h)
    have h₁ : a + i + 1 ≠ a + j := by
      intro h
      apply hi1j
      apply add_left_cancel (a := a)
      simpa [add_assoc] using h
    have h₂ : a + j + 1 ≠ a + i := by
      intro h
      apply hj1i
      apply add_left_cancel (a := a)
      simpa [add_assoc] using h
    have h := hsimple.2.2 (a + i) (a + j) h₀ h₁ h₂
    simpa [shiftPolygon, add_assoc] using h

/-- Cyclic index translation preserves positive consecutive orientation. -/
theorem positiveOrientation_shift [NeZero n] {v : ZMod n → ℂ}
    (horient : ∀ i : ZMod n,
      0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (a : ZMod n) :
    ∀ i : ZMod n,
      0 < crossR2 ((shiftPolygon v a) (i - 1))
        ((shiftPolygon v a) i) ((shiftPolygon v a) (i + 1)) := by
  intro i
  change 0 < crossR2 (v (a + (i - 1))) (v (a + i)) (v (a + (i + 1)))
  convert horient (a + i) using 1
  all_goals ring_nf

/-- Shift a lexicographically lowest vertex to index zero. -/
theorem shift_zero_min_im_then_re [NeZero n] (v : ZMod n → ℂ) :
    ∃ a : ZMod n,
      (∀ i, ((shiftPolygon v a) 0).im ≤ ((shiftPolygon v a) i).im) ∧
      (∀ i, ((shiftPolygon v a) 0).im = ((shiftPolygon v a) i).im →
        ((shiftPolygon v a) 0).re ≤ ((shiftPolygon v a) i).re) := by
  obtain ⟨a, him, hre⟩ := exists_vertex_min_im_then_re v
  refine ⟨a, ?_, ?_⟩
  · intro i
    simpa [shiftPolygon] using him (a + i)
  · intro i hi
    simpa [shiftPolygon] using hre (a + i) (by simpa [shiftPolygon] using hi)

theorem cyclicEdge_ne_zero [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (k : ℕ) :
    cyclicEdge v k ≠ 0 := by
  unfold cyclicEdge cyclicVertex
  rw [sub_ne_zero]
  simpa [Nat.cast_add] using (hsimple.1 (k : ZMod n)).symm

theorem cyclicEdgeLength_pos [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (k : ℕ) :
    0 < cyclicEdgeLength v k := by
  unfold cyclicEdgeLength
  exact norm_pos_iff.mpr (cyclicEdge_ne_zero hsimple k)

theorem cyclicEdge_periodic [NeZero n] (v : ZMod n → ℂ) (k : ℕ) :
    cyclicEdge v (k + n) = cyclicEdge v k := by
  simp [cyclicEdge, cyclicVertex, Nat.cast_add]

theorem cyclicEdgeTurn_periodic [NeZero n] (v : ZMod n → ℂ) (k : ℕ) :
    cyclicEdgeTurn v (k + n) = cyclicEdgeTurn v k := by
  unfold cyclicEdgeTurn
  rw [show k + n + 1 = (k + 1) + n by omega,
    cyclicEdge_periodic v (k + 1), cyclicEdge_periodic v k]

/-- A sum over one full period is unchanged by a natural-number shift. -/
private theorem sum_range_periodic_nat_shift {M : Type*} [AddCommGroup M]
    (f : ℕ → M) (n a : ℕ) (hper : ∀ k, f (k + n) = f k) :
    (∑ k ∈ Finset.range n, f (a + k)) =
      ∑ k ∈ Finset.range n, f k := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hfirst := Finset.sum_range_succ' (fun k => f (a + k)) n
      have hlast := Finset.sum_range_succ (fun k => f (a + k)) n
      have hrot :
          (∑ k ∈ Finset.range n, f (a + 1 + k)) =
            ∑ k ∈ Finset.range n, f (a + k) := by
        rw [show (∑ k ∈ Finset.range n, f (a + 1 + k)) =
            ∑ k ∈ Finset.range n, f (a + (k + 1)) by
          apply Finset.sum_congr rfl
          intro k _
          congr 1
          omega]
        rw [hfirst] at hlast
        rw [hper a] at hlast
        have heq :
            (∑ k ∈ Finset.range n, f (a + (k + 1))) + f a =
              (∑ k ∈ Finset.range n, f (a + k)) + f a := by
          simpa using hlast
        exact add_right_cancel heq
      rw [hrot, ih]

/-- After a cyclic index shift, lifted edges are the correspondingly shifted
edges of the original polygon. -/
theorem cyclicEdge_shift_val [NeZero n] (v : ZMod n → ℂ)
    (a : ZMod n) (k : ℕ) :
    cyclicEdge (shiftPolygon v a) k = cyclicEdge v (a.val + k) := by
  simp [cyclicEdge, cyclicVertex, shiftPolygon, Nat.cast_add, add_assoc]

/-- Principal edge turns commute with cyclic index shifts. -/
theorem cyclicEdgeTurn_shift_val [NeZero n] (v : ZMod n → ℂ)
    (a : ZMod n) (k : ℕ) :
    cyclicEdgeTurn (shiftPolygon v a) k =
      cyclicEdgeTurn v (a.val + k) := by
  unfold cyclicEdgeTurn
  rw [cyclicEdge_shift_val, cyclicEdge_shift_val]
  simp [add_assoc]

/-- The total principal edge turn over one period is invariant under cyclic
index shifts. -/
theorem sum_cyclicEdgeTurn_shift [NeZero n] (v : ZMod n → ℂ)
    (a : ZMod n) :
    (∑ k ∈ Finset.range n, cyclicEdgeTurn (shiftPolygon v a) k) =
      ∑ k ∈ Finset.range n, cyclicEdgeTurn v k := by
  simp_rw [cyclicEdgeTurn_shift_val]
  exact sum_range_periodic_nat_shift (cyclicEdgeTurn v) n a.val
    (cyclicEdgeTurn_periodic v)

/-- The `ZMod` consecutive-orientation hypothesis in the natural-number lift. -/
theorem crossR2_cyclicVertex_pos_of_positiveOrientation [NeZero n]
    {v : ZMod n → ℂ}
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (k : ℕ) :
    0 < crossR2 (cyclicVertex v k) (cyclicVertex v (k + 1))
      (cyclicVertex v (k + 2)) := by
  have h := horient ((k + 1 : ℕ) : ZMod n)
  have htwo : (2 : ZMod n) = 1 + 1 := by norm_num
  simpa [cyclicVertex, Nat.cast_add, htwo, add_assoc] using h

/-- The imaginary part of the consecutive-edge quotient is the oriented
twice-area divided by the positive squared norm of the first edge. -/
theorem cyclicEdge_ratio_im (v : ZMod n → ℂ) (k : ℕ) :
    (cyclicEdge v (k + 1) / cyclicEdge v k).im =
      crossR2 (cyclicVertex v k) (cyclicVertex v (k + 1))
        (cyclicVertex v (k + 2)) / Complex.normSq (cyclicEdge v k) := by
  rw [Complex.div_im]
  simp only [cyclicEdge, crossR2, Complex.sub_re, Complex.sub_im]
  rw [show k + 1 + 1 = k + 2 by omega]
  ring

/-- Positive local orientation makes every principal edge turn strictly
between `0` and `π`. -/
theorem cyclicEdgeTurn_mem_Ioo [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (k : ℕ) : cyclicEdgeTurn v k ∈ Set.Ioo 0 Real.pi := by
  have hcross := crossR2_cyclicVertex_pos_of_positiveOrientation horient k
  have him : 0 < (cyclicEdge v (k + 1) / cyclicEdge v k).im := by
    rw [cyclicEdge_ratio_im]
    exact div_pos hcross (Complex.normSq_pos.mpr (cyclicEdge_ne_zero hsimple k))
  refine ⟨?_, ?_⟩
  · unfold cyclicEdgeTurn
    refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le) ?_
    intro hzero
    exact (ne_of_gt him) ((Complex.arg_eq_zero_iff.mp hzero.symm).2)
  · unfold cyclicEdgeTurn
    exact Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt him))

/-- The principal turn between two consecutive lifted edges splits through
the corresponding two-edge secant. -/
private theorem principalTurn_cyclicEdge_split [NeZero n]
    {v : ZMod n → ℂ}
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (i : ℕ) :
    principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1)) =
      principalTurn (cyclicSecant v i (i + 1))
          (cyclicSecant v i (i + 2)) +
        principalTurn (cyclicSecant v i (i + 2))
          (cyclicSecant v (i + 1) (i + 2)) := by
  have hcrossVertex :=
    crossR2_cyclicVertex_pos_of_positiveOrientation horient i
  have hcross : 0 < crossR2 0 (cyclicEdge v i) (cyclicEdge v (i + 1)) := by
    unfold cyclicEdge
    rw [show i + 1 + 1 = i + 2 by omega]
    rw [crossR2_edge_vectors]
    exact hcrossVertex
  have hsplit := principalTurn_add_split_of_cross_pos hcross
  have hsum : cyclicEdge v i + cyclicEdge v (i + 1) =
      cyclicSecant v i (i + 2) := by
    unfold cyclicEdge cyclicSecant
    rw [show i + 1 + 1 = i + 2 by omega]
    ring
  rw [← hsum]
  simpa [cyclicSecant, cyclicEdge,
    show i + 1 + 1 = i + 2 by omega] using hsplit

/-- Hopf's open-chain identity on the polygonal secant grid, cut just before
the closing edge. -/
private theorem hopf_open_chain_sum [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    (∑ i ∈ Finset.range (n - 2),
        principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1))) =
      (∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j) (cyclicSecant v 0 (j + 1))) +
      ∑ i ∈ Finset.range (n - 2),
        principalTurn (cyclicSecant v i (n - 1))
          (cyclicSecant v (i + 1) (n - 1)) := by
  have hn3 := three_le_of_positiveOrientation horient
  let T : ℕ → ℝ := fun i =>
    principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1))
  let H : ℕ → ℕ → ℝ := fun i j =>
    principalTurn (cyclicSecant v i j) (cyclicSecant v i (j + 1))
  let V : ℕ → ℕ → ℝ := fun i j =>
    principalTurn (cyclicSecant v i j) (cyclicSecant v (i + 1) j)
  have htriangle : ∀ i, T i = H i (i + 1) + V i (i + 2) := by
    intro i
    simpa [T, H, V] using principalTurn_cyclicEdge_split horient i
  have hsquare : ∀ i j, i + 1 < j → j ≤ n - 3 + 1 →
      H i j + V i (j + 1) = V i j + H (i + 1) j := by
    intro i j hij hj
    have hdisj := hsimple.natural_edges_disjoint_of_separated
      (i := i) (j := j) hij (by omega) (Or.inl (by omega))
    simpa [H, V, cyclicSecant] using
      principalTurn_secant_square_of_disjoint_segments hdisj
  have hgrid := hopf_grid_sum T H V htriangle (n - 3) hsquare
  have hsub1 : n - 3 + 1 = n - 2 := by omega
  have hsub2 : n - 3 + 2 = n - 1 := by omega
  rw [hsub1, hsub2] at hgrid
  simpa [T, H, V] using hgrid

/-- The canonical heading advances by the principal edge turn. -/
@[simp] theorem cyclicEdgeHeading_succ (v : ZMod n → ℂ) (k : ℕ) :
    cyclicEdgeHeading v (k + 1) =
      cyclicEdgeHeading v k + cyclicEdgeTurn v k := by
  rfl

/-- The lifted heading is its initial value plus the accumulated principal
edge turns. -/
theorem cyclicEdgeHeading_eq_initial_add_sum (v : ZMod n → ℂ)
    (k : ℕ) :
    cyclicEdgeHeading v k = cyclicEdgeHeading v 0 +
      ∑ i ∈ Finset.range k, cyclicEdgeTurn v i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [cyclicEdgeHeading_succ, ih, Finset.sum_range_succ]
      ring

/-- One positive turn is equivalently the statement that the principal edge
turns over one period sum to `2π`. -/
theorem hasPositiveTurningNumberOne_iff_sum (v : ZMod n → ℂ) :
    HasPositiveTurningNumberOne v ↔
      (∑ i ∈ Finset.range n, cyclicEdgeTurn v i) = 2 * Real.pi := by
  rw [HasPositiveTurningNumberOne,
    cyclicEdgeHeading_eq_initial_add_sum]
  constructor <;> intro h <;> linarith

/-- Positive local orientation makes the canonical lifted heading strictly
increasing. -/
theorem cyclicEdgeHeading_strictMono [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    StrictMono (cyclicEdgeHeading v) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [cyclicEdgeHeading_succ]
  exact lt_add_of_pos_right _ (cyclicEdgeTurn_mem_Ioo hsimple horient k).1

/-- Each canonical heading increment is strictly less than `π`. -/
theorem cyclicEdgeHeading_succ_lt_add_pi [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (k : ℕ) :
    cyclicEdgeHeading v (k + 1) < cyclicEdgeHeading v k + Real.pi := by
  rw [cyclicEdgeHeading_succ]
  simpa [add_comm] using
    add_lt_add_left (cyclicEdgeTurn_mem_Ioo hsimple horient k).2
      (cyclicEdgeHeading v k)

/-- Modulo `2π`, the canonical lifted heading is the ordinary argument of
the corresponding edge. -/
theorem cyclicEdgeHeading_coe_angle [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (k : ℕ) :
    (cyclicEdgeHeading v k : Real.Angle) =
      (Complex.arg (cyclicEdge v k) : Real.Angle) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [cyclicEdgeHeading_succ, Real.Angle.coe_add, ih]
      unfold cyclicEdgeTurn
      rw [Complex.arg_div_coe_angle
        (cyclicEdge_ne_zero hsimple (k + 1)) (cyclicEdge_ne_zero hsimple k)]
      abel

/-- The complex exponential of the lifted heading is the exponential of the
principal edge argument. -/
private theorem exp_cyclicEdgeHeading_mul_I [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (k : ℕ) :
    Complex.exp ((cyclicEdgeHeading v k : ℂ) * Complex.I) =
      Complex.exp ((Complex.arg (cyclicEdge v k) : ℂ) * Complex.I) := by
  have hangle := cyclicEdgeHeading_coe_angle hsimple k
  have hcos := congrArg Real.Angle.cos hangle
  have hsin := congrArg Real.Angle.sin hangle
  apply Complex.ext
  · simpa [Complex.exp_ofReal_mul_I_re] using hcos
  · simpa [Complex.exp_ofReal_mul_I_im] using hsin

/-- Algebraic reconstruction of each edge from its canonical lifted heading
and Euclidean length. -/
theorem cyclicEdge_length_mul_exp_heading [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (k : ℕ) :
    (cyclicEdgeLength v k : ℂ) *
        Complex.exp ((cyclicEdgeHeading v k : ℂ) * Complex.I) =
      cyclicEdge v k := by
  unfold cyclicEdgeLength
  rw [exp_cyclicEdgeHeading_mul_I hsimple k,
    Complex.norm_mul_exp_arg_mul_I]

/-- The one-period scalar Umlaufsatz conclusion propagates to every shifted
natural lift because the principal turn sequence is cyclic. -/
theorem cyclicEdgeHeading_add_n [NeZero n] {v : ZMod n → ℂ}
    (hone : HasPositiveTurningNumberOne v) (k : ℕ) :
    cyclicEdgeHeading v (k + n) =
      cyclicEdgeHeading v k + 2 * Real.pi := by
  induction k with
  | zero =>
      simpa [HasPositiveTurningNumberOne] using hone
  | succ k ih =>
      rw [show k + 1 + n = k + n + 1 by omega,
        cyclicEdgeHeading_succ, cyclicEdgeHeading_succ, ih,
        cyclicEdgeTurn_periodic]
      ring

/-! ## Telescoping reconstruction and support sums -/

/-- Lifted vertices are periodic with the polygon size. -/
theorem cyclicVertex_periodic [NeZero n] (v : ZMod n → ℂ) (k : ℕ) :
    cyclicVertex v (k + n) = cyclicVertex v k := by
  simp [cyclicVertex, Nat.cast_add]

/-! ## Evaluation of the lowest-vertex boundary cut -/

/-- Vertex zero differs from every other natural representative in the open
fundamental range. -/
private theorem vertex_zero_ne_nat [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n) {j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j < n) :
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
      have h := zmod_natCast_ne_of_lt (n := n) (a := 0) (b := j)
        (by omega) hjn (Nat.ne_of_lt (by omega))
      simpa using h
    have h1jz : (0 : ZMod n) + 1 ≠ (j : ZMod n) := by
      have hraw := zmod_natCast_ne_of_lt (n := n) (a := 1) (b := j)
        (by omega) hjn (by omega)
      have h : (1 : ZMod n) ≠ (j : ZMod n) := by
        simpa using hraw
      simpa using h
    have hj10z : (j : ZMod n) + 1 ≠ 0 := by
      have hj1n : j + 1 < n := by omega
      have hraw := zmod_natCast_ne_of_lt (n := n) (a := j + 1) (b := 0)
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

/-- On the closed upper half-plane cut along the negative real axis, a
principal turn is the ordinary difference of principal arguments. -/
private theorem principalTurn_eq_sub_arg_of_upper_rightCut {u w : ℂ}
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
  have huarg0 : 0 ≤ Complex.arg u :=
    Complex.arg_nonneg_iff.mpr hu
  have hwarg0 : 0 ≤ Complex.arg w :=
    Complex.arg_nonneg_iff.mpr hw
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
  have hp : principalTurn u w ∈ Set.Ioc (-Real.pi) Real.pi := by
    exact Complex.arg_mem_Ioc (w / u)
  have hreal := congrArg Real.Angle.toReal hcoe
  rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hp,
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hdiff] at hreal
  exact hreal

/-- The closing principal turn complements the upper-cut argument difference
to π. -/
private theorem principalTurn_neg_left_add_arg_sub_of_upper_rightCut
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
  have hzu := principalTurn_eq_sub_arg_of_upper_rightCut
    hz hzr hu hur
  unfold principalTurn at hzu ⊢
  rw [div_neg, hneg, hzu]
  ring

/-- A finite sum of successive differences over an interval telescopes. -/
private theorem sum_Ico_succ_sub (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
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

/-- Principal turns telescope along a chain contained in the upper cut. -/
private theorem sum_principalTurn_upper_rightCut
    (U : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b)
    (him : ∀ j, a ≤ j → j ≤ b → 0 ≤ (U j).im)
    (hre : ∀ j, a ≤ j → j ≤ b → (U j).im = 0 → 0 < (U j).re) :
    (∑ j ∈ Finset.Ico a b, principalTurn (U j) (U (j + 1))) =
      Complex.arg (U b) - Complex.arg (U a) := by
  rw [← sum_Ico_succ_sub (fun j => Complex.arg (U j)) hab]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  apply principalTurn_eq_sub_arg_of_upper_rightCut
  · exact him j hj.1 (by omega)
  · exact hre j hj.1 (by omega)
  · exact him (j + 1) (by omega) (by omega)
  · exact hre (j + 1) (by omega) (by omega)

/-- From a lexicographically lowest vertex, every nontrivial secant lies in
the upper cut and never points along the nonpositive real ray. -/
private theorem cyclicSecant_zero_upper_rightCut [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re)
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) :
    0 ≤ (cyclicSecant v 0 j).im ∧
      ((cyclicSecant v 0 j).im = 0 →
        0 < (cyclicSecant v 0 j).re) := by
  have him := hminIm (j : ZMod n)
  have hne := vertex_zero_ne_nat hsimple hn3 hj1 hjn
  constructor
  · simpa [cyclicSecant, cyclicVertex] using sub_nonneg.mpr him
  · intro hzero
    have himEq : (v 0).im = (v (j : ZMod n)).im := by
      simpa [cyclicSecant, cyclicVertex] using
        (sub_eq_zero.mp hzero).symm
    have hre := hminReOnTie (j : ZMod n) himEq
    have hsecne : cyclicSecant v 0 j ≠ 0 := by
      unfold cyclicSecant
      rw [sub_ne_zero]
      exact hne.symm
    have hreNonneg : 0 ≤ (cyclicSecant v 0 j).re := by
      simpa [cyclicSecant, cyclicVertex] using sub_nonneg.mpr hre
    exact lt_of_le_of_ne hreNonneg fun hreZero =>
      hsecne (Complex.ext hreZero.symm hzero)

/-- The upper radial boundary chain telescopes to the difference of its
endpoint arguments. -/
private theorem top_sum_eq_arg_sub [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re) :
    (∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j)
          (cyclicSecant v 0 (j + 1))) =
      Complex.arg (cyclicSecant v 0 (n - 1)) -
        Complex.arg (cyclicSecant v 0 1) := by
  apply sum_principalTurn_upper_rightCut
  · omega
  · intro j hj1 hjlast
    exact (cyclicSecant_zero_upper_rightCut hsimple hn3 hminIm
      hminReOnTie hj1 (by omega)).1
  · intro j hj1 hjlast
    exact (cyclicSecant_zero_upper_rightCut hsimple hn3 hminIm
      hminReOnTie hj1 (by omega)).2

/-- The lower radial boundary is the same chain traversed after negating both
secants, so it equals the upper radial boundary. -/
private theorem lower_sum_eq_top_sum [NeZero n] (v : ZMod n → ℂ) :
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
  rw [hfirst, hsecond, principalTurn_neg]

/-- Positive orientation at vertex zero is the positive cross product of the
first and last radial secants from vertex zero. -/
private theorem cross_first_lastSecant_pos [NeZero n]
    {v : ZMod n → ℂ} (hn3 : 3 ≤ n)
    (horient : ∀ i : ZMod n,
      0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    0 < crossR2 0 (cyclicSecant v 0 1)
      (cyclicSecant v 0 (n - 1)) := by
  have hlast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    simp
  have h := horient (0 : ZMod n)
  simp only [zero_sub, zero_add] at h
  rw [← hlast] at h
  have heq :
      crossR2 0 (cyclicSecant v 0 1)
          (cyclicSecant v 0 (n - 1)) =
        crossR2 (v ((n - 1 : ℕ) : ZMod n)) (v 0) (v 1) := by
    unfold cyclicSecant cyclicVertex crossR2
    simp only [Nat.cast_zero, Nat.cast_one, Complex.zero_re, Complex.zero_im,
      Complex.sub_re, Complex.sub_im]
    ring
  rw [heq]
  exact h

/-- For a lowest-vertex cut, the upper radial chain and the closing edge turn
sum exactly to π. -/
private theorem top_add_closing_eq_pi [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (horient : ∀ i : ZMod n,
      0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
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
  have hu := cyclicSecant_zero_upper_rightCut hsimple hn3 hminIm
    hminReOnTie (j := 1) (by omega) (by omega)
  have hz := cyclicSecant_zero_upper_rightCut hsimple hn3 hminIm
    hminReOnTie (j := n - 1) (by omega) (by omega)
  have hcross := cross_first_lastSecant_pos hn3 horient
  have hcomp : principalTurn (-z) u +
      (Complex.arg z - Complex.arg u) = Real.pi :=
    principalTurn_neg_left_add_arg_sub_of_upper_rightCut
      hu.1 hu.2 hz.1 hz.2 hcross
  have htop := top_sum_eq_arg_sub hsimple hn3 hminIm hminReOnTie
  have hedge0 : cyclicEdge v 0 = u := by
    simp [u, cyclicEdge, cyclicSecant, cyclicVertex]
  have hedgeLast : cyclicEdge v (n - 1) = -z := by
    simp [z, cyclicEdge, cyclicSecant, cyclicVertex,
      show n - 1 + 1 = n by omega]
  rw [htop, hedge0, hedgeLast]
  linarith

/-- The full closed Hopf-grid boundary evaluates to one positive turn when
vertex zero is the lexicographically lowest vertex. -/
private theorem hopf_boundary_value_of_lex_min [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (hn3 : 3 ≤ n)
    (horient : ∀ i : ZMod n,
      0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
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
  have htop := top_add_closing_eq_pi hsimple hn3 horient
    hminIm hminReOnTie
  have hlower := lower_sum_eq_top_sum v
  rw [hlower]
  linarith

/-- The closed Hopf grid reduces the full tangent-turn sum to two radial
boundary chains based at vertex zero and two copies of the closing turn. -/
private theorem hopf_closed_boundary_sum [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    (∑ i ∈ Finset.range n,
        principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1))) =
      (∑ j ∈ Finset.Ico 1 (n - 1),
        principalTurn (cyclicSecant v 0 j) (cyclicSecant v 0 (j + 1))) +
      2 * principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) +
      ∑ r ∈ Finset.range (n - 2),
        principalTurn (cyclicSecant v (r + 1) n)
          (cyclicSecant v (r + 2) n) := by
  have hn3 := three_le_of_positiveOrientation horient
  have hopen := hopf_open_chain_sum hsimple horient
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
      principalTurn_cyclicEdge_split horient (r + 1)
  have hsquare : ∀ r, r + 1 < n - 2 →
      H r (n - 2) + V r (n - 2 + 1) =
        V r (n - 2) + H (r + 1) (n - 2) := by
    intro r hr
    have hdisj := hsimple.natural_edges_disjoint_of_separated
      (i := r + 1) (j := n - 1) (by omega) (by omega) (Or.inr (by omega))
    have hnm1 : n - 2 + 1 = n - 1 := by omega
    have hnm2 : n - 2 + 2 = n := by omega
    have hlast : n - 1 + 1 = n := by omega
    simp only [H, V, hnm1, hnm2, hlast]
    simpa [cyclicSecant, add_assoc, hlast] using
      principalTurn_secant_square_of_disjoint_segments hdisj
  have htransport := hopf_column_transport T H V htriangle
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
  have hcrossLast :
      0 < crossR2 0 (cyclicEdge v (n - 1)) (cyclicEdge v 0) := by
    have hvertex :=
      crossR2_cyclicVertex_pos_of_positiveOrientation horient (n - 1)
    have hedge :
        0 < crossR2 0 (cyclicEdge v (n - 1)) (cyclicEdge v n) := by
      unfold cyclicEdge
      have hlast : n - 1 + 1 = n := by omega
      have hlast2 : n - 1 + 2 = n + 1 := by omega
      rw [hlast]
      rw [crossR2_edge_vectors]
      rw [hlast, hlast2] at hvertex
      exact hvertex
    rwa [hedgeN] at hedge
  have hcrossConnector :
      0 < crossR2 0 (cyclicSecant v 0 (n - 1)) (cyclicSecant v 1 n) := by
    rw [hsec0Last, hsec1N]
    have heq : crossR2 0 (-cyclicEdge v (n - 1)) (-cyclicEdge v 0) =
        crossR2 0 (cyclicEdge v (n - 1)) (cyclicEdge v 0) := by
      unfold crossR2
      simp
    rwa [heq]
  have hconnector :
      principalTurn (cyclicSecant v 0 (n - 1))
          (cyclicSecant v 1 (n - 1)) +
        principalTurn (cyclicSecant v 1 (n - 1))
          (cyclicSecant v 1 n) =
        principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) := by
    have hs := principalTurn_add_split_of_cross_pos hcrossConnector
    rw [hsecSum] at hs
    have hleft : principalTurn (cyclicSecant v 0 (n - 1))
        (cyclicSecant v 1 n) =
          principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) := by
      rw [hsec0Last, hsec1N, principalTurn_neg]
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

/-- At a lowest-vertex cut, the principal turns over one period sum to one
full positive turn. -/
private theorem sum_cyclicEdgeTurn_eq_two_pi_of_lex_min [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n,
      0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hminIm : ∀ i : ZMod n, (v 0).im ≤ (v i).im)
    (hminReOnTie : ∀ i : ZMod n,
      (v 0).im = (v i).im → (v 0).re ≤ (v i).re) :
    (∑ i ∈ Finset.range n, cyclicEdgeTurn v i) = 2 * Real.pi := by
  have hn3 := three_le_of_positiveOrientation horient
  calc
    (∑ i ∈ Finset.range n, cyclicEdgeTurn v i) =
        ∑ i ∈ Finset.range n,
          principalTurn (cyclicEdge v i) (cyclicEdge v (i + 1)) := by
            rfl
    _ = (∑ j ∈ Finset.Ico 1 (n - 1),
          principalTurn (cyclicSecant v 0 j)
            (cyclicSecant v 0 (j + 1))) +
        2 * principalTurn (cyclicEdge v (n - 1)) (cyclicEdge v 0) +
        ∑ r ∈ Finset.range (n - 2),
          principalTurn (cyclicSecant v (r + 1) n)
            (cyclicSecant v (r + 2) n) :=
      hopf_closed_boundary_sum hsimple horient
    _ = 2 * Real.pi :=
      hopf_boundary_value_of_lex_min hsimple hn3 horient
        hminIm hminReOnTie

/-- Source-free positive polygonal Umlaufsatz: every simple polygon whose
successive triples are positively oriented has turning number one. -/
theorem positivePolygonalUmlaufsatz : PositivePolygonalUmlaufsatz := by
  intro n _ v hsimple horient
  obtain ⟨a, hminIm, hminReOnTie⟩ := shift_zero_min_im_then_re v
  let w := shiftPolygon v a
  have hsimpleW : IsSimplePolygon w := by
    exact isSimplePolygon_shift hsimple a
  have horientW : ∀ i : ZMod n,
      0 < crossR2 (w (i - 1)) (w i) (w (i + 1)) := by
    exact positiveOrientation_shift horient a
  have hsumW :
      (∑ i ∈ Finset.range n, cyclicEdgeTurn w i) = 2 * Real.pi :=
    sum_cyclicEdgeTurn_eq_two_pi_of_lex_min hsimpleW horientW
      hminIm hminReOnTie
  have hsumV :
      (∑ i ∈ Finset.range n, cyclicEdgeTurn v i) = 2 * Real.pi := by
    rw [← sum_cyclicEdgeTurn_shift v a]
    exact hsumW
  exact (hasPositiveTurningNumberOne_iff_sum v).2 hsumV

/-- Per-polygon form of the source-free positive polygonal Umlaufsatz. -/
theorem hasPositiveTurningNumberOne_of_simple_positiveOrientation [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n,
      0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    HasPositiveTurningNumberOne v :=
  positivePolygonalUmlaufsatz n v hsimple horient

/-- Telescoping reconstruction from the lifted outgoing edges. -/
private theorem cyclicVertex_eq_base_add_sum_edges (v : ZMod n → ℂ) (j : ℕ) :
    cyclicVertex v j = cyclicVertex v 0 + ∑ m ∈ Finset.range j, cyclicEdge v m := by
  induction j with
  | zero =>
      simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      unfold cyclicEdge
      ring

/-- Interval form of telescoping reconstruction. -/
private theorem cyclicVertex_sub_eq_sum_edges (v : ZMod n → ℂ)
    {k j : ℕ} (hkj : k ≤ j) :
    cyclicVertex v j - cyclicVertex v k =
      ∑ m ∈ Finset.Ico k j, cyclicEdge v m := by
  rw [Finset.sum_Ico_eq_sub _ hkj]
  have hj := cyclicVertex_eq_base_add_sum_edges v j
  have hk := cyclicVertex_eq_base_add_sum_edges v k
  linear_combination hj - hk

/-- Left-distance telescoping in the canonical edge-heading frame. -/
private theorem im_rot_cyclicVertex_sub [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) {k j : ℕ} (hkj : k ≤ j) :
    (Complex.exp (((-cyclicEdgeHeading v k : ℝ) : ℂ) * Complex.I) *
        (cyclicVertex v j - cyclicVertex v k)).im =
      ∑ m ∈ Finset.Ico k j,
        cyclicEdgeLength v m *
          Real.sin (cyclicEdgeHeading v m - cyclicEdgeHeading v k) := by
  rw [cyclicVertex_sub_eq_sum_edges v hkj, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← cyclicEdge_length_mul_exp_heading hsimple m]
  have hexp :
      Complex.exp (((-cyclicEdgeHeading v k : ℝ) : ℂ) * Complex.I) *
          ((cyclicEdgeLength v m : ℂ) *
            Complex.exp ((cyclicEdgeHeading v m : ℂ) * Complex.I)) =
        (cyclicEdgeLength v m : ℂ) *
          Complex.exp (((cyclicEdgeHeading v m - cyclicEdgeHeading v k : ℝ) : ℂ) *
            Complex.I) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hexp, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `sin` is strictly negative on the open second half of a positive turn. -/
private theorem sin_neg_of_pi_lt {x : ℝ} (hπ : Real.pi < x)
    (h2π : x < 2 * Real.pi) : Real.sin x < 0 := by
  have hsub : Real.sin (2 * Real.pi - x) = -Real.sin x := Real.sin_two_pi_sub x
  have hpos : 0 < Real.sin (2 * Real.pi - x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [hsub] at hpos
  linarith

/-- Weak support on one lifted period, conditional only on the one-turn
Umlaufsatz equality. -/
private theorem support_left_nonneg_of_turningNumberOne [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hone : HasPositiveTurningNumberOne v) (k : ℕ) {j : ℕ}
    (hkj : k ≤ j) (hjn : j ≤ k + n) :
    0 ≤ (Complex.exp (((-cyclicEdgeHeading v k : ℝ) : ℂ) * Complex.I) *
      (cyclicVertex v j - cyclicVertex v k)).im := by
  rw [im_rot_cyclicVertex_sub hsimple hkj]
  have hmono := cyclicEdgeHeading_strictMono hsimple horient
  have hzero : ∑ m ∈ Finset.Ico k (k + n),
      cyclicEdgeLength v m *
        Real.sin (cyclicEdgeHeading v m - cyclicEdgeHeading v k) = 0 := by
    have H := im_rot_cyclicVertex_sub hsimple (Nat.le_add_right k n)
    rw [cyclicVertex_periodic, sub_self, mul_zero, Complex.zero_im] at H
    exact H.symm
  have hsplit :
      (∑ m ∈ Finset.Ico k j, cyclicEdgeLength v m *
        Real.sin (cyclicEdgeHeading v m - cyclicEdgeHeading v k)) =
        -∑ m ∈ Finset.Ico j (k + n), cyclicEdgeLength v m *
          Real.sin (cyclicEdgeHeading v m - cyclicEdgeHeading v k) := by
    have hc := Finset.sum_Ico_consecutive
      (fun m => cyclicEdgeLength v m *
        Real.sin (cyclicEdgeHeading v m - cyclicEdgeHeading v k)) hkj hjn
    rw [hzero] at hc
    linarith
  by_cases hcross : ∀ m ∈ Finset.Ico k j,
      cyclicEdgeHeading v m - cyclicEdgeHeading v k ≤ Real.pi
  · apply Finset.sum_nonneg
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hαnn : 0 ≤ cyclicEdgeHeading v m - cyclicEdgeHeading v k :=
      sub_nonneg.2 (hmono.monotone hm.1)
    exact mul_nonneg (cyclicEdgeLength_pos hsimple m).le
      (Real.sin_nonneg_of_nonneg_of_le_pi hαnn
        (hcross m (Finset.mem_Ico.2 hm)))
  · push Not at hcross
    obtain ⟨m₀, hm₀mem, hm₀⟩ := hcross
    rw [Finset.mem_Ico] at hm₀mem
    rw [hsplit, neg_nonneg]
    apply Finset.sum_nonpos
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm₀m : m₀ < m := lt_of_lt_of_le hm₀mem.2 hm.1
    have hαgt : Real.pi < cyclicEdgeHeading v m - cyclicEdgeHeading v k := by
      have h := hmono hm₀m
      linarith
    have hkm : k < m := lt_of_le_of_lt hm₀mem.1 hm₀m
    have hwin : cyclicEdgeHeading v k < cyclicEdgeHeading v m ∧
        cyclicEdgeHeading v m < cyclicEdgeHeading v k + 2 * Real.pi := by
      refine ⟨hmono hkm, ?_⟩
      have hw := hmono hm.2
      rw [cyclicEdgeHeading_add_n hone] at hw
      exact hw
    have hsin : Real.sin
        (cyclicEdgeHeading v m - cyclicEdgeHeading v k) < 0 :=
      sin_neg_of_pi_lt hαgt (by linarith [hwin.2])
    exact mul_nonpos_of_nonneg_of_nonpos
      (cyclicEdgeLength_pos hsimple m).le hsin.le

/-- Strict support on the interior vertices of one lifted period, conditional
only on the one-turn Umlaufsatz equality. -/
private theorem support_left_pos_of_turningNumberOne [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hone : HasPositiveTurningNumberOne v) (k : ℕ) {j : ℕ}
    (hkj : k + 1 < j) (hjn : j < k + n) :
    0 < (Complex.exp (((-cyclicEdgeHeading v k : ℝ) : ℂ) * Complex.I) *
      (cyclicVertex v j - cyclicVertex v k)).im := by
  rw [im_rot_cyclicVertex_sub hsimple (by omega : k ≤ j)]
  have hmono := cyclicEdgeHeading_strictMono hsimple horient
  have hzero : ∑ m ∈ Finset.Ico k (k + n),
      cyclicEdgeLength v m *
        Real.sin (cyclicEdgeHeading v m - cyclicEdgeHeading v k) = 0 := by
    have H := im_rot_cyclicVertex_sub hsimple (Nat.le_add_right k n)
    rw [cyclicVertex_periodic, sub_self, mul_zero, Complex.zero_im] at H
    exact H.symm
  have hsplit :
      (∑ m ∈ Finset.Ico k j, cyclicEdgeLength v m *
        Real.sin (cyclicEdgeHeading v m - cyclicEdgeHeading v k)) =
        -∑ m ∈ Finset.Ico j (k + n), cyclicEdgeLength v m *
          Real.sin (cyclicEdgeHeading v m - cyclicEdgeHeading v k) := by
    have hc := Finset.sum_Ico_consecutive
      (fun m => cyclicEdgeLength v m *
        Real.sin (cyclicEdgeHeading v m - cyclicEdgeHeading v k))
      (by omega : k ≤ j) (by omega : j ≤ k + n)
    rw [hzero] at hc
    linarith
  by_cases hcross : ∀ m ∈ Finset.Ico k j,
      cyclicEdgeHeading v m - cyclicEdgeHeading v k ≤ Real.pi
  · apply Finset.sum_pos'
    · intro m hm
      rw [Finset.mem_Ico] at hm
      have hαnn : 0 ≤ cyclicEdgeHeading v m - cyclicEdgeHeading v k :=
        sub_nonneg.2 (hmono.monotone hm.1)
      exact mul_nonneg (cyclicEdgeLength_pos hsimple m).le
        (Real.sin_nonneg_of_nonneg_of_le_pi hαnn
          (hcross m (Finset.mem_Ico.2 hm)))
    · refine ⟨k + 1, Finset.mem_Ico.2 ⟨Nat.le_add_right k 1, hkj⟩, ?_⟩
      have hstep : cyclicEdgeHeading v (k + 1) - cyclicEdgeHeading v k =
          cyclicEdgeTurn v k := by
        rw [cyclicEdgeHeading_succ]
        ring
      have hturn := cyclicEdgeTurn_mem_Ioo hsimple horient k
      rw [hstep]
      exact mul_pos (cyclicEdgeLength_pos hsimple (k + 1))
        (Real.sin_pos_of_pos_of_lt_pi hturn.1 hturn.2)
  · push Not at hcross
    obtain ⟨m₀, hm₀mem, hm₀⟩ := hcross
    rw [Finset.mem_Ico] at hm₀mem
    rw [hsplit, neg_pos]
    apply Finset.sum_neg
    · intro m hm
      rw [Finset.mem_Ico] at hm
      have hm₀m : m₀ < m := lt_of_lt_of_le hm₀mem.2 hm.1
      have hαgt : Real.pi < cyclicEdgeHeading v m - cyclicEdgeHeading v k := by
        have h := hmono hm₀m
        linarith
      have hkm : k < m := lt_of_le_of_lt hm₀mem.1 hm₀m
      have hwin : cyclicEdgeHeading v k < cyclicEdgeHeading v m ∧
          cyclicEdgeHeading v m < cyclicEdgeHeading v k + 2 * Real.pi := by
        refine ⟨hmono hkm, ?_⟩
        have hw := hmono hm.2
        rw [cyclicEdgeHeading_add_n hone] at hw
        exact hw
      exact mul_neg_of_pos_of_neg (cyclicEdgeLength_pos hsimple m)
        (sin_neg_of_pi_lt hαgt (by linarith [hwin.2]))
    · exact ⟨j, Finset.mem_Ico.2 ⟨le_rfl, hjn⟩⟩

/-! ## Cyclic support consequences -/

/-- A cyclic vertex represented in the natural block anchored at `a`. -/
private theorem cyclicVertex_sub_val [NeZero n] (v : ZMod n → ℂ)
    (a c : ZMod n) :
    cyclicVertex v (a.val + (c - a).val) = v c := by
  unfold cyclicVertex
  congr 1
  rw [Nat.cast_add, ZMod.natCast_rightInverse a,
    ZMod.natCast_rightInverse (c - a)]
  ring

/-- The outgoing cyclic edge reconstructed from the canonical heading. -/
private theorem cyclicEdgeVector_at_val [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) (a : ZMod n) :
    v (a + 1) = v a +
      (cyclicEdgeLength v a.val : ℂ) *
        Complex.exp ((cyclicEdgeHeading v a.val : ℂ) * Complex.I) := by
  have h := cyclicEdge_length_mul_exp_heading hsimple a.val
  unfold cyclicEdge cyclicVertex at h
  rw [Nat.cast_add, ZMod.natCast_rightInverse a] at h
  have h' :
      (cyclicEdgeLength v a.val : ℂ) *
          Complex.exp ((cyclicEdgeHeading v a.val : ℂ) * Complex.I) =
        v (a + 1) - v a := by
    simpa using h
  rw [h']
  ring

/-- The signed area against a polar edge vector is its length times the
corresponding left-distance functional. -/
private theorem crossR2_cyclicEdgeVector (A C : ℂ) (r ψ : ℝ) :
    crossR2 A (A + (r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) C =
      r * (Complex.exp (((-ψ : ℝ) : ℂ) * Complex.I) * (C - A)).im := by
  unfold crossR2
  simp only [add_sub_cancel_left, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  ring

/-- A one-turn positively oriented polygon has global weak edge support. -/
theorem convexEdgeSupport_of_turningNumberOne [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hone : HasPositiveTurningNumberOne v) :
    ConvexEdgeSupport v := by
  intro a c
  set t := (c - a).val
  have htlt : t < n := ZMod.val_lt (c - a)
  have hc : cyclicVertex v (a.val + t) = v c :=
    cyclicVertex_sub_val v a c
  have hleft :
      0 ≤ (Complex.exp (((-cyclicEdgeHeading v a.val : ℝ) : ℂ) * Complex.I) *
        (v c - v a)).im := by
    rw [← hc, show v a = cyclicVertex v a.val by simp [cyclicVertex]]
    exact support_left_nonneg_of_turningNumberOne hsimple horient hone a.val
      (by omega) (by omega)
  rw [cyclicEdgeVector_at_val hsimple, crossR2_cyclicEdgeVector]
  exact mul_nonneg (cyclicEdgeLength_pos hsimple a.val).le hleft

/-- A one-turn positively oriented polygon has strict global edge support away
from the two endpoints of each edge. -/
theorem strictConvexEdgeSupport_of_turningNumberOne [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1)))
    (hone : HasPositiveTurningNumberOne v) :
    StrictConvexEdgeSupport v := by
  intro a c hca hca1
  set t := (c - a).val
  have hb : ((t : ℕ) : ZMod n) = c - a :=
    ZMod.natCast_rightInverse (c - a)
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hb
    exact hca (sub_eq_zero.1 hb.symm)
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, Nat.cast_one] at hb
    exact hca1 (by linear_combination hb.symm)
  have htn : t < n := ZMod.val_lt (c - a)
  have hc : cyclicVertex v (a.val + t) = v c :=
    cyclicVertex_sub_val v a c
  have hleft :
      0 < (Complex.exp (((-cyclicEdgeHeading v a.val : ℝ) : ℂ) * Complex.I) *
        (v c - v a)).im := by
    rw [← hc, show v a = cyclicVertex v a.val by simp [cyclicVertex]]
    exact support_left_pos_of_turningNumberOne hsimple horient hone a.val
      (by omega) (by omega)
  rw [cyclicEdgeVector_at_val hsimple, crossR2_cyclicEdgeVector]
  exact mul_pos (cyclicEdgeLength_pos hsimple a.val) hleft

/-- A simple positively oriented polygon has global weak edge support. -/
theorem convexEdgeSupport_of_simple_positiveOrientation [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n,
      0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ConvexEdgeSupport v :=
  convexEdgeSupport_of_turningNumberOne hsimple horient
    (hasPositiveTurningNumberOne_of_simple_positiveOrientation
      hsimple horient)

/-- A simple positively oriented polygon has strict support by every oriented
edge away from that edge's two endpoints. -/
theorem strictConvexEdgeSupport_of_simple_positiveOrientation [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n,
      0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    StrictConvexEdgeSupport v :=
  strictConvexEdgeSupport_of_turningNumberOne hsimple horient
    (hasPositiveTurningNumberOne_of_simple_positiveOrientation
      hsimple horient)

/-! ## The integral period defect -/

/-- Edge periodicity forces the total lifted heading defect to be an integral
multiple of `2π`.  This part does not use simplicity beyond nondegenerate edges. -/
theorem cyclicEdgeHeading_period_integer [NeZero n] {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v) :
    ∃ m : ℤ, cyclicEdgeHeading v n =
      cyclicEdgeHeading v 0 + 2 * Real.pi * m := by
  have hedge : cyclicEdge v n = cyclicEdge v 0 := by
    simpa using cyclicEdge_periodic v 0
  have hangle : (cyclicEdgeHeading v n : Real.Angle) =
      (cyclicEdgeHeading v 0 : Real.Angle) := by
    rw [cyclicEdgeHeading_coe_angle hsimple,
      cyclicEdgeHeading_coe_angle hsimple, hedge]
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hangle
  refine ⟨m, ?_⟩
  linarith

/-- Under positive consecutive orientation, the integral period is positive. -/
theorem cyclicEdgeHeading_period_positive_integer [NeZero n]
    {v : ZMod n → ℂ}
    (hsimple : IsSimplePolygon v)
    (horient : ∀ i : ZMod n, 0 < crossR2 (v (i - 1)) (v i) (v (i + 1))) :
    ∃ m : ℤ, 0 < m ∧ cyclicEdgeHeading v n =
      cyclicEdgeHeading v 0 + 2 * Real.pi * m := by
  obtain ⟨m, hm⟩ := cyclicEdgeHeading_period_integer hsimple
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hinc := cyclicEdgeHeading_strictMono hsimple horient hn
  have hmreal : 0 < (m : ℝ) := by
    rw [hm] at hinc
    nlinarith [Real.pi_pos]
  exact ⟨m, by exact_mod_cast hmreal, hm⟩

end Gluck.Discrete
