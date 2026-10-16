/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.TangentChord

/-!
# Discrete D1: convexity and simplicity (Euclidean, positive)

The positive-curvature simplicity layer of the discrete Menger program. A closed
Euclidean development whose turning angles all lie in `(0, π)` and sum to `2π`
has strictly monotone edge directions, hence bounds a convex region and is
therefore simple. In the positive case (`0 < κ i` for all `i`) simplicity is
free, exactly parallel to smooth Gluck.

* `heading_lt_succ`, `heading_strictMono` — the heading is strictly increasing.
* `heading_sub_lt_two_pi` — the strict heading-window bound on one period.
* `im_rot_vertex_sub` — the left-distance telescoping identity.
* `support_left_nonneg`, `support_left_pos` — the support half-plane crux.
* `polygonR2_edge_ne`, `polygonR2_consecutive_inter`,
  `polygonR2_nonadjacent_disjoint` — the three simplicity clauses.
* `isSimplePolygon_of_turningPositive` — L1: positive turning ⇒ simple.
* `realizesR2_const` — the constant branch of D-R²-pos (first `RealizesR2`
  witness).

-/

@[expose] public section

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

/-! ## Heading windows -/

/-- One development step advances the heading by the next turning angle. -/
private lemma heading_succ' (κ ℓ : ZMod n → ℝ) (j : ℕ) :
    heading κ ℓ (j + 1) = heading κ ℓ j + turningAngle 0 κ ℓ ((j + 1 : ℕ) : ZMod n) := by
  unfold heading
  rw [Finset.sum_range_succ]

/-- Strict monotonicity, one step: with all `κ i > 0` on a moderate arc, the
heading strictly increases at each step. Project-local (bespoke development). -/
lemma heading_lt_succ {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) (j : ℕ) :
    heading κ ℓ j < heading κ ℓ (j + 1) := by
  rw [heading_succ']
  have := turningAngle_pos h (hκ ((j + 1 : ℕ) : ZMod n))
  linarith

/-- The heading is strictly increasing on `ℕ`. Project-local. -/
lemma heading_strictMono {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) : StrictMono (heading κ ℓ) :=
  strictMono_nat_of_lt_succ (heading_lt_succ h hκ)

/-- Heading window bound: with total turning `2π`, for `j < k < j + n` the
heading `ψ k` lies strictly between `ψ j` and `ψ j + 2π`. Project-local. -/
lemma heading_sub_lt_two_pi [NeZero n] {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) (hT : turningSum κ ℓ = 2 * Real.pi)
    {j k : ℕ} (hjk : j < k) (hkn : k < j + n) :
    heading κ ℓ j < heading κ ℓ k ∧ heading κ ℓ k < heading κ ℓ j + 2 * Real.pi := by
  refine ⟨heading_strictMono h hκ hjk, ?_⟩
  have := heading_strictMono h hκ hkn
  rwa [heading_add_n hT] at this

/-! ## The support half-plane -/

/-- Left-distance telescoping: for `k ≤ j`, the signed distance of vertex `P j`
to the left of edge line `k` telescopes into a sum of `ℓ_m sin(ψ_m − ψ_k)`.
Project-local (bespoke development). -/
lemma im_rot_vertex_sub (κ ℓ : ZMod n → ℝ) {k j : ℕ} (hkj : k ≤ j) :
    (Complex.exp (((-heading κ ℓ k : ℝ) : ℂ) * Complex.I)
        * (vertexR2 κ ℓ j - vertexR2 κ ℓ k)).im
      = ∑ m ∈ Finset.Ico k j,
          ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k) := by
  have hdiff : vertexR2 κ ℓ j - vertexR2 κ ℓ k
      = ∑ m ∈ Finset.Ico k j,
          (ℓ (m : ZMod n) : ℂ) * Complex.exp ((heading κ ℓ m : ℂ) * Complex.I) := by
    rw [vertexR2, vertexR2, ← Finset.sum_Ico_eq_sub _ hkj]
  rw [hdiff, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hexp : Complex.exp (((-heading κ ℓ k : ℝ) : ℂ) * Complex.I)
        * ((ℓ (m : ZMod n) : ℂ) * Complex.exp ((heading κ ℓ m : ℂ) * Complex.I))
      = (ℓ (m : ZMod n) : ℂ)
          * Complex.exp (((heading κ ℓ m - heading κ ℓ k : ℝ) : ℂ) * Complex.I) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hexp, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `sin` is strictly negative on the open second half of the circle. -/
private lemma sin_neg_of_pi_lt {x : ℝ} (h1 : Real.pi < x) (h2 : x < 2 * Real.pi) :
    Real.sin x < 0 := by
  have hsub : Real.sin (2 * Real.pi - x) = -Real.sin x := Real.sin_two_pi_sub x
  have hpos : 0 < Real.sin (2 * Real.pi - x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [hsub] at hpos
  linarith

/-- Support half-plane (weak form): every developed vertex `P j` on one lifted
period lies weakly to the left of edge line `k`. THE crux of L1. Project-local. -/
lemma support_left_nonneg [NeZero n] {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (k : ℕ) {j : ℕ}
    (hkj : k ≤ j) (hjn : j ≤ k + n) :
    0 ≤ (Complex.exp (((-heading κ ℓ k : ℝ) : ℂ) * Complex.I)
          * (vertexR2 κ ℓ j - vertexR2 κ ℓ k)).im := by
  rw [im_rot_vertex_sub κ ℓ hkj]
  have hmono := heading_strictMono h hκ
  -- backward representation via closure: ∑_{[k,j)} = −∑_{[j,k+n)}
  have hzero : ∑ m ∈ Finset.Ico k (k + n),
      ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k) = 0 := by
    have H := im_rot_vertex_sub κ ℓ (Nat.le_add_right k n)
    rw [vertexR2_add_n hE hT k, sub_self, mul_zero, Complex.zero_im] at H
    exact H.symm
  have hsplit : ∑ m ∈ Finset.Ico k j,
        ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k)
      = -∑ m ∈ Finset.Ico j (k + n),
          ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k) := by
    have hc := Finset.sum_Ico_consecutive
      (fun m => ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k)) hkj hjn
    rw [hzero] at hc
    linarith
  by_cases hcross : ∀ m ∈ Finset.Ico k j, heading κ ℓ m - heading κ ℓ k ≤ Real.pi
  · -- forward: every increment is nonnegative
    apply Finset.sum_nonneg
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hαnn : 0 ≤ heading κ ℓ m - heading κ ℓ k :=
      sub_nonneg.2 (hmono.monotone hm.1)
    exact mul_nonneg (h.length_pos _).le
      (Real.sin_nonneg_of_nonneg_of_le_pi hαnn (hcross m (Finset.mem_Ico.2 hm)))
  · -- backward: past the π-crossing every increment is nonpositive
    push Not at hcross
    obtain ⟨m₀, hm₀mem, hm₀⟩ := hcross
    rw [Finset.mem_Ico] at hm₀mem
    rw [hsplit, neg_nonneg]
    apply Finset.sum_nonpos
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm₀m : m₀ < m := lt_of_lt_of_le hm₀mem.2 hm.1
    have hαgt : Real.pi < heading κ ℓ m - heading κ ℓ k := by
      have := hmono hm₀m; linarith
    have hkm : k < m := lt_of_le_of_lt hm₀mem.1 hm₀m
    have hwin := heading_sub_lt_two_pi h hκ hT hkm hm.2
    have : Real.sin (heading κ ℓ m - heading κ ℓ k) < 0 :=
      sin_neg_of_pi_lt hαgt (by linarith [hwin.2])
    exact mul_nonpos_of_nonneg_of_nonpos (h.length_pos _).le this.le

/-- Support half-plane (strict form): every developed vertex `P j` strictly
interior to one lifted period lies strictly left of edge line `k`. Project-local. -/
lemma support_left_pos [NeZero n] {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hκ : ∀ i : ZMod n, 0 < κ i) (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (k : ℕ) {j : ℕ}
    (hkj : k + 1 < j) (hjn : j < k + n) :
    0 < (Complex.exp (((-heading κ ℓ k : ℝ) : ℂ) * Complex.I)
          * (vertexR2 κ ℓ j - vertexR2 κ ℓ k)).im := by
  rw [im_rot_vertex_sub κ ℓ (by omega : k ≤ j)]
  have hmono := heading_strictMono h hκ
  have hzero : ∑ m ∈ Finset.Ico k (k + n),
      ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k) = 0 := by
    have H := im_rot_vertex_sub κ ℓ (Nat.le_add_right k n)
    rw [vertexR2_add_n hE hT k, sub_self, mul_zero, Complex.zero_im] at H
    exact H.symm
  have hsplit : ∑ m ∈ Finset.Ico k j,
        ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k)
      = -∑ m ∈ Finset.Ico j (k + n),
          ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k) := by
    have hc := Finset.sum_Ico_consecutive
      (fun m => ℓ (m : ZMod n) * Real.sin (heading κ ℓ m - heading κ ℓ k))
      (by omega : k ≤ j) (by omega : j ≤ k + n)
    rw [hzero] at hc
    linarith
  by_cases hcross : ∀ m ∈ Finset.Ico k j, heading κ ℓ m - heading κ ℓ k ≤ Real.pi
  · -- forward: the (k+1) increment is strictly positive, the rest nonnegative
    apply Finset.sum_pos'
    · intro m hm
      rw [Finset.mem_Ico] at hm
      have hαnn : 0 ≤ heading κ ℓ m - heading κ ℓ k :=
        sub_nonneg.2 (hmono.monotone hm.1)
      exact mul_nonneg (h.length_pos _).le
        (Real.sin_nonneg_of_nonneg_of_le_pi hαnn (hcross m (Finset.mem_Ico.2 hm)))
    · refine ⟨k + 1, Finset.mem_Ico.2 ⟨Nat.le_add_right k 1, hkj⟩, ?_⟩
      have hstep : heading κ ℓ (k + 1) - heading κ ℓ k
          = turningAngle 0 κ ℓ ((k + 1 : ℕ) : ZMod n) := by
        rw [heading_succ']; ring
      have hpos : 0 < turningAngle 0 κ ℓ ((k + 1 : ℕ) : ZMod n) :=
        turningAngle_pos h (hκ _)
      have hlt : turningAngle 0 κ ℓ ((k + 1 : ℕ) : ZMod n) < Real.pi :=
        lt_of_abs_lt (abs_turningAngle_lt_pi h _)
      rw [hstep]
      exact mul_pos (h.length_pos _)
        (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
  · -- backward: past the π-crossing every increment is strictly negative
    push Not at hcross
    obtain ⟨m₀, hm₀mem, hm₀⟩ := hcross
    rw [Finset.mem_Ico] at hm₀mem
    rw [hsplit, neg_pos]
    apply Finset.sum_neg
    · intro m hm
      rw [Finset.mem_Ico] at hm
      have hm₀m : m₀ < m := lt_of_lt_of_le hm₀mem.2 hm.1
      have hαgt : Real.pi < heading κ ℓ m - heading κ ℓ k := by
        have := hmono hm₀m; linarith
      have hkm : k < m := lt_of_le_of_lt hm₀mem.1 hm₀m
      have hwin := heading_sub_lt_two_pi h hκ hT hkm hm.2
      exact mul_neg_of_pos_of_neg (h.length_pos _)
        (sin_neg_of_pi_lt hαgt (by linarith [hwin.2]))
    · exact ⟨j, Finset.mem_Ico.2 ⟨le_rfl, hjn⟩⟩

/-! ## Simplicity from support -/

/-- The cyclic vertex `P (a + t)` is the lifted development vertex `k + t`. -/
private lemma polygonR2_add_nat [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (a : ZMod n) (t : ℕ) :
    polygonR2 κ ℓ (a + (t : ZMod n)) = vertexR2 κ ℓ (a.val + t) := by
  rw [vertexR2_eq_polygon hE hT]
  congr 1
  rw [Nat.cast_add, ZMod.natCast_rightInverse a]

/-- Any cyclic vertex `P c` is a lifted development vertex `k + (c − a).val`, in
the block `[k, k+n)` anchored at edge `a` (`k = a.val`). -/
private lemma polygonR2_sub_val [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (a c : ZMod n) :
    polygonR2 κ ℓ c = vertexR2 κ ℓ (a.val + (c - a).val) := by
  rw [vertexR2_eq_polygon hE hT]
  congr 1
  rw [Nat.cast_add, ZMod.natCast_rightInverse a, ZMod.natCast_rightInverse (c - a)]
  ring

/-- The left-distance functional `z ↦ Im(u·(z − P))` is affine: it respects
convex combinations. Project-local. -/
private lemma im_rot_affine (u P x y : ℂ) {s t : ℝ} (hst : s + t = 1) :
    (u * ((s • x + t • y) - P)).im
      = s * (u * (x - P)).im + t * (u * (y - P)).im := by
  have key : (s • x + t • y) - P = s • (x - P) + t • (y - P) := by
    have hst' : (s : ℂ) + (t : ℂ) = 1 := by exact_mod_cast hst
    simp only [Complex.real_smul]
    linear_combination P * hst'
  rw [key, mul_add, mul_smul_comm, mul_smul_comm, Complex.add_im, Complex.smul_im,
    Complex.smul_im, smul_eq_mul, smul_eq_mul]

/-- The signed area against an edge of polar direction `ψ` is its length
times the corresponding left-distance functional. -/
private lemma crossR2_edgeVector (A C : ℂ) (r ψ : ℝ) :
    crossR2 A
        (A + (r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) C =
      r * (Complex.exp (((-ψ : ℝ) : ℂ) * Complex.I) * (C - A)).im := by
  unfold crossR2
  simp only [add_sub_cancel_left, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  ring

/-- The outgoing cyclic edge is the corresponding polar edge vector in the
chosen natural lift. -/
private lemma polygonR2_edgeVector [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi)
    (a : ZMod n) :
    polygonR2 κ ℓ (a + 1) = polygonR2 κ ℓ a +
      (ℓ a : ℂ) * Complex.exp ((heading κ ℓ a.val : ℂ) * Complex.I) := by
  have hnext := polygonR2_add_nat hE hT a 1
  have hnext' : polygonR2 κ ℓ (a + 1) = vertexR2 κ ℓ (a.val + 1) := by
    simpa using hnext
  rw [hnext', show polygonR2 κ ℓ a = vertexR2 κ ℓ a.val from rfl,
    vertexR2_succ]
  rw [ZMod.natCast_rightInverse a]

/-- Global oriented-edge support for a closed one-turn positive development:
every cyclic vertex lies weakly to the left of every oriented polygon edge. -/
theorem crossR2_polygonR2_edge_vertex_nonneg [NeZero n] {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) (hκ : ∀ i : ZMod n, 0 < κ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi)
    (a c : ZMod n) :
    0 ≤ crossR2 (polygonR2 κ ℓ a) (polygonR2 κ ℓ (a + 1))
      (polygonR2 κ ℓ c) := by
  set t := (c - a).val with ht
  have hc : polygonR2 κ ℓ c = vertexR2 κ ℓ (a.val + t) :=
    polygonR2_sub_val hE hT a c
  have htlt : t < n := by
    simpa [ht] using ZMod.val_lt (c - a)
  have hleft :
      0 ≤ (Complex.exp (((-heading κ ℓ a.val : ℝ) : ℂ) * Complex.I) *
        (polygonR2 κ ℓ c - polygonR2 κ ℓ a)).im := by
    rw [hc, show polygonR2 κ ℓ a = vertexR2 κ ℓ a.val from rfl]
    exact support_left_nonneg h hκ hE hT a.val (by omega) (by omega)
  rw [polygonR2_edgeVector hE hT, crossR2_edgeVector]
  exact mul_nonneg (h.length_pos a).le hleft

/-- Nondegenerate edges: `P i ≠ P (i+1)` since the edge vector has modulus
`ℓ i > 0`. Project-local. -/
lemma polygonR2_edge_ne [NeZero n] {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (i : ZMod n) :
    polygonR2 κ ℓ i ≠ polygonR2 κ ℓ (i + 1) := by
  have e1 : polygonR2 κ ℓ (i + 1) = vertexR2 κ ℓ (i.val + 1) := by
    have := polygonR2_add_nat hE hT i 1
    simpa using this
  have hd : vertexR2 κ ℓ (i.val + 1) - vertexR2 κ ℓ i.val
      = (ℓ ((i.val : ℕ) : ZMod n) : ℂ)
          * Complex.exp ((heading κ ℓ i.val : ℂ) * Complex.I) := by
    rw [vertexR2_succ]; ring
  have hne : (ℓ ((i.val : ℕ) : ZMod n) : ℂ)
      * Complex.exp ((heading κ ℓ i.val : ℂ) * Complex.I) ≠ 0 := by
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    exact_mod_cast ne_of_gt (h.length_pos _)
  rw [show polygonR2 κ ℓ i = vertexR2 κ ℓ i.val from rfl, e1]
  intro heq
  apply hne
  rw [← hd, heq, sub_self]

/-- Cyclic support half-plane: a cyclic vertex `P c` distinct from both
endpoints of edge `a` lies strictly left of edge line `a`. Project-local. -/
private lemma support_pos_cyclic [NeZero n] {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) (hκ : ∀ i : ZMod n, 0 < κ i) (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (a c : ZMod n) (hca : c ≠ a)
    (hca1 : c ≠ a + 1) :
    0 < (Complex.exp (((-heading κ ℓ a.val : ℝ) : ℂ) * Complex.I)
          * (polygonR2 κ ℓ c - polygonR2 κ ℓ a)).im := by
  set t := (c - a).val with htdef
  have hb : ((t : ℕ) : ZMod n) = c - a := ZMod.natCast_rightInverse (c - a)
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, Nat.cast_zero] at hb; exact hca (sub_eq_zero.1 hb.symm)
  have ht1 : t ≠ 1 := by
    intro h1; rw [h1, Nat.cast_one] at hb
    exact hca1 (by linear_combination hb.symm)
  have htn : t < n := ZMod.val_lt (c - a)
  have hpc : polygonR2 κ ℓ c = vertexR2 κ ℓ (a.val + t) := polygonR2_sub_val hE hT a c
  have hpa : polygonR2 κ ℓ a = vertexR2 κ ℓ a.val := rfl
  rw [hpc, hpa]
  exact support_left_pos h hκ hE hT a.val (by omega) (by omega)

/-- Strict global support away from the two endpoints of the oriented edge. -/
theorem crossR2_polygonR2_edge_vertex_pos [NeZero n] {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) (hκ : ∀ i : ZMod n, 0 < κ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi)
    (a c : ZMod n) (hca : c ≠ a) (hca1 : c ≠ a + 1) :
    0 < crossR2 (polygonR2 κ ℓ a) (polygonR2 κ ℓ (a + 1))
      (polygonR2 κ ℓ c) := by
  have hleft := support_pos_cyclic h hκ hE hT a c hca hca1
  rw [polygonR2_edgeVector hE hT, crossR2_edgeVector]
  exact mul_pos (h.length_pos a) hleft

/-- The left-distance functional vanishes on the anchoring edge's far endpoint
`P (i+1)` (it lies on edge line `i`). Project-local. -/
private lemma im_rot_edge_end_zero [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (i : ZMod n) :
    (Complex.exp (((-heading κ ℓ i.val : ℝ) : ℂ) * Complex.I)
        * (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)).im = 0 := by
  have e1 : polygonR2 κ ℓ (i + 1) = vertexR2 κ ℓ (i.val + 1) := by
    simpa using polygonR2_add_nat hE hT i 1
  rw [e1, show polygonR2 κ ℓ i = vertexR2 κ ℓ i.val from rfl,
    im_rot_vertex_sub κ ℓ (show i.val ≤ i.val + 1 by omega)]
  rw [Finset.sum_Ico_succ_top (le_refl i.val)]
  simp

/-- Non-adjacent edges are disjoint: both endpoints of the far edge lie strictly
left of the near edge line, so the whole far segment does. Project-local. -/
lemma polygonR2_nonadjacent_disjoint [NeZero n] {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) (hκ : ∀ i : ZMod n, 0 < κ i) (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (i j : ZMod n) (hij : i ≠ j)
    (hij1 : i + 1 ≠ j) (hji1 : j + 1 ≠ i) :
    segment ℝ (polygonR2 κ ℓ i) (polygonR2 κ ℓ (i + 1))
        ∩ segment ℝ (polygonR2 κ ℓ j) (polygonR2 κ ℓ (j + 1)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hz1, hz2⟩
  obtain ⟨r, r', hr, hr', hrr, hz1eq⟩ := hz1
  obtain ⟨s, s', hs, hs', hss, hz2eq⟩ := hz2
  -- L(z) computed from the near edge: on the edge line, hence 0
  have hLnear : (Complex.exp (((-heading κ ℓ i.val : ℝ) : ℂ) * Complex.I)
      * (z - polygonR2 κ ℓ i)).im = 0 := by
    rw [← hz1eq, im_rot_affine _ _ _ _ hrr, sub_self, mul_zero, Complex.zero_im,
      mul_zero, zero_add, im_rot_edge_end_zero hE hT i, mul_zero]
  -- L(z) computed from the far edge: strictly positive
  have hLj : 0 < (Complex.exp (((-heading κ ℓ i.val : ℝ) : ℂ) * Complex.I)
      * (polygonR2 κ ℓ j - polygonR2 κ ℓ i)).im :=
    support_pos_cyclic h hκ hE hT i j (Ne.symm hij) (Ne.symm hij1)
  have hLj1 : 0 < (Complex.exp (((-heading κ ℓ i.val : ℝ) : ℂ) * Complex.I)
      * (polygonR2 κ ℓ (j + 1) - polygonR2 κ ℓ i)).im :=
    support_pos_cyclic h hκ hE hT i (j + 1) hji1
      (by intro hcontra; exact hij (by linear_combination -hcontra))
  have hLfar : 0 < (Complex.exp (((-heading κ ℓ i.val : ℝ) : ℂ) * Complex.I)
      * (z - polygonR2 κ ℓ i)).im := by
    rw [← hz2eq, im_rot_affine _ _ _ _ hss]
    rcases eq_or_lt_of_le hs with hs0 | hspos
    · have hs'1 : s' = 1 := by linarith
      rw [← hs0, zero_mul, zero_add, hs'1, one_mul]; exact hLj1
    · nlinarith [mul_pos hspos hLj, mul_nonneg hs' hLj1.le]
  linarith

/-- Consecutive edges meet only at their shared vertex. The far endpoint of the
second edge lies strictly left of the first edge line, pinning the intersection
to `P (i+1)`. Project-local. -/
lemma polygonR2_consecutive_inter [NeZero n] {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) (hκ : ∀ i : ZMod n, 0 < κ i) (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (hn : 3 ≤ n) (i : ZMod n) :
    segment ℝ (polygonR2 κ ℓ i) (polygonR2 κ ℓ (i + 1))
        ∩ segment ℝ (polygonR2 κ ℓ (i + 1)) (polygonR2 κ ℓ (i + 1 + 1))
      = {polygonR2 κ ℓ (i + 1)} := by
  have hLj2 : 0 < (Complex.exp (((-heading κ ℓ i.val : ℝ) : ℂ) * Complex.I)
      * (polygonR2 κ ℓ (i + 1 + 1) - polygonR2 κ ℓ i)).im := by
    have e2 : polygonR2 κ ℓ (i + 1 + 1) = vertexR2 κ ℓ (i.val + 2) := by
      have h2 := polygonR2_add_nat hE hT i 2
      rw [show i + ((2 : ℕ) : ZMod n) = i + 1 + 1 from by push_cast; ring] at h2
      exact h2
    rw [e2, show polygonR2 κ ℓ i = vertexR2 κ ℓ i.val from rfl]
    exact support_left_pos h hκ hE hT i.val (by omega) (by omega)
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩, ?_⟩
  rintro z ⟨hz1, hz2⟩
  obtain ⟨r, r', hr, hr', hrr, hz1eq⟩ := hz1
  obtain ⟨s, s', hs, hs', hss, hz2eq⟩ := hz2
  have hLnear : (Complex.exp (((-heading κ ℓ i.val : ℝ) : ℂ) * Complex.I)
      * (z - polygonR2 κ ℓ i)).im = 0 := by
    rw [← hz1eq, im_rot_affine _ _ _ _ hrr, sub_self, mul_zero, Complex.zero_im,
      mul_zero, zero_add, im_rot_edge_end_zero hE hT i, mul_zero]
  have hLfar : (Complex.exp (((-heading κ ℓ i.val : ℝ) : ℂ) * Complex.I)
      * (z - polygonR2 κ ℓ i)).im
      = s' * (Complex.exp (((-heading κ ℓ i.val : ℝ) : ℂ) * Complex.I)
          * (polygonR2 κ ℓ (i + 1 + 1) - polygonR2 κ ℓ i)).im := by
    rw [← hz2eq, im_rot_affine _ _ _ _ hss, im_rot_edge_end_zero hE hT i, mul_zero,
      zero_add]
  have hs'0 : s' = 0 := by
    have hz : s' * (Complex.exp (((-heading κ ℓ i.val : ℝ) : ℂ) * Complex.I)
        * (polygonR2 κ ℓ (i + 1 + 1) - polygonR2 κ ℓ i)).im = 0 := by
      rw [← hLfar, hLnear]
    exact (mul_eq_zero.1 hz).resolve_right (ne_of_gt hLj2)
  rw [← hz2eq, hs'0, zero_smul, add_zero, show s = 1 from by linarith, one_smul]

/-- **L1: positive turning ⇒ simple.** A closed positively-oriented moderate-arc
development with total turning `2π` is a simple polygon. Project-local — the
discrete analogue of smooth simplicity being free in the positive case. -/
theorem isSimplePolygon_of_turningPositive [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hn : 3 ≤ n) (h : ModerateArc 0 κ ℓ) (hκ : ∀ i : ZMod n, 0 < κ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) :
    IsSimplePolygon (polygonR2 κ ℓ) :=
  ⟨fun i => polygonR2_edge_ne h hE hT i,
   fun i => polygonR2_consecutive_inter h hκ hE hT hn i,
   fun i j hij hij1 hji1 => polygonR2_nonadjacent_disjoint h hκ hE hT i j hij hij1 hji1⟩

/-! ## The constant branch of D-R²-pos -/

/-- **Constant positive profiles are realized.** For `n ≥ 3` and `c > 0` the
constant curvature profile `κ ≡ c` is Euclidean-realizable, witnessed by the
regular `n`-gon of edge length `(2/c) sin(π/n)`. The first genuine `RealizesR2`
witness of the discrete program. -/
theorem realizesR2_const [NeZero n] (hn : 3 ≤ n) {c : ℝ} (hc : 0 < c) :
    RealizesR2 (fun _ : ZMod n => c) := by
  obtain ⟨hMA, _, hsum, hclose⟩ := regularGon_closes hn hc
  exact ⟨fun _ => 2 / c * Real.sin (Real.pi / n), hMA, hclose, hsum,
    isSimplePolygon_of_turningPositive hn hMA (fun _ => hc) hclose hsum⟩

end Gluck.Discrete
