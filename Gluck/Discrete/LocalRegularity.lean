/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.TangentChord
public import Gluck.Statements

/-!
# Discrete local regularity (Dahlberg admissibility)

This file formalizes Dahlberg's admissibility layer for plane polygons
(B.E.J. Dahlberg, *A Discrete Four Vertex Theorem*): the circumcenter of a
vertex triple (his discrete circle of curvature), the vertex sector
`𝒜(P)`, local regularity (his Definition 1), his elementary sufficient
condition (Proposition 1, non-reflex case), and the plateau-aware
local-extrema vocabulary together with the bridge from the combinatorial
DFV window to his conclusion class.

* `circumcenterR2` — closed-form circumcenter of a plane triple.
* `re_conj_circumcenterR2_sub`, `circumcenterR2_equidist` — the
  perpendicular-bisector identities and equidistance.
* `vertexSector`, `LocallyRegularR2` — Dahlberg's sector `𝒜(P)` and
  Definition 1 (non-collinear scope; see the blueprint chapter preamble).
* `locallyRegularR2_of_obtuse` — Proposition 1: interior angles `≥ π/2`
  give local regularity.
* `locallyRegular_development` — closed moderate-arc developments with
  positive curvature and turning `≤ π/2` are locally regular.
* `PlateauMaxRun`, `PlateauMinRun`, `IsPlateauLocalMax`,
  `IsPlateauLocalMin` — plateau local extrema on a cyclic profile.
* `dfv_plateau_extrema` — the DFV window produces two disjoint plateau
  maxima and two disjoint plateau minima.

-/

@[expose] public section

namespace Gluck.Discrete

open scoped Real
open Complex (normSq)

variable {n : ℕ}

/-! ## Circumcenters of vertex triples -/

/-- The signed twice-area as the imaginary part of the Hermitian product of
the two edge vectors at `A`. -/
lemma crossR2_eq_im_conj_mul (A B C : ℂ) :
    crossR2 A B C = ((starRingEnd ℂ) (B - A) * (C - A)).im := by
  simp only [crossR2, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Perpendicular-bisector identities** for the circumcenter: the projection
of `c - p` on each edge vector is half that edge's squared length. -/
lemma re_conj_circumcenterR2_sub {p q r : ℂ} (h : crossR2 p q r ≠ 0) :
    ((starRingEnd ℂ) (q - p) * (circumcenterR2 p q r - p)).re = normSq (q - p) / 2 ∧
      ((starRingEnd ℂ) (r - p) * (circumcenterR2 p q r - p)).re = normSq (r - p) / 2 := by
  have hζ : circumcenterR2 p q r - p
      = (Complex.I * ((normSq (r - p) : ℝ) * (q - p) - (normSq (q - p) : ℝ) * (r - p)))
          / (2 * (crossR2 p q r : ℂ)) := by
    rw [circumcenterR2]; ring
  have hden : (2 * (crossR2 p q r : ℂ)) = ((2 * crossR2 p q r : ℝ) : ℂ) := by push_cast; ring
  have hne : (2 * crossR2 p q r : ℝ) ≠ 0 := by
    intro h0; exact h (by linarith)
  constructor <;>
  · rw [hζ, hden, mul_div_assoc', Complex.div_ofReal_re]
    rw [div_eq_div_iff hne two_ne_zero]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.normSq_apply, crossR2]
    ring

/-- Expansion of `normSq` under subtraction (project-local: Mathlib has no
`Complex.normSq_sub`). -/
private lemma normSq_sub' (z w : ℂ) :
    normSq (z - w) = normSq z - 2 * ((starRingEnd ℂ) w * z).re + normSq w := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- **The circumcenter is equidistant** from the three vertices of a
non-collinear triple. -/
lemma circumcenterR2_equidist {p q r : ℂ} (h : crossR2 p q r ≠ 0) :
    dist (circumcenterR2 p q r) q = dist (circumcenterR2 p q r) p ∧
      dist (circumcenterR2 p q r) r = dist (circumcenterR2 p q r) p := by
  obtain ⟨h1, h2⟩ := re_conj_circumcenterR2_sub h
  have key : ∀ x : ℂ,
      ((starRingEnd ℂ) (x - p) * (circumcenterR2 p q r - p)).re = normSq (x - p) / 2 →
        dist (circumcenterR2 p q r) x = dist (circumcenterR2 p q r) p := by
    intro x hx
    have hxp : circumcenterR2 p q r - x = (circumcenterR2 p q r - p) - (x - p) := by ring
    have hsq : normSq (circumcenterR2 p q r - x) = normSq (circumcenterR2 p q r - p) := by
      rw [hxp, normSq_sub' _ _, hx]; ring
    rw [dist_eq_norm, dist_eq_norm,
      ← Real.sqrt_sq (norm_nonneg (circumcenterR2 p q r - x)),
      ← Real.sqrt_sq (norm_nonneg (circumcenterR2 p q r - p)),
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hsq]
  exact ⟨key q h1, key r h2⟩

/-! ## Vertex sectors and local regularity -/

/-- Dahlberg's vertex sector `𝒜(P)` at vertex `i` of the cyclic polygon `v`:
the closed convex cone at `v i` spanned by the two incident edge directions.
(For a non-reflex vertex this is exactly his closed convex sector; the `k = 0`
half-plane convention is out of scope — see the blueprint chapter preamble.) -/
def vertexSector (v : ZMod n → ℂ) (i : ZMod n) : Set ℂ :=
  {z | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
    z = v i + (s : ℂ) * (v (i - 1) - v i) + (t : ℂ) * (v (i + 1) - v i)}

/-- **Dahlberg's Definition 1** (locally regular polygon, non-collinear
scope): every consecutive vertex triple is non-collinear and the center of
its circle of curvature lies in the vertex sector. -/
def LocallyRegularR2 (v : ZMod n → ℂ) : Prop :=
  ∀ i : ZMod n, crossR2 (v i) (v (i - 1)) (v (i + 1)) ≠ 0 ∧
    circumcenterR2 (v i) (v (i - 1)) (v (i + 1)) ∈ vertexSector v i

/-! ## Dahlberg's Proposition 1 (non-reflex case) -/

/-- Core algebraic identity behind Proposition 1: the circumcenter direction
`i(|w|²u − |u|²w)/(2δ)` written in the basis `u, w`, with the explicit
Cramer coordinates `s = |w|²(|u|² − R)/(2δ²)`, `t = |u|²(|w|² − R)/(2δ²)`
where `R = Re(ū w)` and `δ = Im(ū w)`. -/
private lemma sector_coords_key {u w : ℂ} (h : u.re * w.im - u.im * w.re ≠ 0) :
    Complex.I * ((normSq w : ℝ) * u - (normSq u : ℝ) * w)
        / (2 * ((u.re * w.im - u.im * w.re : ℝ) : ℂ))
      = ((normSq w * (normSq u - (u.re * w.re + u.im * w.im))
            / (2 * (u.re * w.im - u.im * w.re) ^ 2) : ℝ) : ℂ) * u
        + ((normSq u * (normSq w - (u.re * w.re + u.im * w.im))
            / (2 * (u.re * w.im - u.im * w.re) ^ 2) : ℝ) : ℂ) * w := by
  have hden : (2 * ((u.re * w.im - u.im * w.re : ℝ) : ℂ))
      = ((2 * (u.re * w.im - u.im * w.re) : ℝ) : ℂ) := by push_cast; ring
  have hne1 : (2 * (u.re * w.im - u.im * w.re) : ℝ) ≠ 0 := by
    intro h0; exact h (by linarith)
  have hne2 : (2 * (u.re * w.im - u.im * w.re) ^ 2 : ℝ) ≠ 0 :=
    mul_ne_zero two_ne_zero (pow_ne_zero 2 h)
  -- the cross-multiplied polynomial identity
  have key : Complex.I * ((normSq w : ℝ) * u - (normSq u : ℝ) * w)
        * ((2 * (u.re * w.im - u.im * w.re) ^ 2 : ℝ) : ℂ)
      = (((normSq w * (normSq u - (u.re * w.re + u.im * w.im)) : ℝ) : ℂ) * u
          + ((normSq u * (normSq w - (u.re * w.re + u.im * w.im)) : ℝ) : ℂ) * w)
        * ((2 * (u.re * w.im - u.im * w.re) : ℝ) : ℂ) := by
    apply Complex.ext <;>
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      ring
  rw [hden, Complex.ofReal_div, Complex.ofReal_div, div_mul_eq_mul_div,
    div_mul_eq_mul_div, ← add_div, div_eq_div_iff
      (Complex.ofReal_ne_zero.2 hne1) (Complex.ofReal_ne_zero.2 hne2)]
  linear_combination key

/-- **Sharp Cramer bound** (automaticity layer): under the non-collinearity
guard, the bound `Re(ū w) ≤ min (|u|², |w|²)` on the edge vectors `u = q - p`,
`w = r - p` places the circumcenter in the closed cone at `p` spanned by
them — the Cramer numerators `|u|² − R` and `|w|² − R` are nonnegative
exactly under this bound. (`circumcenterR2_mem_cone` is the special case
`R ≤ 0`.) -/
lemma circumcenterR2_mem_cone_of_le {p q r : ℂ} (h : crossR2 p q r ≠ 0)
    (hre : ((starRingEnd ℂ) (q - p) * (r - p)).re
      ≤ min (normSq (q - p)) (normSq (r - p))) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      circumcenterR2 p q r = p + (s : ℂ) * (q - p) + (t : ℂ) * (r - p) := by
  have hδ : (q - p).re * (r - p).im - (q - p).im * (r - p).re ≠ 0 := by
    simpa [crossR2] using h
  have hR : (q - p).re * (r - p).re + (q - p).im * (r - p).im
      ≤ min (normSq (q - p)) (normSq (r - p)) := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hre
    linarith
  have hR1 : (q - p).re * (r - p).re + (q - p).im * (r - p).im ≤ normSq (q - p) :=
    hR.trans (min_le_left _ _)
  have hR2 : (q - p).re * (r - p).re + (q - p).im * (r - p).im ≤ normSq (r - p) :=
    hR.trans (min_le_right _ _)
  have hd2 : (0 : ℝ) < 2 * ((q - p).re * (r - p).im - (q - p).im * (r - p).re) ^ 2 := by
    have h1 : (0 : ℝ) ≤ ((q - p).re * (r - p).im - (q - p).im * (r - p).re) ^ 2 :=
      sq_nonneg _
    have h2 : ((q - p).re * (r - p).im - (q - p).im * (r - p).re) ^ 2 ≠ 0 :=
      pow_ne_zero 2 hδ
    have := lt_of_le_of_ne h1 (Ne.symm h2)
    linarith
  refine ⟨normSq (r - p) * (normSq (q - p)
        - ((q - p).re * (r - p).re + (q - p).im * (r - p).im))
      / (2 * ((q - p).re * (r - p).im - (q - p).im * (r - p).re) ^ 2),
    normSq (q - p) * (normSq (r - p)
        - ((q - p).re * (r - p).re + (q - p).im * (r - p).im))
      / (2 * ((q - p).re * (r - p).im - (q - p).im * (r - p).re) ^ 2), ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (Complex.normSq_nonneg _) (by linarith)) hd2.le
  · exact div_nonneg (mul_nonneg (Complex.normSq_nonneg _) (by linarith)) hd2.le
  · have key := sector_coords_key hδ
    rw [circumcenterR2]
    simp only [crossR2]
    linear_combination key

/-- Under the non-collinearity guard, a non-acute vertex (`Re(ū w) ≤ 0`)
places the circumcenter in the closed cone at `p` spanned by the two edge
vectors — the single-vertex core of Dahlberg's Proposition 1. Special case
of the sharp Cramer bound `circumcenterR2_mem_cone_of_le`. -/
lemma circumcenterR2_mem_cone {p q r : ℂ} (h : crossR2 p q r ≠ 0)
    (hre : ((starRingEnd ℂ) (q - p) * (r - p)).re ≤ 0) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      circumcenterR2 p q r = p + (s : ℂ) * (q - p) + (t : ℂ) * (r - p) :=
  circumcenterR2_mem_cone_of_le h
    (hre.trans (le_min (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)))

/-- **Dahlberg's Proposition 1, non-reflex case**: if every consecutive
triple is non-collinear and every interior angle is at least `π/2`
(`Re(ē⁻ e⁺) ≤ 0`), the polygon is locally regular. -/
theorem locallyRegularR2_of_obtuse {v : ZMod n → ℂ}
    (hcross : ∀ i : ZMod n, crossR2 (v i) (v (i - 1)) (v (i + 1)) ≠ 0)
    (hre : ∀ i : ZMod n,
      ((starRingEnd ℂ) (v (i - 1) - v i) * (v (i + 1) - v i)).re ≤ 0) :
    LocallyRegularR2 v := by
  intro i
  refine ⟨hcross i, ?_⟩
  obtain ⟨s, t, hs, ht, heq⟩ := circumcenterR2_mem_cone (hcross i) (hre i)
  exact ⟨s, t, hs, ht, heq⟩

/-! ## Closed developments with sub-right turning are locally regular -/

/-- One development step advances the heading by the next turning angle
(local copy of the private `heading_succ` of `TangentChord.lean`). -/
private lemma heading_step (κ ℓ : ZMod n → ℝ) (j : ℕ) :
    heading κ ℓ (j + 1)
      = heading κ ℓ j + turningAngle 0 κ ℓ ((j + 1 : ℕ) : ZMod n) := by
  unfold heading
  rw [Finset.sum_range_succ]

/-- The two edge vectors at any vertex of a closed development: the incoming
edge is `−ℓ_{i−1} e^{iψ}`, the outgoing edge `ℓ_i e^{iψ'}`, with headings
differing by the turning angle at the vertex. -/
private lemma polygon_edges [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (i : ZMod n) :
    ∃ ψ ψ' : ℝ, ψ' - ψ = turningAngle 0 κ ℓ i ∧
      polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i
        = -((ℓ (i - 1) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) ∧
      polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i
        = (ℓ i : ℂ) * Complex.exp ((ψ' : ℂ) * Complex.I) := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set k : ℕ := i.val + (n - 1) with hk
  -- casts of the three lifted indices
  have hn1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub hpos, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hiv : ((i.val : ℕ) : ZMod n) = i := ZMod.natCast_rightInverse i
  have hc0 : ((k : ℕ) : ZMod n) = i - 1 := by
    rw [hk, Nat.cast_add, hiv, hn1]; ring
  have hc1 : ((k + 1 : ℕ) : ZMod n) = i := by
    rw [hk, Nat.cast_add, Nat.cast_add, Nat.cast_one, hiv, hn1]; ring
  have hc2 : ((k + 1 + 1 : ℕ) : ZMod n) = i + 1 := by
    rw [hk, Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one, hiv, hn1]; ring
  -- the polygon vertices as development vertices
  have e0 : polygonR2 κ ℓ (i - 1) = vertexR2 κ ℓ k := by
    rw [← hc0, ← vertexR2_eq_polygon hE hT]
  have e1 : polygonR2 κ ℓ i = vertexR2 κ ℓ (k + 1) := by
    rw [← hc1, ← vertexR2_eq_polygon hE hT]
  have e2 : polygonR2 κ ℓ (i + 1) = vertexR2 κ ℓ (k + 1 + 1) := by
    rw [← hc2, ← vertexR2_eq_polygon hE hT]
  -- the two edge vectors
  have hu : vertexR2 κ ℓ (k + 1) - vertexR2 κ ℓ k
      = (ℓ (i - 1) : ℂ) * Complex.exp ((heading κ ℓ k : ℂ) * Complex.I) := by
    rw [vertexR2_succ, hc0]; ring
  have hw : vertexR2 κ ℓ (k + 1 + 1) - vertexR2 κ ℓ (k + 1)
      = (ℓ i : ℂ) * Complex.exp ((heading κ ℓ (k + 1) : ℂ) * Complex.I) := by
    rw [vertexR2_succ, hc1]; ring
  refine ⟨heading κ ℓ k, heading κ ℓ (k + 1), ?_, ?_, ?_⟩
  · rw [heading_step, hc1]; ring
  · rw [e0, e1]; linear_combination -hu
  · rw [e2, e1]; linear_combination hw

/-- The Hermitian product of the two edge vectors at any vertex of a closed
development: `ē⁻ e⁺ = −ℓ_{i−1} ℓ_i e^{iθ_i}`. -/
private lemma conj_edge_mul_edge [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (i : ZMod n) :
    (starRingEnd ℂ) (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i)
        * (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)
      = ((-(ℓ (i - 1) * ℓ i) : ℝ) : ℂ)
          * Complex.exp ((turningAngle 0 κ ℓ i : ℂ) * Complex.I) := by
  obtain ⟨ψ, ψ', hd, hem, hep⟩ := polygon_edges hE hT i
  -- conjugate of the incoming edge direction
  have hconjI : (starRingEnd ℂ) ((ψ : ℂ) * Complex.I)
      = -((ψ : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have harg : -((ψ : ℂ) * Complex.I) + (ψ' : ℂ) * Complex.I
      = (turningAngle 0 κ ℓ i : ℂ) * Complex.I := by
    rw [← hd]
    push_cast
    ring
  rw [hem, hep, map_neg, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hconjI]
  calc -((ℓ (i - 1) : ℂ) * Complex.exp (-((ψ : ℂ) * Complex.I)))
        * ((ℓ i : ℂ) * Complex.exp ((ψ' : ℂ) * Complex.I))
      = -((ℓ (i - 1) : ℂ) * (ℓ i : ℂ))
          * (Complex.exp (-((ψ : ℂ) * Complex.I))
              * Complex.exp ((ψ' : ℂ) * Complex.I)) := by ring
    _ = -((ℓ (i - 1) : ℂ) * (ℓ i : ℂ))
          * Complex.exp (-((ψ : ℂ) * Complex.I) + (ψ' : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
    _ = ((-(ℓ (i - 1) * ℓ i) : ℝ) : ℂ)
          * Complex.exp ((turningAngle 0 κ ℓ i : ℂ) * Complex.I) := by
        rw [harg]; push_cast; ring

/-- The real inner product of the two rays from a developed vertex to its
neighbours.  This identity only uses closure and total turning; in particular,
it remains valid at compactified walls. -/
theorem polygonVertexAdjacentInner_eq_neg_length_mul_cos [NeZero n]
    {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (i : ZMod n) :
    ((starRingEnd ℂ) (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i) *
        (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)).re =
      -(ℓ (i - 1) * ℓ i) * Real.cos (turningAngle 0 κ ℓ i) := by
  rw [conj_edge_mul_edge hE hT i, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re]

/-- The oriented cross product of the same two neighbour rays.  Like the
inner-product identity, this is valid on the compactified boundary. -/
theorem polygonVertexAdjacentCross_eq_neg_length_mul_sin [NeZero n]
    {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (i : ZMod n) :
    crossR2 0
        (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i)
        (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i) =
      -(ℓ (i - 1) * ℓ i) * Real.sin (turningAngle 0 κ ℓ i) := by
  rw [crossR2_eq_im_conj_mul]
  simp only [sub_zero]
  rw [conj_edge_mul_edge hE hT i,
    Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- **Closed moderate-arc developments with sub-right turning are locally
regular**: positive curvature and turning angles `≤ π/2` give, at every
vertex, a non-collinear triple with interior angle `≥ π/2`, so Dahlberg's
Proposition 1 applies. (The closure hypotheses make the cyclic edges of
`polygonR2` genuine development edges.) -/
theorem locallyRegular_development [NeZero n] {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) (hκ : ∀ i : ZMod n, 0 < κ i)
    (hθ : ∀ i : ZMod n, turningAngle 0 κ ℓ i ≤ Real.pi / 2)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) :
    LocallyRegularR2 (polygonR2 κ ℓ) := by
  have hedge : ∀ i : ZMod n,
      ((starRingEnd ℂ) (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i)
          * (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)).re
        = -(ℓ (i - 1) * ℓ i) * Real.cos (turningAngle 0 κ ℓ i)
      ∧ ((starRingEnd ℂ) (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i)
          * (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)).im
        = -(ℓ (i - 1) * ℓ i) * Real.sin (turningAngle 0 κ ℓ i) := by
    intro i
    rw [conj_edge_mul_edge hE hT i]
    constructor
    · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hθpos : ∀ i : ZMod n, 0 < turningAngle 0 κ ℓ i :=
    fun i => turningAngle_pos h (hκ i)
  apply locallyRegularR2_of_obtuse
  · -- non-collinearity: the cross product is −ℓ' ℓ sin θ ≠ 0
    intro i
    rw [crossR2_eq_im_conj_mul, (hedge i).2]
    have hsin : 0 < Real.sin (turningAngle 0 κ ℓ i) :=
      Real.sin_pos_of_pos_of_lt_pi (hθpos i)
        (lt_of_le_of_lt (hθ i) (half_lt_self Real.pi_pos))
    have hl1 := h.length_pos (i - 1)
    have hl2 := h.length_pos i
    have : -(ℓ (i - 1) * ℓ i) * Real.sin (turningAngle 0 κ ℓ i) < 0 := by
      nlinarith [mul_pos (mul_pos hl1 hl2) hsin]
    exact ne_of_lt this
  · -- interior angle ≥ π/2: the projection is −ℓ' ℓ cos θ ≤ 0
    intro i
    rw [(hedge i).1]
    have hcos : 0 ≤ Real.cos (turningAngle 0 κ ℓ i) :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθpos i, Real.pi_pos], hθ i⟩
    have hl1 := h.length_pos (i - 1)
    have hl2 := h.length_pos i
    nlinarith [mul_nonneg (mul_pos hl1 hl2).le hcos]

/-! ## Local regularity is automatic for moderate developments -/

/-- `normSq` of a scaled unit vector `r · e^{iφ}`. -/
private lemma normSq_scaled_exp (r φ : ℝ) :
    normSq ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) = r ^ 2 := by
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp]
  simp [Complex.mul_re, Complex.normSq_ofReal]
  ring

/-- The trigonometric core of the automaticity layer: for angles with
nonnegative sines and cosines and `sin (a + b) ≥ 0`,
`−sin a sin b · cos (a + b) ≤ min (sin² a) (sin² b)` — both differences
factor as `sin cos sin(a+b)` products via the Pythagorean identity. -/
private lemma neg_sin_mul_cos_add_le {a b : ℝ} (ha : 0 ≤ Real.sin a)
    (hb : 0 ≤ Real.sin b) (hca : 0 ≤ Real.cos a) (hcb : 0 ≤ Real.cos b)
    (hab : 0 ≤ Real.sin (a + b)) :
    -(Real.sin a * Real.sin b) * Real.cos (a + b)
      ≤ min (Real.sin a ^ 2) (Real.sin b ^ 2) := by
  have h1 : Real.sin a ^ 2 + Real.sin a * Real.sin b * Real.cos (a + b)
      = Real.sin a * Real.cos b * Real.sin (a + b) := by
    rw [Real.sin_add, Real.cos_add]
    linear_combination (-(Real.sin a ^ 2)) * Real.sin_sq_add_cos_sq b
  have h2 : Real.sin b ^ 2 + Real.sin a * Real.sin b * Real.cos (a + b)
      = Real.sin b * Real.cos a * Real.sin (a + b) := by
    rw [Real.sin_add, Real.cos_add]
    linear_combination (-(Real.sin b ^ 2)) * Real.sin_sq_add_cos_sq a
  rw [le_min_iff]
  constructor
  · nlinarith [mul_nonneg (mul_nonneg ha hcb) hab]
  · nlinarith [mul_nonneg (mul_nonneg hb hca) hab]

/-- **Moderate-arc developments are locally regular — no turning restriction**
(automaticity layer): for a closed positive moderate development the (TA) law
itself supplies the sharp Cramer bound `Re(ū w) ≤ min (|u|², |w|²)` at every
vertex — both arcsin half-angles lie in `[0, π/2]`, so
`−cos θ sin a sin b ≤ min (sin² a, sin² b)` — and the sub-right-turning
hypothesis of `locallyRegular_development` is unnecessary. -/
theorem locallyRegular_development_moderate [NeZero n] {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) (hκ : ∀ i : ZMod n, 0 < κ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) :
    LocallyRegularR2 (polygonR2 κ ℓ) := by
  intro i
  obtain ⟨ψ, ψ', hd, hem, hep⟩ := polygon_edges hE hT i
  have hl1 := h.length_pos (i - 1)
  have hl2 := h.length_pos i
  have hκi := hκ i
  -- turning-angle bounds: θ ∈ (0, π)
  have hθpos : 0 < turningAngle 0 κ ℓ i := turningAngle_pos h hκi
  have hθlt : turningAngle 0 κ ℓ i < Real.pi := by
    have := abs_turningAngle_lt_pi h i
    rw [abs_lt] at this
    exact this.2
  have hsinθ : 0 < Real.sin (turningAngle 0 κ ℓ i) :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  -- re/im of the edge Hermitian product
  have hprod := conj_edge_mul_edge hE hT i
  have hre_eq : ((starRingEnd ℂ) (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i)
        * (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)).re
      = -(ℓ (i - 1) * ℓ i) * Real.cos (turningAngle 0 κ ℓ i) := by
    rw [hprod, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him_eq : ((starRingEnd ℂ) (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i)
        * (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)).im
      = -(ℓ (i - 1) * ℓ i) * Real.sin (turningAngle 0 κ ℓ i) := by
    rw [hprod, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  -- non-collinearity: the cross product is −ℓ' ℓ sin θ ≠ 0
  have hcross : crossR2 (polygonR2 κ ℓ i) (polygonR2 κ ℓ (i - 1))
      (polygonR2 κ ℓ (i + 1)) ≠ 0 := by
    rw [crossR2_eq_im_conj_mul, him_eq]
    have : -(ℓ (i - 1) * ℓ i) * Real.sin (turningAngle 0 κ ℓ i) < 0 := by
      nlinarith [mul_pos (mul_pos hl1 hl2) hsinθ]
    exact ne_of_lt this
  refine ⟨hcross, ?_⟩
  -- the (TA) arcsin decomposition θ = A + B with A, B ∈ (0, π/2]
  set A := Real.arcsin (κ i * (ℓ (i - 1) / 2)) with hA
  set B := Real.arcsin (κ i * (ℓ i / 2)) with hB
  have hθAB : turningAngle 0 κ ℓ i = A + B := by
    rw [turningAngle, hA, hB, tK_zero, tK_zero]
  have hargl : κ i * (ℓ (i - 1) / 2) < 1 := by
    have := h.wall_left i
    rwa [tK_zero, abs_of_pos hκi] at this
  have hargr : κ i * (ℓ i / 2) < 1 := by
    have := h.wall_right i
    rwa [tK_zero, abs_of_pos hκi] at this
  have hargl0 : 0 ≤ κ i * (ℓ (i - 1) / 2) := (mul_pos hκi (half_pos hl1)).le
  have hargr0 : 0 ≤ κ i * (ℓ i / 2) := (mul_pos hκi (half_pos hl2)).le
  have hsinA : Real.sin A = κ i * (ℓ (i - 1) / 2) := by
    rw [hA]; exact Real.sin_arcsin (by linarith) hargl.le
  have hsinB : Real.sin B = κ i * (ℓ i / 2) := by
    rw [hB]; exact Real.sin_arcsin (by linarith) hargr.le
  have hcosA : 0 ≤ Real.cos A := by
    rw [hA, Real.cos_arcsin]; positivity
  have hcosB : 0 ≤ Real.cos B := by
    rw [hB, Real.cos_arcsin]; positivity
  -- the trigonometric core, instantiated at the (TA) half-angles
  have htrig := neg_sin_mul_cos_add_le (hsinA ▸ hargl0) (hsinB ▸ hargr0)
    hcosA hcosB (by rw [← hθAB]; exact hsinθ.le)
  rw [hsinA, hsinB, le_min_iff] at htrig
  -- edge norms and the sharp Cramer bound
  have hnu : normSq (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i) = ℓ (i - 1) ^ 2 := by
    rw [hem, Complex.normSq_neg, normSq_scaled_exp]
  have hnw : normSq (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i) = ℓ i ^ 2 := by
    rw [hep, normSq_scaled_exp]
  have hre_le : ((starRingEnd ℂ) (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i)
        * (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)).re
      ≤ min (normSq (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i))
          (normSq (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)) := by
    rw [hre_eq, hnu, hnw, le_min_iff, hθAB]
    constructor
    · nlinarith [htrig.1, mul_pos hκi hκi]
    · nlinarith [htrig.2, mul_pos hκi hκi]
  obtain ⟨s, t, hs, ht, heq⟩ := circumcenterR2_mem_cone_of_le hcross hre_le
  exact ⟨s, t, hs, ht, heq⟩

/-! ## Coherence: the circumcenter in the open vertex cone -/

lemma vertexCone_subset_vertexSector (v : ZMod n → ℂ) (i : ZMod n) :
    vertexCone v i ⊆ vertexSector v i := by
  rintro z ⟨s, t, hs, ht, rfl⟩
  exact ⟨s, t, hs.le, ht.le, rfl⟩

lemma CoherentR2.locallyRegularR2 {v : ZMod n → ℂ} (h : CoherentR2 v) :
    LocallyRegularR2 v :=
  fun i => ⟨(h i).1, vertexCone_subset_vertexSector v i (h i).2⟩

/-- **Strict Cramer bound**: `Re(ū w) < min (|u|², |w|²)` places the
circumcenter in the open cone at `p` spanned by `u = q - p` and `w = r - p`. -/
lemma circumcenterR2_mem_openCone_of_lt {p q r : ℂ} (h : crossR2 p q r ≠ 0)
    (hre : ((starRingEnd ℂ) (q - p) * (r - p)).re
      < min (normSq (q - p)) (normSq (r - p))) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
      circumcenterR2 p q r = p + (s : ℂ) * (q - p) + (t : ℂ) * (r - p) := by
  have hδ : (q - p).re * (r - p).im - (q - p).im * (r - p).re ≠ 0 := by
    simpa [crossR2] using h
  obtain ⟨hqp, -, hrp⟩ := pairwise_ne_of_crossR2_ne_zero h
  have hu : 0 < normSq (q - p) := Complex.normSq_pos.2 (sub_ne_zero.2 (Ne.symm hqp))
  have hw : 0 < normSq (r - p) := Complex.normSq_pos.2 (sub_ne_zero.2 hrp)
  have hR : (q - p).re * (r - p).re + (q - p).im * (r - p).im
      < min (normSq (q - p)) (normSq (r - p)) := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hre
    linarith
  have hR1 := hR.trans_le (min_le_left _ _)
  have hR2 := hR.trans_le (min_le_right _ _)
  have hd2 : (0 : ℝ) < 2 * ((q - p).re * (r - p).im - (q - p).im * (r - p).re) ^ 2 := by
    have := pow_pos (abs_pos.2 hδ) 2
    rw [sq_abs] at this
    linarith
  refine ⟨normSq (r - p) * (normSq (q - p)
        - ((q - p).re * (r - p).re + (q - p).im * (r - p).im))
      / (2 * ((q - p).re * (r - p).im - (q - p).im * (r - p).re) ^ 2),
    normSq (q - p) * (normSq (r - p)
        - ((q - p).re * (r - p).re + (q - p).im * (r - p).im))
      / (2 * ((q - p).re * (r - p).im - (q - p).im * (r - p).re) ^ 2), ?_, ?_, ?_⟩
  · exact div_pos (mul_pos hw (by linarith)) hd2
  · exact div_pos (mul_pos hu (by linarith)) hd2
  · have key := sector_coords_key hδ
    rw [circumcenterR2]
    simp only [crossR2]
    linear_combination key

/-- Strict form of `neg_sin_mul_cos_add_le`. -/
private lemma neg_sin_mul_cos_add_lt {a b : ℝ} (ha : 0 < Real.sin a)
    (hb : 0 < Real.sin b) (hca : 0 < Real.cos a) (hcb : 0 < Real.cos b)
    (hab : 0 < Real.sin (a + b)) :
    -(Real.sin a * Real.sin b) * Real.cos (a + b)
      < min (Real.sin a ^ 2) (Real.sin b ^ 2) := by
  have h1 : Real.sin a ^ 2 + Real.sin a * Real.sin b * Real.cos (a + b)
      = Real.sin a * Real.cos b * Real.sin (a + b) := by
    rw [Real.sin_add, Real.cos_add]
    linear_combination (-(Real.sin a ^ 2)) * Real.sin_sq_add_cos_sq b
  have h2 : Real.sin b ^ 2 + Real.sin a * Real.sin b * Real.cos (a + b)
      = Real.sin b * Real.cos a * Real.sin (a + b) := by
    rw [Real.sin_add, Real.cos_add]
    linear_combination (-(Real.sin b ^ 2)) * Real.sin_sq_add_cos_sq a
  rw [lt_min_iff]
  constructor
  · nlinarith [mul_pos (mul_pos ha hcb) hab]
  · nlinarith [mul_pos (mul_pos hb hca) hab]

/-- **Closed positive moderate-arc developments are coherent**: the
circumcenter of every consecutive triple lies in the *open* vertex cone.
Strict strengthening of `locallyRegular_development_moderate`: both arcsin
half-angles lie in `(0, π/2)` because the moderate-arc walls are strict. -/
theorem coherent_development_moderate [NeZero n] {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) (hκ : ∀ i : ZMod n, 0 < κ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) :
    CoherentR2 (polygonR2 κ ℓ) := by
  intro i
  obtain ⟨ψ, ψ', hd, hem, hep⟩ := polygon_edges hE hT i
  have hl1 := h.length_pos (i - 1)
  have hl2 := h.length_pos i
  have hκi := hκ i
  have hθpos : 0 < turningAngle 0 κ ℓ i := turningAngle_pos h hκi
  have hθlt : turningAngle 0 κ ℓ i < Real.pi := by
    have := abs_turningAngle_lt_pi h i
    rw [abs_lt] at this
    exact this.2
  have hsinθ : 0 < Real.sin (turningAngle 0 κ ℓ i) :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  have hprod := conj_edge_mul_edge hE hT i
  have hre_eq : ((starRingEnd ℂ) (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i)
        * (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)).re
      = -(ℓ (i - 1) * ℓ i) * Real.cos (turningAngle 0 κ ℓ i) := by
    rw [hprod, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him_eq : ((starRingEnd ℂ) (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i)
        * (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)).im
      = -(ℓ (i - 1) * ℓ i) * Real.sin (turningAngle 0 κ ℓ i) := by
    rw [hprod, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hcross : crossR2 (polygonR2 κ ℓ i) (polygonR2 κ ℓ (i - 1))
      (polygonR2 κ ℓ (i + 1)) ≠ 0 := by
    rw [crossR2_eq_im_conj_mul, him_eq]
    have : -(ℓ (i - 1) * ℓ i) * Real.sin (turningAngle 0 κ ℓ i) < 0 := by
      nlinarith [mul_pos (mul_pos hl1 hl2) hsinθ]
    exact ne_of_lt this
  refine ⟨hcross, ?_⟩
  set A := Real.arcsin (κ i * (ℓ (i - 1) / 2)) with hA
  set B := Real.arcsin (κ i * (ℓ i / 2)) with hB
  have hθAB : turningAngle 0 κ ℓ i = A + B := by
    rw [turningAngle, hA, hB, tK_zero, tK_zero]
  have hargl : κ i * (ℓ (i - 1) / 2) < 1 := by
    have := h.wall_left i
    rwa [tK_zero, abs_of_pos hκi] at this
  have hargr : κ i * (ℓ i / 2) < 1 := by
    have := h.wall_right i
    rwa [tK_zero, abs_of_pos hκi] at this
  have hargl0 : 0 < κ i * (ℓ (i - 1) / 2) := mul_pos hκi (half_pos hl1)
  have hargr0 : 0 < κ i * (ℓ i / 2) := mul_pos hκi (half_pos hl2)
  have hsinA : Real.sin A = κ i * (ℓ (i - 1) / 2) := by
    rw [hA]; exact Real.sin_arcsin (by linarith) hargl.le
  have hsinB : Real.sin B = κ i * (ℓ i / 2) := by
    rw [hB]; exact Real.sin_arcsin (by linarith) hargr.le
  have hcosA : 0 < Real.cos A := by
    rw [hA, Real.cos_arcsin]
    exact Real.sqrt_pos.2 (by nlinarith)
  have hcosB : 0 < Real.cos B := by
    rw [hB, Real.cos_arcsin]
    exact Real.sqrt_pos.2 (by nlinarith)
  have htrig := neg_sin_mul_cos_add_lt (hsinA ▸ hargl0) (hsinB ▸ hargr0)
    hcosA hcosB (by rw [← hθAB]; exact hsinθ)
  rw [hsinA, hsinB, lt_min_iff] at htrig
  have hnu : normSq (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i) = ℓ (i - 1) ^ 2 := by
    rw [hem, Complex.normSq_neg, normSq_scaled_exp]
  have hnw : normSq (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i) = ℓ i ^ 2 := by
    rw [hep, normSq_scaled_exp]
  have hre_lt : ((starRingEnd ℂ) (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i)
        * (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)).re
      < min (normSq (polygonR2 κ ℓ (i - 1) - polygonR2 κ ℓ i))
          (normSq (polygonR2 κ ℓ (i + 1) - polygonR2 κ ℓ i)) := by
    rw [hre_eq, hnu, hnw, lt_min_iff, hθAB]
    constructor
    · nlinarith [htrig.1, mul_pos hκi hκi]
    · nlinarith [htrig.2, mul_pos hκi hκi]
  exact circumcenterR2_mem_openCone_of_lt hcross hre_lt

/-! ## Plateau-aware local extrema on a cyclic profile -/

/-- **Plateau local maximum** (Dahlberg): `i` lies on a constant run of `f`
of length `< n` whose two extended neighbours drop strictly below the run
value. -/
def IsPlateauLocalMax (f : ZMod n → ℝ) (i : ZMod n) : Prop :=
  ∃ a k : ℕ, k < n ∧ PlateauMaxRun f a k ∧ ∃ m ≤ k, i = ((a + m : ℕ) : ZMod n)

/-- **Plateau local minimum**: as `IsPlateauLocalMax` with the strict
inequalities reversed. -/
def IsPlateauLocalMin (f : ZMod n → ℝ) (i : ZMod n) : Prop :=
  ∃ a k : ℕ, k < n ∧ PlateauMinRun f a k ∧ ∃ m ≤ k, i = ((a + m : ℕ) : ZMod n)

/-- A short run (`k < n`) makes its start a plateau local maximum. -/
lemma PlateauMaxRun.isPlateauLocalMax {f : ZMod n → ℝ} {a k : ℕ} (hk : k < n)
    (h : PlateauMaxRun f a k) : IsPlateauLocalMax f (a : ZMod n) :=
  ⟨a, k, hk, h, 0, Nat.zero_le k, by rw [Nat.add_zero]⟩

/-- A short run (`k < n`) makes its start a plateau local minimum. -/
lemma PlateauMinRun.isPlateauLocalMin {f : ZMod n → ℝ} {a k : ℕ} (hk : k < n)
    (h : PlateauMinRun f a k) : IsPlateauLocalMin f (a : ZMod n) :=
  ⟨a, k, hk, h, 0, Nat.zero_le k, by rw [Nat.add_zero]⟩

/-! ## The DFV window yields Dahlberg's conclusion class -/

/-- Interval max-run extraction on `ℕ`: on `[lo, hi]` with an interior-value
witness `w` beating both endpoints, the maximal constant run through the
argmax lies strictly inside and drops strictly at both ends. -/
private lemma exists_max_run (f : ℕ → ℝ) {lo hi w : ℕ} (hlow : lo ≤ w)
    (hwhi : w ≤ hi) (hlo : f lo < f w) (hhi : f hi < f w) :
    ∃ a b : ℕ, lo < a ∧ a ≤ b ∧ b < hi ∧
      (∀ x, a ≤ x → x ≤ b → f x = f a) ∧
      f (a - 1) < f a ∧ f (b + 1) < f a := by
  classical
  obtain ⟨j, hjmem, hjmax⟩ :=
    (Finset.Icc lo hi).exists_max_image f ⟨w, Finset.mem_Icc.2 ⟨hlow, hwhi⟩⟩
  rw [Finset.mem_Icc] at hjmem
  obtain ⟨hloj, hjhi⟩ := hjmem
  have hmax : ∀ x, lo ≤ x → x ≤ hi → f x ≤ f j := fun x h1 h2 =>
    hjmax x (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hflo : f lo < f j := lt_of_lt_of_le hlo (hmax w hlow hwhi)
  have hfhi : f hi < f j := lt_of_lt_of_le hhi (hmax w hlow hwhi)
  have hloj' : lo < j := lt_of_le_of_ne hloj (by rintro rfl; exact lt_irrefl _ hflo)
  have hjhi' : j < hi := lt_of_le_of_ne hjhi (by rintro rfl; exact lt_irrefl _ hfhi)
  -- leftmost and rightmost extent of the constant plateau through the argmax
  have hPL : ∃ d, f (j - d) ≠ f j :=
    ⟨j - lo, by rw [Nat.sub_sub_self hloj]; exact ne_of_lt hflo⟩
  have hPR : ∃ d, f (j + d) ≠ f j :=
    ⟨hi - j, by rw [Nat.add_sub_cancel' hjhi]; exact ne_of_lt hfhi⟩
  have hdLspec : f (j - Nat.find hPL) ≠ f j := Nat.find_spec hPL
  have hdRspec : f (j + Nat.find hPR) ≠ f j := Nat.find_spec hPR
  have hdLpos : 0 < Nat.find hPL := by
    rcases Nat.eq_zero_or_pos (Nat.find hPL) with h0 | h0
    · rw [h0, Nat.sub_zero] at hdLspec; exact absurd rfl hdLspec
    · exact h0
  have hdRpos : 0 < Nat.find hPR := by
    rcases Nat.eq_zero_or_pos (Nat.find hPR) with h0 | h0
    · rw [h0, Nat.add_zero] at hdRspec; exact absurd rfl hdRspec
    · exact h0
  have hdLle : Nat.find hPL ≤ j - lo := by
    by_contra hcon
    push Not at hcon
    exact Nat.find_min hPL hcon
      (by rw [Nat.sub_sub_self hloj]; exact ne_of_lt hflo)
  have hdRle : Nat.find hPR ≤ hi - j := by
    by_contra hcon
    push Not at hcon
    exact Nat.find_min hPR hcon
      (by rw [Nat.add_sub_cancel' hjhi]; exact ne_of_lt hfhi)
  have hconstL : ∀ d, d < Nat.find hPL → f (j - d) = f j := fun d hd =>
    not_ne_iff.1 (Nat.find_min hPL hd)
  have hconstR : ∀ d, d < Nat.find hPR → f (j + d) = f j := fun d hd =>
    not_ne_iff.1 (Nat.find_min hPR hd)
  -- the run and its constancy
  have key : ∀ x, j - Nat.find hPL + 1 ≤ x → x ≤ j + Nat.find hPR - 1 →
      f x = f j := by
    intro x hax hxb
    rcases Nat.lt_or_ge j x with hjx | hxj
    · have hd : x - j < Nat.find hPR := by omega
      have := hconstR (x - j) hd
      rwa [Nat.add_sub_cancel' hjx.le] at this
    · have hd : j - x < Nat.find hPL := by omega
      have := hconstL (j - x) hd
      rwa [Nat.sub_sub_self hxj] at this
  have hdLj : Nat.find hPL ≤ j := le_trans hdLle (Nat.sub_le j lo)
  refine ⟨j - Nat.find hPL + 1, j + Nat.find hPR - 1, by omega, by omega, by omega,
    ?_, ?_, ?_⟩
  · intro x hax hxb
    rw [key x hax hxb, key (j - Nat.find hPL + 1) le_rfl (by omega)]
  · have e1 : j - Nat.find hPL + 1 - 1 = j - Nat.find hPL := by omega
    have hlt : f (j - Nat.find hPL) < f j :=
      lt_of_le_of_ne (hmax (j - Nat.find hPL) (by omega) (by omega)) hdLspec
    rw [e1, key (j - Nat.find hPL + 1) le_rfl (by omega)]
    exact hlt
  · have e1 : j + Nat.find hPR - 1 + 1 = j + Nat.find hPR := by omega
    have hlt : f (j + Nat.find hPR) < f j :=
      lt_of_le_of_ne (hmax (j + Nat.find hPR) (by omega) (by omega)) hdRspec
    rw [e1, key (j - Nat.find hPL + 1) le_rfl (by omega)]
    exact hlt

/-- Distinct lifts within one period have distinct residues. -/
private lemma natCast_zmod_ne {x y : ℕ} (h1 : x < y) (h2 : y < x + n) :
    ((x : ℕ) : ZMod n) ≠ ((y : ℕ) : ZMod n) := by
  intro heq
  rw [ZMod.natCast_eq_natCast_iff] at heq
  have hdvd := (Nat.modEq_iff_dvd' h1.le).1 heq
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Package an `ℕ`-interval max run as a `PlateauMaxRun`. -/
private lemma plateauMaxRun_of_natRun {κ : ZMod n → ℝ} {a b : ℕ} (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hconst : ∀ x, a ≤ x → x ≤ b → κ ((x : ℕ) : ZMod n) = κ ((a : ℕ) : ZMod n))
    (hL : κ ((a - 1 : ℕ) : ZMod n) < κ ((a : ℕ) : ZMod n))
    (hR : κ ((b + 1 : ℕ) : ZMod n) < κ ((a : ℕ) : ZMod n)) :
    PlateauMaxRun κ a (b - a) := by
  refine ⟨fun m hm => hconst (a + m) (by omega) (by omega), ?_, ?_⟩
  · rw [show (a : ZMod n) - 1 = ((a - 1 : ℕ) : ZMod n) from by
      rw [Nat.cast_sub ha, Nat.cast_one]]
    exact hL
  · rw [show a + (b - a) + 1 = b + 1 from by omega]
    exact hR

/-- Package an `ℕ`-interval min run as a `PlateauMinRun`. -/
private lemma plateauMinRun_of_natRun {κ : ZMod n → ℝ} {a b : ℕ} (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hconst : ∀ x, a ≤ x → x ≤ b → κ ((x : ℕ) : ZMod n) = κ ((a : ℕ) : ZMod n))
    (hL : κ ((a : ℕ) : ZMod n) < κ ((a - 1 : ℕ) : ZMod n))
    (hR : κ ((a : ℕ) : ZMod n) < κ ((b + 1 : ℕ) : ZMod n)) :
    PlateauMinRun κ a (b - a) := by
  refine ⟨fun m hm => hconst (a + m) (by omega) (by omega), ?_, ?_⟩
  · rw [show (a : ZMod n) - 1 = ((a - 1 : ℕ) : ZMod n) from by
      rw [Nat.cast_sub ha, Nat.cast_one]]
    exact hL
  · rw [show a + (b - a) + 1 = b + 1 from by omega]
    exact hR

/-- **The DFV window yields Dahlberg's conclusion class**: a cyclic profile
with a four-vertex window (lifts `i₁ < i₂ < i₃ < i₄ < i₁ + n` alternating
across the level `c`) has two plateau local maxima and two plateau local
minima with pairwise disjoint runs. Pure finite combinatorics on `ℕ`-lifts.
(The window hypothesis is the unfolding of `Gluck.Discrete.DFV κ c` as defined
in `Gluck/Discrete/Converse.lean`.) -/
theorem dfv_plateau_extrema {κ : ZMod n → ℝ} {c : ℝ} {i₁ i₂ i₃ i₄ : ℕ}
    (h12 : i₁ < i₂) (h23 : i₂ < i₃) (h34 : i₃ < i₄) (h41 : i₄ < i₁ + n)
    (hκ1 : c < κ ((i₁ : ℕ) : ZMod n)) (hκ2 : κ ((i₂ : ℕ) : ZMod n) < c)
    (hκ3 : c < κ ((i₃ : ℕ) : ZMod n)) (hκ4 : κ ((i₄ : ℕ) : ZMod n) < c) :
    (∃ a₁ k₁ a₂ k₂ : ℕ, k₁ < n ∧ k₂ < n ∧
        PlateauMaxRun κ a₁ k₁ ∧ PlateauMaxRun κ a₂ k₂ ∧
        ∀ m₁, m₁ ≤ k₁ → ∀ m₂, m₂ ≤ k₂ →
          ((a₁ + m₁ : ℕ) : ZMod n) ≠ ((a₂ + m₂ : ℕ) : ZMod n)) ∧
    (∃ a₁ k₁ a₂ k₂ : ℕ, k₁ < n ∧ k₂ < n ∧
        PlateauMinRun κ a₁ k₁ ∧ PlateauMinRun κ a₂ k₂ ∧
        ∀ m₁, m₁ ≤ k₁ → ∀ m₂, m₂ ≤ k₂ →
          ((a₁ + m₁ : ℕ) : ZMod n) ≠ ((a₂ + m₂ : ℕ) : ZMod n)) := by
  -- the two period-shifted window values
  have e1 : ((i₁ + n : ℕ) : ZMod n) = ((i₁ : ℕ) : ZMod n) := by
    push_cast [ZMod.natCast_self]; ring
  have e2 : ((i₂ + n : ℕ) : ZMod n) = ((i₂ : ℕ) : ZMod n) := by
    push_cast [ZMod.natCast_self]; ring
  constructor
  · -- MAXIMA: arcs (i₂, i₄) through i₃ and (i₄, i₂+n) through i₁+n
    obtain ⟨a, b, hA1, hA2, hA3, hAc, hAL, hAR⟩ :=
      exists_max_run (fun m : ℕ => κ ((m : ℕ) : ZMod n)) h23.le h34.le
        (lt_trans hκ2 hκ3) (lt_trans hκ4 hκ3)
    obtain ⟨a', b', hB1, hB2, hB3, hBc, hBL, hBR⟩ :=
      exists_max_run (fun m : ℕ => κ ((m : ℕ) : ZMod n)) h41.le
        (show i₁ + n ≤ i₂ + n by omega)
        (by simp only [e1]; exact lt_trans hκ4 hκ1)
        (by simp only [e1, e2]; exact lt_trans hκ2 hκ1)
    have hk1 : b - a < n := by omega
    have hk2 : b' - a' < n := by omega
    refine ⟨a, b - a, a', b' - a', hk1, hk2,
      plateauMaxRun_of_natRun (by omega) hA2 hAc hAL hAR,
      plateauMaxRun_of_natRun (by omega) hB2 hBc hBL hBR, ?_⟩
    intro m₁ hm₁ m₂ hm₂
    exact natCast_zmod_ne (by omega) (by omega)
  · -- MINIMA: arcs (i₁, i₃) through i₂ and (i₃, i₁+n) through i₄
    obtain ⟨a, b, hA1, hA2, hA3, hAc, hAL, hAR⟩ :=
      exists_max_run (fun m : ℕ => -κ ((m : ℕ) : ZMod n)) h12.le h23.le
        (by simpa using lt_trans hκ2 hκ1)
        (by simpa using lt_trans hκ2 hκ3)
    obtain ⟨a', b', hB1, hB2, hB3, hBc, hBL, hBR⟩ :=
      exists_max_run (fun m : ℕ => -κ ((m : ℕ) : ZMod n)) h34.le
        (show i₄ ≤ i₁ + n by omega)
        (by simpa using lt_trans hκ4 hκ3)
        (by simp only [e1]; simpa using lt_trans hκ4 hκ1)
    have hk1 : b - a < n := by omega
    have hk2 : b' - a' < n := by omega
    refine ⟨a, b - a, a', b' - a', hk1, hk2,
      plateauMinRun_of_natRun (by omega) hA2
        (fun x h1 h2 => neg_inj.1 (hAc x h1 h2)) (by simpa using hAL)
        (by simpa using hAR),
      plateauMinRun_of_natRun (by omega) hB2
        (fun x h1 h2 => neg_inj.1 (hBc x h1 h2)) (by simpa using hBL)
        (by simpa using hBR), ?_⟩
    intro m₁ hm₁ m₂ hm₂
    exact natCast_zmod_ne (by omega) (by omega)

end Gluck.Discrete
