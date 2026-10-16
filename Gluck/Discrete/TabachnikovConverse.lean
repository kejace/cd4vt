/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.TabachnikovFourActive
public import Gluck.Statements

/-!
# Tabachnikov's discrete converse in his own vocabulary

Tabachnikov (*Converse Sturm–Hurwitz–Kellogg theorem and related results*,
arXiv:0710.5902, Problem 2) conjectures: if a cyclic sequence `r₁, …, rₙ`
(`n ≥ 4`) has at least two local maxima and two local minima, then it is the
sequence of radii of the circles circumscribing consecutive vertex triples of
a *coherent* convex `n`-gon — one where the center of each such circle lies
inside the cone of the middle vertex.

`tabachnikovProblem2_all` proves this in the curvature/turning-angle gauge
(`RealizesR2`). This file collates the pieces into a single statement
phrased with radii, convexity, coherence and circumradii:

* `dist_circumcenterR2_mul` — the circumradius identity `2|Δ| R = abc`.
* `IsPlateauTwoMaxTwoMin` — at least two distinct local maxima and two
  distinct local minima, local extrema counted plateau-aware (Dahlberg).
* `IsCoherentConvexPolygon` — simple, strictly convex (counterclockwise) and
  coherent (`CoherentR2`: circumcenter in the *open* vertex cone).
* `tabachnikov_converse` — the collated theorem, including the
  non-degeneracy clause: adjacent radii that differ force the four
  consecutive vertices off a common circle.
-/

@[expose] public section

namespace Gluck.Discrete

open Complex (normSq)

variable {n : ℕ}

/-! ## The circumradius identity -/

/-- **Circumradius identity** `2|Δ| · R = |pq| · |qr| · |rp|` for a
non-collinear triple, where `Δ = crossR2 p q r` is twice the signed area and
`R` the distance from `circumcenterR2 p q r` to `p`. -/
theorem dist_circumcenterR2_mul {p q r : ℂ} (h : crossR2 p q r ≠ 0) :
    dist (circumcenterR2 p q r) p * (2 * |crossR2 p q r|) =
      dist p q * dist q r * dist r p := by
  set δ := crossR2 p q r with hδ
  set u := q - p with hu
  set w := r - p with hw
  set num : ℂ := (normSq w : ℂ) * u - (normSq u : ℂ) * w with hnum
  have hζ : (circumcenterR2 p q r - p) * (2 * (δ : ℂ)) = Complex.I * num := by
    have h2 : (2 * (δ : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 h)
    rw [circumcenterR2, add_sub_cancel_left, div_mul_cancel₀ _ h2]
  have hsq : normSq (circumcenterR2 p q r - p) * (4 * δ ^ 2) =
      normSq u * normSq w * normSq (w - u) := by
    have := congrArg normSq hζ
    simp only [map_mul, Complex.normSq_I, Complex.normSq_ofReal, one_mul] at this
    have h2 : normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
    rw [h2] at this
    have hn : normSq num = normSq u * normSq w * normSq (w - u) := by
      simp only [hnum, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [← hn, ← this]
    ring
  have hL : 0 ≤ dist (circumcenterR2 p q r) p * (2 * |δ|) := by positivity
  have hR : 0 ≤ dist p q * dist q r * dist r p := by positivity
  refine (pow_left_inj₀ hL hR two_ne_zero).1 ?_
  have e1 : dist (circumcenterR2 p q r) p ^ 2 = normSq (circumcenterR2 p q r - p) := by
    rw [dist_eq_norm, Complex.normSq_eq_norm_sq]
  have e2 : dist p q ^ 2 = normSq u := by
    rw [dist_comm, dist_eq_norm, Complex.normSq_eq_norm_sq]
  have e3 : dist q r ^ 2 = normSq (w - u) := by
    rw [dist_comm, dist_eq_norm, Complex.normSq_eq_norm_sq, hw, hu, sub_sub_sub_cancel_right]
  have e4 : dist r p ^ 2 = normSq w := by
    rw [dist_eq_norm, Complex.normSq_eq_norm_sq]
  calc (dist (circumcenterR2 p q r) p * (2 * |δ|)) ^ 2
      = dist (circumcenterR2 p q r) p ^ 2 * (4 * δ ^ 2) := by
        rw [mul_pow, mul_pow, sq_abs]; ring
    _ = (dist p q * dist q r * dist r p) ^ 2 := by
        rw [e1, hsq, mul_pow, mul_pow, e2, e3, e4]; ring

/-- The circumradius of a non-collinear triple is the reciprocal of the
absolute signed Menger curvature, read with the middle vertex first. -/
theorem dist_circumcenterR2_eq_inv_abs_signedMenger {A B C : ℂ}
    (h : crossR2 B A C ≠ 0) :
    dist (circumcenterR2 B A C) B = 1 / |signedMengerR2 A B C| := by
  have hABC : crossR2 A B C = -crossR2 B A C := by
    rw [← crossR2_cycle A B C]; exact crossR2_swap B A C
  obtain ⟨hBA, hAC, hCB⟩ := pairwise_ne_of_crossR2_ne_zero h
  have hd1 : 0 < dist A B := dist_pos.2 (Ne.symm hBA)
  have hd2 : 0 < dist B C := dist_pos.2 (Ne.symm hCB)
  have hd3 : 0 < dist C A := dist_pos.2 (Ne.symm hAC)
  have hδ : 0 < |crossR2 B A C| := abs_pos.2 h
  have key := dist_circumcenterR2_mul h
  rw [signedMengerR2, hABC, abs_div, abs_mul, abs_neg, abs_mul, abs_mul, abs_two,
    abs_of_pos hd1, abs_of_pos hd2, abs_of_pos hd3, one_div_div]
  rw [eq_div_iff (by positivity)]
  rw [dist_comm B A, dist_comm C B, dist_comm A C] at key
  linarith [key]

/-! ## Menger curvature and circumradius of the realized polygon -/

/-- The closed positive moderate-arc polygon has signed Menger curvature
`κ i` at every vertex. -/
theorem signedMengerR2_polygonR2 [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * Real.pi) (i : ZMod n) :
    signedMengerR2 (polygonR2 κ ℓ (i - 1)) (polygonR2 κ ℓ i) (polygonR2 κ ℓ (i + 1)) =
      κ i := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set k : ℕ := i.val + (n - 1) with hk
  have hn1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub hpos, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hiv : ((i.val : ℕ) : ZMod n) = i := ZMod.natCast_rightInverse i
  have hc0 : ((k : ℕ) : ZMod n) = i - 1 := by
    rw [hk, Nat.cast_add, hiv, hn1]; ring
  have hc1 : ((k + 1 : ℕ) : ZMod n) = i := by
    rw [hk, Nat.cast_add, Nat.cast_add, Nat.cast_one, hiv, hn1]; ring
  have hc2 : ((k + 1 + 1 : ℕ) : ZMod n) = i + 1 := by
    rw [hk, Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one, hiv, hn1]; ring
  have e0 : vertexR2 κ ℓ k = polygonR2 κ ℓ (i - 1) := by
    rw [vertexR2_eq_polygon hE hT k, hc0]
  have e1 : vertexR2 κ ℓ (k + 1) = polygonR2 κ ℓ i := by
    rw [vertexR2_eq_polygon hE hT (k + 1), hc1]
  have e2 : vertexR2 κ ℓ (k + 1 + 1) = polygonR2 κ ℓ (i + 1) := by
    rw [vertexR2_eq_polygon hE hT (k + 1 + 1), hc2]
  rw [← e0, ← e1, ← e2, signedMengerR2_development hMA k, hc1]

/-! ## The collated statement -/

/-- Four points lie on a common circle. -/
def Concyclic4 (a b c d : ℂ) : Prop :=
  ∃ (o : ℂ) (ρ : ℝ), dist a o = ρ ∧ dist b o = ρ ∧ dist c o = ρ ∧ dist d o = ρ

private lemma plateauMaxRun_inv {r : ZMod n → ℝ} (hr : ∀ i, 0 < r i) {a k : ℕ}
    (h : PlateauMaxRun r a k) : PlateauMinRun (fun i => 1 / r i) a k := by
  obtain ⟨hc, h1, h2⟩ := h
  refine ⟨fun m hm => by simp only [hc m hm], ?_, ?_⟩
  · exact one_div_lt_one_div_of_lt (hr _) h1
  · exact one_div_lt_one_div_of_lt (hr _) h2

private lemma plateauMinRun_inv {r : ZMod n → ℝ} (hr : ∀ i, 0 < r i) {a k : ℕ}
    (h : PlateauMinRun r a k) : PlateauMaxRun (fun i => 1 / r i) a k := by
  obtain ⟨hc, h1, h2⟩ := h
  refine ⟨fun m hm => by simp only [hc m hm], ?_, ?_⟩
  · exact one_div_lt_one_div_of_lt (hr _) h1
  · exact one_div_lt_one_div_of_lt (hr _) h2

/-- The reciprocal of a positive two-max/two-min sequence lies in the
extremum-form hypothesis class of the discrete converse. -/
lemma discreteFourVertexExtrema_inv {r : ZMod n → ℝ} (hr : ∀ i, 0 < r i)
    (h : IsPlateauTwoMaxTwoMin r) : DiscreteFourVertexExtrema (fun i => 1 / r i) := by
  obtain ⟨⟨a₁, k₁, a₂, k₂, hk₁, hk₂, hM₁, hM₂, hd⟩, ⟨b₁, j₁, b₂, j₂, hj₁, hj₂, hm₁, hm₂, he⟩⟩ := h
  exact ⟨fun i => one_div_pos.2 (hr i), Or.inr
    ⟨⟨b₁, j₁, b₂, j₂, hj₁, hj₂, plateauMinRun_inv hr hm₁, plateauMinRun_inv hr hm₂, he⟩,
     ⟨a₁, k₁, a₂, k₂, hk₁, hk₂, plateauMaxRun_inv hr hM₁, plateauMaxRun_inv hr hM₂, hd⟩⟩⟩

/-- Uniqueness of the circumcenter: a point equidistant from a non-collinear
triple is its circumcenter. -/
lemma eq_circumcenterR2_of_equidist {p q r o : ℂ} (h : crossR2 p q r ≠ 0)
    (hq : dist q o = dist p o) (hr : dist r o = dist p o) :
    o = circumcenterR2 p q r := by
  obtain ⟨h1, h2⟩ := re_conj_circumcenterR2_sub h
  have hq' : normSq (q - o) = normSq (p - o) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ← dist_eq_norm,
      ← dist_eq_norm, hq]
  have hr' : normSq (r - o) = normSq (p - o) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ← dist_eq_norm,
      ← dist_eq_norm, hr]
  set c := circumcenterR2 p q r
  have hδ : (q - p).re * (r - p).im - (q - p).im * (r - p).re ≠ 0 := by
    simpa [crossR2] using h
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hq' hr'
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im, Complex.normSq_apply] at h1 h2
  -- both `o` and `c` solve the same 2×2 linear system with determinant `δ`
  have e1 : ((q - p).re) * (o.re - c.re) + ((q - p).im) * (o.im - c.im) = 0 := by
    simp only [Complex.sub_re, Complex.sub_im]; nlinarith
  have e2 : ((r - p).re) * (o.re - c.re) + ((r - p).im) * (o.im - c.im) = 0 := by
    simp only [Complex.sub_re, Complex.sub_im]; nlinarith
  have hx : o.re - c.re = 0 := by
    have := mul_left_cancel₀ hδ (show ((q - p).re * (r - p).im - (q - p).im * (r - p).re)
      * (o.re - c.re) = ((q - p).re * (r - p).im - (q - p).im * (r - p).re) * 0 by
        linear_combination (r - p).im * e1 - (q - p).im * e2)
    exact this
  have hy : o.im - c.im = 0 := by
    have := mul_left_cancel₀ hδ (show ((q - p).re * (r - p).im - (q - p).im * (r - p).re)
      * (o.im - c.im) = ((q - p).re * (r - p).im - (q - p).im * (r - p).re) * 0 by
        linear_combination (q - p).re * e2 - (r - p).re * e1)
    exact this
  exact Complex.ext (by linarith) (by linarith)

/-- In a polygon whose consecutive triples are non-collinear, four
consecutive concyclic vertices force equal circumradii at the two middle
vertices. -/
lemma vertexCircumradius_eq_of_concyclic {v : ZMod n → ℂ} (i : ZMod n)
    (h₀ : crossR2 (v i) (v (i - 1)) (v (i + 1)) ≠ 0)
    (h₁ : crossR2 (v (i + 1)) (v (i + 1 - 1)) (v (i + 1 + 1)) ≠ 0)
    (hc : Concyclic4 (v (i - 1)) (v i) (v (i + 1)) (v (i + 2))) :
    vertexCircumradius v i = vertexCircumradius v (i + 1) := by
  obtain ⟨o, ρ, ha, hb, hc', hd⟩ := hc
  have hsub : i + 1 - 1 = i := by ring
  have hadd : i + 1 + 1 = i + 2 := by ring
  rw [hsub, hadd] at h₁
  have ho₀ : o = circumcenterR2 (v i) (v (i - 1)) (v (i + 1)) :=
    eq_circumcenterR2_of_equidist h₀ (by rw [ha, hb]) (by rw [hc', hb])
  have ho₁ : o = circumcenterR2 (v (i + 1)) (v i) (v (i + 2)) :=
    eq_circumcenterR2_of_equidist h₁ (by rw [hb, hc']) (by rw [hd, hc'])
  unfold vertexCircumradius
  rw [hsub, hadd, ← ho₀, ← ho₁, dist_comm, hb, dist_comm, hc']

/-- **Tabachnikov's Problem 2, collated statement.** Let `n ≥ 4` and let
`r : ZMod n → ℝ` be a cyclic sequence of positive numbers with at least two
local maxima and two local minima (plateau-aware). Then there is a coherent
convex polygon `v` whose circle through `v (i - 1), v i, v (i + 1)` has radius
`r i` for every `i`, with signed Menger curvature `1 / r i`. Moreover, if no
two cyclically adjacent radii are equal, then no four consecutive vertices of
`v` lie on a common circle (Tabachnikov's non-degeneracy condition). -/
theorem tabachnikov_converse [NeZero n] (hn : 4 ≤ n) {r : ZMod n → ℝ}
    (hr : ∀ i, 0 < r i) (hext : IsPlateauTwoMaxTwoMin r) :
    ∃ v : ZMod n → ℂ, IsCoherentConvexPolygon v ∧
      (∀ i, vertexCircumradius v i = r i) ∧
      (∀ i, signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) = 1 / r i) ∧
      ((∀ i, r i ≠ r (i + 1)) →
        ∀ i, ¬ Concyclic4 (v (i - 1)) (v i) (v (i + 1)) (v (i + 2))) := by
  set κ : ZMod n → ℝ := fun i => 1 / r i with hκdef
  have hκ : ∀ i, 0 < κ i := fun i => one_div_pos.2 (hr i)
  have hreal : RealizesR2 κ :=
    tabachnikovProblem2_iff_extrema_form.mp (tabachnikovProblem2_all hn) κ
      (discreteFourVertexExtrema_inv hr hext)
  obtain ⟨ℓ, hMA, hE, hT, hsimple⟩ := hreal
  have hn3 : 3 ≤ n := by omega
  have hcoh := coherent_development_moderate hMA hκ hE hT
  have hmenger := signedMengerR2_polygonR2 hMA hE hT
  have hrad : ∀ i, vertexCircumradius (polygonR2 κ ℓ) i = r i := by
    intro i
    rw [vertexCircumradius, dist_circumcenterR2_eq_inv_abs_signedMenger (hcoh i).1,
      hmenger i, abs_of_pos (hκ i), hκdef, one_div_one_div]
  refine ⟨polygonR2 κ ℓ,
    ⟨hsimple, fun a c hca hca1 => crossR2_polygonR2_edge_vertex_pos hMA hκ hE hT a c hca hca1,
      hcoh⟩, hrad, hmenger, ?_⟩
  intro hne i hcon
  apply hne i
  rw [← hrad i, ← hrad (i + 1)]
  exact vertexCircumradius_eq_of_concyclic i (hcoh i).1 (hcoh (i + 1)).1 hcon

/-- The geometric converse: prescribed positive plateau-extremal radii are realized
by one coherent strictly convex polygon. -/
theorem tabachnikov_converse_geometric [NeZero n] (hn : 4 ≤ n) {r : ZMod n → ℝ}
    (hr : ∀ i, 0 < r i) (hext : IsPlateauTwoMaxTwoMin r) :
    ∃ v : ZMod n → ℂ, IsCoherentConvexPolygon v ∧
      ∀ i, vertexCircumradius v i = r i :=
  (tabachnikov_converse hn hr hext).imp fun _ h ↦ ⟨h.1, h.2.1⟩

end Gluck.Discrete
