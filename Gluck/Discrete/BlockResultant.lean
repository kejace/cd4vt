/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Discrete.Defs

/-!
# Two-edge blocks and the cross-block angle

The geometric half of layer (i-3) of the zigzag chain: the **two-edge block
resultant identity**.  Two consecutive edges whose shared vertex has curvature
`1/r` and whose (TA) half-angles there are `π/2 − x`, `π/2 − y` are two chords
of one circle of radius `r`, of lengths `2r cos x`, `2r cos y`, meeting at the
turn `π − x − y`.  Their developed sum is again a single chord of the same
circle:

`2r cos x · e^{iψ} + 2r cos y · e^{i(ψ+π−x−y)} = 2r sin(x+y) · e^{i(ψ+π/2−y)}`

— an exact closed form with **no** hypothesis on `r, x, y, ψ`.  Consequently
two blocks with radii `r, s`, deficits `(p,q)`, `(m,n)` and intervening turn
`w` satisfy `T₂ · conj T₁ = ‖T₂‖‖T₁‖ · e^{i(π−H)}` with `H = p + n − w`, and
for a quadrilateral whose curvature maxima sit at vertices `1` and `3` the
developed closure `Gluck.Discrete.closureGap` is exactly `T₁ + T₂` with
`w = θ₂` the single intervening turn.

* `sin_add_sin_mul_exp` — the elementary two-chord identity.
* `blockResultant`, `blockResultant_eq`, `norm_blockResultant`,
  `blockResultant_ne_zero` — the block resultant and its polar closed form.
* `polar_mul_conj`, `blockResultant_mul_conj` — the cross-block angle `π − H`.
* `turningAngle_of_deficits` — (TA) at a radius-minimum vertex is `π − x − y`.
* `closureGap_eq_sum_of_subset` — dormant (zero-length) edges drop out of the
  closure.
* `closureGap_eq_two_blocks`, `closureGap_two_block_form`,
  `closureGap_two_block_angle` — the `n = 4` identification: the quadrilateral
  closure is `T₁ + T₂`, and the pair satisfies exactly the hypotheses
  `hT₁ne` / `hT₂ne` / `hangle` of `Gluck.Discrete.exists_two_block_closure`.

**Scope.**  Nothing here proves any realization: `n = 4` positive-DFV
realizability is already unconditional in this tree
(`discreteGluckConverse_R2_pos_four`), so the value of the capstone is that it
supplies, in closed form and against an in-tree ground truth, the exact input
that `exists_two_block_closure` consumes — not a new theorem.  The ambient
even case, in which the two blocks are separated by dormant zero-length edges
and `w` is an accumulated turn, is branch (iv) and is NOT carried out here.

-/

namespace Gluck.Discrete

open scoped Real

/-! ## The elementary chord identity -/

/-- `lem:br_sin_exp` — the two-chord identity
`sin u + sin v · e^{i(u+v)} = sin(u+v) · e^{iv}` in `ℂ`, for all real `u, v`.
The imaginary parts agree trivially; the real parts are the subtraction
formula `sin ((u+v) − v) = sin (u+v) cos v − cos (u+v) sin v`. -/
theorem sin_add_sin_mul_exp (u v : ℝ) :
    (Real.sin u : ℂ) + (Real.sin v : ℂ) * Complex.exp (((u + v : ℝ) : ℂ) * Complex.I) =
      (Real.sin (u + v) : ℂ) * Complex.exp ((v : ℂ) * Complex.I) := by
  have hre : Real.sin u + Real.sin v * Real.cos (u + v) = Real.sin (u + v) * Real.cos v := by
    have h := Real.sin_sub (u + v) v
    rw [add_sub_cancel_right] at h
    linarith
  have hre' : (Real.sin u : ℂ) + (Real.sin v : ℂ) * (Real.cos (u + v) : ℂ) =
      (Real.sin (u + v) : ℂ) * (Real.cos v : ℂ) := by exact_mod_cast hre
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  linear_combination hre'

/-! ## The block resultant and its closed form -/

/-- `def:br_block` — the block resultant `𝒯(r, ψ, x, y)`: the developed sum of
the two edge vectors of a two-edge block — two chords of a circle of radius
`r`, of lengths `2r cos x` and `2r cos y`, the first leaving at heading `ψ`
and the second after the turn `π − x − y` prescribed by (TA) at their shared
vertex. -/
noncomputable def blockResultant (r ψ x y : ℝ) : ℂ :=
  ((2 * r * Real.cos x : ℝ) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) +
    ((2 * r * Real.cos y : ℝ) : ℂ) *
      Complex.exp (((ψ + (π - x - y) : ℝ) : ℂ) * Complex.I)

/-- `lem:br_closed_form` — the block resultant is a single chord of the same
circle: `𝒯(r,ψ,x,y) = 2r sin(x+y) · e^{i(ψ+π/2−y)}`, unconditionally. -/
theorem blockResultant_eq (r ψ x y : ℝ) :
    blockResultant r ψ x y =
      ((2 * r * Real.sin (x + y) : ℝ) : ℂ) *
        Complex.exp (((ψ + π / 2 - y : ℝ) : ℂ) * Complex.I) := by
  have key := sin_add_sin_mul_exp (π / 2 - x) (π / 2 - y)
  rw [Real.sin_pi_div_two_sub, Real.sin_pi_div_two_sub] at key
  have hsum : Real.sin (π / 2 - x + (π / 2 - y)) = Real.sin (x + y) := by
    rw [show π / 2 - x + (π / 2 - y) = π - (x + y) by ring, Real.sin_pi_sub]
  rw [hsum] at key
  unfold blockResultant
  rw [show ((ψ + (π - x - y) : ℝ) : ℂ) * Complex.I =
        (ψ : ℂ) * Complex.I + ((π / 2 - x + (π / 2 - y) : ℝ) : ℂ) * Complex.I by
      push_cast [-Complex.ofReal_sin, -Complex.ofReal_cos]; ring,
    show ((ψ + π / 2 - y : ℝ) : ℂ) * Complex.I =
        (ψ : ℂ) * Complex.I + ((π / 2 - y : ℝ) : ℂ) * Complex.I by
      push_cast [-Complex.ofReal_sin, -Complex.ofReal_cos]; ring,
    Complex.exp_add, Complex.exp_add]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination 2 * (r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) * key

/-- `lem:br_norm` — the modulus of the block resultant is `2r sin(x+y)` when
that quantity is nonnegative. -/
theorem norm_blockResultant {r x y : ℝ} (ψ : ℝ) (hr : 0 ≤ r)
    (hs : 0 ≤ Real.sin (x + y)) :
    ‖blockResultant r ψ x y‖ = 2 * r * Real.sin (x + y) := by
  rw [blockResultant_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) hs)]

/-- `lem:br_ne_zero` — the block resultant of a nondegenerate block does not
vanish. -/
theorem blockResultant_ne_zero {r x y : ℝ} (ψ : ℝ) (hr : 0 < r)
    (hs : 0 < Real.sin (x + y)) : blockResultant r ψ x y ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_blockResultant ψ hr.le hs.le]
  exact (mul_pos (mul_pos two_pos hr) hs).ne'

/-- `lem:br_polar` — polar product: `(R₂ e^{iφ₂}) · conj (R₁ e^{iφ₁}) =
R₁R₂ · e^{i(φ₂−φ₁)}` for real `R₁, R₂, φ₁, φ₂`. -/
theorem polar_mul_conj (R₁ R₂ φ₁ φ₂ : ℝ) :
    ((R₂ : ℂ) * Complex.exp ((φ₂ : ℂ) * Complex.I)) *
      (starRingEnd ℂ) ((R₁ : ℂ) * Complex.exp ((φ₁ : ℂ) * Complex.I)) =
      ((R₁ * R₂ : ℝ) : ℂ) * Complex.exp (((φ₂ - φ₁ : ℝ) : ℂ) * Complex.I) := by
  have hconj : (starRingEnd ℂ) (Complex.exp ((φ₁ : ℂ) * Complex.I)) =
      Complex.exp (-((φ₁ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [map_mul, Complex.conj_ofReal, hconj,
    show (((φ₂ - φ₁ : ℝ) : ℂ) * Complex.I) =
      (φ₂ : ℂ) * Complex.I + -((φ₁ : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.ofReal_mul]
  ring

/-! ## The cross-block angle -/

/-- `lem:br_cross_angle` — the cross-block angle is `π − H`: for two blocks
with radii `r, s`, deficits `(p, q)`, `(m, n)` and intervening turn `w`
(the second block leaving at heading `ψ + (π − p − q) + w`),
`T₂ · conj T₁ = ‖T₂‖‖T₁‖ · e^{i(π−H)}` with `H = p + n − w`. -/
theorem blockResultant_mul_conj {r s : ℝ} (ψ p q m n w : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hpq : 0 ≤ Real.sin (p + q)) (hmn : 0 ≤ Real.sin (m + n)) :
    blockResultant s (ψ + (π - p - q) + w) m n *
        (starRingEnd ℂ) (blockResultant r ψ p q) =
      ((‖blockResultant s (ψ + (π - p - q) + w) m n‖ *
          ‖blockResultant r ψ p q‖ : ℝ) : ℂ) *
        Complex.exp (((π - (p + n - w) : ℝ) : ℂ) * Complex.I) := by
  rw [norm_blockResultant _ hs hmn, norm_blockResultant _ hr hpq,
    blockResultant_eq, blockResultant_eq, polar_mul_conj,
    show (ψ + (π - p - q) + w + π / 2 - n) - (ψ + π / 2 - q) = π - (p + n - w) by ring,
    show (2 * s * Real.sin (m + n) * (2 * r * Real.sin (p + q)) : ℝ) =
      (2 * r * Real.sin (p + q) * (2 * s * Real.sin (m + n)) : ℝ) by ring]

/-! ## Identification with the developed closure -/

/-- `lem:br_turn_min` — the (TA) turn at a radius-minimum vertex: if
`κ i = 1/r`, `ℓ (i−1) = 2r cos x` and `ℓ i = 2r cos y` with `r > 0` and
`x, y ∈ [0, π/2]`, then the Euclidean turning angle at `i` is `π − x − y`. -/
theorem turningAngle_of_deficits {N : ℕ} {κ ℓ : ZMod N → ℝ} {i : ZMod N}
    {r x y : ℝ} (hr : 0 < r) (hκ : κ i = 1 / r)
    (hx : x ∈ Set.Icc 0 (π / 2)) (hy : y ∈ Set.Icc 0 (π / 2))
    (hprev : ℓ (i - 1) = 2 * r * Real.cos x) (hcur : ℓ i = 2 * r * Real.cos y) :
    turningAngle 0 κ ℓ i = π - x - y := by
  have hr' : r ≠ 0 := hr.ne'
  have harc : ∀ z : ℝ, z ∈ Set.Icc 0 (π / 2) →
      Real.arcsin (1 / r * (2 * r * Real.cos z / 2)) = π / 2 - z := by
    intro z hz
    have h1 : 1 / r * (2 * r * Real.cos z / 2) = Real.cos z := by
      field_simp
    rw [h1, ← Real.sin_pi_div_two_sub,
      Real.arcsin_sin (by linarith [hz.2, Real.pi_pos]) (by linarith [hz.1])]
  simp only [turningAngle, tK_zero, hκ, hprev, hcur]
  rw [harc x hx, harc y hy]
  ring

/-- `lem:br_sum_support` — dormant edges drop out of the closure: if
`S ⊆ range n` contains every index of nonzero length, the closure gap is the
sum over `S` alone. -/
theorem closureGap_eq_sum_of_subset {n : ℕ} (κ ℓ : ZMod n → ℝ) {S : Finset ℕ}
    (hS : S ⊆ Finset.range n)
    (hout : ∀ j ∈ Finset.range n, j ∉ S → ℓ (j : ZMod n) = 0) :
    closureGap κ ℓ =
      ∑ j ∈ S, (ℓ (j : ZMod n) : ℂ) *
        Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) := by
  unfold closureGap vertexR2
  exact (Finset.sum_subset hS fun j hj hjS => by rw [hout j hj hjS]; simp).symm

/-- `lem:br_split4` — the quadrilateral closure splits into two bracketed
blocks: `E(κ,ℓ) = (ℓ₀e^{iψ₀} + ℓ₁e^{iψ₁}) + (ℓ₂e^{iψ₂} + ℓ₃e^{iψ₃})`. -/
theorem closureGap_eq_two_blocks (κ ℓ : ZMod 4 → ℝ) :
    closureGap κ ℓ =
      ((ℓ ((0 : ℕ) : ZMod 4) : ℂ) * Complex.exp ((heading κ ℓ 0 : ℂ) * Complex.I) +
        (ℓ ((1 : ℕ) : ZMod 4) : ℂ) * Complex.exp ((heading κ ℓ 1 : ℂ) * Complex.I)) +
      ((ℓ ((2 : ℕ) : ZMod 4) : ℂ) * Complex.exp ((heading κ ℓ 2 : ℂ) * Complex.I) +
        (ℓ ((3 : ℕ) : ZMod 4) : ℂ) * Complex.exp ((heading κ ℓ 3 : ℂ) * Complex.I)) := by
  unfold closureGap vertexR2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  ring

/-- Local copy of the private `heading_succ` of `TangentChord.lean` (public in
`Inhabitant.lean`, not imported here): the heading gains one turn per step. -/
private lemma heading_step {n : ℕ} (κ ℓ : ZMod n → ℝ) (j : ℕ) :
    heading κ ℓ (j + 1) = heading κ ℓ j + turningAngle 0 κ ℓ ((j + 1 : ℕ) : ZMod n) := by
  unfold heading; rw [Finset.sum_range_succ]

/-- `thm:br_two_block_n4` — the two-block form of a quadrilateral closure:
with curvature maxima at vertices `1` and `3` (`κ₁ = 1/r`, `κ₃ = 1/s`, edge
lengths `2r cos p, 2r cos q, 2s cos m, 2s cos n`), the developed closure is
`E(κ,ℓ) = T₁ + T₂` with `T₁ = 𝒯(r, ψ₀, p, q)` and
`T₂ = 𝒯(s, ψ₀ + (π − p − q) + θ₂, m, n)`. -/
theorem closureGap_two_block_form {κ ℓ : ZMod 4 → ℝ} {r s p q m n : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hp : p ∈ Set.Icc 0 (π / 2)) (hq : q ∈ Set.Icc 0 (π / 2))
    (hm : m ∈ Set.Icc 0 (π / 2)) (hn : n ∈ Set.Icc 0 (π / 2))
    (hκ1 : κ 1 = 1 / r) (hκ3 : κ 3 = 1 / s)
    (hl0 : ℓ 0 = 2 * r * Real.cos p) (hl1 : ℓ 1 = 2 * r * Real.cos q)
    (hl2 : ℓ 2 = 2 * s * Real.cos m) (hl3 : ℓ 3 = 2 * s * Real.cos n) :
    closureGap κ ℓ =
      blockResultant r (heading κ ℓ 0) p q +
        blockResultant s
          (heading κ ℓ 0 + (π - p - q) + turningAngle 0 κ ℓ 2) m n := by
  have hθ1 : turningAngle 0 κ ℓ 1 = π - p - q :=
    turningAngle_of_deficits hr hκ1 hp hq
      (by rw [show (1 : ZMod 4) - 1 = 0 by decide]; exact hl0) hl1
  have hθ3 : turningAngle 0 κ ℓ 3 = π - m - n :=
    turningAngle_of_deficits hs hκ3 hm hn
      (by rw [show (3 : ZMod 4) - 1 = 2 by decide]; exact hl2) hl3
  have e1 : heading κ ℓ 1 = heading κ ℓ 0 + turningAngle 0 κ ℓ ((1 : ℕ) : ZMod 4) :=
    heading_step κ ℓ 0
  have e2 : heading κ ℓ 2 = heading κ ℓ 1 + turningAngle 0 κ ℓ ((2 : ℕ) : ZMod 4) :=
    heading_step κ ℓ 1
  have e3 : heading κ ℓ 3 = heading κ ℓ 2 + turningAngle 0 κ ℓ ((3 : ℕ) : ZMod 4) :=
    heading_step κ ℓ 2
  rw [Nat.cast_one] at e1
  rw [Nat.cast_ofNat] at e2 e3
  rw [closureGap_eq_two_blocks]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  unfold blockResultant
  rw [hl0, hl1, hl2, hl3, e3, e2, e1, hθ1, hθ3]

/-- `thm:br_two_block_angle_n4` — the quadrilateral cross-block identity, the
capstone of layer (i-3b).  In the situation of `closureGap_two_block_form`,
with additionally `0 < sin(p+q)` and `0 < sin(m+n)`, the pair
`T₁ = 𝒯(r, ψ₀, p, q)`, `T₂ = 𝒯(s, ψ₀ + (π−p−q) + θ₂, m, n)` satisfies:
both are nonzero with moduli `2r sin(p+q)`, `2s sin(m+n)`; the cross-block
identity `T₂ · conj T₁ = ‖T₂‖‖T₁‖ · e^{i(π−H)}` with `H = p + n − θ₂`; and
`E(κ,ℓ) = T₁ + T₂`.

These are exactly the hypotheses `hT₁ne`, `hT₂ne` and `hangle` of
`Gluck.Discrete.exists_two_block_closure` (whose conclusion `T₁ + T₂ = 0` is
then exactly `E(κ,ℓ) = 0`).  **No realization is claimed**: `n = 4`
positive-DFV realizability is already unconditional in this tree
(`discreteGluckConverse_R2_pos_four`); this capstone supplies the closed-form
input of the two-block machinery against that in-tree ground truth.  The
ambient form, with the two blocks separated by dormant zero-length edges and
`θ₂` replaced by an accumulated turn, is branch (iv) and is not proved here. -/
theorem closureGap_two_block_angle {κ ℓ : ZMod 4 → ℝ} {r s p q m n : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hp : p ∈ Set.Icc 0 (π / 2)) (hq : q ∈ Set.Icc 0 (π / 2))
    (hm : m ∈ Set.Icc 0 (π / 2)) (hn : n ∈ Set.Icc 0 (π / 2))
    (hκ1 : κ 1 = 1 / r) (hκ3 : κ 3 = 1 / s)
    (hl0 : ℓ 0 = 2 * r * Real.cos p) (hl1 : ℓ 1 = 2 * r * Real.cos q)
    (hl2 : ℓ 2 = 2 * s * Real.cos m) (hl3 : ℓ 3 = 2 * s * Real.cos n)
    (hpq : 0 < Real.sin (p + q)) (hmn : 0 < Real.sin (m + n)) :
    blockResultant r (heading κ ℓ 0) p q ≠ 0 ∧
    blockResultant s (heading κ ℓ 0 + (π - p - q) + turningAngle 0 κ ℓ 2) m n ≠ 0 ∧
    ‖blockResultant r (heading κ ℓ 0) p q‖ = 2 * r * Real.sin (p + q) ∧
    ‖blockResultant s (heading κ ℓ 0 + (π - p - q) + turningAngle 0 κ ℓ 2) m n‖ =
      2 * s * Real.sin (m + n) ∧
    blockResultant s (heading κ ℓ 0 + (π - p - q) + turningAngle 0 κ ℓ 2) m n *
        (starRingEnd ℂ) (blockResultant r (heading κ ℓ 0) p q) =
      ((‖blockResultant s (heading κ ℓ 0 + (π - p - q) + turningAngle 0 κ ℓ 2) m n‖ *
          ‖blockResultant r (heading κ ℓ 0) p q‖ : ℝ) : ℂ) *
        Complex.exp (((π - (p + n - turningAngle 0 κ ℓ 2) : ℝ) : ℂ) * Complex.I) ∧
    closureGap κ ℓ =
      blockResultant r (heading κ ℓ 0) p q +
        blockResultant s (heading κ ℓ 0 + (π - p - q) + turningAngle 0 κ ℓ 2) m n :=
  ⟨blockResultant_ne_zero _ hr hpq,
   blockResultant_ne_zero _ hs hmn,
   norm_blockResultant _ hr.le hpq.le,
   norm_blockResultant _ hs.le hmn.le,
   blockResultant_mul_conj (heading κ ℓ 0) p q m n (turningAngle 0 κ ℓ 2)
     hr.le hs.le hpq.le hmn.le,
   closureGap_two_block_form hr hs hp hq hm hn hκ1 hκ3 hl0 hl1 hl2 hl3⟩

end Gluck.Discrete
