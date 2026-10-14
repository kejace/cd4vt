/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Gluck.Discrete.TangentChord

/-!
# Rotationally equivariant point families are non-collinear

A purely planar chapter: a family `C : ZMod n → ℂ` that is equivariant for an
affine rotation of order `m ≥ 3` — i.e. `C (k + p) = ω * C k + c` with
`ω = exp (2πi/m)` — is either constant or has non-collinear range.

The mechanism is the signed area of a rotation orbit: for `u ≠ 0` the triple
`O + u, O + ωu, O + ω²u` has signed area `2|u|² sin t (1 − cos t)` with
`t = 2π/m`, strictly positive exactly because `m ≥ 3` puts `t ∈ (0, π)`.
At `m = 2` the expression vanishes identically, so nothing is stated there.

* `crossR2_rotation_orbit` — the signed-area identity for a general angle `t`.
* `crossR2_rotation_orbit_pos` — strict positivity for `t = 2π/m`, `m ≥ 3`.
* `not_collinear_of_crossR2_ne_zero` — nonzero signed area forbids collinearity.
* `rotationFixedPoint_spec` — the unique fixed point of an affine rotation.
* `not_collinear_of_rotational_equivariant` — the capstone.

This file is deliberately independent of `Gluck.Discrete.RotationalPeriodic`
(the rotation root is written out as an explicit exponential); the intended
application to the moment centres of `p`-periodic configurations is recorded in
the blueprint remark `rem:rotational_regular_use`.

-/

namespace Gluck.Discrete

/-! ## The orbit triangle -/

/-- **Signed area of a rotation orbit.** For `ω = exp(i t)` the ordered triple
`O + u, O + ωu, O + ω²u` has signed twice-area
`|u|² (2 sin t − sin 2t) = 2 |u|² sin t (1 − cos t)`. Project-local: the
planar orbit geometry of a rotation is not in Mathlib. -/
lemma crossR2_rotation_orbit (t : ℝ) (O u : ℂ) :
    crossR2 (O + u) (O + Complex.exp ((t : ℂ) * Complex.I) * u)
      (O + Complex.exp ((t : ℂ) * Complex.I) ^ 2 * u)
    = 2 * Complex.normSq u * (Real.sin t * (1 - Real.cos t)) := by
  have hre : (Complex.exp ((t : ℂ) * Complex.I)).re = Real.cos t :=
    Complex.exp_ofReal_mul_I_re t
  have him : (Complex.exp ((t : ℂ) * Complex.I)).im = Real.sin t :=
    Complex.exp_ofReal_mul_I_im t
  simp only [crossR2, Complex.normSq_apply, pow_two, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, hre, him]
  linear_combination ((u.re * u.re + u.im * u.im) * Real.sin t) *
    (Real.sin_sq_add_cos_sq t)

/-- **Positivity for order at least three.** At `t = 2π/m` with `m ≥ 3` the
orbit signed area is strictly positive for `u ≠ 0`: `t ∈ (0, π)` makes both
`sin t` and `1 − cos t` strictly positive. The hypothesis `m ≥ 3` is sharp —
at `m = 2` the area vanishes identically. -/
lemma crossR2_rotation_orbit_pos {m : ℕ} (hm : 3 ≤ m) (O : ℂ) {u : ℂ}
    (hu : u ≠ 0) :
    0 < crossR2 (O + u)
      (O + Complex.exp (2 * Real.pi * Complex.I / m) * u)
      (O + Complex.exp (2 * Real.pi * Complex.I / m) ^ 2 * u) := by
  have harg : 2 * Real.pi * Complex.I / m = ((2 * Real.pi / m : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, crossR2_rotation_orbit]
  have hm0 : (0 : ℝ) < m := by
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hπ := Real.pi_pos
  have ht0 : 0 < 2 * Real.pi / m := by positivity
  have htπ : 2 * Real.pi / m < Real.pi := by
    rw [div_lt_iff₀ hm0]
    have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hsin : 0 < Real.sin (2 * Real.pi / m) :=
    Real.sin_pos_of_pos_of_lt_pi ht0 htπ
  have hcos : Real.cos (2 * Real.pi / m) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl htπ.le ht0
    rwa [Real.cos_zero] at this
  have hnormSq : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have h1c : 0 < 1 - Real.cos (2 * Real.pi / m) := by linarith
  positivity

/-- **A nonzero signed area forbids collinearity** of the three-point set,
over `ℝ` in `ℂ`. Project-local bridge between `crossR2` and Mathlib's
`Collinear`. -/
lemma not_collinear_of_crossR2_ne_zero {A B C : ℂ} (h : crossR2 A B C ≠ 0) :
    ¬ Collinear ℝ ({A, B, C} : Set ℂ) := by
  intro hcol
  obtain ⟨v, hv⟩ :=
    (collinear_iff_of_mem (Set.mem_insert A {B, C})).mp hcol
  obtain ⟨β, hβ⟩ := hv B (by simp)
  obtain ⟨γ, hγ⟩ := hv C (by simp)
  apply h
  rw [hβ, hγ]
  simp only [vadd_eq_add, Complex.real_smul, crossR2, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## Equivariant families -/

/-- **The fixed point of an affine rotation.** For `m ≥ 2` and
`ω = exp(2πi/m)`: `ω ≠ 1` (so `O = c/(1−ω)` is well defined), and the affine
map `z ↦ ω z + c` fixes `O`, hence `ω z + c − O = ω (z − O)` for every `z`.
Project-local. -/
lemma rotationFixedPoint_spec {m : ℕ} (hm : 2 ≤ m) (c : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I / m) ≠ 1 ∧
    Complex.exp (2 * Real.pi * Complex.I / m)
        * (c / (1 - Complex.exp (2 * Real.pi * Complex.I / m))) + c
      = c / (1 - Complex.exp (2 * Real.pi * Complex.I / m)) ∧
    ∀ z : ℂ,
      Complex.exp (2 * Real.pi * Complex.I / m) * z + c
          - c / (1 - Complex.exp (2 * Real.pi * Complex.I / m))
        = Complex.exp (2 * Real.pi * Complex.I / m)
          * (z - c / (1 - Complex.exp (2 * Real.pi * Complex.I / m))) := by
  have hω : Complex.exp (2 * Real.pi * Complex.I / m) ≠ 1 :=
    (Complex.isPrimitiveRoot_exp m (by omega)).ne_one (by omega)
  have h1 : (1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I / m) ≠ 0 :=
    sub_ne_zero_of_ne (Ne.symm hω)
  refine ⟨hω, ?_, fun z => ?_⟩
  · field_simp
    ring
  · field_simp
    ring

/-- **Equivariant families are constant or non-collinear.** Let `n = m·p` with
`m ≥ 3`, `ω = exp(2πi/m)`, and let `C : ZMod n → ℂ` satisfy the equivariance
`C (k + p) = ω C k + c`. If `C` is not constant then its range is not
collinear over `ℝ`.

This is the planar half of the crux-C discharge for rotationally symmetric
configurations; the hypothesis `m ≥ 3` is sharp (at `m = 2` the orbit area
vanishes identically and the argument is genuinely absent). -/
theorem not_collinear_of_rotational_equivariant
    {n m p : ℕ} (_hn : n = m * p) (hm : 3 ≤ m) (_hp : 1 ≤ p) {c : ℂ}
    {C : ZMod n → ℂ}
    (hC : ∀ k : ZMod n, C (k + (p : ZMod n))
        = Complex.exp (2 * Real.pi * Complex.I / m) * C k + c)
    (hnc : ∃ k k' : ZMod n, C k ≠ C k') :
    ¬ Collinear ℝ (Set.range C) := by
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hωdef
  obtain ⟨-, -, hfix⟩ := rotationFixedPoint_spec (by omega : 2 ≤ m) c
  set O : ℂ := c / (1 - ω) with hOdef
  -- some value differs from the fixed point
  have hex : ∃ k : ZMod n, C k ≠ O := by
    by_contra hall
    simp only [not_exists, not_ne_iff] at hall
    obtain ⟨k, k', hne⟩ := hnc
    exact hne ((hall k).trans (hall k').symm)
  obtain ⟨k, hk⟩ := hex
  have hu : C k - O ≠ 0 := sub_ne_zero_of_ne hk
  -- the three orbit points, in fixed-point-centred form
  have h1 : C k = O + (C k - O) := by ring
  have h2 : C (k + (p : ZMod n)) = O + ω * (C k - O) := by
    rw [hC k]
    linear_combination hfix (C k)
  have h3 : C (k + (p : ZMod n) + (p : ZMod n)) = O + ω ^ 2 * (C k - O) := by
    rw [hC (k + (p : ZMod n)), h2]
    linear_combination hfix (O + ω * (C k - O))
  have hpos : 0 < crossR2 (C k) (C (k + (p : ZMod n)))
      (C (k + (p : ZMod n) + (p : ZMod n))) := by
    rw [h1, h2, h3]
    exact crossR2_rotation_orbit_pos hm O hu
  intro hcol
  refine not_collinear_of_crossR2_ne_zero (ne_of_gt hpos) (hcol.subset ?_)
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl <;> exact Set.mem_range_self _

end Gluck.Discrete
