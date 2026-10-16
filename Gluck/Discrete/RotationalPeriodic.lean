/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.Closing
public import Gluck.Discrete.Converse
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Rotationally periodic profiles close, and realizability at every composite `n`

For `n = m * p` with `p`-periodic curvature and length data of total turning
`2π`, the heading advances by exactly `2π/m` across each `p`-block, so the
development is equivariant for the rotation by the primitive `m`-th root of
unity `ω = exp(2πi/m)`: the `j`-th block of edges is `ω^j` times the zeroth
block. Summing the blocks produces the factor `∑_{j<m} ω^j = 0`, so closure is
*free* for rotationally periodic data (`rotational_symmetry_closes`) — the
`m`-fold generalization of `central_symmetry_closes` (the case `m = 2`).

Combined with an intermediate-value argument producing a closing constant edge
length, this yields the chapter capstone `realizesR2_of_periodic`: for every
factorization `n = m * p` with `m, p ≥ 2`, **every** strictly positive
`p`-periodic profile on `ZMod n` is realizable. Specializing gives a
non-constant realizable positive-DFV profile at every composite `n`
(`exists_nonconstant_realizesR2_of_composite`).

**Scope.** This is a subclass theorem: it realizes profiles that happen to be
periodic. Prime `n` admits no factorization with `m, p ≥ 2` and gains nothing;
the general positive-DFV converse is Tabachnikov's Problem 2 (arXiv:0710.5902)
and remains open — nothing here bears on it.

-/

@[expose] public section

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

/-! ## Rotational periodicity of the development -/

/-- **`lem:rot_turning_period`.** For `p`-periodic `κ` and `ℓ` (invariant under
the index shift by the class of `p`), the Euclidean turning angle is
`p`-periodic. The statement of `turningAngle_add_half` is generic in the shift,
so this is that lemma applied at shift `p`. -/
theorem turningAngle_add_period {p : ℕ} {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i) (i : ZMod n) :
    turningAngle 0 κ ℓ (i + (p : ZMod n)) = turningAngle 0 κ ℓ i :=
  turningAngle_add_half hκ hℓ i

/-- Project-local Mathlib supplement: the sum of a `p`-periodic function over
`j` consecutive periods is `j` times the one-period sum (Mathlib has no
periodic-block range-sum lemma). -/
private lemma sum_range_mul_of_periodic (f : ℕ → ℝ) {p : ℕ}
    (hf : ∀ k, f (k + p) = f k) (j : ℕ) :
    ∑ k ∈ Finset.range (j * p), f k = j * ∑ k ∈ Finset.range p, f k := by
  have hext : ∀ j' k : ℕ, f (k + j' * p) = f k := by
    intro j'
    induction j' with
    | zero => intro k; simp
    | succ j' ih =>
      intro k
      have hsplit : k + (j' + 1) * p = k + j' * p + p := by ring
      rw [hsplit, hf, ih]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have hblock : ∑ k ∈ Finset.range p, f (j * p + k)
        = ∑ k ∈ Finset.range p, f k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.add_comm (j * p) k]
      exact hext j k
    rw [hblock]
    push_cast
    ring

/-- **`lem:rot_block_sum`.** Under `n = m * p`, `p`-periodicity of `κ, ℓ`, and
total turning `2π`, every `p`-block of turning angles sums to `2π/m`: for all
`a : ℕ`, `∑_{k < p} turningAngle 0 κ ℓ ((a + k : ℕ) : ZMod n) = 2π/m`. A run
of `m` consecutive blocks is a full period summing to `2π`
(`sum_range_natCast_add`), and all blocks are equal by `p`-periodicity. -/
theorem turningAngle_block_sum_period [NeZero n] {m p : ℕ} (hn : n = m * p)
    (hm : 1 ≤ m) {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i)
    (hT : turningSum κ ℓ = 2 * Real.pi) (a : ℕ) :
    ∑ k ∈ Finset.range p, turningAngle 0 κ ℓ ((a + k : ℕ) : ZMod n)
      = 2 * Real.pi / m := by
  have hper : ∀ k : ℕ,
      turningAngle 0 κ ℓ ((a + (k + p) : ℕ) : ZMod n)
        = turningAngle 0 κ ℓ ((a + k : ℕ) : ZMod n) := by
    intro k
    have hcast : ((a + (k + p) : ℕ) : ZMod n)
        = ((a + k : ℕ) : ZMod n) + (p : ZMod n) := by push_cast; ring
    rw [hcast, turningAngle_add_period hκ hℓ]
  have hfull : ∑ k ∈ Finset.range n,
      turningAngle 0 κ ℓ ((a + k : ℕ) : ZMod n) = 2 * Real.pi := by
    rw [sum_range_natCast_add (turningAngle 0 κ ℓ) a]
    exact hT
  have hrange : Finset.range n = Finset.range (m * p) := by rw [hn]
  rw [hrange, sum_range_mul_of_periodic
    (fun k => turningAngle 0 κ ℓ ((a + k : ℕ) : ZMod n)) hper m] at hfull
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  rw [eq_div_iff hm0.ne']
  linear_combination hfull

/-- **`lem:rot_heading_period`.** Under the hypotheses of
`turningAngle_block_sum_period`, the heading advances by exactly `2π/m` over
each `p`-block: `heading κ ℓ (j + p) = heading κ ℓ j + 2π/m`. -/
theorem heading_add_period [NeZero n] {m p : ℕ} (hn : n = m * p) (hm : 1 ≤ m)
    {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i)
    (hT : turningSum κ ℓ = 2 * Real.pi) (j : ℕ) :
    heading κ ℓ (j + p) = heading κ ℓ j + 2 * Real.pi / m := by
  unfold heading
  rw [show j + p + 1 = (j + 1) + p from by ring,
    Finset.sum_range_add (fun i => turningAngle 0 κ ℓ (i : ZMod n)) (j + 1) p]
  congr 1
  exact turningAngle_block_sum_period hn hm hκ hℓ hT (j + 1)

/-! ## The rotation root and its vanishing geometric sum -/

/-- **`def:rotation_root`.** The primitive `m`-th root of unity
`ω_m = exp(2πi/m)`, written in the exact shape used by Mathlib's
`Complex.isPrimitiveRoot_exp`. -/
noncomputable def rotationRoot (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / m)

/-- **`lem:rot_geom_sum`.** The geometric sum of the rotation root vanishes for
every `m ≥ 2`: `∑_{j<m} ω_m^j = 0`. -/
theorem rotationRoot_geom_sum {m : ℕ} (hm : 2 ≤ m) :
    ∑ j ∈ Finset.range m, rotationRoot m ^ j = 0 :=
  (Complex.isPrimitiveRoot_exp m (by omega)).geom_sum_eq_zero (by omega)

/-! ## Closure is free -/

/-- **`lem:rot_vertex_period`.** Blockwise rotation of the development: under
`n = m * p`, `p`-periodic data, and total turning `2π`, the development
satisfies `v (k + p) = v p + ω_m · v k` for every `k : ℕ`. Each edge of the
shifted block is `ω_m` times its mate one block earlier. -/
theorem vertexR2_add_period [NeZero n] {m p : ℕ} (hn : n = m * p) (hm : 1 ≤ m)
    {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i)
    (hT : turningSum κ ℓ = 2 * Real.pi) (k : ℕ) :
    vertexR2 κ ℓ (k + p) = vertexR2 κ ℓ p + rotationRoot m * vertexR2 κ ℓ k := by
  have hedge : ∀ j : ℕ,
      (ℓ ((j + p : ℕ) : ZMod n) : ℂ)
          * Complex.exp ((heading κ ℓ (j + p) : ℂ) * Complex.I)
        = rotationRoot m * ((ℓ ((j : ℕ) : ZMod n) : ℂ)
          * Complex.exp ((heading κ ℓ j : ℂ) * Complex.I)) := by
    intro j
    have hcast : ((j + p : ℕ) : ZMod n) = ((j : ℕ) : ZMod n) + (p : ZMod n) := by
      push_cast; ring
    rw [hcast, hℓ, heading_add_period hn hm hκ hℓ hT j]
    have hsplit : ((heading κ ℓ j + 2 * Real.pi / m : ℝ) : ℂ) * Complex.I
        = 2 * Real.pi * Complex.I / m
          + (heading κ ℓ j : ℂ) * Complex.I := by
      push_cast; ring
    rw [hsplit, Complex.exp_add]
    simp only [rotationRoot]
    ring
  induction k with
  | zero =>
    have h0 : vertexR2 κ ℓ 0 = 0 := by simp [vertexR2]
    rw [Nat.zero_add, h0, mul_zero, add_zero]
  | succ k ih =>
    rw [show k + 1 + p = (k + p) + 1 from by ring, vertexR2_succ, vertexR2_succ,
      ih, hedge k]
    ring

/-- **`lem:rot_vertex_block`.** The `j`-th block endpoint of the development is
the geometric partial sum times the first block endpoint:
`v (j * p) = (∑_{i<j} ω_m^i) · v p`. -/
theorem vertexR2_block_geom [NeZero n] {m p : ℕ} (hn : n = m * p) (hm : 1 ≤ m)
    {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i)
    (hT : turningSum κ ℓ = 2 * Real.pi) (j : ℕ) :
    vertexR2 κ ℓ (j * p)
      = (∑ i ∈ Finset.range j, rotationRoot m ^ i) * vertexR2 κ ℓ p := by
  induction j with
  | zero => simp [vertexR2]
  | succ j ih =>
    rw [Nat.succ_mul, vertexR2_add_period hn hm hκ hℓ hT (j * p), ih,
      geom_sum_succ]
    ring

/-- **`thm:rotational_symmetry_closes`.** Rotationally periodic profiles close:
for `n = m * p` with `m ≥ 2`, `p`-periodic `κ, ℓ`, and total turning `2π`, the
closure gap vanishes. The gap is `v (m·p) = (∑_{i<m} ω_m^i) · v p`, and the
geometric sum vanishes because `ω_m` is a primitive `m`-th root of unity. No
winding, determinant, Miranda or boundary-exclusion machinery is used. -/
theorem rotational_symmetry_closes [NeZero n] {m p : ℕ} (hn : n = m * p)
    (hm : 2 ≤ m) {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i)
    (hT : turningSum κ ℓ = 2 * Real.pi) :
    closureGap κ ℓ = 0 := by
  have hgap : closureGap κ ℓ = vertexR2 κ ℓ (m * p) := congrArg (vertexR2 κ ℓ) hn
  rw [hgap, vertexR2_block_geom hn (by omega) hκ hℓ hT m,
    rotationRoot_geom_sum hm, zero_mul]

/-- **`cor:central_symmetry_from_rotational`.** Consistency check: taking
`m = 2` in `rotational_symmetry_closes` reproduces the central-symmetry closing
lemma `central_symmetry_closes` — there `ω_2 = -1` and the vanishing geometric
sum `1 + (-1) = 0` is exactly the pairwise cancellation of opposite edges. -/
theorem central_symmetry_closes_of_rotational [NeZero n] {m : ℕ}
    (hn : n = 2 * m) {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (m : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (m : ZMod n)) = ℓ i)
    (hT : turningSum κ ℓ = 2 * Real.pi) :
    closureGap κ ℓ = 0 :=
  rotational_symmetry_closes hn le_rfl hκ hℓ hT

/-! ## A closing constant edge length exists -/

/-- **`lem:rot_turning_const_length`.** On a constant edge length `ℓ ≡ s` the
turning sum of a `p`-periodic profile on `ZMod (m·p)` collapses to `2m` times
the one-block arcsine sum: `turningSum κ s = 2m ∑_{r<p} arcsin(κ_r s / 2)`. -/
theorem turningSum_const_length_periodic [NeZero n] {m p : ℕ} (hn : n = m * p)
    {κ : ZMod n → ℝ} (hκp : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i) (s : ℝ) :
    turningSum κ (fun _ => s)
      = 2 * m * ∑ r ∈ Finset.range p,
          Real.arcsin (κ ((r : ℕ) : ZMod n) * s / 2) := by
  have hsum : turningSum κ (fun _ => s)
      = ∑ k ∈ Finset.range n,
          2 * Real.arcsin (κ ((k : ℕ) : ZMod n) * s / 2) := by
    rw [show turningSum κ (fun _ => s)
        = ∑ i : ZMod n, turningAngle 0 κ (fun _ => s) i from rfl,
      ← sum_range_natCast_add (turningAngle 0 κ (fun _ => s)) 0]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Nat.zero_add, turningAngle, tK_zero]
    rw [show κ ((k : ℕ) : ZMod n) * s / 2 = κ ((k : ℕ) : ZMod n) * (s / 2) from
      mul_div_assoc _ _ _]
    ring
  have hper : ∀ k : ℕ,
      2 * Real.arcsin (κ ((k + p : ℕ) : ZMod n) * s / 2)
        = 2 * Real.arcsin (κ ((k : ℕ) : ZMod n) * s / 2) := by
    intro k
    have hcast : ((k + p : ℕ) : ZMod n) = ((k : ℕ) : ZMod n) + (p : ZMod n) := by
      push_cast; ring
    rw [hcast, hκp]
  have hrange : Finset.range n = Finset.range (m * p) := by rw [hn]
  rw [hsum, hrange, sum_range_mul_of_periodic
    (fun k => 2 * Real.arcsin (κ ((k : ℕ) : ZMod n) * s / 2)) hper m,
    ← Finset.mul_sum]
  ring

/-- **`lem:rot_wall_bound`.** At the collapse wall `s = 2/M`, where `M` is an
attained upper bound of the profile over one period, the turning sum of a
strictly positive `p`-periodic profile overshoots `2π` (using `m ≥ 2` and
`p ≥ 2`): the maximizing vertex contributes `arcsin 1 = π/2` per block and
every other vertex contributes strictly positively. -/
theorem two_pi_lt_turningSum_periodic_wall [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 2 ≤ m) (hp : 2 ≤ p) {κ : ZMod n → ℝ}
    (hκp : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hκ : ∀ i, 0 < κ i) {M : ℝ} {r₀ : ℕ} (hr₀ : r₀ < p)
    (hM : κ ((r₀ : ℕ) : ZMod n) = M)
    (_hMub : ∀ r < p, κ ((r : ℕ) : ZMod n) ≤ M) :
    2 * Real.pi < turningSum κ (fun _ => 2 / M) := by
  have hM0 : 0 < M := hM ▸ hκ _
  rw [turningSum_const_length_periodic hn hκp]
  have hgpos : ∀ r : ℕ, 0 < Real.arcsin (κ ((r : ℕ) : ZMod n) * (2 / M) / 2) :=
    fun r => Real.arcsin_pos.2
      (div_pos (mul_pos (hκ _) (div_pos two_pos hM0)) two_pos)
  have hg0 : Real.arcsin (κ ((r₀ : ℕ) : ZMod n) * (2 / M) / 2) = Real.pi / 2 := by
    rw [show κ ((r₀ : ℕ) : ZMod n) * (2 / M) / 2 = 1 from by
      rw [hM]; field_simp]
    exact Real.arcsin_one
  obtain ⟨j₁, hj₁mem, hj₁ne⟩ : ∃ j₁, j₁ ∈ Finset.range p ∧ j₁ ≠ r₀ := by
    rcases Nat.eq_zero_or_pos r₀ with h0 | h0
    · exact ⟨1, Finset.mem_range.mpr (by omega), by omega⟩
    · exact ⟨0, Finset.mem_range.mpr (by omega), by omega⟩
  have hblock : Real.pi / 2
      < ∑ r ∈ Finset.range p, Real.arcsin (κ ((r : ℕ) : ZMod n) * (2 / M) / 2) := by
    have h := Finset.single_lt_sum hj₁ne (Finset.mem_range.mpr hr₀) hj₁mem
      (hgpos j₁) (fun k _ _ => (hgpos k).le)
    rw [hg0] at h
    exact h
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hstep : 2 * (m : ℝ) * (Real.pi / 2)
      < 2 * (m : ℝ) * ∑ r ∈ Finset.range p,
          Real.arcsin (κ ((r : ℕ) : ZMod n) * (2 / M) / 2) :=
    mul_lt_mul_of_pos_left hblock (by linarith)
  nlinarith [Real.pi_pos]

/-- Iterated `p`-periodicity along the natural-number lift: shifting the lifted
index by any multiple of `p` leaves a `p`-periodic profile unchanged. -/
private lemma apply_natCast_add_mul_period {κ : ZMod n → ℝ} {p : ℕ}
    (hκp : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i) (k : ℕ) :
    ∀ j : ℕ, κ ((k + j * p : ℕ) : ZMod n) = κ ((k : ℕ) : ZMod n) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hcast : ((k + (j + 1) * p : ℕ) : ZMod n)
        = ((k + j * p : ℕ) : ZMod n) + (p : ZMod n) := by push_cast; ring
    rw [hcast, hκp, ih]

/-- Every value of a `p`-periodic profile is attained on the lifted block
`{0, …, p-1}`. -/
private lemma exists_period_rep [NeZero n] {p : ℕ} (hp : 0 < p)
    {κ : ZMod n → ℝ} (hκp : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (i : ZMod n) : ∃ r, r < p ∧ κ i = κ ((r : ℕ) : ZMod n) := by
  refine ⟨i.val % p, Nat.mod_lt _ hp, ?_⟩
  have h := apply_natCast_add_mul_period hκp (i.val % p) (i.val / p)
  rw [Nat.mod_add_div'] at h
  rw [← h, ZMod.natCast_rightInverse i]

/-- **`lem:rot_exists_length`.** A closing constant edge length exists: for
`n = m * p` with `m, p ≥ 2` and a strictly positive `p`-periodic profile `κ`,
there is a constant length `ℓ ≡ s` that is moderate for `κ` and has total
turning exactly `2π`. Intermediate value theorem on `[0, 2/M]`, `M` the block
maximum; interiority of `s` gives moderateness. -/
theorem exists_constant_length_periodic [NeZero n] {m p : ℕ} (hn : n = m * p)
    (hm : 2 ≤ m) (hp : 2 ≤ p) {κ : ZMod n → ℝ}
    (hκp : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hκ : ∀ i, 0 < κ i) :
    ∃ s : ℝ, ModerateArc 0 κ (fun _ => s) ∧
      turningSum κ (fun _ => s) = 2 * Real.pi := by
  obtain ⟨r₀, hr₀mem, hr₀max⟩ :=
    Finset.exists_max_image (Finset.range p) (fun r => κ ((r : ℕ) : ZMod n))
      ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hM0 : 0 < κ ((r₀ : ℕ) : ZMod n) := hκ _
  have hMub : ∀ r < p, κ ((r : ℕ) : ZMod n) ≤ κ ((r₀ : ℕ) : ZMod n) :=
    fun r hr => hr₀max r (Finset.mem_range.mpr hr)
  have hκle : ∀ i : ZMod n, κ i ≤ κ ((r₀ : ℕ) : ZMod n) := by
    intro i
    obtain ⟨r, hr, hi⟩ := exists_period_rep (by omega) hκp i
    rw [hi]
    exact hMub r hr
  have hwall0 : 0 < 2 / κ ((r₀ : ℕ) : ZMod n) := div_pos two_pos hM0
  have hgcont : Continuous (fun t : ℝ => turningSum κ (fun _ => t)) := by
    have h := (turningSum_smul_tendsto_zero (n := n) (κ := κ)
      (ℓ₀ := fun _ => 1)).1
    simpa using h
  have hg0 : turningSum κ (fun _ => (0 : ℝ)) = 0 := by
    simp [turningSum, turningAngle, tK_zero]
  have hgwall : 2 * Real.pi
      < turningSum κ (fun _ => 2 / κ ((r₀ : ℕ) : ZMod n)) :=
    two_pi_lt_turningSum_periodic_wall hn hm hp hκp hκ
      (Finset.mem_range.mp hr₀mem) rfl hMub
  have hmem : 2 * Real.pi ∈ Set.Ioo (turningSum κ (fun _ => (0 : ℝ)))
      (turningSum κ (fun _ => 2 / κ ((r₀ : ℕ) : ZMod n))) := by
    rw [hg0]
    exact ⟨by positivity, hgwall⟩
  obtain ⟨s, hs, hgs⟩ :=
    intermediate_value_Ioo hwall0.le hgcont.continuousOn hmem
  refine ⟨s, ?_, hgs⟩
  have hks : ∀ i : ZMod n, κ i * s < 2 := by
    intro i
    have h1 : κ i * s ≤ κ ((r₀ : ℕ) : ZMod n) * s :=
      mul_le_mul_of_nonneg_right (hκle i) hs.1.le
    have h2 : κ ((r₀ : ℕ) : ZMod n) * s < 2 := by
      have h3 : κ ((r₀ : ℕ) : ZMod n) * s
          < κ ((r₀ : ℕ) : ZMod n) * (2 / κ ((r₀ : ℕ) : ZMod n)) :=
        mul_lt_mul_of_pos_left hs.2 hM0
      rwa [show κ ((r₀ : ℕ) : ZMod n) * (2 / κ ((r₀ : ℕ) : ZMod n)) = 2 from by
        field_simp] at h3
    linarith
  rw [moderateArc_zero_iff]
  intro i
  refine ⟨hs.1, ?_, ?_⟩ <;>
  · rw [abs_of_pos (hκ i),
      show κ i * (s / 2) = κ i * s / 2 from (mul_div_assoc _ _ _).symm]
    linarith [hks i]

/-! ## Realizability at every composite `n` -/

/-- **`thm:realizes_periodic`.** Periodic positive profiles are realizable: for
every factorization `n = m * p` with `m ≥ 2` and `p ≥ 2`, every strictly
positive `p`-periodic curvature profile on `ZMod n` satisfies `RealizesR2`.
The closing constant edge length of `exists_constant_length_periodic` is
trivially `p`-periodic, so closure is free by `rotational_symmetry_closes`,
and positivity makes the closed development simple.

This is a subclass theorem; the general positive-DFV converse is Tabachnikov's
Problem 2 and remains open. -/
theorem realizesR2_of_periodic [NeZero n] {m p : ℕ} (hn : n = m * p)
    (hm : 2 ≤ m) (hp : 2 ≤ p) {κ : ZMod n → ℝ}
    (hκp : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hκ : ∀ i, 0 < κ i) :
    RealizesR2 κ := by
  obtain ⟨s, hMA, hT⟩ := exists_constant_length_periodic hn hm hp hκp hκ
  have hclose : closureGap κ (fun _ => s) = 0 :=
    rotational_symmetry_closes hn hm hκp (fun _ => rfl) hT
  have hn3 : 3 ≤ n := by
    have h4 : 2 * 2 ≤ m * p := Nat.mul_le_mul hm hp
    omega
  exact ⟨fun _ => s, hMA, hclose, hT,
    isSimplePolygon_of_turningPositive hn3 hMA hκ hclose hT⟩

/-- **`def:alternating_profile`.** The `2`-periodic profile on `ZMod n` taking
the value `a` at indices of even representative and `b` at odd ones. -/
def alternatingProfile (a b : ℝ) : ZMod n → ℝ := fun i =>
  if i.val % 2 = 0 then a else b

/-- The alternating profile at a lifted index below `n` reads off the parity of
the lift. -/
private lemma alternatingProfile_natCast (a b : ℝ) {k : ℕ} (hk : k < n) :
    alternatingProfile (n := n) a b ((k : ℕ) : ZMod n)
      = if k % 2 = 0 then a else b := by
  unfold alternatingProfile
  rw [ZMod.val_cast_of_lt hk]

/-- The alternating profile is `2`-periodic (for even `n > 2`). -/
private lemma alternatingProfile_add_two [NeZero n] (h2n : 2 < n)
    (hdvd : 2 ∣ n) (a b : ℝ) (i : ZMod n) :
    alternatingProfile a b (i + ((2 : ℕ) : ZMod n)) = alternatingProfile a b i := by
  unfold alternatingProfile
  have hval : (i + ((2 : ℕ) : ZMod n)).val % 2 = i.val % 2 := by
    rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt h2n,
      Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod_right]
  rw [hval]

/-- **`thm:realizes_alternating`.** Every even `n = 2m ≥ 4` carries a
realizable alternating profile: for `a, b > 0` the profile
`alternatingProfile a b` satisfies `RealizesR2`, via the factorization
`n = m · 2` in `realizesR2_of_periodic`. -/
theorem realizesR2_alternating [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (hm : 2 ≤ m) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    RealizesR2 (alternatingProfile (n := n) a b) := by
  have hn' : n = m * 2 := by omega
  refine realizesR2_of_periodic hn' hm le_rfl ?_ ?_
  · exact fun i => alternatingProfile_add_two (by omega) ⟨m, hn⟩ a b i
  · intro i
    unfold alternatingProfile
    split <;> assumption

/-- **`lem:alternating_dfv`.** For `n = 2m ≥ 4` and `a > b > 0` the alternating
profile satisfies the positive discrete four-vertex hypothesis (window at level
`(a+b)/2` on the lifted indices `0 < 1 < 2 < 3`), and it is not constant. -/
theorem discreteFourVertexPos_alternating [NeZero n] {m : ℕ} (hn : n = 2 * m)
    (hm : 2 ≤ m) {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    DiscreteFourVertexPos (alternatingProfile (n := n) a b) ∧
      ¬ ∃ c, ∀ i : ZMod n, alternatingProfile (n := n) a b i = c := by
  have hn4 : 4 ≤ n := by omega
  have h0 : alternatingProfile (n := n) a b ((0 : ℕ) : ZMod n) = a := by
    rw [alternatingProfile_natCast a b (by omega)]; norm_num
  have h1 : alternatingProfile (n := n) a b ((1 : ℕ) : ZMod n) = b := by
    rw [alternatingProfile_natCast a b (by omega)]; norm_num
  have h2 : alternatingProfile (n := n) a b ((2 : ℕ) : ZMod n) = a := by
    rw [alternatingProfile_natCast a b (by omega)]; norm_num
  have h3 : alternatingProfile (n := n) a b ((3 : ℕ) : ZMod n) = b := by
    rw [alternatingProfile_natCast a b (by omega)]; norm_num
  refine ⟨⟨?_, Or.inr ⟨(a + b) / 2, by linarith, 0, 1, 2, 3,
    by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
  · intro i
    unfold alternatingProfile
    split <;> linarith
  · rw [h0]; linarith
  · rw [h1]; linarith
  · rw [h2]; linarith
  · rw [h3]; linarith
  · rintro ⟨c, hc⟩
    have ha' := hc ((0 : ℕ) : ZMod n)
    have hb' := hc ((1 : ℕ) : ZMod n)
    rw [h0] at ha'
    rw [h1] at hb'
    linarith

/-- One period of the composite-`n` witness: value `2` at block starts, `1`
elsewhere. -/
def spikeProfile (p : ℕ) : ZMod n → ℝ := fun i =>
  if i.val % p = 0 then 2 else 1

/-- The spike profile at a lifted index below `n` reads off the residue of the
lift. -/
private lemma spikeProfile_natCast {p k : ℕ} (hk : k < n) :
    spikeProfile (n := n) p ((k : ℕ) : ZMod n)
      = if k % p = 0 then 2 else 1 := by
  unfold spikeProfile
  rw [ZMod.val_cast_of_lt hk]

/-- **`cor:composite_nonvacuity`.** Non-vacuity at every composite `n`: for
every factorization `n = m * p` with `m, p ≥ 2` there is a strictly positive,
non-constant profile on `ZMod n` satisfying `DiscreteFourVertexPos` and
`RealizesR2`. Witness: the `p`-periodic profile with one period
`(2, 1, …, 1)`; its four-vertex window sits at level `3/2` on the lifted
indices `0 < 1 < p < p + 1`. -/
theorem exists_nonconstant_realizesR2_of_composite [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 2 ≤ m) (hp : 2 ≤ p) :
    ∃ κ : ZMod n → ℝ, DiscreteFourVertexPos κ ∧ RealizesR2 κ ∧
      ¬ ∃ c, ∀ i : ZMod n, κ i = c := by
  have h2p : 2 * p ≤ m * p := Nat.mul_le_mul_right p hm
  have hn2p : 2 * p ≤ n := by rw [hn]; exact h2p
  have hpn : p < n := by omega
  have hp1n : p + 1 < n := by omega
  have hdvd : p ∣ n := ⟨m, by rw [hn, Nat.mul_comm]⟩
  have hpos : ∀ i : ZMod n, 0 < spikeProfile (n := n) p i := by
    intro i
    unfold spikeProfile
    split <;> norm_num
  have hper : ∀ i : ZMod n,
      spikeProfile (n := n) p (i + (p : ZMod n)) = spikeProfile (n := n) p i := by
    intro i
    unfold spikeProfile
    have hval : (i + (p : ZMod n)).val % p = i.val % p := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hpn,
        Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod_right]
    rw [hval]
  have hv0 : spikeProfile (n := n) p ((0 : ℕ) : ZMod n) = 2 := by
    rw [spikeProfile_natCast (by omega), if_pos (Nat.zero_mod p)]
  have hv1 : spikeProfile (n := n) p ((1 : ℕ) : ZMod n) = 1 := by
    rw [spikeProfile_natCast (by omega),
      if_neg (by rw [Nat.mod_eq_of_lt (by omega)]; omega)]
  have hvp : spikeProfile (n := n) p ((p : ℕ) : ZMod n) = 2 := by
    rw [spikeProfile_natCast hpn, if_pos (Nat.mod_self p)]
  have hvp1 : spikeProfile (n := n) p ((p + 1 : ℕ) : ZMod n) = 1 := by
    rw [spikeProfile_natCast hp1n,
      if_neg (by rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]; omega)]
  refine ⟨spikeProfile (n := n) p, ⟨hpos, Or.inr ⟨3 / 2, by norm_num,
    0, 1, p, p + 1, by omega, by omega, by omega, by omega,
    ?_, ?_, ?_, ?_⟩⟩, realizesR2_of_periodic hn hm hp hper hpos, ?_⟩
  · rw [hv0]; norm_num
  · rw [hv1]; norm_num
  · rw [hvp]; norm_num
  · rw [hvp1]; norm_num
  · rintro ⟨c, hc⟩
    have h2 := hc ((0 : ℕ) : ZMod n)
    have h1 := hc ((1 : ℕ) : ZMod n)
    rw [hv0] at h2
    rw [hv1] at h1
    linarith

end Gluck.Discrete
