/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.CollaredConverse
public import Gluck.Discrete.RotationalPeriodic
public import Gluck.Discrete.RotationalRegular

/-!
# The moment centres of a rotationally periodic configuration are equivariant

For `n = m * p` with `p`-periodic curvature and length data, closed
(`closureGap = 0`) with total turning `2π`, the moment centres of
`CollaredConverse.lean` satisfy the exact rotational equivariance

  `momentCenter (k + p) = rotationRoot m * momentCenter k + vertexR2 κ ℓ p`.

Composed with the planar input `not_collinear_of_rotational_equivariant`
(`RotationalRegular.lean`, `m ≥ 3` only) and the rank-one characterization
`momentCenter_const_iff`, this discharges crux C — moment rank — for every
NON-CONSTANT positive `p`-periodic profile at `m ≥ 3`.  Consequence: the
regular collar interior `collarRegularInterior` is nonempty at every
`n = m·p` with `m ≥ 3`, `p ≥ 2` — that is, at every composite `n ≥ 6` —
replacing the two ad hoc point witnesses (`n = 4` rhombus, `n = 6` hexagon)
by an infinite family.

**Scope.**  This makes the TARGET of crux B′ demonstrably nonempty; it does
NOT prove crux A′, crux B′, or the rank-two case of crux C, all of which
remain open external research.  Prime `n` gains nothing (a `p`-periodic
profile with `p < n` prime is constant — the rank-one failure stratum).
`m = 2` — hence `n = 4` and every purely centrally symmetric configuration —
is genuinely out of reach of this argument: the orbit signed area of
`not_collinear_of_rotational_equivariant` vanishes identically at `m = 2`.
Nothing here bears on Tabachnikov's Problem 2.

-/

@[expose] public section

namespace Gluck.Discrete

open scoped Real

variable {n : ℕ}

/-! ## The arcsine slopes are periodic -/

/-- **`lem:rotcollar_slope_a_period`.**  For `p`-periodic `κ` and `ℓ` the
incoming arcsine slope `a_i = (κ_i/2)/√(1-(κ_i ℓ_{i-1}/2)²)` is `p`-periodic:
it is a fixed function of `κ_i` and `ℓ_{i-1}`, and both are shift-invariant
(after the index commutation `i + p - 1 = (i - 1) + p` in `ZMod n`). -/
theorem collarA_add_period {p : ℕ} {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i) (i : ZMod n) :
    collarA κ ℓ (i + (p : ZMod n)) = collarA κ ℓ i := by
  unfold collarA
  rw [hκ i, show i + (p : ZMod n) - 1 = (i - 1) + (p : ZMod n) from by ring,
    hℓ (i - 1)]

/-- **`lem:rotcollar_slope_b_period`.**  For `p`-periodic `κ` and `ℓ` the
outgoing arcsine slope `b_i = (κ_i/2)/√(1-(κ_i ℓ_i/2)²)` is `p`-periodic; no
index commutation is needed. -/
theorem collarB_add_period {p : ℕ} {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i) (i : ZMod n) :
    collarB κ ℓ (i + (p : ZMod n)) = collarB κ ℓ i := by
  unfold collarB
  rw [hκ i, hℓ i]

/-! ## Reading the moment centre at a natural index -/

/-- **`lem:rotcollar_heading_mul`.**  Under total turning `2π` the heading
advances by exactly `2π` per full period, hence by `2πt` over `t` periods. -/
theorem heading_add_mul_n [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hT : turningSum κ ℓ = 2 * Real.pi) (a t : ℕ) :
    heading κ ℓ (a + n * t) = heading κ ℓ a + 2 * Real.pi * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show a + n * (t + 1) = (a + n * t) + n from by ring, heading_add_n hT,
      ih]
    push_cast
    ring

/-- **`lem:rotcollar_exp_heading`.**  The heading phase depends only on the
residue of the index: `exp(i ψ_{(j̄).val}) = exp(i ψ_j)`, because the two
headings differ by an integer multiple of `2π`. -/
theorem exp_heading_val_natCast [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hT : turningSum κ ℓ = 2 * Real.pi) (j : ℕ) :
    Complex.exp ((heading κ ℓ ((j : ZMod n)).val : ℂ) * Complex.I)
      = Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [show j = j % n + n * (j / n) from (Nat.mod_add_div j n).symm]
  rw [heading_add_mul_n hT (j % n) (j / n)]
  push_cast
  rw [add_mul, Complex.exp_add,
    show (2 : ℂ) * Real.pi * (j / n : ℕ) * Complex.I
        = ((j / n : ℕ) : ℤ) * (2 * Real.pi * Complex.I) from by
      rw [Int.cast_natCast]; ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **`lem:rotcollar_center_natCast`.**  At a closed configuration of total
turning `2π` the moment centre read at the reduction of a natural index `j`
uses the vertex and heading at `j` itself: the `ZMod`-indexed scalar
coefficient is untouched, `vertexR2` is `n`-periodic (`vertexR2_eq_polygon`),
and the heading phase depends only on the residue
(`exp_heading_val_natCast`). -/
theorem momentCenter_natCast [NeZero n] {κ ℓ : ZMod n → ℝ}
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi) (j : ℕ) :
    momentCenter κ ℓ (j : ZMod n)
      = vertexR2 κ ℓ j
        + (((ℓ (j : ZMod n) * collarA κ ℓ ((j : ZMod n) + 1) : ℝ) : ℂ)
              + Complex.I)
            / ((collarB κ ℓ (j : ZMod n) + collarA κ ℓ ((j : ZMod n) + 1) : ℝ) : ℂ)
          * Complex.exp ((heading κ ℓ j : ℂ) * Complex.I) := by
  have hv : vertexR2 κ ℓ ((j : ZMod n)).val = vertexR2 κ ℓ j := by
    have h := vertexR2_eq_polygon hE hT j
    simp only [polygonR2] at h
    exact h.symm
  unfold momentCenter
  rw [hv, exp_heading_val_natCast hT j]

/-! ## Equivariance of the moment centres -/

/-- **`thm:rotcollar_center_period`.**  THE CRUX: for `n = m·p`, `p`-periodic
`κ, ℓ`, closed with total turning `2π`, the moment centres are exactly
equivariant for the rotation by `ω = exp(2πi/m)`:

  `C_{k+p} = ω C_k + v_p`.

The scalar coefficient is `p`-periodic (`collarA_add_period`,
`collarB_add_period`), the vertex satisfies `v_{j+p} = v_p + ω v_j`
(`vertexR2_add_period`), and the heading advances by `2π/m` per block
(`heading_add_period`), so the phase picks up exactly the factor `ω`. -/
theorem momentCenter_add_period [NeZero n] {m p : ℕ} (hn : n = m * p)
    (hm : 1 ≤ m) {κ ℓ : ZMod n → ℝ}
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi)
    (k : ZMod n) :
    momentCenter κ ℓ (k + (p : ZMod n))
      = rotationRoot m * momentCenter κ ℓ k + vertexR2 κ ℓ p := by
  have hjk : ((k.val : ℕ) : ZMod n) = k := ZMod.natCast_rightInverse k
  have hcast : ((k.val + p : ℕ) : ZMod n) = k + (p : ZMod n) := by
    rw [Nat.cast_add, hjk]
  have hphase :
      Complex.exp (((heading κ ℓ k.val + 2 * Real.pi / m : ℝ) : ℂ) * Complex.I)
        = rotationRoot m
            * Complex.exp ((heading κ ℓ k.val : ℂ) * Complex.I) := by
    rw [rotationRoot, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  conv_lhs => rw [← hcast]
  conv_rhs => rw [← hjk]
  rw [momentCenter_natCast hE hT (k.val + p), momentCenter_natCast hE hT k.val,
    hcast, hjk, hℓ k, collarB_add_period hκ hℓ k,
    show k + (p : ZMod n) + 1 = (k + 1) + (p : ZMod n) from by ring,
    collarA_add_period hκ hℓ (k + 1),
    vertexR2_add_period hn hm hκ hℓ hT k.val,
    heading_add_period hn hm hκ hℓ hT k.val, hphase]
  ring

/-! ## Crux C on the rotationally periodic locus -/

/-- **`thm:rotcollar_not_collinear`.**  For `n = m·p` with `m ≥ 3`, a
non-constant positive strictly moderate-arc `p`-periodic closed configuration
of total turning `2π` has non-collinear moment centres: the equivariance
`momentCenter_add_period` feeds the planar input
`not_collinear_of_rotational_equivariant`, and non-constancy of the centres
is the reverse direction of the rank-one characterization
`momentCenter_const_iff`. -/
theorem not_collinear_momentCenter_of_periodic [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 3 ≤ m) (hp : 1 ≤ p) {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (hpos : ∀ i, 0 < κ i)
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi)
    (hnc : ¬ ∀ i j : ZMod n, κ i = κ j) :
    ¬ Collinear ℝ (Set.range (momentCenter κ ℓ)) := by
  refine not_collinear_of_rotational_equivariant hn hm hp
    (c := vertexR2 κ ℓ p) (fun k => ?_) ?_
  · exact momentCenter_add_period hn (by omega) hκ hℓ hE hT k
  · by_contra hnex
    apply hnc
    refine (momentCenter_const_iff hMA hpos hE hT).mp fun k k' => ?_
    by_contra hne
    exact hnex ⟨k, k', hne⟩

/-- **`thm:rotcollar_moment_rank`.**  Crux C holds on the non-constant
rotationally periodic locus at `m ≥ 3`: moment rank via
`momentRank_iff_not_collinear`, whose slope-sum positivity side condition is
automatic for a positive profile. -/
theorem momentRank_of_periodic [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 3 ≤ m) (hp : 1 ≤ p) {κ ℓ : ZMod n → ℝ}
    (hMA : ModerateArc 0 κ ℓ) (hpos : ∀ i, 0 < κ i)
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi)
    (hnc : ¬ ∀ i j : ZMod n, κ i = κ j) :
    MomentRank κ ℓ := by
  rw [momentRank_iff_not_collinear hE
    (fun k => add_pos (collarB_pos hMA (hpos k)) (collarA_pos hMA (hpos (k + 1))))]
  exact not_collinear_momentCenter_of_periodic hn hm hp hMA hpos hκ hℓ hE hT hnc

/-- **`thm:rotcollar_mem`.**  A non-constant positive `p`-periodic closed
strictly moderate-arc configuration of total turning `2π` at `n = m·p`,
`m ≥ 3`, lies in the regular collar interior of every chamber containing its
profile. -/
theorem mem_collarRegularInterior_of_periodic [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 3 ≤ m) (hp : 1 ≤ p) {κ ℓ : ZMod n → ℝ}
    {S : Set (ZMod n → ℝ)} (hS : κ ∈ S)
    (hMA : ModerateArc 0 κ ℓ) (hpos : ∀ i, 0 < κ i)
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hℓ : ∀ i : ZMod n, ℓ (i + (p : ZMod n)) = ℓ i)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * Real.pi)
    (hnc : ¬ ∀ i j : ZMod n, κ i = κ j) :
    (κ, ℓ) ∈ collarRegularInterior S := by
  refine ⟨⟨hS, hMA, ?_⟩,
    momentRank_of_periodic hn hm hp hMA hpos hκ hℓ hE hT hnc⟩
  simp only [closureMapR3]
  rw [Prod.mk_eq_zero]
  exact ⟨hE, by rw [hT]; ring⟩

/-! ## Non-vacuity at every composite index -/

/-- **`thm:rotcollar_nonempty`.**  For every `n = m·p` with `m ≥ 3`, `p ≥ 2`
and every strictly positive non-constant `p`-periodic profile `κ`, the
regular collar interior over the singleton chamber `{κ}` is nonempty: the
closing constant length of `exists_constant_length_periodic` is trivially
`p`-periodic, closure is free by `rotational_symmetry_closes`, and
`mem_collarRegularInterior_of_periodic` applies. -/
theorem collarRegularInterior_nonempty_of_periodic [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 3 ≤ m) (hp : 2 ≤ p) {κ : ZMod n → ℝ}
    (hpos : ∀ i, 0 < κ i)
    (hκ : ∀ i : ZMod n, κ (i + (p : ZMod n)) = κ i)
    (hnc : ¬ ∀ i j : ZMod n, κ i = κ j) :
    (collarRegularInterior {κ}).Nonempty := by
  obtain ⟨s, hMA, hT⟩ :=
    exists_constant_length_periodic hn (by omega) hp hκ hpos
  have hℓ : ∀ i : ZMod n,
      (fun _ : ZMod n => s) (i + (p : ZMod n)) = (fun _ : ZMod n => s) i :=
    fun _ => rfl
  have hE := rotational_symmetry_closes hn (by omega) hκ hℓ hT
  exact ⟨(κ, fun _ => s),
    mem_collarRegularInterior_of_periodic hn hm (by omega) rfl hMA hpos hκ hℓ
      hE hT hnc⟩

/-- **`def:rotcollar_spike`.**  The block spike profile: value `2` at indices
whose representative is divisible by `p`, value `1` elsewhere.  Strictly
positive by construction; `p`-periodic when `p ∣ n`; non-constant when
`2 ≤ p ≤ n`.  (The private `spikeProfile` of `RotationalPeriodic.lean` has
the same shape; this public version is re-proved here rather than
de-privatizing that file.) -/
def blockSpikeProfile (p : ℕ) : ZMod n → ℝ := fun i =>
  if i.val % p = 0 then 2 else 1

/-- **`lem:rotcollar_spike_spec`.**  For `n = m·p` with `m ≥ 1`, `p ≥ 2` the
block spike profile is strictly positive, `p`-periodic and non-constant. -/
theorem blockSpikeProfile_spec [NeZero n] {m p : ℕ} (hn : n = m * p)
    (_hm : 1 ≤ m) (hp : 2 ≤ p) :
    (∀ i : ZMod n, 0 < blockSpikeProfile (n := n) p i) ∧
      (∀ i : ZMod n, blockSpikeProfile (n := n) p (i + (p : ZMod n))
        = blockSpikeProfile (n := n) p i) ∧
      ¬ ∀ i j : ZMod n,
        blockSpikeProfile (n := n) p i = blockSpikeProfile (n := n) p j := by
  have hdvd : p ∣ n := ⟨m, by rw [hn]; exact Nat.mul_comm m p⟩
  have hn2 : 2 ≤ n := by
    have : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hdvd
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold blockSpikeProfile
    split <;> norm_num
  · intro i
    unfold blockSpikeProfile
    have hval : (i + (p : ZMod n)).val % p = i.val % p := by
      have hpn : p % n % p = 0 := by
        rw [Nat.mod_mod_of_dvd _ hdvd, Nat.mod_self]
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ hdvd,
        Nat.add_mod, hpn, add_zero, Nat.mod_mod_of_dvd _ (dvd_refl p)]
    rw [hval]
  · intro hall
    have h01 := hall ((0 : ℕ) : ZMod n) ((1 : ℕ) : ZMod n)
    unfold blockSpikeProfile at h01
    rw [ZMod.val_cast_of_lt (by omega : 0 < n),
      ZMod.val_cast_of_lt (by omega : 1 < n)] at h01
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < p)] at h01
    norm_num at h01

/-- **`cor:rotcollar_nonvacuity`.**  Non-vacuity of the regular collar
interior at every `n = m·p` with `m ≥ 3`, `p ≥ 2` — i.e.\ at every composite
`n ≥ 6`: the block spike profile is a strictly positive non-constant
`p`-periodic witness. -/
theorem exists_nonconstant_collarRegularInterior_nonempty [NeZero n]
    {m p : ℕ} (hn : n = m * p) (hm : 3 ≤ m) (hp : 2 ≤ p) :
    ∃ κ : ZMod n → ℝ, (∀ i, 0 < κ i) ∧ (¬ ∀ i j : ZMod n, κ i = κ j) ∧
      (collarRegularInterior {κ}).Nonempty := by
  obtain ⟨hpos, hper, hnc⟩ := blockSpikeProfile_spec hn (by omega) hp
  exact ⟨blockSpikeProfile p, hpos, hnc,
    collarRegularInterior_nonempty_of_periodic hn hm hp hpos hper hnc⟩

/-- **`cor:rotcollar_alternating`.**  Concrete even-`n` readout: at
`n = 2m ≥ 6` the alternating profile with distinct positive values has
nonempty regular collar interior, via the factorization `n = m·2`. -/
theorem collarRegularInterior_nonempty_alternating [NeZero n] {m : ℕ}
    (hn : n = 2 * m) (hm : 3 ≤ m) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    (collarRegularInterior {alternatingProfile (n := n) a b}).Nonempty := by
  have hn' : n = m * 2 := by omega
  have hpos : ∀ i, 0 < alternatingProfile (n := n) a b i := by
    intro i
    unfold alternatingProfile
    split <;> assumption
  have hper : ∀ i : ZMod n,
      alternatingProfile (n := n) a b (i + ((2 : ℕ) : ZMod n))
        = alternatingProfile (n := n) a b i := by
    intro i
    unfold alternatingProfile
    have hval : (i + ((2 : ℕ) : ZMod n)).val % 2 = i.val % 2 := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 2 < n),
        Nat.mod_mod_of_dvd _ ⟨m, hn⟩, Nat.add_mod_right]
    rw [hval]
  have hnc : ¬ ∀ i j : ZMod n,
      alternatingProfile (n := n) a b i = alternatingProfile (n := n) a b j := by
    intro hall
    have h01 := hall ((0 : ℕ) : ZMod n) ((1 : ℕ) : ZMod n)
    unfold alternatingProfile at h01
    rw [ZMod.val_cast_of_lt (by omega : 0 < n),
      ZMod.val_cast_of_lt (by omega : 1 < n)] at h01
    norm_num at h01
    exact hab h01
  exact collarRegularInterior_nonempty_of_periodic hn' hm le_rfl hpos hper hnc

/-- Project-local Mathlib supplement (arithmetic readout of
`rem:rotcollar_scope`): every composite `n ≥ 6` admits a factorization
`n = m·p` with `m ≥ 3` and `p ≥ 2`.  If the least prime factor is `2` take
`(n/2, 2)`; otherwise it is at least `3` and `(minFac n, n / minFac n)`
works. -/
private lemma exists_factorization_of_composite {n : ℕ} (hn6 : 6 ≤ n)
    (hnp : ¬ n.Prime) : ∃ m p : ℕ, n = m * p ∧ 3 ≤ m ∧ 2 ≤ p := by
  have hq := Nat.minFac_prime (show n ≠ 1 by omega)
  obtain ⟨d, hd⟩ := Nat.minFac_dvd n
  rcases eq_or_lt_of_le hq.two_le with heq | hlt
  · rw [← heq] at hd
    exact ⟨d, 2, by omega, by omega, le_rfl⟩
  · refine ⟨n.minFac, d, hd, by omega, ?_⟩
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · exfalso
      have hcase : d = 0 ∨ d = 1 := by omega
      rcases hcase with h0 | h1
      · rw [h0, Nat.mul_zero] at hd
        omega
      · rw [h1, Nat.mul_one] at hd
        exact hnp (by rw [hd]; exact hq)
    · exact hd2

/-- Non-vacuity of the regular collar interior at **every composite
`n ≥ 6`**, with the factorization bookkeeping of `rem:rotcollar_scope`
discharged: some strictly positive non-constant profile has nonempty regular
collar interior.  (`n = 4` is the sole composite gap — its only factorization
is `2·2`, out of reach of the `m ≥ 3` planar input — and prime `n` is
untouched; nothing here bears on Tabachnikov's Problem 2.) -/
theorem exists_nonconstant_collarRegularInterior_nonempty_of_notPrime
    [NeZero n] (hn6 : 6 ≤ n) (hnp : ¬ n.Prime) :
    ∃ κ : ZMod n → ℝ, (∀ i, 0 < κ i) ∧ (¬ ∀ i j : ZMod n, κ i = κ j) ∧
      (collarRegularInterior {κ}).Nonempty := by
  obtain ⟨m, p, hn, hm, hp⟩ := exists_factorization_of_composite hn6 hnp
  exact exists_nonconstant_collarRegularInterior_nonempty hn hm hp

end Gluck.Discrete
