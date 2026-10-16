/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.Converse

/-!
# The graft contraction (G-comb)

This file is the downward, purely combinatorial half of the circle-pinned ear
graft (repo-root `notes/plans/GRAFT_INDUCTION_PLAN.md`, §1.1).  Given a positive cyclic
curvature word of length `n ≥ 6` carrying a strict four-vertex window, we
contract one *adjacent pair* of entries into a single free *cap value* `s`,
producing a word of length `n - 1` that still carries a strict four-vertex
window and is still everywhere positive.  Nothing analytic happens here: the
entire content is that the cyclic pattern of crossings of a level survives the
contraction.

Throughout the parent has length `m + 2` and the child has length `m + 1`; the
standing hypothesis is `4 ≤ m`, i.e. parent length at least `6` and child
length at least `5`.

The last section settles how restrictive it is to demand a contraction site
whose *whole* pair range is admissible — the form the downstream endpoint
bracket consumes.  `inBlockLevel_or_alternatingTieDegenerate` shows that a
positive windowed profile either admits such an in-block level or is
`AlternatingTieDegenerate`, a stratum which for `n ≥ 6` is contained in the
finite union of the diagonal hyperplanes `{κ i₁ = κ i₂}`, `i₁ ≠ i₂`
(`exists_ne_eq_of_alternatingTieDegenerate`);
`exists_graft_contraction_attaining` is the attaining corollary.

-/

@[expose] public section

namespace Gluck.Discrete

variable {n : ℕ}

/-! ## The contracted child -/

/-- **The graft child** `ch(κ,s) : ZMod (m + 1) → ℝ`: the parent
`κ : ZMod (m + 2) → ℝ` with its two last entries `κ m`, `κ (m+1)` contracted
into the single free cap value `s`.  In words the child is
`(κ_0, …, κ_{m-1}, s)`.  The two parent entries `κ_m, κ_{m+1}` are the
*contracted pair*; the value `s` is the free cap.  Because `val(k) < m + 1 < m + 2`
whenever `val(k) ≠ m`, the parent index in the second branch is the residue with
the same numeric value, so no wraparound occurs. -/
noncomputable def graftChild {m : ℕ} (κ : ZMod (m + 2) → ℝ) (s : ℝ) : ZMod (m + 1) → ℝ :=
  fun k => if k.val = m then s else κ ((k.val : ℕ) : ZMod (m + 2))

/-- **The copied part of the child**: if `val(k) < m` then
`ch(κ,s)_k = κ_{val(k)}`.  Immediate from the definition: the test
`val(k) = m` fails. -/
theorem graftChild_of_lt {m : ℕ} (κ : ZMod (m + 2) → ℝ) (s : ℝ) {k : ZMod (m + 1)}
    (hk : k.val < m) : graftChild κ s k = κ ((k.val : ℕ) : ZMod (m + 2)) := by
  simp only [graftChild, if_neg (Nat.ne_of_lt hk)]

/-- **The cap entry of the child**: `ch(κ,s)_m̄ = s`, where `m̄` denotes the
residue of `m` in `ZMod (m + 1)`.  Since `m < m + 1`, the residue `m̄` has
`val(m̄) = m`, so the first branch of `graftChild` applies. -/
theorem graftChild_last {m : ℕ} (κ : ZMod (m + 2) → ℝ) (s : ℝ) :
    graftChild κ s ((m : ℕ) : ZMod (m + 1)) = s := by
  have hval : (((m : ℕ) : ZMod (m + 1))).val = m := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.lt_succ_self m)]
  simp [graftChild, hval]

/-- **The copied part of the child, in `ℕ`-lift form**: for a natural index
`p < m` the child's value at the residue of `p` is the parent's value at the
residue of `p`.  This is `graftChild_of_lt` composed with
`ZMod.val_natCast_of_lt`; it is the form actually used when transporting
window lifts. -/
theorem graftChild_natCast_of_lt {m : ℕ} (κ : ZMod (m + 2) → ℝ) (s : ℝ) {p : ℕ}
    (hp : p < m) :
    graftChild κ s ((p : ℕ) : ZMod (m + 1)) = κ ((p : ℕ) : ZMod (m + 2)) := by
  have hval : (((p : ℕ) : ZMod (m + 1))).val = p := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [graftChild_of_lt κ s (by rw [hval]; exact hp), hval]

/-! ## Two preparatory facts about windows -/

/-- Shifting a natural index down by a multiple of `n` does not change its
residue.  Auxiliary for the normalization of window lifts. -/
private theorem natCast_sub_mul_zmod {n a q : ℕ} (h : n * q ≤ a) :
    (((a - n * q : ℕ)) : ZMod n) = ((a : ℕ) : ZMod n) := by
  have hsplit : ((a : ℕ) : ZMod n) = (((a - n * q : ℕ)) : ZMod n) + ((n * q : ℕ) : ZMod n) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  rw [hsplit, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]

/-- Shifting a natural index down by `n` does not change its residue. -/
private theorem natCast_sub_self_zmod {n a : ℕ} (h : n ≤ a) :
    (((a - n : ℕ)) : ZMod n) = ((a : ℕ) : ZMod n) := by
  have := natCast_sub_mul_zmod (n := n) (a := a) (q := 1) (by omega)
  simpa using this

/-- **Denormalized window**: four strictly increasing `ℕ`-lifts all `< n`
whose values alternate across `c` — in either of the two phases — give a
four-vertex window at level `c`.  In the second phase the window is
`(b₂, b₃, b₄, b₁ + n)`. -/
theorem DFV.of_increasing {n : ℕ} {κ : ZMod n → ℝ} {c : ℝ} {b₁ b₂ b₃ b₄ : ℕ}
    (h12 : b₁ < b₂) (h23 : b₂ < b₃) (h34 : b₃ < b₄) (h4 : b₄ < n)
    (hsign :
      (c < κ ((b₁ : ℕ) : ZMod n) ∧ κ ((b₂ : ℕ) : ZMod n) < c ∧
        c < κ ((b₃ : ℕ) : ZMod n) ∧ κ ((b₄ : ℕ) : ZMod n) < c) ∨
      (κ ((b₁ : ℕ) : ZMod n) < c ∧ c < κ ((b₂ : ℕ) : ZMod n) ∧
        κ ((b₃ : ℕ) : ZMod n) < c ∧ c < κ ((b₄ : ℕ) : ZMod n))) :
    DFV κ c := by
  rcases hsign with ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩
  · exact ⟨b₁, b₂, b₃, b₄, h12, h23, h34, by omega, t1, t2, t3, t4⟩
  · refine ⟨b₂, b₃, b₄, b₁ + n, h23, h34, by omega, by omega, t2, t3, t4, ?_⟩
    have hcast : ((b₁ + n : ℕ) : ZMod n) = ((b₁ : ℕ) : ZMod n) := by
      rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    rw [hcast]
    exact t1

/-- **Normalized window**: every four-vertex window can be presented by four
strictly increasing `ℕ`-lifts all `< n`, with the alternation in one of the
two phases.  One translates the lifts down by a multiple of `n` so the first
lies in `[0, n)`, and then rotates the labels of the (at most three) lifts that
still exceed `n - 1`. -/
theorem DFV.exists_increasing {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {c : ℝ}
    (h : DFV κ c) :
    ∃ b₁ b₂ b₃ b₄ : ℕ, b₁ < b₂ ∧ b₂ < b₃ ∧ b₃ < b₄ ∧ b₄ < n ∧
      ((c < κ ((b₁ : ℕ) : ZMod n) ∧ κ ((b₂ : ℕ) : ZMod n) < c ∧
          c < κ ((b₃ : ℕ) : ZMod n) ∧ κ ((b₄ : ℕ) : ZMod n) < c) ∨
       (κ ((b₁ : ℕ) : ZMod n) < c ∧ c < κ ((b₂ : ℕ) : ZMod n) ∧
          κ ((b₃ : ℕ) : ZMod n) < c ∧ c < κ ((b₄ : ℕ) : ZMod n))) := by
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, s1, s2, s3, s4⟩ := h
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- translate all four lifts down by the multiple `t = n * (i₁ / n)` of `n`
  obtain ⟨t, hcast, hd⟩ :
      ∃ t : ℕ, (∀ a : ℕ, t ≤ a → ((a - t : ℕ) : ZMod n) = ((a : ℕ) : ZMod n)) ∧
        t + i₁ % n = i₁ := by
    refine ⟨n * (i₁ / n), fun a ha => natCast_sub_mul_zmod ha, Nat.div_add_mod i₁ n⟩
  have hmodlt : i₁ % n < n := Nat.mod_lt _ hn
  obtain ⟨a₁, a₂, a₃, a₄, ha12, ha23, ha34, ha41, ha1n, e1, e2, e3, e4⟩ :
      ∃ a₁ a₂ a₃ a₄ : ℕ, a₁ < a₂ ∧ a₂ < a₃ ∧ a₃ < a₄ ∧ a₄ < a₁ + n ∧ a₁ < n ∧
        ((a₁ : ℕ) : ZMod n) = ((i₁ : ℕ) : ZMod n) ∧
        ((a₂ : ℕ) : ZMod n) = ((i₂ : ℕ) : ZMod n) ∧
        ((a₃ : ℕ) : ZMod n) = ((i₃ : ℕ) : ZMod n) ∧
        ((a₄ : ℕ) : ZMod n) = ((i₄ : ℕ) : ZMod n) :=
    ⟨i₁ - t, i₂ - t, i₃ - t, i₄ - t, by omega, by omega, by omega, by omega, by omega,
      hcast _ (by omega), hcast _ (by omega), hcast _ (by omega), hcast _ (by omega)⟩
  rw [← e1] at s1
  rw [← e2] at s2
  rw [← e3] at s3
  rw [← e4] at s4
  -- how many of the translated lifts still exceed `n - 1`?
  rcases Nat.lt_or_ge a₄ n with hA | hA
  · exact ⟨a₁, a₂, a₃, a₄, ha12, ha23, ha34, hA, Or.inl ⟨s1, s2, s3, s4⟩⟩
  rcases Nat.lt_or_ge a₃ n with hB | hB
  · refine ⟨a₄ - n, a₁, a₂, a₃, by omega, ha12, ha23, hB, Or.inr ⟨?_, s1, s2, s3⟩⟩
    rw [natCast_sub_self_zmod hA]
    exact s4
  rcases Nat.lt_or_ge a₂ n with hC | hC
  · refine ⟨a₃ - n, a₄ - n, a₁, a₂, by omega, by omega, ha12, hC, Or.inl ⟨?_, ?_, s1, s2⟩⟩
    · rw [natCast_sub_self_zmod hB]; exact s3
    · rw [natCast_sub_self_zmod hA]; exact s4
  · refine ⟨a₂ - n, a₃ - n, a₄ - n, a₁, by omega, by omega, by omega, ha1n,
      Or.inr ⟨?_, ?_, ?_, s1⟩⟩
    · rw [natCast_sub_self_zmod hC]; exact s2
    · rw [natCast_sub_self_zmod hB]; exact s3
    · rw [natCast_sub_self_zmod hA]; exact s4

/-- **Windows are rotation invariant**: if `DFV(κ, c)` holds then
`DFV(j ↦ κ_{j+r}, c)` holds for every residue `r`. -/
theorem DFV.comp_add {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {c : ℝ} (h : DFV κ c)
    (r : ZMod n) : DFV (fun i => κ (i + r)) c := by
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, s1, s2, s3, s4⟩ := h
  have key : ∀ a : ℕ, ((a + (-r).val : ℕ) : ZMod n) + r = ((a : ℕ) : ZMod n) := by
    intro a
    rw [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id]
    ring
  refine ⟨i₁ + (-r).val, i₂ + (-r).val, i₃ + (-r).val, i₄ + (-r).val,
    by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩ <;>
    simp only [key] <;> assumption

/-- **A window can be moved to a generic level**: if every value is positive
and `DFV(κ, c)` holds, then there is a level `c' > 0` with `DFV(κ, c')` and
`κ_i ≠ c'` for every `i`. -/
theorem DFV.exists_generic_level {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {c : ℝ}
    (hpos : ∀ i, 0 < κ i) (h : DFV κ c) :
    ∃ c' : ℝ, 0 < c' ∧ DFV κ c' ∧ ∀ i, κ i ≠ c' := by
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, s1, s2, s3, s4⟩ := h
  have hMN : max (κ ((i₂ : ℕ) : ZMod n)) (κ ((i₄ : ℕ) : ZMod n))
      < min (κ ((i₁ : ℕ) : ZMod n)) (κ ((i₃ : ℕ) : ZMod n)) := by
    apply max_lt <;> apply lt_min <;> linarith
  have hinf : (Set.Ioo (max (κ ((i₂ : ℕ) : ZMod n)) (κ ((i₄ : ℕ) : ZMod n)))
      (min (κ ((i₁ : ℕ) : ZMod n)) (κ ((i₃ : ℕ) : ZMod n)))).Infinite :=
    Set.Ioo_infinite hMN
  obtain ⟨c', hc'⟩ := (hinf.sdiff (Set.finite_range κ)).nonempty
  obtain ⟨⟨hlo, hhi⟩, hnot⟩ := hc'
  have h2 : κ ((i₂ : ℕ) : ZMod n) ≤ max (κ ((i₂ : ℕ) : ZMod n)) (κ ((i₄ : ℕ) : ZMod n)) :=
    le_max_left _ _
  have h4 : κ ((i₄ : ℕ) : ZMod n) ≤ max (κ ((i₂ : ℕ) : ZMod n)) (κ ((i₄ : ℕ) : ZMod n)) :=
    le_max_right _ _
  have h1 : min (κ ((i₁ : ℕ) : ZMod n)) (κ ((i₃ : ℕ) : ZMod n)) ≤ κ ((i₁ : ℕ) : ZMod n) :=
    min_le_left _ _
  have h3 : min (κ ((i₁ : ℕ) : ZMod n)) (κ ((i₃ : ℕ) : ZMod n)) ≤ κ ((i₃ : ℕ) : ZMod n) :=
    min_le_right _ _
  refine ⟨c', ?_, ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, by linarith, by linarith,
    by linarith, by linarith⟩, ?_⟩
  · have := hpos ((i₂ : ℕ) : ZMod n)
    linarith
  · intro i hi
    exact hnot ⟨i, hi⟩

/-! ## The contraction lemma -/

/-- **The block case with the rotation already performed.**  If the two last
positions `m̄`, `m̄+1` of `lam : ZMod (m + 2) → ℝ` lie on the same side of `c`,
and the cap value `s` lies on that same side, then contracting them preserves
the window.  This is the mathematical core of
`exists_graft_contraction_of_eq_succ`; the named lemma is the wrapper that
performs the rotation. -/
theorem exists_graft_contraction_of_pair {m : ℕ} (hm : 4 ≤ m)
    {lam : ZMod (m + 2) → ℝ} {c : ℝ} (hdfv : DFV lam c)
    (hpair : (c < lam ((m : ℕ) : ZMod (m + 2))) ↔ (c < lam ((m + 1 : ℕ) : ZMod (m + 2))))
    {s : ℝ} (hs1 : (c < lam ((m : ℕ) : ZMod (m + 2))) → c < s)
    (hs2 : (¬ c < lam ((m : ℕ) : ZMod (m + 2))) → s < c) :
    DFV (graftChild lam s) c := by
  obtain ⟨b₁, b₂, b₃, b₄, h12, h23, h34, h4, hpat⟩ := hdfv.exists_increasing
  -- the two entries of the contracted pair lie on the same side of `c`
  have hside : ∀ p : ℕ, (p = m ∨ p = m + 1) →
      ((c < lam ((p : ℕ) : ZMod (m + 2))) ↔ (c < lam ((m : ℕ) : ZMod (m + 2)))) := by
    rintro p (rfl | rfl)
    · exact Iff.rfl
    · exact hpair.symm
  -- at most one window index lies in the contracted pair
  have hb3 : b₃ < m := by
    by_contra hcon
    have i3 := hside b₃ (Or.inl (by omega))
    have i4 := hside b₄ (Or.inr (by omega))
    rcases hpat with ⟨_, _, p3, p4⟩ | ⟨_, _, p3, p4⟩
    · exact absurd (i4.mpr (i3.mp p3)) (not_lt.mpr p4.le)
    · exact absurd (i3.mpr (i4.mp p4)) (not_lt.mpr p3.le)
  have gc : ∀ p : ℕ, p < m →
      graftChild lam s ((p : ℕ) : ZMod (m + 1)) = lam ((p : ℕ) : ZMod (m + 2)) :=
    fun p hp => graftChild_natCast_of_lt lam s hp
  by_cases hb4lt : b₄ < m
  · -- no window index is in the contracted pair: the child copies all four
    refine DFV.of_increasing h12 h23 h34 (by omega) ?_
    rw [gc b₁ (by omega), gc b₂ (by omega), gc b₃ (by omega), gc b₄ hb4lt]
    exact hpat
  · -- exactly one window index is in the contracted pair; it becomes the cap
    have hb4' : b₄ = m ∨ b₄ = m + 1 := by omega
    have i4 := hside b₄ hb4'
    refine DFV.of_increasing (b₁ := b₁) (b₂ := b₂) (b₃ := b₃) (b₄ := m)
      h12 h23 (by omega) (by omega) ?_
    rw [gc b₁ (by omega), gc b₂ (by omega), gc b₃ (by omega), graftChild_last]
    rcases hpat with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩
    · exact Or.inl ⟨p1, p2, p3, hs2 (fun hh => absurd (i4.mpr hh) (not_lt.mpr p4.le))⟩
    · exact Or.inr ⟨p1, p2, p3, hs1 (i4.mp p4)⟩

/-- **Repeated adjacent sign: contract inside a block.**  Let `4 ≤ m`, let
`κ : ZMod (m + 2) → ℝ` be positive, let `c` be a level with `DFV(κ, c)`, and
suppose some `j` satisfies `(c < κ j) ↔ (c < κ (j + 1))`, i.e. the two entries
of the adjacent pair `j, j+1` lie on the same side of `c`.  Rotating by
`j - m̄` moves that pair to the last two positions; contracting it into the cap
preserves the window: choosing `s` on the same side of `c` as the pair gives
`DFV(ch(λ, s), c)`. -/
theorem exists_graft_contraction_of_eq_succ {m : ℕ} (hm : 4 ≤ m)
    {κ : ZMod (m + 2) → ℝ} {c : ℝ} (_hgen : ∀ i, κ i ≠ c) (hdfv : DFV κ c)
    {j : ZMod (m + 2)} (hj : (c < κ j) ↔ (c < κ (j + 1))) :
    ∀ s : ℝ, ((c < κ j) → c < s) → ((¬ c < κ j) → s < c) →
      DFV (graftChild (fun i => κ (i + (j - ((m : ℕ) : ZMod (m + 2))))) s) c := by
  intro s hs1 hs2
  have hev1 : κ (((m : ℕ) : ZMod (m + 2)) + (j - ((m : ℕ) : ZMod (m + 2)))) = κ j := by
    congr 1
    ring
  have hev2 : κ (((m + 1 : ℕ) : ZMod (m + 2)) + (j - ((m : ℕ) : ZMod (m + 2))))
      = κ (j + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  refine exists_graft_contraction_of_pair hm (DFV.comp_add hdfv _) ?_ ?_ ?_
  · rw [hev1, hev2]; exact hj
  · rw [hev1]; exact hs1
  · rw [hev1]; exact hs2

/-- **No repeated adjacent sign: the level-zigzag case.**  Let `4 ≤ m`, let
`κ : ZMod (m + 2) → ℝ` be positive, let `c` be a level with `DFV(κ, c)`, and
suppose consecutive signs always differ.  Then contracting the last pair into
the cap gives `DFV(ch(κ, s), c)` for every `s < c`: since consecutive signs
alternate, the four child positions carry an alternating window, and the cap
entry has the appropriate side of `c`. -/
theorem exists_graft_contraction_of_ne_succ {m : ℕ} (hm : 4 ≤ m)
    -- `hdfv` is unconsumed: the zigzag case builds its child window de novo at
    -- positions `0,1,2,3` (or `1,2,3,4`) and never reads the input window.
    {κ : ZMod (m + 2) → ℝ} {c : ℝ} (hgen : ∀ i, κ i ≠ c) (_hdfv : DFV κ c)
    (hne : ∀ j : ZMod (m + 2), ¬ ((c < κ j) ↔ (c < κ (j + 1)))) :
    ∀ s : ℝ, s < c → DFV (graftChild κ s) c := by
  intro s hs
  -- genericity turns "not above the level" into "strictly below"
  have hlt : ∀ i : ZMod (m + 2), ¬ (c < κ i) → κ i < c := fun i h =>
    lt_of_le_of_ne (not_lt.mp h) (hgen i)
  -- the alternation, transported to `ℕ`-lifts
  have alt : ∀ p : ℕ, (c < κ ((p : ℕ) : ZMod (m + 2))) ↔
      ¬ (c < κ ((p + 1 : ℕ) : ZMod (m + 2))) := by
    intro p
    have h := hne ((p : ℕ) : ZMod (m + 2))
    rw [Nat.cast_add, Nat.cast_one]
    tauto
  have gc : ∀ p : ℕ, p < m →
      graftChild κ s ((p : ℕ) : ZMod (m + 1)) = κ ((p : ℕ) : ZMod (m + 2)) :=
    fun p hp => graftChild_natCast_of_lt κ s hp
  have a0 := alt 0
  have a1 := alt 1
  have a2 := alt 2
  have a3 := alt 3
  norm_num at a0 a1 a2 a3
  by_cases h0 : c < κ ((0 : ℕ) : ZMod (m + 2))
  · -- the child window is at positions `0, 1, 2, 3`
    have h1 : ¬ (c < κ ((1 : ℕ) : ZMod (m + 2))) := by
      have := a0.mp (by simpa using h0)
      simpa using this
    have h2 : c < κ ((2 : ℕ) : ZMod (m + 2)) := by
      by_contra hh
      exact h1 (by simpa using a1.mpr (by simpa using hh))
    have h3 : ¬ (c < κ ((3 : ℕ) : ZMod (m + 2))) := by
      have := a2.mp (by simpa using h2)
      simpa using this
    refine DFV.of_increasing (b₁ := 0) (b₂ := 1) (b₃ := 2) (b₄ := 3)
      (by omega) (by omega) (by omega) (by omega) ?_
    rw [gc 0 (by omega), gc 1 (by omega), gc 2 (by omega), gc 3 (by omega)]
    exact Or.inl ⟨h0, hlt _ h1, h2, hlt _ h3⟩
  · -- the child window is at positions `1, 2, 3, 4`
    have h1 : c < κ ((1 : ℕ) : ZMod (m + 2)) := by
      by_contra hh
      exact h0 (by simpa using a0.mpr (by simpa using hh))
    have h2 : ¬ (c < κ ((2 : ℕ) : ZMod (m + 2))) := by
      have := a1.mp (by simpa using h1)
      simpa using this
    have h3 : c < κ ((3 : ℕ) : ZMod (m + 2)) := by
      by_contra hh
      exact h2 (by simpa using a2.mpr (by simpa using hh))
    have h4 : ¬ (c < κ ((4 : ℕ) : ZMod (m + 2))) := by
      have := a3.mp (by simpa using h3)
      simpa using this
    refine DFV.of_increasing (b₁ := 1) (b₂ := 2) (b₃ := 3) (b₄ := 4)
      (by omega) (by omega) (by omega) (by omega) ?_
    rw [gc 1 (by omega), gc 2 (by omega), gc 3 (by omega)]
    -- position `4` of the child is either a copy (when `5 ≤ m`) or the cap
    by_cases hm4 : 4 < m
    · rw [gc 4 hm4]
      exact Or.inl ⟨h1, hlt _ h2, h3, hlt _ h4⟩
    · have hm4' : m = 4 := by omega
      have hcap : ((4 : ℕ) : ZMod (m + 1)) = ((m : ℕ) : ZMod (m + 1)) := by rw [hm4']
      rw [hcap, graftChild_last]
      exact Or.inl ⟨h1, hlt _ h2, h3, hs⟩

/-- **(G-comb), interval form**: let `4 ≤ m` and let `κ : ZMod (m + 2) → ℝ` be
everywhere positive with `DFV(κ, c)` for some `c > 0`.  Then there is a rotation
`r` and reals `0 ≤ a < b` such that for every `s ∈ (a, b)` the child
`ch(i ↦ κ_{i+r}, s)` satisfies `DiscreteFourVertexPos`. -/
theorem exists_graft_contraction_interval {m : ℕ} (hm : 4 ≤ m)
    {κ : ZMod (m + 2) → ℝ} (hpos : ∀ i, 0 < κ i) {c : ℝ} (_hc : 0 < c)
    (hdfv : DFV κ c) :
    ∃ (r : ZMod (m + 2)) (a b : ℝ), 0 ≤ a ∧ a < b ∧
      ∀ s ∈ Set.Ioo a b,
        DiscreteFourVertexPos (graftChild (fun i => κ (i + r)) s) := by
  obtain ⟨c', hc'pos, hdfv', hgen⟩ := DFV.exists_generic_level hpos hdfv
  -- the child of a positive parent is positive as soon as the cap is
  have hchildpos : ∀ μ : ZMod (m + 2) → ℝ, (∀ i, 0 < μ i) → ∀ s : ℝ, 0 < s →
      ∀ k, 0 < graftChild μ s k := by
    intro μ hμ s hs k
    by_cases h : k.val = m
    · simpa [graftChild, h] using hs
    · simpa [graftChild, h] using hμ ((k.val : ℕ) : ZMod (m + 2))
  by_cases hex : ∃ j : ZMod (m + 2), ((c' < κ j) ↔ (c' < κ (j + 1)))
  · obtain ⟨j, hj⟩ := hex
    have hposrot : ∀ i, 0 < κ (i + (j - ((m : ℕ) : ZMod (m + 2)))) := fun i => hpos _
    refine ⟨j - ((m : ℕ) : ZMod (m + 2)), ?_⟩
    by_cases hjs : c' < κ j
    · refine ⟨c', c' + 1, hc'pos.le, by linarith, fun s hsm => ?_⟩
      exact ⟨hchildpos _ hposrot s (by linarith [hsm.1]), Or.inr ⟨c', hc'pos,
        exists_graft_contraction_of_eq_succ hm hgen hdfv' hj s (fun _ => hsm.1)
          (fun h => absurd hjs h)⟩⟩
    · refine ⟨0, c', le_refl 0, hc'pos, fun s hsm => ?_⟩
      exact ⟨hchildpos _ hposrot s hsm.1, Or.inr ⟨c', hc'pos,
        exists_graft_contraction_of_eq_succ hm hgen hdfv' hj s (fun h => absurd h hjs)
          (fun _ => hsm.2)⟩⟩
  · have hne : ∀ j : ZMod (m + 2), ¬ ((c' < κ j) ↔ (c' < κ (j + 1))) := fun j hj =>
      hex ⟨j, hj⟩
    refine ⟨0, 0, c', le_refl 0, hc'pos, fun s hsm => ?_⟩
    simp only [add_zero]
    exact ⟨hchildpos κ hpos s hsm.1, Or.inr ⟨c', hc'pos,
      exists_graft_contraction_of_ne_succ hm hgen hdfv' hne s hsm.2⟩⟩

/-- **(G-comb), point form**: under the hypotheses of the interval form there
are a rotation `r` and a cap value `s > 0` with
`DiscreteFourVertexPos (ch(i ↦ κ_{i+r}, s))`.  Take any point of the nonempty
open interval supplied by the interval form. -/
theorem exists_graft_contraction {m : ℕ} (hm : 4 ≤ m)
    {κ : ZMod (m + 2) → ℝ} (hpos : ∀ i, 0 < κ i) {c : ℝ} (hc : 0 < c)
    (hdfv : DFV κ c) :
    ∃ (r : ZMod (m + 2)) (s : ℝ), 0 < s ∧
      DiscreteFourVertexPos (graftChild (fun i => κ (i + r)) s) := by
  obtain ⟨r, a, b, ha, hab, hmem⟩ := exists_graft_contraction_interval hm hpos hc hdfv
  exact ⟨r, (a + b) / 2, by linarith, hmem _ ⟨by linarith, by linarith⟩⟩

/-! ## (G-comb)′: the range-mode menu -/

/-- The child of an everywhere-positive parent with a positive cap value is
everywhere positive.  This is the argument that appears inline inside
`exists_graft_contraction_interval`, extracted for reuse by the three
(G-comb)′ statements below. -/
private theorem graftChild_pos {m : ℕ} {μ : ZMod (m + 2) → ℝ} (hμ : ∀ i, 0 < μ i)
    {s : ℝ} (hs : 0 < s) (k : ZMod (m + 1)) : 0 < graftChild μ s k := by
  by_cases h : k.val = m
  · simpa [graftChild, h] using hs
  · simpa [graftChild, h] using hμ ((k.val : ℕ) : ZMod (m + 2))

/-- **In-block contraction: the whole pair range is admissible.**  Let `4 ≤ m`,
let `κ : ZMod (m + 2) → ℝ` be everywhere positive and let `c'` be a generic
level (no value of `κ` equals it) carrying a window.  Suppose the adjacent pair
`j, j + 1` is *in-block*, i.e. both entries lie strictly on the same side of
`c'`.  Then, with `r = j - m̄` the rotation placing that pair at the two
contracted positions, **every** `s` in the closed interval spanned by the two
entries gives a `DiscreteFourVertexPos` child.

Because the level is generic, both entries lie strictly on one side of `c'`,
hence so does every point of the closed interval they span; the two branches of
`exists_graft_contraction_of_eq_succ` apply verbatim. -/
theorem exists_graft_contraction_inBlock {m : ℕ} (hm : 4 ≤ m)
    {κ : ZMod (m + 2) → ℝ} (hpos : ∀ i, 0 < κ i) {c' : ℝ} (hc' : 0 < c')
    (hgen : ∀ i, κ i ≠ c') (hdfv : DFV κ c')
    {j : ZMod (m + 2)} (hj : (c' < κ j) ↔ (c' < κ (j + 1))) :
    ∀ s ∈ Set.uIcc (κ j) (κ (j + 1)),
      DiscreteFourVertexPos
        (graftChild (fun i => κ (i + (j - ((m : ℕ) : ZMod (m + 2))))) s) := by
  intro s hs
  have hlo : min (κ j) (κ (j + 1)) ≤ s := hs.1
  have hhi : s ≤ max (κ j) (κ (j + 1)) := hs.2
  have hposrot : ∀ i, 0 < κ (i + (j - ((m : ℕ) : ZMod (m + 2)))) := fun i => hpos _
  by_cases hjs : c' < κ j
  · -- the pair sits above the level: so does every point of its range
    have hj1 : c' < κ (j + 1) := hj.mp hjs
    have hsc : c' < s := lt_of_lt_of_le (lt_min hjs hj1) hlo
    exact ⟨fun k => graftChild_pos hposrot (hc'.trans hsc) k,
      Or.inr ⟨c', hc', exists_graft_contraction_of_eq_succ hm hgen hdfv hj s
        (fun _ => hsc) (fun h => absurd hjs h)⟩⟩
  · -- the pair sits below the level; positivity of `κ` supplies the lower bound
    have hj0 : κ j < c' := lt_of_le_of_ne (not_lt.mp hjs) (hgen j)
    have hj1 : κ (j + 1) < c' :=
      lt_of_le_of_ne (not_lt.mp fun h => hjs (hj.mpr h)) (hgen (j + 1))
    have hsc : s < c' := lt_of_le_of_lt hhi (max_lt hj0 hj1)
    have hs0 : 0 < s := lt_of_lt_of_le (lt_min (hpos j) (hpos (j + 1))) hlo
    exact ⟨fun k => graftChild_pos hposrot hs0 k,
      Or.inr ⟨c', hc', exists_graft_contraction_of_eq_succ hm hgen hdfv hj s
        (fun h => absurd h hjs) (fun _ => hsc)⟩⟩

/-- **Boundary contraction: the sub-range below the level is admissible.**  In
the complementary case — no adjacent pair is in-block at the generic level `c'`,
i.e. `κ` alternates across `c'` at every adjacent pair — *any* `j` may be taken
as the contraction site: every `s` with `0 < s < c'` gives a
`DiscreteFourVertexPos` child of the rotated parent.  Moreover the pair
straddles `c'`, so `(min (κ j) (κ (j+1)), c')` is a nonempty part of the pair's
own range on which the conclusion holds. -/
theorem exists_graft_contraction_boundary {m : ℕ} (hm : 4 ≤ m)
    {κ : ZMod (m + 2) → ℝ} (hpos : ∀ i, 0 < κ i) {c' : ℝ} (hc' : 0 < c')
    (hgen : ∀ i, κ i ≠ c') (hdfv : DFV κ c')
    (hne : ∀ i : ZMod (m + 2), ¬ ((c' < κ i) ↔ (c' < κ (i + 1))))
    (j : ZMod (m + 2)) :
    min (κ j) (κ (j + 1)) < c' ∧ c' < max (κ j) (κ (j + 1)) ∧
      ∀ s ∈ Set.Ioo (0 : ℝ) c',
        DiscreteFourVertexPos
          (graftChild (fun i => κ (i + (j - ((m : ℕ) : ZMod (m + 2))))) s) := by
  -- the pair straddles the level: exactly one of its entries is above `c'`
  have hstr : (κ j < c' ∧ c' < κ (j + 1)) ∨ (κ (j + 1) < c' ∧ c' < κ j) := by
    rcases lt_or_gt_of_ne (hgen j) with h1 | h1 <;>
      rcases lt_or_gt_of_ne (hgen (j + 1)) with h2 | h2
    · exact absurd ⟨fun h => absurd h (by linarith), fun h => absurd h (by linarith)⟩ (hne j)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact absurd ⟨fun _ => h2, fun _ => h1⟩ (hne j)
  refine ⟨?_, ?_, ?_⟩
  · rcases hstr with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact lt_of_le_of_lt (min_le_left _ _) h1
    · exact lt_of_le_of_lt (min_le_right _ _) h1
  · rcases hstr with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact lt_of_lt_of_le h2 (le_max_right _ _)
    · exact lt_of_lt_of_le h2 (le_max_left _ _)
  -- the rotated parent is again positive, generic, windowed and everywhere
  -- alternating, so the zigzag case applies to it verbatim
  · intro s hsm
    set r : ZMod (m + 2) := j - ((m : ℕ) : ZMod (m + 2))
    have hposrot : ∀ i, 0 < κ (i + r) := fun i => hpos _
    have hgenrot : ∀ i, κ (i + r) ≠ c' := fun i => hgen _
    have hdfvrot : DFV (fun i => κ (i + r)) c' := DFV.comp_add hdfv r
    have hnerot : ∀ i : ZMod (m + 2),
        ¬ ((c' < (fun i => κ (i + r)) i) ↔ (c' < (fun i => κ (i + r)) (i + 1))) := by
      intro i
      have h := hne (i + r)
      have hshift : (i + 1) + r = (i + r) + 1 := by ring
      simpa [hshift] using h
    exact ⟨fun k => graftChild_pos hposrot hsm.1 k,
      Or.inr ⟨c', hc',
        exists_graft_contraction_of_ne_succ hm hgenrot hdfvrot hnerot s hsm.2⟩⟩

/-- **(G-comb)′, packaged.**  Let `4 ≤ m` and let `κ : ZMod (m + 2) → ℝ` be
everywhere positive with `DFV(κ, c)` at some `c > 0`.  Then there are a rotation
`r` and reals `0 ≤ a ≤ b` such that the closed interval `[a, b]` is contained in
the closed interval spanned by the two contracted entries `κ_{m̄+r}`,
`κ_{m̄+1+r}`, every `s ∈ [a, b]` is positive and gives a
`DiscreteFourVertexPos` child, and `a < b` whenever the two contracted entries
differ.

The proof splits on whether an in-block adjacent pair exists at the generic
level.  In the in-block case `[a, b]` is the whole closed pair range; in the
complementary case it is a closed sub-interval of
`(min (pair), c')`, which is nonempty because the pair straddles `c'`. -/
theorem exists_graft_contraction_range {m : ℕ} (hm : 4 ≤ m)
    {κ : ZMod (m + 2) → ℝ} (hpos : ∀ i, 0 < κ i) {c : ℝ} (_hc : 0 < c)
    (hdfv : DFV κ c) :
    ∃ (r : ZMod (m + 2)) (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧
      Set.Icc a b ⊆ Set.uIcc (κ (((m : ℕ) : ZMod (m + 2)) + r))
        (κ (((m + 1 : ℕ) : ZMod (m + 2)) + r)) ∧
      (κ (((m : ℕ) : ZMod (m + 2)) + r) ≠ κ (((m + 1 : ℕ) : ZMod (m + 2)) + r) → a < b) ∧
      ∀ s ∈ Set.Icc a b, 0 < s ∧
        DiscreteFourVertexPos (graftChild (fun i => κ (i + r)) s) := by
  obtain ⟨c', hc'pos, hdfv', hgen⟩ := DFV.exists_generic_level hpos hdfv
  by_cases hex : ∃ j : ZMod (m + 2), ((c' < κ j) ↔ (c' < κ (j + 1)))
  · -- in-block: take the whole closed pair range
    obtain ⟨j, hj⟩ := hex
    have hev1 : κ (((m : ℕ) : ZMod (m + 2)) + (j - ((m : ℕ) : ZMod (m + 2)))) = κ j := by
      congr 1
      ring
    have hev2 : κ (((m + 1 : ℕ) : ZMod (m + 2)) + (j - ((m : ℕ) : ZMod (m + 2))))
        = κ (j + 1) := by
      rw [Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    refine ⟨j - ((m : ℕ) : ZMod (m + 2)), min (κ j) (κ (j + 1)), max (κ j) (κ (j + 1)),
      ?_, min_le_max, ?_, ?_, ?_⟩
    · exact le_of_lt (lt_min (hpos j) (hpos (j + 1)))
    · rw [hev1, hev2]
      exact subset_rfl
    · rw [hev1, hev2]
      exact fun hne => min_lt_max.mpr hne
    · intro s hsm
      refine ⟨lt_of_lt_of_le (lt_min (hpos j) (hpos (j + 1))) hsm.1, ?_⟩
      exact exists_graft_contraction_inBlock hm hpos hc'pos hgen hdfv' hj s
        ⟨hsm.1, hsm.2⟩
  · -- boundary: take a closed sub-interval of `(min (pair), c')`
    have hne : ∀ i : ZMod (m + 2), ¬ ((c' < κ i) ↔ (c' < κ (i + 1))) := fun i hi =>
      hex ⟨i, hi⟩
    have hmm : (((m + 1 : ℕ) : ZMod (m + 2))) = ((m : ℕ) : ZMod (m + 2)) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    obtain ⟨hlt, hgt, hmain⟩ :=
      exists_graft_contraction_boundary hm hpos hc'pos hgen hdfv' hne
        ((m : ℕ) : ZMod (m + 2))
    have hrz : (((m : ℕ) : ZMod (m + 2)) - ((m : ℕ) : ZMod (m + 2))) = 0 := sub_self _
    rw [hrz] at hmain
    set d : ℝ := min (κ ((m : ℕ) : ZMod (m + 2))) (κ (((m : ℕ) : ZMod (m + 2)) + 1)) with hd
    have hdpos : 0 < d := lt_min (hpos _) (hpos _)
    refine ⟨0, d + (c' - d) / 3, d + 2 * (c' - d) / 3, by linarith, by linarith, ?_, ?_, ?_⟩
    · simp only [add_zero, hmm]
      intro s hsm
      refine Set.mem_uIcc.mpr ?_
      rcases le_total (κ ((m : ℕ) : ZMod (m + 2))) (κ (((m : ℕ) : ZMod (m + 2)) + 1)) with h | h
      · left
        constructor
        · have : d = κ ((m : ℕ) : ZMod (m + 2)) := by rw [hd, min_eq_left h]
          linarith [hsm.1]
        · have : c' < κ (((m : ℕ) : ZMod (m + 2)) + 1) := by
            rw [max_eq_right h] at hgt; exact hgt
          linarith [hsm.2]
      · right
        constructor
        · have : d = κ (((m : ℕ) : ZMod (m + 2)) + 1) := by rw [hd, min_eq_right h]
          linarith [hsm.1]
        · have : c' < κ ((m : ℕ) : ZMod (m + 2)) := by
            rw [max_eq_left h] at hgt; exact hgt
          linarith [hsm.2]
    · exact fun _ => by linarith
    · intro s hsm
      refine ⟨by linarith [hsm.1], ?_⟩
      simpa using hmain s ⟨by linarith [hsm.1], by linarith [hsm.2]⟩

/-! ## The in-block dichotomy -/

/-- **The in-block stratum**: `κ` *admits an in-block level* when some generic
positive level carries a window and has an adjacent pair on one side of it.
This is the hypothesis under which the contraction attains **both** entries of
the contracted pair, which is what the downstream endpoint bracket consumes. -/
def InBlockLevel {n : ℕ} (κ : ZMod n → ℝ) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ (∀ i, κ i ≠ c') ∧ DFV κ c' ∧
    ∃ j : ZMod n, ((c' < κ j) ↔ (c' < κ (j + 1)))

/-- **The alternating tie-degenerate stratum**: there is a generic positive
level `c'` carrying a window at which `κ` alternates at *every* adjacent pair,
and moreover at most one element of `U(c') = {i | c' < κ i}` is non-minimal in
`U(c')` and at most one element of `D(c') = {i | κ i < c'}` is non-maximal in
`D(c')`.  For `n ≥ 6` the last two clauses each force an exact tie between two
distinct entries of `κ` (`exists_ne_eq_of_alternatingTieDegenerate`), so this
stratum is contained in the finite union of the diagonal hyperplanes
`{κ i₁ = κ i₂}`, `i₁ ≠ i₂`.  That containment is what is proved; no statement
about the *interior* of the stratum is available here, and none may be cited. -/
def AlternatingTieDegenerate {n : ℕ} (κ : ZMod n → ℝ) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ (∀ i, κ i ≠ c') ∧ DFV κ c' ∧
    (∀ i : ZMod n, ¬ ((c' < κ i) ↔ (c' < κ (i + 1)))) ∧
    (∀ i₁ i₂ : ZMod n, c' < κ i₁ → c' < κ i₂ →
      (∃ i, c' < κ i ∧ κ i < κ i₁) → (∃ i, c' < κ i ∧ κ i < κ i₂) → i₁ = i₂) ∧
    (∀ j₁ j₂ : ZMod n, κ j₁ < c' → κ j₂ < c' →
      (∃ j, κ j < c' ∧ κ j₁ < κ j) → (∃ j, κ j < c' ∧ κ j₂ < κ j) → j₁ = j₂)

/-- **The parity law of an alternating profile.**  If the sign of `κ - c` flips
at every adjacent pair of `ZMod n`, then the side of `c` on which `κ_{k̄}` lies
is determined by the parity of `k` alone:
`(c < κ_{k̄}) ↔ (Even k ↔ c < κ_{0̄})`.  Equivalently, the up-set
`U(c) = {i | c < κ i}` is exactly one of the two parity classes of residues.
No positivity, genericity or window hypothesis is used — alternation alone. -/
theorem alternating_parity {n : ℕ} {κ : ZMod n → ℝ} {c : ℝ}
    (halt : ∀ i : ZMod n, ¬ ((c < κ i) ↔ (c < κ (i + 1)))) (k : ℕ) :
    ((c < κ ((k : ℕ) : ZMod n)) ↔ (Even k ↔ (c < κ ((0 : ℕ) : ZMod n)))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := halt ((k : ℕ) : ZMod n)
    have hcast : (((k + 1 : ℕ)) : ZMod n) = ((k : ℕ) : ZMod n) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hcast, Nat.even_add_one]
    tauto

/-- **An alternating profile has no adjacent equality.**  If `κ j = κ (j + 1)`
then the biconditional `(c < κ j) ↔ (c < κ (j + 1))` holds by reflexivity,
which is exactly what alternation at `j` forbids. -/
theorem ne_adjacent_of_alternating {n : ℕ} {κ : ZMod n → ℝ} {c : ℝ}
    (halt : ∀ i : ZMod n, ¬ ((c < κ i) ↔ (c < κ (i + 1)))) (j : ZMod n) :
    κ j ≠ κ (j + 1) := fun hj => halt j (by rw [hj])

/-- **The residue carries an exact tie.**  For `6 ≤ n`, an alternating
tie-degenerate profile has two *distinct* indices at which it takes the same
value.  Hence the alternating tie-degenerate stratum is contained in the finite
union of the diagonal hyperplanes `{κ i₁ = κ i₂}`, `i₁ ≠ i₂`.  This is the
precise formal content behind the informal slogan that the residue "has empty
interior"; that slogan is *not* a theorem of this development.

The proof is the parity law plus clause (2) of `AlternatingTieDegenerate`:
alternation puts `0̄, 2̄, 4̄` (or `1̄, 3̄, 5̄`) all on the up-side, and they are
pairwise distinct because `0 ≤ k < k' ≤ 5 < 6 ≤ n`; clause (2) makes at most
one of the three non-minimal in `U(c')`, so two are minimal, and two mutually
false strict inequalities on `ℝ` force equality.  Clause (3) — the mirror
statement on the down-side `D(c')` — is genuinely unused: it yields the same
conclusion by the same argument, and either one suffices. -/
theorem exists_ne_eq_of_alternatingTieDegenerate {n : ℕ} (hn : 6 ≤ n)
    {κ : ZMod n → ℝ} (h : AlternatingTieDegenerate κ) :
    ∃ i₁ i₂ : ZMod n, i₁ ≠ i₂ ∧ κ i₁ = κ i₂ := by
  obtain ⟨c', _hc'pos, _hgen, _hdfv, halt, hup, -⟩ := h
  haveI : NeZero n := ⟨by omega⟩
  -- distinct small residues: `k < k' < n` lift to distinct elements of `ZMod n`
  have hne : ∀ k k' : ℕ, k < k' → k' < n → ((k : ℕ) : ZMod n) ≠ ((k' : ℕ) : ZMod n) := by
    intro k k' hkk' hk'n hEq
    have h1 : ((k : ZMod n)).val = k := ZMod.val_cast_of_lt (by omega)
    have h2 : ((k' : ZMod n)).val = k' := ZMod.val_cast_of_lt hk'n
    rw [hEq, h2] at h1
    omega
  -- two distinct elements of `U(c')`, each minimal in `U(c')`, are tied
  have tie : ∀ a b : ZMod n, a ≠ b → c' < κ a → c' < κ b →
      ¬ (∃ i, c' < κ i ∧ κ i < κ a) → ¬ (∃ i, c' < κ i ∧ κ i < κ b) →
      ∃ i₁ i₂ : ZMod n, i₁ ≠ i₂ ∧ κ i₁ = κ i₂ := by
    intro a b hab ha hb hma hmb
    refine ⟨a, b, hab, ?_⟩
    have h1 : κ a ≤ κ b := not_lt.mp fun hlt => hma ⟨b, hb, hlt⟩
    have h2 : κ b ≤ κ a := not_lt.mp fun hlt => hmb ⟨a, ha, hlt⟩
    linarith
  -- three pairwise distinct residues on the up-side, by the parity law
  obtain ⟨x, y, z, hxy, hxz, hyz, hxU, hyU, hzU⟩ :
      ∃ x y z : ZMod n, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ c' < κ x ∧ c' < κ y ∧ c' < κ z := by
    by_cases h0 : c' < κ ((0 : ℕ) : ZMod n)
    · exact ⟨((0 : ℕ) : ZMod n), ((2 : ℕ) : ZMod n), ((4 : ℕ) : ZMod n),
        hne 0 2 (by omega) (by omega), hne 0 4 (by omega) (by omega),
        hne 2 4 (by omega) (by omega), h0,
        (alternating_parity halt 2).mpr ⟨fun _ => h0, fun _ => by decide⟩,
        (alternating_parity halt 4).mpr ⟨fun _ => h0, fun _ => by decide⟩⟩
    · exact ⟨((1 : ℕ) : ZMod n), ((3 : ℕ) : ZMod n), ((5 : ℕ) : ZMod n),
        hne 1 3 (by omega) (by omega), hne 1 5 (by omega) (by omega),
        hne 3 5 (by omega) (by omega),
        (alternating_parity halt 1).mpr ⟨fun he => absurd he (by decide),
          fun he => absurd he h0⟩,
        (alternating_parity halt 3).mpr ⟨fun he => absurd he (by decide),
          fun he => absurd he h0⟩,
        (alternating_parity halt 5).mpr ⟨fun he => absurd he (by decide),
          fun he => absurd he h0⟩⟩
  -- at most one of the three is non-minimal in `U(c')`, so two of them are
  by_cases hx : ∃ i, c' < κ i ∧ κ i < κ x
  · have hy : ¬ ∃ i, c' < κ i ∧ κ i < κ y := fun hy => hxy (hup x y hxU hyU hx hy)
    have hz : ¬ ∃ i, c' < κ i ∧ κ i < κ z := fun hz => hxz (hup x z hxU hzU hx hz)
    exact tie y z hyz hyU hzU hy hz
  · by_cases hy : ∃ i, c' < κ i ∧ κ i < κ y
    · have hz : ¬ ∃ i, c' < κ i ∧ κ i < κ z := fun hz => hyz (hup y z hyU hzU hy hz)
      exact tie x z hxz hxU hzU hx hz
    · exact tie x y hxy hxU hyU hx hy

/-- **Alternation forces even length.**  If the sign of `κ - c` flips at every
adjacent pair of `ZMod n`, then `n` is even.  This is the parity law
`alternating_parity` instantiated at `k = n`, where `n̄ = 0̄`. -/
theorem even_of_alternating {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {c : ℝ}
    (halt : ∀ i : ZMod n, ¬ ((c < κ i) ↔ (c < κ (i + 1)))) : Even n := by
  have hn := alternating_parity halt n
  rw [ZMod.natCast_self, Nat.cast_zero] at hn
  tauto

/-- **Odd length always admits an in-block level.**  Move the window to a
generic level `c' > 0`; if no adjacent pair were in-block there, `κ` would
alternate across `c'` at every pair, and `even_of_alternating` would make `n`
even. -/
theorem inBlockLevel_of_odd {n : ℕ} (hodd : Odd n) {κ : ZMod n → ℝ}
    (hpos : ∀ i, 0 < κ i) {c : ℝ} (_hc : 0 < c) (hdfv : DFV κ c) :
    InBlockLevel κ := by
  obtain ⟨k, hk⟩ := hodd
  haveI : NeZero n := ⟨by rintro rfl; omega⟩
  obtain ⟨c', hc'pos, hdfv', hgen⟩ := DFV.exists_generic_level hpos hdfv
  by_cases hex : ∃ j : ZMod n, ((c' < κ j) ↔ (c' < κ (j + 1)))
  · exact ⟨c', hc'pos, hgen, hdfv', hex⟩
  · exfalso
    obtain ⟨l, hl⟩ :=
      even_of_alternating (κ := κ) (c := c') (fun i hi => hex ⟨i, hi⟩)
    omega

/-- **A generic level inside a nonempty open interval.**  Since `ZMod n` is
finite the range of `κ` is finite, while `(lo, hi)` is infinite; so the interval
contains a point that `κ` never attains.  This is the level-shifting device of
`DFV.exists_generic_level`, isolated for the two band lemmas. -/
private theorem exists_generic_mem_Ioo {n : ℕ} [NeZero n] (κ : ZMod n → ℝ) {lo hi : ℝ}
    (h : lo < hi) : ∃ c'' ∈ Set.Ioo lo hi, ∀ i, κ i ≠ c'' := by
  obtain ⟨c'', hc''⟩ := ((Set.Ioo_infinite h).sdiff (Set.finite_range κ)).nonempty
  exact ⟨c'', hc''.1, fun i hi => hc''.2 ⟨i, hi⟩⟩

/-- **Two disjoint high–low adjacent pairs make a window.**  If `a ≠ b` and both
`(a, a+1)` and `(b, b+1)` straddle `c` downwards, then `DFV(κ, c)`.  The proof
lifts the two residues to `[0, n)`, orders them, and hands the quadruple to
`DFV.of_increasing`: when the larger pair does not wrap, the increasing
quadruple is `(e, e+1, f, f+1)` in the high–low phase; when it wraps
(`f + 1 = n`) it is `(0, e, e+1, f)` in the low–high phase, which is exactly the
second disjunct of `DFV.of_increasing`. -/
private theorem DFV.of_two_pairs {n : ℕ} [NeZero n] {κ : ZMod n → ℝ} {c : ℝ}
    {a b : ZMod n} (hab : a ≠ b) (ha : c < κ a) (ha1 : κ (a + 1) < c)
    (hb : c < κ b) (hb1 : κ (b + 1) < c) : DFV κ c := by
  have hcast : ∀ i : ZMod n, ((i.val : ℕ) : ZMod n) = i := by
    intro i; simp [ZMod.natCast_val, ZMod.cast_id]
  have hsucc : ∀ i : ZMod n, (((i.val + 1 : ℕ)) : ZMod n) = i + 1 := by
    intro i; rw [Nat.cast_add, Nat.cast_one, hcast]
  -- the ordered case; the statement is symmetric in `a` and `b`
  have core : ∀ x y : ZMod n, x.val < y.val → c < κ x → κ (x + 1) < c → c < κ y →
      κ (y + 1) < c → DFV κ c := by
    intro x y hlt hx hx1 hy hy1
    have hyn : y.val < n := ZMod.val_lt y
    have hxy1 : x.val + 1 < y.val := by
      rcases Nat.lt_or_ge (x.val + 1) y.val with h | h
      · exact h
      · exfalso
        have heq : x.val + 1 = y.val := by omega
        have : x + 1 = y := by rw [← hsucc x, heq, hcast]
        rw [this] at hx1
        linarith
    rcases Nat.lt_or_ge (y.val + 1) n with hfy | hfy
    · refine DFV.of_increasing (b₁ := x.val) (b₂ := x.val + 1) (b₃ := y.val)
        (b₄ := y.val + 1) (by omega) hxy1 (by omega) hfy (Or.inl ⟨?_, ?_, ?_, ?_⟩)
      · rw [hcast]; exact hx
      · rw [hsucc]; exact hx1
      · rw [hcast]; exact hy
      · rw [hsucc]; exact hy1
    · -- the larger pair wraps: `y.val + 1 = n`, so `κ_{y+1} = κ_{0̄}`
      have hyn1 : y.val + 1 = n := by omega
      have hzero : ((0 : ℕ) : ZMod n) = y + 1 := by
        rw [Nat.cast_zero, ← hsucc y, hyn1, ZMod.natCast_self]
      have hx0 : 0 < x.val := by
        rcases Nat.eq_zero_or_pos x.val with h | h
        · exfalso
          have : x = y + 1 := by rw [← hcast x, h, hzero]
          rw [this] at hx
          linarith
        · exact h
      refine DFV.of_increasing (b₁ := 0) (b₂ := x.val) (b₃ := x.val + 1)
        (b₄ := y.val) hx0 (by omega) hxy1 hyn (Or.inr ⟨?_, ?_, ?_, ?_⟩)
      · rw [hzero]; exact hy1
      · rw [hcast]; exact hx
      · rw [hsucc]; exact hx1
      · rw [hcast]; exact hy
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · exact core a b h ha ha1 hb hb1
  · exact absurd (by rw [← hcast a, h, hcast]) hab
  · exact core b a h hb hb1 ha ha1

/-- **The up-band.**  Suppose `κ` alternates across the generic level `c'` at
every adjacent pair, `i₀` lies above `c'` (in the intended application it
minimises `κ` over `U(c')`), and two *distinct* indices `i₁ ≠ i₂` carry values
strictly above `κ_{i₀}`.  Then `κ` admits an in-block level: push the level up
to a generic `c''` between `κ_{i₀}` and `min(κ_{i₁}, κ_{i₂})`.  The two pairs
`(i₁, i₁+1)`, `(i₂, i₂+1)` still straddle `c''` downwards, so `c''` carries a
window, while `(i₀, i₀+1)` now lies entirely *below* `c''` — an in-block pair. -/
theorem inBlockLevel_of_up_band {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (_hpos : ∀ i, 0 < κ i) {c' : ℝ} (hc' : 0 < c') (hgen : ∀ i, κ i ≠ c')
    (halt : ∀ i : ZMod n, ¬ ((c' < κ i) ↔ (c' < κ (i + 1))))
    {i₀ : ZMod n} (hi₀ : c' < κ i₀) (_hmin : ∀ i, c' < κ i → κ i₀ ≤ κ i)
    {i₁ i₂ : ZMod n} (hne : i₁ ≠ i₂) (h₁ : κ i₀ < κ i₁) (h₂ : κ i₀ < κ i₂) :
    InBlockLevel κ := by
  -- alternation, in the two directions actually used
  have hdown : ∀ i : ZMod n, c' < κ i → κ (i + 1) < c' := by
    intro i hi
    have h := halt i
    have hnot : ¬ (c' < κ (i + 1)) := by tauto
    exact lt_of_le_of_ne (not_lt.mp hnot) (hgen (i + 1))
  -- a generic level strictly between `κ_{i₀}` and the two larger values
  obtain ⟨c'', ⟨hlo, hhi⟩, hgen''⟩ :=
    exists_generic_mem_Ioo κ (lo := κ i₀) (hi := min (κ i₁) (κ i₂)) (lt_min h₁ h₂)
  have hc''pos : 0 < c'' := by linarith
  have hi₁ : c' < κ i₁ := by linarith
  have hi₂ : c' < κ i₂ := by linarith
  refine ⟨c'', hc''pos, hgen'', ?_, i₀, ?_⟩
  · refine DFV.of_two_pairs hne ?_ ?_ ?_ ?_
    · exact lt_of_lt_of_le hhi (min_le_left _ _)
    · have := hdown i₁ hi₁; linarith
    · exact lt_of_lt_of_le hhi (min_le_right _ _)
    · have := hdown i₂ hi₂; linarith
  · have h0 := hdown i₀ hi₀
    constructor <;> intro h <;> linarith

/-- **The down-band.**  Mirror of `inBlockLevel_of_up_band`, moving the level
*down*: with `j₀` below the generic level `c'` (in the application maximising
`κ` over `D(c')`) and two distinct `j₁ ≠ j₂` strictly below `κ_{j₀}`, pick a
generic `c''` between `max(κ_{j₁}, κ_{j₂})` and `κ_{j₀}`.  The two pairs
`(j₁-1, j₁)`, `(j₂-1, j₂)` straddle `c''` downwards, so `c''` carries a window,
and `(j₀, j₀+1)` now lies entirely *above* `c''`.  Positivity of `κ` is what
keeps `c''` positive here. -/
theorem inBlockLevel_of_down_band {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hpos : ∀ i, 0 < κ i) {c' : ℝ} (_hc' : 0 < c') (_hgen : ∀ i, κ i ≠ c')
    (halt : ∀ i : ZMod n, ¬ ((c' < κ i) ↔ (c' < κ (i + 1))))
    {j₀ : ZMod n} (hj₀ : κ j₀ < c') (_hmax : ∀ j, κ j < c' → κ j ≤ κ j₀)
    {j₁ j₂ : ZMod n} (hne : j₁ ≠ j₂) (h₁ : κ j₁ < κ j₀) (h₂ : κ j₂ < κ j₀) :
    InBlockLevel κ := by
  -- alternation, in the direction actually used
  have hup : ∀ i : ZMod n, κ i < c' → c' < κ (i + 1) := by
    intro i hi
    have h := halt i
    have hnA : ¬ (c' < κ i) := not_lt.mpr hi.le
    tauto
  have hpred : ∀ i : ZMod n, κ i < c' → c' < κ (i - 1) := by
    intro i hi
    have h := hup (i - 1)
    have he : i - 1 + 1 = i := by ring
    rw [he] at h
    have hnB : ¬ (c' < κ i) := not_lt.mpr hi.le
    have h' := halt (i - 1)
    rw [he] at h'
    tauto
  -- a generic level strictly between the two smaller values and `κ_{j₀}`
  obtain ⟨c'', ⟨hlo, hhi⟩, hgen''⟩ :=
    exists_generic_mem_Ioo κ (lo := max (κ j₁) (κ j₂)) (hi := κ j₀) (max_lt h₁ h₂)
  have hc''pos : 0 < c'' := by
    have := hpos j₁
    have := le_max_left (κ j₁) (κ j₂)
    linarith
  have hj₁ : κ j₁ < c' := by
    have := le_max_left (κ j₁) (κ j₂); linarith
  have hj₂ : κ j₂ < c' := by
    have := le_max_right (κ j₁) (κ j₂); linarith
  have hab : j₁ - 1 ≠ j₂ - 1 := fun h => hne (by
    have h2 : j₁ - 1 + 1 = j₂ - 1 + 1 := by rw [h]
    calc j₁ = j₁ - 1 + 1 := by ring
      _ = j₂ - 1 + 1 := h2
      _ = j₂ := by ring)
  have he₁ : j₁ - 1 + 1 = j₁ := by ring
  have he₂ : j₂ - 1 + 1 = j₂ := by ring
  refine ⟨c'', hc''pos, hgen'', ?_, j₀, ?_⟩
  · refine DFV.of_two_pairs hab ?_ ?_ ?_ ?_
    · have := hpred j₁ hj₁; linarith
    · rw [he₁]
      have := le_max_left (κ j₁) (κ j₂); linarith
    · have := hpred j₂ hj₂; linarith
    · rw [he₂]
      have := le_max_right (κ j₁) (κ j₂); linarith
  · have h0 := hup j₀ hj₀
    constructor <;> intro _ <;> linarith

/-- **The in-block dichotomy.**  A positive profile carrying a window either
admits an in-block level or is alternating tie-degenerate.  Move the window to a
generic level `c'`; if no adjacent pair is in-block there, `κ` alternates at
every pair, and failure of either counting clause of
`AlternatingTieDegenerate` feeds the corresponding band lemma — the minimum of
`κ` over `U(c')` for the up-band, the maximum over `D(c')` for the down-band. -/
theorem inBlockLevel_or_alternatingTieDegenerate {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hpos : ∀ i, 0 < κ i) {c : ℝ} (_hc : 0 < c) (hdfv : DFV κ c) :
    InBlockLevel κ ∨ AlternatingTieDegenerate κ := by
  obtain ⟨c', hc'pos, hdfv', hgen⟩ := DFV.exists_generic_level hpos hdfv
  by_cases hex : ∃ j : ZMod n, ((c' < κ j) ↔ (c' < κ (j + 1)))
  · exact Or.inl ⟨c', hc'pos, hgen, hdfv', hex⟩
  have halt : ∀ i : ZMod n, ¬ ((c' < κ i) ↔ (c' < κ (i + 1))) := fun i hi => hex ⟨i, hi⟩
  -- extremisers on the two sides, produced from any inhabitant of that side
  have hUmin : ∀ i : ZMod n, c' < κ i →
      ∃ i₀, c' < κ i₀ ∧ ∀ i, c' < κ i → κ i₀ ≤ κ i := by
    intro i0 hi0
    have : Nonempty {i : ZMod n // c' < κ i} := ⟨⟨i0, hi0⟩⟩
    obtain ⟨x, hx⟩ := Finite.exists_min (fun x : {i : ZMod n // c' < κ i} => κ x.1)
    exact ⟨x.1, x.2, fun i hi => hx ⟨i, hi⟩⟩
  have hDmax : ∀ j : ZMod n, κ j < c' →
      ∃ j₀, κ j₀ < c' ∧ ∀ j, κ j < c' → κ j ≤ κ j₀ := by
    intro j0 hj0
    have : Nonempty {j : ZMod n // κ j < c'} := ⟨⟨j0, hj0⟩⟩
    obtain ⟨x, hx⟩ := Finite.exists_max (fun x : {j : ZMod n // κ j < c'} => κ x.1)
    exact ⟨x.1, x.2, fun j hj => hx ⟨j, hj⟩⟩
  by_cases h2 : ∀ i₁ i₂ : ZMod n, c' < κ i₁ → c' < κ i₂ →
      (∃ i, c' < κ i ∧ κ i < κ i₁) → (∃ i, c' < κ i ∧ κ i < κ i₂) → i₁ = i₂
  · by_cases h3 : ∀ j₁ j₂ : ZMod n, κ j₁ < c' → κ j₂ < c' →
        (∃ j, κ j < c' ∧ κ j₁ < κ j) → (∃ j, κ j < c' ∧ κ j₂ < κ j) → j₁ = j₂
    · exact Or.inr ⟨c', hc'pos, hgen, hdfv', halt, h2, h3⟩
    · -- the down side has two non-maximal elements: move the level down
      push Not at h3
      obtain ⟨j₁, j₂, hj₁, hj₂, ⟨a, ha, haj₁⟩, ⟨b, hb, hbj₂⟩, hne⟩ := h3
      obtain ⟨j₀, hj₀, hmax⟩ := hDmax a ha
      exact Or.inl (inBlockLevel_of_down_band hpos hc'pos hgen halt hj₀ hmax hne
        (lt_of_lt_of_le haj₁ (hmax a ha)) (lt_of_lt_of_le hbj₂ (hmax b hb)))
  · -- the up side has two non-minimal elements: move the level up
    push Not at h2
    obtain ⟨i₁, i₂, hi₁, hi₂, ⟨a, ha, hai₁⟩, ⟨b, hb, hbi₂⟩, hne⟩ := h2
    obtain ⟨i₀, hi₀, hmin⟩ := hUmin a ha
    exact Or.inl (inBlockLevel_of_up_band hpos hc'pos hgen halt hi₀ hmin hne
      (lt_of_le_of_lt (hmin a ha) hai₁) (lt_of_le_of_lt (hmin b hb) hbi₂))

/-- **(G-comb)′ with attainment.**  If `4 ≤ m` and the everywhere-positive
parent `κ : ZMod (m + 2) → ℝ` admits an in-block level, then there is a rotation
`r` for which **every** `s` in the closed interval spanned by the two contracted
entries `p = κ_{m̄+r}`, `q = κ_{(m+1)‾+r}` — in particular `s = p` and `s = q`
themselves — is positive and gives a `DiscreteFourVertexPos` child.  This is the
form the downstream endpoint bracket consumes; it is
`exists_graft_contraction_inBlock` with the in-block datum unfolded and the
rotation `r = j - m̄` performed. -/
theorem exists_graft_contraction_attaining {m : ℕ} (hm : 4 ≤ m)
    {κ : ZMod (m + 2) → ℝ} (hpos : ∀ i, 0 < κ i) (hib : InBlockLevel κ) :
    ∃ r : ZMod (m + 2),
      ∀ s ∈ Set.uIcc (κ (((m : ℕ) : ZMod (m + 2)) + r))
          (κ (((m + 1 : ℕ) : ZMod (m + 2)) + r)),
        0 < s ∧ DiscreteFourVertexPos (graftChild (fun i => κ (i + r)) s) := by
  obtain ⟨c', hc'pos, hgen, hdfv, j, hj⟩ := hib
  have hev1 : κ (((m : ℕ) : ZMod (m + 2)) + (j - ((m : ℕ) : ZMod (m + 2)))) = κ j := by
    congr 1
    ring
  have hev2 : κ (((m + 1 : ℕ) : ZMod (m + 2)) + (j - ((m : ℕ) : ZMod (m + 2))))
      = κ (j + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  refine ⟨j - ((m : ℕ) : ZMod (m + 2)), ?_⟩
  rw [hev1, hev2]
  intro s hs
  refine ⟨lt_of_lt_of_le (lt_min (hpos j) (hpos (j + 1))) hs.1, ?_⟩
  exact exists_graft_contraction_inBlock hm hpos hc'pos hgen hdfv hj s hs

/-! ## The plateau site: an equal adjacent pair is always in-block -/

/-- **An adjacent equality gives an in-block level.**  If a positive profile
carrying a window has `κ j = κ (j + 1)` for some `j`, then it admits an in-block
level: move the window to a generic level `c'` (`DFV.exists_generic_level`) and
read the in-block clause at that same index `j` — the biconditional
`(c' < κ j) ↔ (c' < κ (j + 1))` becomes a tautology after rewriting the
equality, with no case split on which side of `c'` the common value lies. -/
theorem inBlockLevel_of_pair_eq {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (hpos : ∀ i, 0 < κ i) {c : ℝ} (_hc : 0 < c) (hdfv : DFV κ c)
    {j : ZMod n} (heq : κ j = κ (j + 1)) : InBlockLevel κ := by
  obtain ⟨c', hc'pos, hdfv', hgen⟩ := DFV.exists_generic_level hpos hdfv
  exact ⟨c', hc'pos, hgen, hdfv', j, by rw [heq]⟩

/-- **The plateau contraction site.**  If `4 ≤ m`, the everywhere-positive
parent `κ : ZMod (m + 2) → ℝ` carries a window at a positive level and has an
equal adjacent pair `κ j = κ (j + 1)`, then the rotation `r = j - m̄` places
that pair at the two contracted slots, and the child taken at the **common
value** is again a positive four-vertex profile.

This is `exists_graft_contraction_inBlock` at the in-block pair supplied by the
equality: the interval `Set.uIcc (κ j) (κ (j + 1))` has collapsed to the single
point `{κ j}`, of which the cap value is trivially a member.  It is the site at
which the dormant-anchor chapter discharges (γ) outright. -/
theorem exists_graft_contraction_plateau {m : ℕ} (hm : 4 ≤ m)
    {κ : ZMod (m + 2) → ℝ} (hpos : ∀ i, 0 < κ i) {c : ℝ} (_hc : 0 < c)
    (hdfv : DFV κ c) {j : ZMod (m + 2)} (heq : κ j = κ (j + 1)) :
    ∃ r : ZMod (m + 2),
      κ (((m : ℕ) : ZMod (m + 2)) + r) = κ (((m + 1 : ℕ) : ZMod (m + 2)) + r) ∧
        0 < κ (((m : ℕ) : ZMod (m + 2)) + r) ∧
        DiscreteFourVertexPos
          (graftChild (fun i => κ (i + r)) (κ (((m : ℕ) : ZMod (m + 2)) + r))) := by
  obtain ⟨c', hc'pos, hdfv', hgen⟩ := DFV.exists_generic_level hpos hdfv
  -- the two index rewritings of `exists_graft_contraction_attaining`
  have hev1 : κ (((m : ℕ) : ZMod (m + 2)) + (j - ((m : ℕ) : ZMod (m + 2)))) = κ j := by
    congr 1
    ring
  have hev2 : κ (((m + 1 : ℕ) : ZMod (m + 2)) + (j - ((m : ℕ) : ZMod (m + 2))))
      = κ (j + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  refine ⟨j - ((m : ℕ) : ZMod (m + 2)), ?_⟩
  rw [hev1, hev2]
  refine ⟨heq, hpos j, ?_⟩
  have hj : (c' < κ j) ↔ (c' < κ (j + 1)) := by rw [heq]
  exact exists_graft_contraction_inBlock hm hpos hc'pos hgen hdfv' hj (κ j)
    (by rw [← heq]; simp)

/-- **The in-block condition is rotation-invariant.**  Both directions use the
same level: genericity transports because `· + r` is a bijection of `ZMod n`,
the window transports by `DFV.comp_add`, and an in-block index `j` for `κ`
becomes the index `j - r` for the rotated profile since `(j - r) + 1 + r
= (j + 1)`.  The backward direction is the forward one applied at `-r`. -/
theorem inBlockLevel_comp_add {n : ℕ} [NeZero n] (κ : ZMod n → ℝ) (r : ZMod n) :
    InBlockLevel (fun i => κ (i + r)) ↔ InBlockLevel κ := by
  -- one direction, stated for an arbitrary profile so it can be reused at `-r`
  have key : ∀ (μ : ZMod n → ℝ) (t : ZMod n),
      InBlockLevel μ → InBlockLevel (fun i => μ (i + t)) := by
    rintro μ t ⟨c', hc'pos, hgen, hdfv, j, hj⟩
    refine ⟨c', hc'pos, fun i => hgen (i + t), hdfv.comp_add t, j - t, ?_⟩
    have e1 : j - t + t = j := by ring
    have e2 : j - t + 1 + t = j + 1 := by ring
    simpa only [e1, e2] using hj
  refine ⟨fun h => ?_, fun h => key κ r h⟩
  have h' := key _ (-r) h
  have hfun : (fun i => κ (i + -r + r)) = κ := by
    funext i
    congr 1
    ring
  rwa [hfun] at h'

end Gluck.Discrete
