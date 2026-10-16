module

public import Gluck.Discrete.SideTangentDFV

/-!
# Two sign blocks when a cyclic list has no four-sign window

Zeros are retained. A positive and a negative coefficient, with no alternating
four-sign window, can be separated by two actual cyclic labels.
-/

@[expose] public section

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- Without a four-sign window, all nonzero coefficients lie in two cyclic sign blocks. -/
theorem exists_sign_blocks_of_not_dfv [NeZero n] {c : ZMod n → ℝ}
    (hpos : ∃ i, 0 < c i) (hneg : ∃ i, c i < 0) (hdfv : ¬ DFV c 0) :
    ∃ a b : ℕ, a < b ∧ b < a + n ∧ c (a : ZMod n) < 0 ∧ 0 < c (b : ZMod n) ∧
      (∀ k, a < k → k < b → c (k : ZMod n) ≤ 0) ∧
      (∀ k, b < k → k < a + n → 0 ≤ c (k : ZMod n)) := by
  classical
  obtain ⟨i, hi⟩ := hpos
  obtain ⟨j, hj⟩ := hneg
  let p := i.val
  have hp : c (p : ZMod n) > 0 := by simpa only [p, ZMod.natCast_zmod_val] using hi
  let d := (j - i).val
  have hdn : d < n := ZMod.val_lt _
  have hd : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    have hij : j = i := by
      have hcast : (d : ZMod n) = j - i := ZMod.natCast_zmod_val _
      rw [hz, Nat.cast_zero] at hcast
      exact sub_eq_zero.mp hcast.symm
    rw [hij] at hj
    linarith
  have hpd : ((p + d : ℕ) : ZMod n) = j := by
    simp only [Nat.cast_add, p, d, ZMod.natCast_zmod_val]
    ring
  have hfirst : ∃ k : ℕ, p < k ∧ k < p + n ∧ c (k : ZMod n) < 0 :=
    ⟨p + d, by omega, by omega, by simpa only [hpd] using hj⟩
  let a := Nat.find hfirst
  obtain ⟨hpa, hap, ha⟩ := Nat.find_spec hfirst
  have hwrap : c ((p + n : ℕ) : ZMod n) > 0 := by
    simpa only [Nat.cast_add, ZMod.natCast_self, add_zero] using hp
  have hnext : ∃ k : ℕ, a < k ∧ 0 < c (k : ZMod n) := ⟨p + n, hap, hwrap⟩
  let b := Nat.find hnext
  obtain ⟨hab, hb⟩ := Nat.find_spec hnext
  have hbp : b ≤ p + n := Nat.find_min' hnext ⟨hap, hwrap⟩
  refine ⟨a, b, hab, by omega, ha, hb, ?_, ?_⟩
  · intro k hak hkb
    apply le_of_not_gt
    intro hk
    exact Nat.find_min hnext hkb ⟨hak, hk⟩
  · intro k hbk hka
    by_cases hkp : k < p + n
    · apply le_of_not_gt
      intro hk
      exact hdfv ⟨p, a, b, k, hpa, hab, hbk, hkp, hp, ha, hb, hk⟩
    · have hnk : n ≤ k := by omega
      have htk : k - n < a := by omega
      have hpt : p ≤ k - n := by omega
      have hnonneg : 0 ≤ c ((k - n : ℕ) : ZMod n) := by
        rcases eq_or_lt_of_le hpt with he | he
        · simpa only [← he] using hp.le
        · apply le_of_not_gt
          intro hk
          exact Nat.find_min hfirst htk ⟨he, by omega, hk⟩
      simpa only [Nat.cast_sub hnk, ZMod.natCast_self, sub_zero] using hnonneg

end Gluck.Discrete.SideTangent
