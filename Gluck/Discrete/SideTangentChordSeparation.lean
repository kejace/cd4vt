import Gluck.Discrete.StrictSupportSimplicity

/-!
# Chord separation for a strictly supported polygon

The strict edge inequalities imply positive orientation of every cyclically
ordered triple. The proof uses the determinant identity in a common open
half-plane, so it needs neither a choice of angles nor a genericity assumption.
-/

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

private lemma cross_trans_in_halfplane {A B U V W : ℂ}
    (hU : 0 < crossR2 A B U) (hV : 0 < crossR2 A B V)
    (hW : 0 < crossR2 A B W)
    (hUV : 0 < crossR2 A U V) (hVW : 0 < crossR2 A V W) :
    0 < crossR2 A U W := by
  have hid : crossR2 A B V * crossR2 A U W =
      crossR2 A B U * crossR2 A V W +
        crossR2 A B W * crossR2 A U V := by
    unfold crossR2
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  exact (mul_pos_iff_of_pos_left hV).mp
    (hid ▸ add_pos (mul_pos hU hVW) (mul_pos hW hUV))

private lemma cast_ne_of_lt [NeZero n] {a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (a : ZMod n) ≠ (b : ZMod n) := by
  intro h
  have hval := congrArg ZMod.val h
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hval
  exact hab hval

private lemma cross_cycle (A B C : ℂ) : crossR2 B C A = crossR2 A B C := by
  unfold crossR2
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- Every cyclically ordered triple of distinct vertices has positive orientation. -/
theorem crossR2_cyclic_triple_pos [NeZero n] {Y : ZMod n → ℂ}
    (hY : StrictConvexEdgeSupport Y) (i : ZMod n) {a b : ℕ}
    (ha : 0 < a) (hab : a < b) (hb : b < n) :
    0 < crossR2 (Y i) (Y (i + (a : ZMod n))) (Y (i + (b : ZMod n))) := by
  have hn : 0 < n := NeZero.pos n
  have hfront : ∀ j : ℕ, 1 < j → j < n →
      0 < crossR2 (Y i) (Y (i + 1)) (Y (i + (j : ZMod n))) := by
    intro j hj hjn
    apply hY
    · have h := cast_ne_of_lt hjn hn (by omega : j ≠ 0)
      simpa only [Nat.cast_zero, add_ne_left] using h
    · exact fun heq ↦ cast_ne_of_lt hjn (by omega : 1 < n)
        (by omega : j ≠ 1) (by simpa only [Nat.cast_one] using add_left_cancel heq)
  have hstep : ∀ j : ℕ, 0 < j → j + 1 < n →
      0 < crossR2 (Y i) (Y (i + (j : ZMod n)))
        (Y (i + ((j + 1 : ℕ) : ZMod n))) := by
    intro j hj hjn
    rw [← cross_cycle]
    have h0j : i ≠ i + (j : ZMod n) := by
      intro heq
      have hc : (0 : ZMod n) = (j : ZMod n) := by
        exact add_left_cancel (by simpa only [add_zero] using heq : i + 0 = i + (j : ZMod n))
      exact cast_ne_of_lt hn (by omega : j < n) (by omega : 0 ≠ j)
        (by simpa only [Nat.cast_zero] using hc)
    have h0s : i ≠ (i + (j : ZMod n)) + 1 := by
      intro heq
      have hc : (0 : ZMod n) = ((j + 1 : ℕ) : ZMod n) := by
        apply add_left_cancel (a := i)
        simpa only [add_zero, Nat.cast_add, Nat.cast_one, add_assoc] using heq
      exact cast_ne_of_lt hn hjn (by omega : 0 ≠ j + 1) (by simpa only [Nat.cast_zero] using hc)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hY (i + (j : ZMod n)) i h0j h0s
  by_cases ha1 : a = 1
  · subst a
    simpa only [Nat.cast_one] using hfront b hab hb
  · have ha2 : 1 < a := by omega
    induction b, hab using Nat.le_induction with
    | base => exact hstep a ha hb
    | succ k hak ih =>
      have hkn : k < n := by omega
      have hk1 : a < k := by omega
      exact cross_trans_in_halfplane (hfront a ha2 (by omega))
        (hfront k (by omega) hkn) (hfront (k + 1) (by omega) hb)
        (ih hkn) (hstep k (by omega) hb)

/-- Natural lifts of a cyclically ordered triple have the same orientation. -/
theorem crossR2_lifted_triple_pos [NeZero n] {Y : ZMod n → ℂ}
    (hY : StrictConvexEdgeSupport Y) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hca : c < a + n) :
    0 < crossR2 (Y (a : ZMod n)) (Y (b : ZMod n)) (Y (c : ZMod n)) := by
  have h := crossR2_cyclic_triple_pos hY (a : ZMod n)
    (a := b - a) (b := c - a) (by omega) (by omega) (by omega)
  simpa only [← Nat.cast_add, Nat.add_sub_of_le (by omega : a ≤ b),
    Nat.add_sub_of_le (by omega : a ≤ c)] using h

end Gluck.Discrete.SideTangent
