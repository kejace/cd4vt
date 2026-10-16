module

public import Gluck.Discrete.FourActiveFrameReindex
public import Gluck.Discrete.RegularFourAnchorReindex

/-!
# Cyclic and reflected transport of regular actual anchors

The sorted-frame constructors preserve literal selected edges. Their
endpoint identities feed the original native derivative transports, so
these operations retain the anchor witness rather than only realizability.
-/

@[expose] public section

namespace Gluck.Discrete.RegularFourAnchor

open FourActiveSlots

variable {n : ℕ} {κ : ZMod n → ℝ}

/-- One actual cyclic shift, including the case in which edge zero crosses
the natural origin and the four retained edge labels rotate. -/
noncomputable def comp_add_one (A : RegularFourAnchor κ) (hκ : ∀ i, 0 < κ i) :
    RegularFourAnchor (fun i => κ (i + 1)) := by
  by_cases h0 : A.frame.edge 0 = 0
  · exact A.rotateReembed hκ (A.frame.shiftOneOfZero h0)
      (A.frame.shiftOneOfZero_start h0 κ) (A.frame.shiftOneOfZero_finish h0 κ)
  · have hp : 0 < A.frame.edge 0 := Nat.pos_of_ne_zero h0
    exact A.reembed (A.frame.shiftOneOfPos hp)
      (A.frame.shiftOneOfPos_start hp κ) (A.frame.shiftOneOfPos_finish hp κ)

/-- Iterating actual one-step shifts preserves a regular four-edge anchor. -/
noncomputable def comp_add_nat (A : RegularFourAnchor κ) (hκ : ∀ i, 0 < κ i)
    (k : ℕ) : RegularFourAnchor (fun i => κ (i + (k : ZMod n))) := by
  induction k with
  | zero => simpa using A
  | succ k ih =>
      have B := ih.comp_add_one (fun i => hκ _)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using B

/-- Arbitrary cyclic shift, with the actual four-edge frame re-sorted as
needed and the native regularity witness retained. -/
noncomputable def comp_add (A : RegularFourAnchor κ) (hκ : ∀ i, 0 < κ i)
    (a : ZMod n) : RegularFourAnchor (fun i => κ (i + a)) := by
  have hn : n ≠ 0 := by have := A.frame.lt_n 0; omega
  letI : NeZero n := ⟨hn⟩
  simpa only [ZMod.natCast_zmod_val] using A.comp_add_nat hκ a.val

/-- Reflection preserves the actual anchor after reversing the sorted
selected edges and swapping the two endpoint sides. -/
noncomputable def comp_neg (A : RegularFourAnchor κ) (hκ : ∀ i, 0 < κ i) :
    RegularFourAnchor (fun i => κ (-i)) :=
  A.reverseReembed hκ A.frame.reverse (A.frame.reverse_start κ) (A.frame.reverse_finish κ)

/-- Restore the original origin from a shifted regular anchor. -/
noncomputable def of_comp_add (a : ZMod n) (hκ : ∀ i, 0 < κ i)
    (A : RegularFourAnchor (fun i => κ (i + a))) : RegularFourAnchor κ := by
  have B := A.comp_add (fun i => hκ _) (-a)
  simpa only [neg_add_cancel_right] using B

/-- Restore the original orientation from a reflected regular anchor. -/
noncomputable def of_comp_neg (hκ : ∀ i, 0 < κ i)
    (A : RegularFourAnchor (fun i => κ (-i))) : RegularFourAnchor κ := by
  have B := A.comp_neg (fun i => hκ _)
  simpa only [neg_neg] using B

theorem nonempty_comp_add_iff (hκ : ∀ i, 0 < κ i) (a : ZMod n) :
    Nonempty (RegularFourAnchor (fun i => κ (i + a))) ↔ Nonempty (RegularFourAnchor κ) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨of_comp_add a hκ A⟩
  · rintro ⟨A⟩
    exact ⟨A.comp_add hκ a⟩

theorem nonempty_comp_neg_iff (hκ : ∀ i, 0 < κ i) :
    Nonempty (RegularFourAnchor (fun i => κ (-i))) ↔ Nonempty (RegularFourAnchor κ) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨of_comp_neg hκ A⟩
  · rintro ⟨A⟩
    exact ⟨A.comp_neg hκ⟩

end Gluck.Discrete.RegularFourAnchor
