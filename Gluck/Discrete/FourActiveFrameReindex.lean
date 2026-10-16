module

public import Gluck.Discrete.RegularFourAnchorTransport

/-!
# Sorted actual four-edge frames under cyclic reindexing

A one-step shift either preserves the order of the four labels or moves the
first selected edge to the end. Reflection reverses edge order and swaps
the literal start and finish readings. No virtual edge is introduced.
-/

@[expose] public section

namespace Gluck.Discrete.FourActiveSlots.Frame

variable {n : ℕ} (F : Frame n)

lemma edge_zero_le (j : Fin 4) : F.edge 0 ≤ F.edge j :=
  F.strictMono.monotone (Fin.zero_le j)

lemma edge_pos_of_zero_pos (h0 : 0 < F.edge 0) (j : Fin 4) : 0 < F.edge j :=
  lt_of_lt_of_le h0 (F.edge_zero_le j)

/-- Shift all selected actual edges one step backwards, when none crosses
the natural origin. -/
def shiftOneOfPos (h0 : 0 < F.edge 0) : Frame n where
  edge j := F.edge j - 1
  strictMono := by
    intro i j hij
    have hi := F.edge_pos_of_zero_pos h0 i
    have hj := F.strictMono hij
    change F.edge i - 1 < F.edge j - 1
    omega
  lt_n j := lt_of_le_of_lt (Nat.sub_le _ _) (F.lt_n j)

@[simp] theorem shiftOneOfPos_residue (h0 : 0 < F.edge 0) (j : Fin 4) :
    (F.shiftOneOfPos h0).residue j = F.residue j - 1 := by
  have hj : 1 ≤ F.edge j := F.edge_pos_of_zero_pos h0 j
  simp [residue, shiftOneOfPos, Nat.cast_sub hj]

theorem shiftOneOfPos_start (h0 : 0 < F.edge 0) (κ : ZMod n → ℝ) :
    (F.shiftOneOfPos h0).start (fun i => κ (i + 1)) = F.start κ := by
  funext j
  simp [start]

theorem shiftOneOfPos_finish (h0 : 0 < F.edge 0) (κ : ZMod n → ℝ) :
    (F.shiftOneOfPos h0).finish (fun i => κ (i + 1)) = F.finish κ := by
  funext j
  simp [finish]

/-- If edge zero is selected, shifting it backwards moves it to the end
of the sorted four-edge frame. -/
def shiftOneOfZero (h0 : F.edge 0 = 0) : Frame n where
  edge := ![F.edge 1 - 1, F.edge 2 - 1, F.edge 3 - 1, n - 1]
  strictMono := by
    have h01 := F.strictMono (show (0 : Fin 4) < 1 by decide)
    have h12 := F.strictMono (show (1 : Fin 4) < 2 by decide)
    have h23 := F.strictMono (show (2 : Fin 4) < 3 by decide)
    have h3 := F.lt_n 3
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    fin_cases j <;> simp <;> omega
  lt_n := by
    intro j
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (F.lt_n 0)
    fin_cases j
    · change F.edge 1 - 1 < n
      exact lt_of_le_of_lt (Nat.sub_le _ _) (F.lt_n 1)
    · change F.edge 2 - 1 < n
      exact lt_of_le_of_lt (Nat.sub_le _ _) (F.lt_n 2)
    · change F.edge 3 - 1 < n
      exact lt_of_le_of_lt (Nat.sub_le _ _) (F.lt_n 3)
    · change n - 1 < n
      omega

theorem shiftOneOfZero_residue (h0 : F.edge 0 = 0) :
    (F.shiftOneOfZero h0).residue = fun j => rotateFour F.residue j - 1 := by
  have h01 := F.strictMono (show (0 : Fin 4) < 1 by decide)
  have h02 := F.strictMono (show (0 : Fin 4) < 2 by decide)
  have h03 := F.strictMono (show (0 : Fin 4) < 3 by decide)
  have h1 : 1 ≤ F.edge 1 := by omega
  have h2 : 1 ≤ F.edge 2 := by omega
  have h3 : 1 ≤ F.edge 3 := by omega
  have hn : 1 ≤ n := by have := F.lt_n 0; omega
  funext j
  fin_cases j <;>
    simp [residue, shiftOneOfZero, rotateFour, h0, Nat.cast_sub h1,
      Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub hn]

theorem shiftOneOfZero_start (h0 : F.edge 0 = 0) (κ : ZMod n → ℝ) :
    (F.shiftOneOfZero h0).start (fun i => κ (i + 1)) = rotateFour (F.start κ) := by
  funext j
  simp only [start, F.shiftOneOfZero_residue h0, sub_add_cancel]
  fin_cases j <;> rfl

theorem shiftOneOfZero_finish (h0 : F.edge 0 = 0) (κ : ZMod n → ℝ) :
    (F.shiftOneOfZero h0).finish (fun i => κ (i + 1)) = rotateFour (F.finish κ) := by
  funext j
  simp only [finish, F.shiftOneOfZero_residue h0, sub_add_cancel]
  fin_cases j <;> rfl

/-- Reflection in the cyclic origin, with the four actual edges listed
again in increasing natural order. -/
def reverse : Frame n where
  edge j := n - 1 - reverseFour F.edge j
  strictMono := by
    have h01 := F.strictMono (show (0 : Fin 4) < 1 by decide)
    have h12 := F.strictMono (show (1 : Fin 4) < 2 by decide)
    have h23 := F.strictMono (show (2 : Fin 4) < 3 by decide)
    have h3 := F.lt_n 3
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    fin_cases j <;> simp [reverseFour] <;> omega
  lt_n := by
    intro j
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (F.lt_n 0)
    exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega)

theorem reverse_residue :
    F.reverse.residue = fun j => -1 - reverseFour F.residue j := by
  have hn : 1 ≤ n := by have := F.lt_n 0; omega
  have hj (j : Fin 4) : F.edge j ≤ n - 1 := by have := F.lt_n j; omega
  funext j
  fin_cases j <;>
    simp [residue, reverse, reverseFour, Nat.cast_sub (hj _),
      Nat.cast_sub hn]

theorem reverse_start (κ : ZMod n → ℝ) :
    F.reverse.start (fun i => κ (-i)) = reverseFour (F.finish κ) := by
  funext j
  simp only [start, F.reverse_residue]
  fin_cases j <;> simp [reverseFour, finish, neg_sub]

theorem reverse_finish (κ : ZMod n → ℝ) :
    F.reverse.finish (fun i => κ (-i)) = reverseFour (F.start κ) := by
  funext j
  simp only [finish, F.reverse_residue]
  fin_cases j <;> simp [reverseFour, start]

end Gluck.Discrete.FourActiveSlots.Frame
