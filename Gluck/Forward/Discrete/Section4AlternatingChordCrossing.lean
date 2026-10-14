/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Gluck.Forward.Discrete.Section4ContactOrientation
import Gluck.Discrete.CircleParameterGeometry

/-!
# Alternating boundary data force a chord crossing

This file isolates the elementary part of the cyclic contact-order problem.
If a finite polygonal chain in a closed disk starts and ends on opposite
sides of a boundary chord, one of its edges meets that chord.  The proof is
finite: take the first chain vertex on the nonpositive side and apply the
two-segment crossing lemma.

What this result does *not* assert is that the chain meets a second
polygonal chain with the same endpoints as the chord.  Replacing the chord
by that chain is precisely the polygonal Jordan/crosscut step still needed
for a full exposed-contact order theorem.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- A finite chain in a closed disk whose endpoints are on opposite strict
sides of a boundary chord has an edge meeting that chord. -/
theorem exists_chainEdge_not_disjoint_boundaryChord
    {O A B : ℂ} {R : ℝ} {p : ℕ → ℂ} {N : ℕ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hinside : ∀ k : ℕ, k ≤ N → dist O (p k) ≤ R)
    (hstart : 0 < crossR2 A B (p 0))
    (hend : crossR2 A B (p N) < 0) :
    ∃ k : ℕ, k < N ∧
      ¬ Disjoint (segment ℝ A B) (segment ℝ (p k) (p (k + 1))) := by
  classical
  let f : ℕ → ℝ := fun k ↦ crossR2 A B (p k)
  have hex : ∃ q : ℕ, q ≤ N ∧ f q ≤ 0 :=
    ⟨N, le_rfl, hend.le⟩
  let q : ℕ := Nat.find hex
  have hq : q ≤ N ∧ f q ≤ 0 := by
    simpa [q] using Nat.find_spec hex
  have hqpos : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hqzero
    have : f 0 ≤ 0 := by simpa [hqzero] using hq.2
    exact (not_le_of_gt hstart) this
  let k : ℕ := q - 1
  have hkq : k + 1 = q := by
    dsimp [k]
    omega
  have hkN : k < N := by
    dsimp [k]
    omega
  have hkLeN : k ≤ N := hkN.le
  have hkpos : 0 < f k := by
    by_contra hnot
    have hkNonpos : f k ≤ 0 := le_of_not_gt hnot
    have hminimal := Nat.find_min hex (m := k) (by
      dsimp [k]
      omega)
    exact hminimal ⟨hkLeN, hkNonpos⟩
  refine ⟨k, hkN, ?_⟩
  rcases lt_or_eq_of_le hq.2 with hqneg | hqzero
  · rw [← hkq] at hqneg
    exact boundaryChord_not_disjoint_segment_of_cross_pos_neg
      hAB hA hB (hinside k hkLeN)
        (hinside (k + 1) (by omega)) hkpos hqneg
  · have hpqChord : p q ∈ segment ℝ A B :=
      mem_boundaryChord_of_cross_eq_zero hAB hA hB
        (hinside q hq.1) (by simpa [f] using hqzero)
    intro hdisjoint
    apply Set.disjoint_left.mp hdisjoint hpqChord
    rw [← hkq]
    exact right_mem_segment ℝ _ _

/-- The same conclusion with the endpoint side signs reversed. -/
theorem exists_chainEdge_not_disjoint_boundaryChord_of_neg_pos
    {O A B : ℂ} {R : ℝ} {p : ℕ → ℂ} {N : ℕ}
    (hAB : A ≠ B)
    (hA : dist O A = R) (hB : dist O B = R)
    (hinside : ∀ k : ℕ, k ≤ N → dist O (p k) ≤ R)
    (hstart : crossR2 A B (p 0) < 0)
    (hend : 0 < crossR2 A B (p N)) :
    ∃ k : ℕ, k < N ∧
      ¬ Disjoint (segment ℝ A B) (segment ℝ (p k) (p (k + 1))) := by
  have hBA : B ≠ A := hAB.symm
  have hstart' : 0 < crossR2 B A (p 0) := by
    rw [crossR2_reverse (p 0) A B, crossR2_cycle_two A B (p 0)]
    linarith
  have hend' : crossR2 B A (p N) < 0 := by
    rw [crossR2_reverse (p N) A B, crossR2_cycle_two A B (p N)]
    linarith
  simpa [segment_symm] using
    exists_chainEdge_not_disjoint_boundaryChord
      hBA hB hA hinside hstart' hend'

/-- Four points occurring alternately around one circle give the opposite
side signs needed by `exists_chainEdge_not_disjoint_boundaryChord_of_neg_pos`.
Thus any disk-contained chain from the second point to the fourth point has
an edge meeting the chord from the first point to the third point. -/
theorem exists_chainEdge_not_disjoint_circleChord_of_alternating
    {O : ℂ} {R θA θC θB θD : ℝ} {p : ℕ → ℂ} {N : ℕ}
    (hR : 0 < R)
    (hAC : θA < θC) (hCB : θC < θB)
    (hBD : θB < θD) (hspan : θD < θA + 2 * Real.pi)
    (hp0 : p 0 = circlePoint O R θC)
    (hpN : p N = circlePoint O R θD)
    (hinside : ∀ k : ℕ, k ≤ N → dist O (p k) ≤ R) :
    ∃ k : ℕ, k < N ∧
      ¬ Disjoint
        (segment ℝ (circlePoint O R θA) (circlePoint O R θB))
        (segment ℝ (p k) (p (k + 1))) := by
  have hACB :
      0 < crossR2 (circlePoint O R θA) (circlePoint O R θC)
        (circlePoint O R θB) :=
    crossR2_circlePoint_pos_of_ordered O hR.ne' hAC hCB
      (by linarith)
  have hABCneg :
      crossR2 (circlePoint O R θA) (circlePoint O R θB)
          (circlePoint O R θC) < 0 := by
    rw [crossR2_swap]
    linarith
  have hABDpos :
      0 < crossR2 (circlePoint O R θA) (circlePoint O R θB)
        (circlePoint O R θD) :=
    crossR2_circlePoint_pos_of_ordered O hR.ne'
      (hAC.trans hCB) hBD hspan
  have hAB : circlePoint O R θA ≠ circlePoint O R θB := by
    intro heq
    rw [heq] at hABDpos
    simp [crossR2] at hABDpos
  apply exists_chainEdge_not_disjoint_boundaryChord_of_neg_pos
      hAB
      (by simp [dist_circlePoint_center, abs_of_pos hR])
      (by simp [dist_circlePoint_center, abs_of_pos hR])
      hinside
  · simpa [hp0] using hABCneg
  · simpa [hpN] using hABDpos

end Gluck.Forward
