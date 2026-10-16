module

public import Gluck.Discrete.SideTangentSquareFan
public import Gluck.Discrete.Converse

/-!
# Cyclic radius differences and the balanced tangential fan

Cyclic relabeling preserves every prescribed radius, including repetitions.
The coefficient at a vertex is the incoming radius minus the outgoing radius.
-/

@[expose] public section

open scoped BigOperators

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- The coefficient that arises by cyclic summation by parts of scaled edges. -/
def radiusDifference (ρ : ZMod n → ℝ) (i : ZMod n) : ℝ := ρ (i - 1) - ρ i

/-- Start the ordered finite list at any original cyclic label. -/
def cyclicLabelEquiv [NeZero n] (s : ZMod n) : Fin n ≃ ZMod n where
  toFun i := s + (i.val : ZMod n)
  invFun j := ⟨(j - s).val, ZMod.val_lt _⟩
  left_inv i := Fin.ext (by simp [ZMod.val_cast_of_lt i.isLt])
  right_inv j := by simp

@[simp] lemma cyclicLabelEquiv_apply [NeZero n] (s : ZMod n) (i : Fin n) :
    cyclicLabelEquiv s i = s + (i.val : ZMod n) := rfl

/-- Every cyclic radius profile has zero total first difference. -/
lemma sum_radiusDifference [NeZero n] (ρ : ZMod n → ℝ) :
    ∑ i, radiusDifference ρ i = 0 := by
  simpa [radiusDifference, sub_eq_add_neg, Finset.sum_add_distrib] using
    sub_eq_zero.mpr (Equiv.sum_comp (Equiv.addRight (-1 : ZMod n)) ρ)

/-- A cyclic change of starting label commutes with taking radius differences. -/
lemma radiusDifference_shift (ρ : ZMod n → ℝ) (s i : ZMod n) :
    radiusDifference (fun j ↦ ρ (s + j)) i = radiusDifference ρ (s + i) := by
  simp only [radiusDifference, add_sub_assoc]

/-- Finite-list sums under the cyclic relabeling equal the original cyclic sums. -/
lemma sum_cyclicLabelEquiv [NeZero n] {M : Type*} [AddCommMonoid M]
    (s : ZMod n) (f : ZMod n → M) :
    ∑ i : Fin n, f (cyclicLabelEquiv s i) = ∑ j : ZMod n, f j :=
  (cyclicLabelEquiv s).sum_comp f

/-- A DFV window has four distinct labels in one cyclic period. -/
lemma four_le_of_dfv {c : ZMod n → ℝ} {a : ℝ} (h : DFV c a) : 4 ≤ n := by
  obtain ⟨i₁, i₂, i₃, i₄, h₁₂, h₂₃, h₃₄, h₄₁, _⟩ := h
  omega

/-- Select the four alternating labels by a cyclic shift, without changing orientation. -/
lemma exists_ordered_shift_of_dfv {c : ZMod n → ℝ} (h : DFV c 0) :
    ∃ s p q r : ℕ, 0 < p ∧ p < q ∧ q < r ∧ r < n ∧
      0 < c (s : ZMod n) ∧ c ((s + p : ℕ) : ZMod n) < 0 ∧
      0 < c ((s + q : ℕ) : ZMod n) ∧ c ((s + r : ℕ) : ZMod n) < 0 := by
  obtain ⟨i₁, i₂, i₃, i₄, h₁₂, h₂₃, h₃₄, h₄₁, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨i₁, i₂ - i₁, i₃ - i₁, i₄ - i₁, by omega, by omega, by omega, by omega,
    h₁, by simpa only [show i₁ + (i₂ - i₁) = i₂ by omega] using h₂,
    by simpa only [show i₁ + (i₃ - i₁) = i₃ by omega] using h₃,
    by simpa only [show i₁ + (i₄ - i₁) = i₄ by omega] using h₄⟩

/-- The explicit finite fan, returned to the original cyclic vertex labels. -/
noncomputable def cyclicFanVertex [NeZero n] (p q r : ℕ) (η : ℝ)
    (s i : ZMod n) : ℂ :=
  fanVertex n p q r η ((cyclicLabelEquiv s).symm i).val

@[simp] lemma cyclicFanVertex_label [NeZero n] (p q r : ℕ) (η : ℝ)
    (s : ZMod n) (i : Fin n) :
    cyclicFanVertex p q r η s (cyclicLabelEquiv s i) = fanVertex n p q r η i := by
  simp only [cyclicFanVertex, Equiv.symm_apply_apply]

/-- A zero-sum cyclic DFV list produces an actual balanced fan after only a cyclic shift.
Every finite label remains present, and coefficients away from the four witnesses are arbitrary. -/
theorem exists_balanced_shiftedFan_of_dfv [NeZero n] {c : ZMod n → ℝ}
    (h : DFV c 0) (hsum : ∑ i, c i = 0) :
    ∃ s : ZMod n, ∃ p q r : ℕ, 0 < p ∧ p < q ∧ q < r ∧ r < n ∧
      ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ a : ℂ, ∃ σ : ℝ,
        ‖a‖ < 1 ∧ 0 < σ ∧ σ ^ 2 + ‖a‖ ^ 2 = 1 ∧
          (∀ i : Fin n, 0 < ProjectiveBall.denominator a (fanVertex n p q r η i)) ∧
          ∑ i : Fin n, c (cyclicLabelEquiv s i) •
            ProjectiveBall.transform a σ (fanVertex n p q r η i) = 0 := by
  obtain ⟨s, p, q, r, hp, hpq, hqr, hr, h₀, h₁, h₂, h₃⟩ :=
    exists_ordered_shift_of_dfv h
  exact ⟨(s : ZMod n), p, q, r, hp, hpq, hqr, hr,
    exists_balanced_squareFan (four_le_of_dfv h) hp hpq hqr hr
      (fun i ↦ c (cyclicLabelEquiv (s : ZMod n) i))
      ((sum_cyclicLabelEquiv (s : ZMod n) c).trans hsum)
      (by simpa only [cyclicLabelEquiv_apply, Nat.cast_zero, add_zero] using h₀)
      (by simpa only [cyclicLabelEquiv_apply, Nat.cast_add] using h₁)
      (by simpa only [cyclicLabelEquiv_apply, Nat.cast_add] using h₂)
      (by simpa only [cyclicLabelEquiv_apply, Nat.cast_add] using h₃)⟩

/-- The balance producer on the original cyclic labels, with every original coefficient. -/
theorem exists_balanced_cyclicFan_of_dfv [NeZero n] {c : ZMod n → ℝ}
    (h : DFV c 0) (hsum : ∑ i, c i = 0) :
    ∃ s : ZMod n, ∃ p q r : ℕ, 0 < p ∧ p < q ∧ q < r ∧ r < n ∧
      ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ a : ℂ, ∃ σ : ℝ,
        ‖a‖ < 1 ∧ 0 < σ ∧ σ ^ 2 + ‖a‖ ^ 2 = 1 ∧
          (∀ i : ZMod n, 0 < ProjectiveBall.denominator a (cyclicFanVertex p q r η s i)) ∧
          ∑ i : ZMod n, c i •
            ProjectiveBall.transform a σ (cyclicFanVertex p q r η s i) = 0 := by
  obtain ⟨s, p, q, r, hp, hpq, hqr, hr, η, hη, hη₁, a, σ, ha, hσ, hσa, hd, hb⟩ :=
    exists_balanced_shiftedFan_of_dfv h hsum
  refine ⟨s, p, q, r, hp, hpq, hqr, hr, η, hη, hη₁, a, σ, ha, hσ, hσa,
    fun i ↦ hd ((cyclicLabelEquiv s).symm i), ?_⟩
  calc
    ∑ i, c i • ProjectiveBall.transform a σ (cyclicFanVertex p q r η s i) =
        ∑ i : Fin n, c (cyclicLabelEquiv s i) • ProjectiveBall.transform a σ
          (cyclicFanVertex p q r η s (cyclicLabelEquiv s i)) :=
      (sum_cyclicLabelEquiv s _).symm
    _ = 0 := by simpa only [cyclicFanVertex_label] using hb

/-- The cyclic label equivalence preserves the next label, including the seam. -/
lemma cyclicLabelEquiv_succ [NeZero n] (s : ZMod n) (i : Fin n) :
    cyclicLabelEquiv s (i + 1) = cyclicLabelEquiv s i + 1 := by
  simp only [cyclicLabelEquiv_apply, Fin.val_add, Fin.val_one', ZMod.natCast_mod,
    Nat.cast_add, Nat.cast_one, add_assoc]

@[simp] lemma cyclicLabelEquiv_symm_val [NeZero n] (s i : ZMod n) :
    ((cyclicLabelEquiv s).symm i).val = (i - s).val := rfl

/-- An admissible radius-difference profile supplies the balanced finite fan unconditionally.
No radius or coefficient is perturbed, and zero differences retain their original labels.
Radius positivity is only needed later when the edges are scaled. -/
theorem exists_balanced_cyclicFan_of_radiusDFV [NeZero n] (ρ : ZMod n → ℝ)
    (h : DFV (radiusDifference ρ) 0) :
    ∃ s : ZMod n, ∃ p q r : ℕ, 0 < p ∧ p < q ∧ q < r ∧ r < n ∧
      ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ a : ℂ, ∃ σ : ℝ,
        ‖a‖ < 1 ∧ 0 < σ ∧ σ ^ 2 + ‖a‖ ^ 2 = 1 ∧
          (∀ i : ZMod n, 0 < ProjectiveBall.denominator a (cyclicFanVertex p q r η s i)) ∧
          ∑ i : ZMod n, (ρ (i - 1) - ρ i) •
            ProjectiveBall.transform a σ (cyclicFanVertex p q r η s i) = 0 :=
  exists_balanced_cyclicFan_of_dfv h (sum_radiusDifference ρ)

end Gluck.Discrete.SideTangent
