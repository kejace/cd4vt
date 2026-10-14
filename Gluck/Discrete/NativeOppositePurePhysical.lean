import Gluck.Discrete.NativeOppositePureNativeRank

/-!
# Physical half-lengths for the opposite-pure slot model

Every active half-length is positive. The eight inequalities below are
the literal endpoint incidence walls of the slots
`(1,1), (p,t), (q,q), (h,l)`, in cyclic edge order.
-/

namespace Gluck.Discrete.NativeOppositePure

def NativeLengthPhysical (p t q h l : ℝ) (L : Fin 4 → ℝ) : Prop :=
  (∀ i, 0 < L i) ∧ L 0 < 1 ∧ p * L 0 < 1 ∧ t * L 1 < 1 ∧
    q * L 1 < 1 ∧ q * L 2 < 1 ∧ h * L 2 < 1 ∧ l * L 3 < 1 ∧ L 3 < 1

private theorem sin_mem_unit_of_acute {z : ℝ}
    (hz : z ∈ Set.Ioo 0 (Real.pi / 2)) : Real.sin z ∈ Set.Ioo 0 1 := by
  refine ⟨Real.sin_pos_of_pos_of_lt_pi hz.1 (by linarith [hz.2, Real.pi_pos]), ?_⟩
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ z by linarith [hz.1, Real.pi_pos]) le_rfl hz.2
  simpa using h

theorem nativeLengthPhysical_splitHalfLengths {p t q h l T : ℝ} {x : Fin 3 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q)
    (hl : 0 < l) (hl1 : l < 1) (hq : 0 < q)
    (ha : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2)) :
    NativeLengthPhysical p t q h l (splitHalfLengths q T x) := by
  have hsa := sin_mem_unit_of_acute ha.1
  have hsb := sin_mem_unit_of_acute ha.2.1
  have hsg := sin_mem_unit_of_acute ha.2.2.1
  have hsd := sin_mem_unit_of_acute ha.2.2.2.1
  refine ⟨?_, hsa.2, ?_, ?_, ?_, ?_, ?_, ?_, hsb.2⟩
  · intro i
    fin_cases i
    · exact hsa.1
    · exact div_pos hsg.1 hq
    · exact div_pos hsd.1 hq
    · exact hsb.1
  · exact endpoint_arg_lt_one hp hp1 ha.1.1 ha.1.2
  · change t * (Real.sin (x 2) / q) < 1
    rw [show t * (Real.sin (x 2) / q) = (t / q) * Real.sin (x 2) by ring]
    exact endpoint_arg_lt_one (div_pos ht hq) ((div_lt_one hq).mpr htq)
      ha.2.2.1.1 ha.2.2.1.2
  · change q * (Real.sin (x 2) / q) < 1
    simpa [mul_div_cancel₀ _ (ne_of_gt hq)] using hsg.2
  · change q * (Real.sin (T - x 2) / q) < 1
    simpa [mul_div_cancel₀ _ (ne_of_gt hq)] using hsd.2
  · change h * (Real.sin (T - x 2) / q) < 1
    convert ha.2.2.2.2 using 1
    ring
  · exact endpoint_arg_lt_one hl hl1 ha.2.1.1 ha.2.1.2

/-- Every strictly physical half-length tuple has the original acute
angle coordinates. This is an exact inverse, with no regularity premise. -/
theorem exists_splitHalfLengths_of_physical {p t q h l : ℝ} {L : Fin 4 → ℝ}
    (hq : 0 < q) (hphysical : NativeLengthPhysical p t q h l L) :
    ∃ T : ℝ, ∃ x : Fin 3 → ℝ,
      StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2) ∧
      splitHalfLengths q T x = L := by
  rcases hphysical with ⟨hpos, h0, _hp0, _ht1, hq1, hq2, hh2, _hl3, h3⟩
  have hqL1 := mul_pos hq (hpos 1)
  have hqL2 := mul_pos hq (hpos 2)
  have hangle {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
      Real.arcsin z ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨Real.arcsin_pos.mpr hz, Real.arcsin_lt_pi_div_two.mpr hz1⟩
  have hs {z : ℝ} (hz : 0 < z) (hz1 : z < 1) : Real.sin (Real.arcsin z) = z :=
    Real.sin_arcsin (by linarith) hz1.le
  let T := Real.arcsin (q * L 1) + Real.arcsin (q * L 2)
  let x : Fin 3 → ℝ :=
    ![Real.arcsin (L 0) + Real.arcsin (L 3), Real.arcsin (L 0), Real.arcsin (q * L 1)]
  have ha : StrictAngles q h (Real.arcsin (L 0)) (Real.arcsin (L 3))
      (Real.arcsin (q * L 1)) (Real.arcsin (q * L 2)) := by
    refine ⟨hangle (hpos 0) h0, hangle (hpos 3) h3,
      hangle hqL1 hq1, hangle hqL2 hq2, ?_⟩
    rw [hs hqL2 hq2]
    have he : (h / q) * (q * L 2) = h * L 2 := by field_simp
    rwa [he]
  refine ⟨T, x, ?_, ?_⟩
  · simpa [x, T] using ha
  · funext i
    fin_cases i
    · exact hs (hpos 0) h0
    · change Real.sin (Real.arcsin (q * L 1)) / q = L 1
      rw [hs hqL1 hq1]
      field_simp
    · change Real.sin (Real.arcsin (q * L 1) + Real.arcsin (q * L 2) -
        Real.arcsin (q * L 1)) / q = L 2
      rw [add_sub_cancel_left, hs hqL2 hq2]
      field_simp
    · simpa [splitHalfLengths, x, T] using hs (hpos 3) h3

/-- Every physical zero of the original four-half-length equations has
surjective derivative. The tuple need not be supplied in angle form. -/
theorem fderiv_nativeLengthController_surjective_of_physical
    {p t q h l : ℝ} {L : Fin 4 → ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hphysical : NativeLengthPhysical p t q h l L)
    (hzero : nativeLengthController p t q h l L = 0) :
    Function.Surjective (fderiv ℝ (nativeLengthController p t q h l) L) := by
  obtain ⟨T, x, ha, hL⟩ := exists_splitHalfLengths_of_physical (zero_lt_one.trans hq) hphysical
  have hsplit : nativeSplitController p t q h l T x = 0 := by
    rw [← nativeLengthController_splitHalfLengths
      (ne_of_gt (zero_lt_one.trans hq)) ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1, hL]
    exact hzero
  rw [← hL]
  exact fderiv_nativeLengthController_surjective hp hp1 hl hl1 ht htq hq hqh ha hsplit

end Gluck.Discrete.NativeOppositePure
