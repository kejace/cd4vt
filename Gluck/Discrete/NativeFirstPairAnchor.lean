import Gluck.Discrete.NativeFirstPairExistence
import Gluck.Discrete.NativeOppositePurePhysical

/-!
# A regular physical native anchor from the first-pair flag

This producer retains the four original endpoint slots. Its output has
positive half-lengths, all eight strict incidence inequalities, exact
native closure and one full turn, and a surjective active derivative.
The bound `p * t < 1` includes both the reversed and matched low cases.
-/

namespace Gluck.Discrete.NativeOppositePure

theorem exists_regular_anchor_of_firstPairFlag {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (hpt : p * t < 1)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l) :
    ∃ L : Fin 4 → ℝ, NativeLengthPhysical p t q h l L ∧
      nativeLengthController p t q h l L = 0 ∧
      Function.Surjective (fderiv ℝ (nativeLengthController p t q h l) L) := by
  obtain ⟨α, β, γ, δ, ha, hclose, hturn⟩ :=
    exists_native_zero_of_firstPairFlag_of_product_lt_one hp hp1 ht hpt hl hl1 hq hqh hflag
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hpq := firstPairFlag_one_lt_mul hp hp1 hl hl1 hq hqh hflag
  have htq : t < q := (mul_lt_mul_iff_right₀ hp).mp (hpt.trans hpq)
  let T := γ + δ
  let x : Fin 3 → ℝ := ![α + β, α, γ]
  have ha' : StrictAngles q h (x 1) (x 0 - x 1) (x 2) (T - x 2) := by
    simpa [x, T] using ha
  have hsplit : nativeSplitController p t q h l T x = 0 := by
    have hz : (nativeHalfClosure p t q h l α β γ δ,
        turnDefect p t q h l α β γ δ) = (0 : ℂ × ℝ) := Prod.ext hclose hturn
    simpa [nativeSplitController, x, T] using hz
  have hphysical := nativeLengthPhysical_splitHalfLengths hp hp1 ht htq hl hl1 hq0 ha'
  have hzero : nativeLengthController p t q h l (splitHalfLengths q T x) = 0 := by
    rw [nativeLengthController_splitHalfLengths (ne_of_gt hq0)
      ha'.1 ha'.2.1 ha'.2.2.1 ha'.2.2.2.1]
    exact hsplit
  exact ⟨splitHalfLengths q T x, hphysical, hzero,
    fderiv_nativeLengthController_surjective_of_physical hp hp1 ht htq hl hl1 hq hqh
      hphysical hzero⟩

/-- In particular the reversed and matched low cases both give a regular
anchor from the original flag, with no additional analytic hypothesis. -/
theorem exists_regular_anchor_of_firstPairFlag_of_le {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htp : t ≤ p)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l) :
    ∃ L : Fin 4 → ℝ, NativeLengthPhysical p t q h l L ∧
      nativeLengthController p t q h l L = 0 ∧
      Function.Surjective (fderiv ℝ (nativeLengthController p t q h l) L) := by
  have hpt : p * t < 1 := by
    have hmul := mul_le_mul_of_nonneg_left htp hp.le
    nlinarith
  exact exists_regular_anchor_of_firstPairFlag hp hp1 ht hpt hl hl1 hq hqh hflag

end Gluck.Discrete.NativeOppositePure
