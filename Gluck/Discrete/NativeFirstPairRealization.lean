module

public import Gluck.Discrete.NativeFirstPairTransition
public import Gluck.Discrete.FourActiveSlotEmbedding

/-!
# First-pair realization with arbitrary hidden curvature words

The four selected edges belong to the original cyclic profile. All other
readings are arbitrary positive real numbers. A produced regular anchor
opens all their edges through the original coherent realization theorem.
-/

@[expose] public section

namespace Gluck.Discrete.FourActiveSlots.Frame

open NativeOppositePure

variable {n : ℕ} [NeZero n] (F : FourActiveSlots.Frame n)

theorem realizesR2_of_native_physical_regular
    {κ : ZMod n → ℝ} {p t q h l : ℝ} {L : Fin 4 → ℝ}
    (hstart : F.start κ = ![1, t, q, l])
    (hfinish : F.finish κ = ![p, q, h, 1])
    (hκ : ∀ i, 0 < κ i) (hphysical : NativeLengthPhysical p t q h l L)
    (hzero : nativeLengthController p t q h l L = 0)
    (hsurj : Function.Surjective (fderiv ℝ (nativeLengthController p t q h l) L)) :
    RealizesR2 κ := by
  rcases hphysical with ⟨hL, h0, hp0, ht1, hq1, hq2, hh2, hl3, h3⟩
  apply F.realizesR2_of_nativeLengthController_regular hstart hfinish hκ hL ?_ ?_ hzero hsurj
  · intro j
    rw [hstart]
    fin_cases j
    · simpa using h0
    · exact ht1
    · exact hq2
    · exact hl3
  · intro j
    rw [hfinish]
    fin_cases j
    · exact hp0
    · exact hq1
    · exact hh2
    · simpa using h3

/-- A first-pair flag with `p*t<1` realizes every positive finite profile
having these four literal selected edges. Hidden readings have no count
or magnitude bound. The conclusion is the original coherent `RealizesR2`. -/
theorem realizesR2_of_firstPairFlag
    {κ : ZMod n → ℝ} {p t q h l : ℝ}
    (hstart : F.start κ = ![1, t, q, l])
    (hfinish : F.finish κ = ![p, q, h, 1])
    (hκ : ∀ i, 0 < κ i)
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (hpt : p * t < 1)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l) : RealizesR2 κ := by
  obtain ⟨L, hphysical, hzero, hsurj⟩ :=
    exists_regular_anchor_of_firstPairFlag hp hp1 ht hpt hl hl1 hq hqh hflag
  exact F.realizesR2_of_native_physical_regular hstart hfinish hκ hphysical hzero hsurj

/-- The original reversed-entry case and the matched case both open all
dormant edges, including arbitrary constant or nonconstant hidden runs. -/
theorem realizesR2_of_firstPairFlag_of_le
    {κ : ZMod n → ℝ} {p t q h l : ℝ}
    (hstart : F.start κ = ![1, t, q, l])
    (hfinish : F.finish κ = ![p, q, h, 1])
    (hκ : ∀ i, 0 < κ i)
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htp : t ≤ p)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l) : RealizesR2 κ := by
  obtain ⟨L, hphysical, hzero, hsurj⟩ :=
    exists_regular_anchor_of_firstPairFlag_of_le hp hp1 ht htp hl hl1 hq hqh hflag
  exact F.realizesR2_of_native_physical_regular hstart hfinish hκ hphysical hzero hsurj

/-- Every actual first negative-to-nonnegative flag transition realizes
the entire finite profile, with no restriction comparing `t` and `p`. -/
theorem realizesR2_of_firstPair_transition
    {κ : ZMod n → ℝ} {p t q h l : ℝ}
    (hstart : F.start κ = ![1, t, q, l])
    (hfinish : F.finish κ = ![p, q, h, 1])
    (hκ : ∀ i, 0 < κ i)
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htq : t < q)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l)
    (hprev : firstPairFlag p t q l < 0) : RealizesR2 κ := by
  obtain ⟨L, hphysical, hzero, hsurj⟩ :=
    exists_regular_anchor_of_firstPair_transition hp hp1 ht htq hl hl1 hq hqh hflag hprev
  exact F.realizesR2_of_native_physical_regular hstart hfinish hκ hphysical hzero hsurj

end Gluck.Discrete.FourActiveSlots.Frame
