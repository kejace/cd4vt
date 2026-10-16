module

public import Gluck.Discrete.FourActiveSlotEmbedding
public import Gluck.Discrete.NativeOppositePurePhysical

/-!
# A regular four-edge anchor retained as geometric data

This witness can be moved between finite curvature words when the four
literal endpoint pairs agree. In particular, restoring constant runs
requires no closedness theorem for the interior realization locus.
-/

@[expose] public section

namespace Gluck.Discrete

/-- Four actual edges and the strict regular native anchor supported on them. -/
structure RegularFourAnchor {n : ℕ} (κ : ZMod n → ℝ) where
  frame : FourActiveSlots.Frame n
  halfLengths : Fin 4 → ℝ
  positive : ∀ j, 0 < halfLengths j
  start_lt : ∀ j, frame.start κ j * halfLengths j < 1
  finish_lt : ∀ j, frame.finish κ j * halfLengths j < 1
  zero : frame.controller κ halfLengths = 0
  regular : Function.Surjective (fderiv ℝ (frame.controller κ) halfLengths)

namespace RegularFourAnchor

theorem realizesR2 {n : ℕ} [NeZero n] {κ : ZMod n → ℝ}
    (A : RegularFourAnchor κ) (hκ : ∀ i, 0 < κ i) : RealizesR2 κ :=
  A.frame.realizesR2_of_controller_regular hκ A.positive A.start_lt A.finish_lt A.zero A.regular

/-- All four-length equations agree when the actual incident readings agree,
irrespective of the number or values of the dormant readings. -/
theorem controller_eq_of_endpoints {m n : ℕ} {μ : ZMod m → ℝ} {κ : ZMod n → ℝ}
    {F : FourActiveSlots.Frame m} {G : FourActiveSlots.Frame n}
    (hstart : G.start κ = F.start μ) (hfinish : G.finish κ = F.finish μ) :
    G.controller κ = F.controller μ := by
  funext L
  simp only [FourActiveSlots.Frame.controller, FourActiveSlots.Frame.turns,
    FourActiveSlots.Frame.startArc, FourActiveSlots.Frame.finishArc, hstart, hfinish]

/-- Lift a regular anchor to any actual four-edge frame with the same literal
endpoint readings. Positivity of all other readings is needed only when the
lifted anchor is opened with `realizesR2`. -/
noncomputable def reembed {m n : ℕ} {μ : ZMod m → ℝ} {κ : ZMod n → ℝ}
    (A : RegularFourAnchor μ) (G : FourActiveSlots.Frame n)
    (hstart : G.start κ = A.frame.start μ) (hfinish : G.finish κ = A.frame.finish μ) :
    RegularFourAnchor κ where
  frame := G
  halfLengths := A.halfLengths
  positive := A.positive
  start_lt := by simpa only [hstart] using A.start_lt
  finish_lt := by simpa only [hfinish] using A.finish_lt
  zero := by rw [controller_eq_of_endpoints hstart hfinish]; exact A.zero
  regular := by rw [controller_eq_of_endpoints hstart hfinish]; exact A.regular

/-- The original coherent realization after a literal endpoint-preserving
lift. This includes inserting arbitrarily many positive dormant readings. -/
theorem realizesR2_of_reembed {m n : ℕ} [NeZero n]
    {μ : ZMod m → ℝ} {κ : ZMod n → ℝ} (A : RegularFourAnchor μ)
    (G : FourActiveSlots.Frame n)
    (hstart : G.start κ = A.frame.start μ) (hfinish : G.finish κ = A.frame.finish μ)
    (hκ : ∀ i, 0 < κ i) : RealizesR2 κ :=
  (A.reembed G hstart hfinish).realizesR2 hκ

/-- Package the physical native slot model as an actual original-word anchor. -/
noncomputable def ofNative {n : ℕ} {κ : ZMod n → ℝ} {p t q h l : ℝ}
    (F : FourActiveSlots.Frame n) {L : Fin 4 → ℝ}
    (hstart : F.start κ = ![1, t, q, l])
    (hfinish : F.finish κ = ![p, q, h, 1])
    (hphysical : NativeOppositePure.NativeLengthPhysical p t q h l L)
    (hzero : NativeOppositePure.nativeLengthController p t q h l L = 0)
    (hsurj : Function.Surjective
      (fderiv ℝ (NativeOppositePure.nativeLengthController p t q h l) L)) :
    RegularFourAnchor κ := by
  rcases hphysical with ⟨hL, h0, hp0, ht1, hq1, hq2, hh2, hl3, h3⟩
  have hfun : F.controller κ = NativeOppositePure.nativeLengthController p t q h l :=
    funext (F.controller_eq_nativeLengthController hstart hfinish)
  refine ⟨F, L, hL, ?_, ?_, ?_, ?_⟩
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
  · rwa [hfun]
  · rwa [hfun]

end RegularFourAnchor

end Gluck.Discrete
