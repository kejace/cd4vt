/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.ClosingCell
public import Gluck.Discrete.CollaredConverse

/-!
# Closedness of uniformly interior realizations

A family of closed configurations whose edge lengths remain in one compact
coordinate box and whose moderate-arc walls retain one positive margin has a
closed profile projection. Consequently, realizability passes to a profile
limit whenever these two quantitative margins are uniform.
-/

@[expose] public section

namespace Gluck.Discrete

open Set

variable {n : ℕ}

/-- The total turning is jointly continuous in the curvature and length profiles. -/
theorem continuous_turningSum [NeZero n] :
    Continuous fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => turningSum p.1 p.2 := by
  unfold turningSum turningAngle
  simp only [tK_zero]
  fun_prop

/-- The joint closure-and-turn residual is continuous. -/
theorem continuous_closureMapR3 [NeZero n] :
    Continuous (@closureMapR3 n _) := by
  unfold closureMapR3
  exact continuous_closureGap.prodMk (continuous_turningSum.sub continuous_const)

/-- Vanishing of the joint residual is exactly closure with total turning `2π`. -/
theorem closureMapR3_eq_zero_iff [NeZero n] (kappa ell : ZMod n → ℝ) :
    closureMapR3 (kappa, ell) = 0 ↔
      closureGap kappa ell = 0 ∧ turningSum kappa ell = 2 * Real.pi := by
  constructor
  · intro h
    have hclose := congrArg Prod.fst h
    have hturn := congrArg Prod.snd h
    simp only [closureMapR3, Prod.fst_zero] at hclose
    simp only [closureMapR3, Prod.snd_zero] at hturn
    exact ⟨hclose, by linarith⟩
  · rintro ⟨hclose, hturn⟩
    apply Prod.ext
    · exact hclose
    · simp only [closureMapR3, Prod.snd_zero]
      linarith

def uniformWallCarrier (K : Set (ZMod n → ℝ)) (eta : ℝ) :
    Set ((ZMod n → ℝ) × K) :=
  {p | ∀ i, |p.1 i| * (p.2.1 (i - 1) / 2) ≤ 1 - eta ∧
    |p.1 i| * (p.2.1 i / 2) ≤ 1 - eta}

def closedRealizationCarrier [NeZero n] (K : Set (ZMod n → ℝ)) (eta : ℝ) :
    Set ((ZMod n → ℝ) × K) :=
  uniformWallCarrier K eta ∩ {p | closureMapR3 (p.1, p.2.1) = 0}

private lemma isClosed_uniform_wall_left_aux (K : Set (ZMod n → ℝ)) (eta : ℝ)
    (i : ZMod n) :
    IsClosed {p : (ZMod n → ℝ) × K |
      |p.1 i| * (p.2.1 (i - 1) / 2) ≤ 1 - eta} := by
  have hkappa : Continuous fun p : (ZMod n → ℝ) × K => |p.1 i| :=
    ((continuous_apply i).comp continuous_fst).abs
  have hell : Continuous fun p : (ZMod n → ℝ) × K => p.2.1 (i - 1) :=
    (continuous_apply (i - 1)).comp (continuous_subtype_val.comp continuous_snd)
  exact isClosed_le (hkappa.mul (hell.div_const 2)) continuous_const

private lemma isClosed_uniform_wall_right_aux (K : Set (ZMod n → ℝ)) (eta : ℝ)
    (i : ZMod n) :
    IsClosed {p : (ZMod n → ℝ) × K | |p.1 i| * (p.2.1 i / 2) ≤ 1 - eta} := by
  have hkappa : Continuous fun p : (ZMod n → ℝ) × K => |p.1 i| :=
    ((continuous_apply i).comp continuous_fst).abs
  have hell : Continuous fun p : (ZMod n → ℝ) × K => p.2.1 i :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  exact isClosed_le (hkappa.mul (hell.div_const 2)) continuous_const

private lemma isClosed_uniform_wall_carrier_aux (K : Set (ZMod n → ℝ)) (eta : ℝ) :
    IsClosed (uniformWallCarrier K eta) := by
  rw [uniformWallCarrier, Set.setOf_forall]
  apply isClosed_iInter
  intro i
  rw [Set.setOf_and]
  exact (isClosed_uniform_wall_left_aux K eta i).inter
    (isClosed_uniform_wall_right_aux K eta i)

private lemma isClosed_closed_realization_carrier_aux [NeZero n]
    (K : Set (ZMod n → ℝ)) (eta : ℝ) :
    IsClosed (closedRealizationCarrier K eta) := by
  have hpair : Continuous (fun p : (ZMod n → ℝ) × K => (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hclosed : IsClosed
      {p : (ZMod n → ℝ) × K | closureMapR3 (p.1, p.2.1) = 0} :=
    isClosed_eq (continuous_closureMapR3.comp hpair) continuous_const
  exact (isClosed_uniform_wall_carrier_aux K eta).inter hclosed

private lemma realizesR2_of_uniform_margin_certificate_aux [NeZero n]
    {kappa ell : ZMod n → ℝ} {a eta : ℝ} (hn : 3 ≤ n)
    (hkappa : ∀ i, 0 < kappa i) (ha : 0 < a) (heta : 0 < eta)
    (hlower : ∀ i, a ≤ ell i)
    (hwalls : ∀ i, |kappa i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
      |kappa i| * (ell i / 2) ≤ 1 - eta)
    (hclose : closureGap kappa ell = 0)
    (hturn : turningSum kappa ell = 2 * Real.pi) :
    RealizesR2 kappa := by
  have hmoderate : ModerateArc 0 kappa ell := moderateArc_zero_iff.mpr fun i =>
    ⟨ha.trans_le (hlower i), (hwalls i).1.trans_lt (sub_lt_self 1 heta),
      (hwalls i).2.trans_lt (sub_lt_self 1 heta)⟩
  exact ⟨ell, hmoderate, hclose, hturn,
    isSimplePolygon_of_turningPositive hn hmoderate hkappa hclose hturn⟩

/-- Uniform positive edge and wall margins make realizability pass to a profile limit. -/
theorem realizesR2_of_mem_closure_uniform_margin [NeZero n]
    {S : Set (ZMod n → ℝ)} {kappa : ZMod n → ℝ} {a b eta : ℝ}
    (hn : 3 ≤ n) (hkappa : ∀ i, 0 < kappa i) (ha : 0 < a) (heta : 0 < eta)
    (hkappaS : kappa ∈ closure S)
    (hS : ∀ kappa' ∈ S, ∃ ell : ZMod n → ℝ,
      (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
      (∀ i, |kappa' i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
        |kappa' i| * (ell i / 2) ≤ 1 - eta) ∧
      closureGap kappa' ell = 0 ∧ turningSum kappa' ell = 2 * Real.pi) :
    RealizesR2 kappa := by
  let K : Set (ZMod n → ℝ) := Set.univ.pi fun _ => Set.Icc a b
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C := closedRealizationCarrier K eta
  have hC : IsClosed C := isClosed_closed_realization_carrier_aux K eta
  have hproj : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
  have hsub : S ⊆ Prod.fst '' C := by
    intro kappa' hkappa'
    obtain ⟨ell, hbounds, hwalls, hclose, hturn⟩ := hS kappa' hkappa'
    let ellK : K := ⟨ell, fun i _ => hbounds i⟩
    refine ⟨(kappa', ellK), ⟨hwalls, ?_⟩, rfl⟩
    exact (closureMapR3_eq_zero_iff kappa' ell).2 ⟨hclose, hturn⟩
  obtain ⟨⟨kappa', ell, hellK⟩, hcert, heq⟩ :=
    closure_minimal hsub hproj hkappaS
  change kappa' = kappa at heq
  obtain ⟨hwalls, hresidual⟩ := hcert
  change ∀ i, |kappa' i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
    |kappa' i| * (ell i / 2) ≤ 1 - eta at hwalls
  have hwalls' : ∀ i, |kappa i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
      |kappa i| * (ell i / 2) ≤ 1 - eta := by
    simpa only [heq] using hwalls
  obtain ⟨hclose, hturn⟩ := (closureMapR3_eq_zero_iff kappa' ell).1 hresidual
  exact realizesR2_of_uniform_margin_certificate_aux hn hkappa ha heta
    (fun i => (hellK i (Set.mem_univ i)).1) hwalls'
    (by simpa only [heq] using hclose) (by simpa only [heq] using hturn)

end Gluck.Discrete
