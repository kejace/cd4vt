module

public import Gluck.Discrete.NativeFirstPairInterior
public import Gluck.Discrete.NativeFirstPairWall
public import Gluck.Discrete.NativeFirstPairFlag
public import Gluck.Discrete.NativeFirstPairBoundaryDerivative
public import Gluck.Discrete.NativeOppositePureClosure

/-!
# Assembly of the physical first-pair construction

The wall curve is the boundary restriction of the explicit interior chart.
The original principal-arcsine flag supplies the starting physical bounds
and the weak negative sign. The first physical exit supplies a positive
endpoint while still strictly inside the original incidence wall. The
proved inward derivative then produces a strict root, including equality
in the original flag. There is no added existence or continuation premise.
-/

@[expose] public section

open Set

namespace Gluck.Discrete.NativeOppositePure

theorem interiorD_wall {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    interiorD p t q (Real.pi / 2) γ = wallD p t q γ := by
  unfold interiorD
  rw [Real.cos_sub_pi_div_two]
  exact (wallD_eq_trig hp hp1 ht hpt hpq hγ0 hγ1).symm

theorem interiorN_wall {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    interiorN p t q (Real.pi / 2) γ = wallN p t q γ := by
  unfold interiorN
  rw [Real.sin_sub_pi_div_two, wallN_eq_trig hp hp1 ht hpt hpq hγ0 hγ1]
  ring

theorem interiorDelta_wall {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    interiorDelta p t q (Real.pi / 2) γ = wallDelta p t q γ := by
  unfold interiorDelta wallDelta
  rw [interiorD_wall hp hp1 ht hpt hpq hγ0 hγ1,
    interiorN_wall hp hp1 ht hpt hpq hγ0 hγ1]

theorem interiorBeta_wall {p t q γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    interiorBeta p t q (Real.pi / 2) γ = wallBeta p t q γ := by
  unfold interiorBeta
  rw [interiorDelta_wall hp hp1 ht hpt hpq hγ0 hγ1]
  simp only [wallBeta, lowTurn, angleAtom, Real.sin_pi_div_two, mul_one]
  ring

theorem interiorHigh_wall {p t q h l γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    interiorHigh p t q h l (Real.pi / 2) γ =
      seamHigh q h l (Real.pi / 2) (wallBeta p t q γ) γ (wallDelta p t q γ) := by
  unfold interiorHigh
  rw [interiorDelta_wall hp hp1 ht hpt hpq hγ0 hγ1,
    interiorBeta_wall hp hp1 ht hpt hpq hγ0 hγ1]

theorem interiorPhysical_wall {p t q h γ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (hpt : p * t < 1) (hpq : 1 < p * q)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2)
    (hwall : (h / q) * Real.sin (wallDelta p t q γ) < 1) :
    InteriorPhysical p t q h (Real.pi / 2) γ := by
  unfold InteriorPhysical
  rw [interiorD_wall hp hp1 ht hpt hpq hγ0 hγ1,
    interiorN_wall hp hp1 ht hpt hpq hγ0 hγ1,
    interiorDelta_wall hp hp1 ht hpt hpq hγ0 hγ1,
    interiorBeta_wall hp hp1 ht hpt hpq hγ0 hγ1]
  exact ⟨wallD_pos hp hp1 ht hpt hpq hγ0 hγ1,
    wallN_pos hp hp1 ht hpt hpq hγ0 hγ1,
    ⟨wallBeta_pos hp hp1 ht hpt hpq hγ0 hγ1,
      wallBeta_lt_pi_div_two hp hp1 ht hpt hpq hγ0 hγ1⟩, hwall⟩

/-- The original flag produces the entire compact physical strip needed
by the inward intermediate-value argument. No sign or continuation
hypothesis is added to the original curvature assumptions. -/
theorem exists_physical_boundary_strip_of_firstPairFlag_of_product_lt_one {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (hpt : p * t < 1)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l) :
    ∃ γhi ∈ Ioo 0 (Real.pi / 2),
      (∀ γ ∈ Icc 0 γhi, InteriorPhysical p t q h (Real.pi / 2) γ) ∧
      interiorHigh p t q h l (Real.pi / 2) 0 ≤ 0 ∧
      0 < interiorHigh p t q h l (Real.pi / 2) γhi := by
  have hpq := firstPairFlag_one_lt_mul hp hp1 hl hl1 hq hqh hflag
  have hsq := firstPairFlag_square_bound hp hp1 hl hl1 hq hqh hflag
  have hh : 1 < h := hq.trans hqh
  have hinit := wall_initial_hwall (t := t) hp hp1 hpq hh hl hl1 hsq
  obtain ⟨γhi, hhi, hwall, hpos⟩ :=
    exists_wall_positive_endpoint hp hp1 ht hpt hpq (by linarith) hl hinit
  refine ⟨γhi, hhi, ?_, ?_, ?_⟩
  · intro γ hγ
    exact interiorPhysical_wall hp hp1 ht hpt hpq hγ.1 (hγ.2.trans hhi.2.le) (hwall γ hγ)
  · rw [interiorHigh_wall hp hp1 ht hpt hpq (le_refl 0) (by positivity)]
    exact wall_initial_high_nonpos hp hp1 hpq (by linarith) hl hsq
  · rwa [interiorHigh_wall hp hp1 ht hpt hpq hhi.1.le hhi.2.le]

/-- A nonnegative original first-pair flag produces a strict interior zero
of the three exact seam/chord equations under the more general bound `p * t < 1`.
Equality of the flag is included. -/
theorem exists_strict_root_of_firstPairFlag_of_product_lt_one {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (hpt : p * t < 1)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l) :
    ∃ α β γ δ : ℝ, StrictAngles q h α β γ δ ∧
      seamLow p t q α β γ δ = 0 ∧ seamHigh q h l α β γ δ = 0 ∧
      chord q α β γ δ = 0 := by
  obtain ⟨γhi, hhi, hphysical, hleft, hright⟩ :=
    exists_physical_boundary_strip_of_firstPairFlag_of_product_lt_one
      hp hp1 ht hpt hl hl1 hq hqh hflag
  have hq0 : 0 < q := zero_lt_one.trans hq
  apply exists_strict_root_of_interior_strip (ne_of_gt hq0) hhi hphysical hleft hright
  intro _
  exact exists_pos_derivative_interiorHigh_boundary hp hp1 hq0 hqh hl hl1
    (hphysical 0 ⟨le_refl 0, hhi.1.le⟩)

/-- The first-pair construction produces exact original native closure
and one lifted full turn, with every angle and high incidence strictly
physical. Arbitrary-word embedding and opening are separate theorems. -/
theorem exists_native_zero_of_firstPairFlag_of_product_lt_one {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (hpt : p * t < 1)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l) :
    ∃ α β γ δ : ℝ, StrictAngles q h α β γ δ ∧
      nativeHalfClosure p t q h l α β γ δ = 0 ∧
      turnDefect p t q h l α β γ δ = 0 := by
  obtain ⟨α, β, γ, δ, ha, hlo, hhi, hc⟩ :=
    exists_strict_root_of_firstPairFlag_of_product_lt_one hp hp1 ht hpt hl hl1 hq hqh hflag
  exact ⟨α, β, γ, δ, ha,
    (native_zero_iff_of_strictAngles hp.le ht.le (zero_lt_one.trans hq) ha).mpr
      ⟨hc, hlo, hhi⟩⟩

/-- The originally missing reversed-entry case, with its original strict
ordering and including a zero flag. -/
theorem exists_native_zero_of_firstPairFlag {p t q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (htp : t < p)
    (hl : 0 < l) (hl1 : l < 1) (hq : 1 < q) (hqh : q < h)
    (hflag : 0 ≤ firstPairFlag p q h l) :
    ∃ α β γ δ : ℝ, StrictAngles q h α β γ δ ∧
      nativeHalfClosure p t q h l α β γ δ = 0 ∧
      turnDefect p t q h l α β γ δ = 0 := by
  have hpt : p * t < 1 := by
    have hmul := mul_lt_mul_of_pos_left htp hp
    nlinarith
  exact exists_native_zero_of_firstPairFlag_of_product_lt_one hp hp1 ht hpt
    hl hl1 hq hqh hflag

/-- The same physical construction includes the matched-low case `t = p`;
no limiting argument or separate scalar producer is required. -/
theorem exists_native_zero_of_firstPairFlag_matched {p q h l : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hl : 0 < l) (hl1 : l < 1)
    (hq : 1 < q) (hqh : q < h) (hflag : 0 ≤ firstPairFlag p q h l) :
    ∃ α β γ δ : ℝ, StrictAngles q h α β γ δ ∧
      nativeHalfClosure p p q h l α β γ δ = 0 ∧
      turnDefect p p q h l α β γ δ = 0 :=
  exists_native_zero_of_firstPairFlag_of_product_lt_one hp hp1 hp (by nlinarith)
    hl hl1 hq hqh hflag

end Gluck.Discrete.NativeOppositePure
