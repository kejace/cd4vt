module

public import Gluck.Discrete.NativeOppositePureDefs

/-!
# Exact native closure for an opposite-pure quadrilateral

The off-zero identity below retains the lifted full-turn defect. Its
correction term is essential before differentiation. No orthogonality
assumption is used.
-/

@[expose] public section

namespace Gluck.Discrete.NativeOppositePure

private theorem sin_pair_phase (a b : ℝ) :
    (Real.sin a : ℂ) + (Real.sin b : ℂ) * unitPhase (a + b) =
      (Real.sin (a + b) : ℂ) * unitPhase b := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, unitPhase_re, unitPhase_im, zero_mul, sub_zero]
    rw [Real.sin_add, Real.cos_add]
    nlinarith [congrArg (fun x : ℝ => Real.sin a * x) (Real.sin_sq_add_cos_sq b)]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, unitPhase_re, unitPhase_im, zero_mul, zero_add]
    ring

private theorem sin_pair_phase_neg (a b : ℝ) :
    (Real.sin a : ℂ) + (Real.sin b : ℂ) * unitPhase (-(a + b)) =
      (Real.sin (a + b) : ℂ) * unitPhase (-b) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, unitPhase_re, unitPhase_im, Real.cos_neg,
      zero_mul, sub_zero]
    rw [Real.sin_add, Real.cos_add]
    nlinarith [congrArg (fun x : ℝ => Real.sin a * x) (Real.sin_sq_add_cos_sq b)]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, unitPhase_re, unitPhase_im, Real.sin_neg,
      zero_mul, zero_add]
    ring

private theorem phase_add_pi (a : ℝ) : unitPhase (a + Real.pi) = -unitPhase a := by
  rw [unitPhase_add, unitPhase_eq_cos_add_sin_mul_I Real.pi]
  simp

/-- Exact off-zero half-closure identity. The last term retains the real
full-turn defect, so this identity can also be differentiated at a zero. -/
theorem nativeHalfClosure_eq (p t q h l α β γ δ : ℝ) :
    nativeHalfClosure p t q h l α β γ δ =
      unitPhase (-β) *
        ((Real.sin (α + β) : ℂ) -
          ((Real.sin (γ + δ) / q : ℝ) : ℂ) * unitPhase (seamLow p t q α β γ δ)) +
      (Real.sin β : ℂ) * unitPhase (-(α + β)) *
        (unitPhase (turnDefect p t q h l α β γ δ) - 1) := by
  have hpair :
      ((Real.sin γ / q : ℝ) : ℂ) * unitPhase (lowTurn p t q α γ) +
        ((Real.sin δ / q : ℝ) : ℂ) * unitPhase (lowTurn p t q α γ + (γ + δ)) =
      ((Real.sin (γ + δ) / q : ℝ) : ℂ) * unitPhase (lowTurn p t q α γ + δ) := by
    calc
      _ = ((Real.sin γ : ℂ) + (Real.sin δ : ℂ) * unitPhase (γ + δ)) *
          unitPhase (lowTurn p t q α γ) / (q : ℂ) := by
            rw [unitPhase_add]
            push_cast
            ring
      _ = (Real.sin (γ + δ) : ℂ) * unitPhase δ *
          unitPhase (lowTurn p t q α γ) / (q : ℂ) := by rw [sin_pair_phase]
      _ = _ := by
        rw [unitPhase_add]
        push_cast
        ring
  have hlast :
      unitPhase (lowTurn p t q α γ + (γ + δ) + highTurn q h l β δ) =
        unitPhase (-(α + β)) * unitPhase (turnDefect p t q h l α β γ δ) := by
    rw [← unitPhase_add]
    have heq : lowTurn p t q α γ + (γ + δ) + highTurn q h l β δ =
        (-(α + β) + turnDefect p t q h l α β γ δ) + 2 * Real.pi := by
      unfold turnDefect
      ring
    rw [heq, unitPhase_add_two_pi]
  have hseam : unitPhase (lowTurn p t q α γ + δ) =
      -(unitPhase (-β) * unitPhase (seamLow p t q α β γ δ)) := by
    rw [← unitPhase_add]
    have heq : lowTurn p t q α γ + δ =
        (-β + seamLow p t q α β γ δ) + Real.pi := by
      unfold seamLow
      ring
    rw [heq, phase_add_pi]
  calc
    _ = (Real.sin α : ℂ) +
        (((Real.sin γ / q : ℝ) : ℂ) * unitPhase (lowTurn p t q α γ) +
          ((Real.sin δ / q : ℝ) : ℂ) * unitPhase (lowTurn p t q α γ + (γ + δ))) +
        (Real.sin β : ℂ) *
          unitPhase (lowTurn p t q α γ + (γ + δ) + highTurn q h l β δ) := by
      unfold nativeHalfClosure
      ring
    _ = _ := by
      rw [hpair, hlast, hseam]
      linear_combination sin_pair_phase_neg α β

private theorem phase_zero : unitPhase 0 = 1 := by simp [unitPhase]

/-- On the principal low-seam branch, the three split equations are exactly
the native vector closure and the lifted full-turn equation. -/
theorem native_zero_iff {p t q h l α β γ δ : ℝ}
    (hr : Real.sin (γ + δ) / q ≠ 0)
    (hlo : -Real.pi < seamLow p t q α β γ δ)
    (hhi : seamLow p t q α β γ δ < Real.pi) :
    (nativeHalfClosure p t q h l α β γ δ = 0 ∧
      turnDefect p t q h l α β γ δ = 0) ↔
    (chord q α β γ δ = 0 ∧ seamLow p t q α β γ δ = 0 ∧
      seamHigh q h l α β γ δ = 0) := by
  constructor
  · rintro ⟨hE, hT⟩
    rw [nativeHalfClosure_eq, hT, phase_zero, sub_self, mul_zero, add_zero] at hE
    have hphase : unitPhase (-β) ≠ 0 := by
      exact Complex.exp_ne_zero _
    have hz := (mul_eq_zero.mp hE).resolve_left hphase
    have him := congrArg Complex.im hz
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, unitPhase_im, zero_mul, add_zero, Complex.zero_im] at him
    have hsin : Real.sin (seamLow p t q α β γ δ) = 0 :=
      (mul_eq_zero.mp (by linarith :
        Real.sin (γ + δ) / q * Real.sin (seamLow p t q α β γ δ) = 0)).resolve_left hr
    have hH : seamLow p t q α β γ δ = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi).mp hsin
    have hre := congrArg Complex.re hz
    rw [hH, phase_zero, mul_one] at hre
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    refine ⟨hre, hH, ?_⟩
    have hs := seamLow_add_seamHigh p t q h l α β γ δ
    rw [hH, hT, zero_add] at hs
    exact hs
  · rintro ⟨hc, hH, hK⟩
    have hT : turnDefect p t q h l α β γ δ = 0 := by
      rw [← seamLow_add_seamHigh, hH, hK, add_zero]
    refine ⟨?_, hT⟩
    rw [nativeHalfClosure_eq, hH, hT, phase_zero, mul_one,
      sub_self, mul_zero, add_zero, ← Complex.ofReal_sub]
    change unitPhase (-β) * (chord q α β γ δ : ℂ) = 0
    rw [hc, Complex.ofReal_zero, mul_zero]

/-- The low seam remains in its unique principal `(-pi,pi)` branch on
acute split angles with nonnegative original low endpoint readings. -/
theorem seamLow_mem_Ioo_of_strictAngles {p t q h α β γ δ : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t) (hq : 0 < q)
    (ha : StrictAngles q h α β γ δ) :
    seamLow p t q α β γ δ ∈ Set.Ioo (-Real.pi) Real.pi := by
  rcases ha with ⟨hα, hβ, hγ, hδ, _⟩
  have hsinα : 0 ≤ Real.sin α :=
    (Real.sin_pos_of_pos_of_lt_pi hα.1 (by linarith [hα.2, Real.pi_pos])).le
  have hsinγ : 0 ≤ Real.sin γ :=
    (Real.sin_pos_of_pos_of_lt_pi hγ.1 (by linarith [hγ.2, Real.pi_pos])).le
  have hA := Real.arcsin_nonneg.mpr (mul_nonneg hp hsinα)
  have hB := Real.arcsin_nonneg.mpr (mul_nonneg (div_nonneg ht hq.le) hsinγ)
  have hA' := Real.arcsin_le_pi_div_two (p * Real.sin α)
  have hB' := Real.arcsin_le_pi_div_two ((t / q) * Real.sin γ)
  unfold seamLow lowTurn angleAtom
  constructor <;> linarith [hβ.1, hβ.2, hδ.1, hδ.2]

/-- Native closure/full turn and the three exact split equations have the
same zeros on the strict acute physical domain. -/
theorem native_zero_iff_of_strictAngles {p t q h l α β γ δ : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t) (hq : 0 < q)
    (ha : StrictAngles q h α β γ δ) :
    (nativeHalfClosure p t q h l α β γ δ = 0 ∧
      turnDefect p t q h l α β γ δ = 0) ↔
    (chord q α β γ δ = 0 ∧ seamLow p t q α β γ δ = 0 ∧
      seamHigh q h l α β γ δ = 0) := by
  have hlow := seamLow_mem_Ioo_of_strictAngles hp ht hq ha
  have hsin : 0 < Real.sin (γ + δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.2.2.1.1, ha.2.2.2.1.1])
      (by linarith [ha.2.2.1.2, ha.2.2.2.1.2])
  exact native_zero_iff (ne_of_gt (div_pos hsin hq)) hlow.1 hlow.2

/-- The real target transformation appearing in the derivative of
`nativeHalfClosure_eq` at a zero. Input coordinates are `(dM,dH,dK)`.
The native correction coefficient is `I * sin β * unitPhase (-(α+β))`. -/
noncomputable def closureTargetLinearMap (β r : ℝ) (c : ℂ) :
    (Fin 3 → ℝ) →ₗ[ℝ] ℂ × ℝ where
  toFun x :=
    (unitPhase (-β) * ((x 0 : ℂ) - Complex.I * (r : ℂ) * (x 1 : ℂ)) +
      c * ((x 1 + x 2 : ℝ) : ℂ), x 1 + x 2)
  map_add' x y := by
    apply Prod.ext <;> dsimp
    · push_cast
      ring
    · ring
  map_smul' a x := by
    apply Prod.ext <;> dsimp
    · simp only [Complex.ofReal_mul, Complex.ofReal_add]
      ring
    · ring

/-- The target differential loses no equation when its common chord radius
is nonzero. This is an exact linear-algebra statement, not a rank assumption. -/
theorem closureTargetLinearMap_eq_zero_iff {β r : ℝ} (hr : r ≠ 0)
    (c : ℂ) (x : Fin 3 → ℝ) :
    closureTargetLinearMap β r c x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have ht : x 1 + x 2 = 0 := congrArg Prod.snd hx
    have hz := congrArg Prod.fst hx
    change unitPhase (-β) * ((x 0 : ℂ) - Complex.I * (r : ℂ) * (x 1 : ℂ)) +
      c * ((x 1 + x 2 : ℝ) : ℂ) = 0 at hz
    rw [ht, Complex.ofReal_zero, mul_zero, add_zero] at hz
    have hphase : unitPhase (-β) ≠ 0 := Complex.exp_ne_zero _
    have he := (mul_eq_zero.mp hz).resolve_left hphase
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, one_mul, sub_zero, mul_zero, Complex.zero_re] at hre
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      zero_mul, one_mul, sub_zero, mul_zero,
      Complex.zero_im] at him
    have hx1 : x 1 = 0 := (mul_eq_zero.mp (by linarith : r * x 1 = 0)).resolve_left hr
    have hx2 : x 2 = 0 := by linarith
    funext i
    fin_cases i
    · exact hre
    · exact hx1
    · exact hx2
  · rintro rfl
    exact map_zero _

/-- Injectivity of the exact native target differential. -/
theorem closureTargetLinearMap_injective {β r : ℝ} (hr : r ≠ 0) (c : ℂ) :
    Function.Injective (closureTargetLinearMap β r c) := by
  intro x y hxy
  have hz : closureTargetLinearMap β r c (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp ((closureTargetLinearMap_eq_zero_iff hr c (x - y)).mp hz)

/-- Explicit inversion of the native target differential. -/
theorem closureTargetLinearMap_surjective {β r : ℝ} (hr : r ≠ 0) (c : ℂ) :
    Function.Surjective (closureTargetLinearMap β r c) := by
  rintro ⟨z, s⟩
  let v : ℂ := unitPhase β * (z - c * (s : ℂ))
  let x : Fin 3 → ℝ := ![v.re, -v.im / r, s + v.im / r]
  have hs : x 1 + x 2 = s := by
    dsimp [x]
    ring
  have hrx : r * (-v.im / r) = -v.im := by
    field_simp
  have hv : (x 0 : ℂ) - Complex.I * (r : ℂ) * (x 1 : ℂ) = v := by
    change (v.re : ℂ) - Complex.I * (r : ℂ) * ((-v.im / r : ℝ) : ℂ) = v
    calc
      _ = (v.re : ℂ) - Complex.I * ((r * (-v.im / r) : ℝ) : ℂ) := by
        push_cast
        ring
      _ = (v.re : ℂ) + (v.im : ℂ) * Complex.I := by
        rw [hrx]
        push_cast
        ring
      _ = v := Complex.re_add_im v
  have hphase : unitPhase (-β) * unitPhase β = 1 := by
    rw [← unitPhase_add]
    simp [phase_zero]
  refine ⟨x, ?_⟩
  apply Prod.ext
  · change unitPhase (-β) * ((x 0 : ℂ) - Complex.I * (r : ℂ) * (x 1 : ℂ)) +
      c * ((x 1 + x 2 : ℝ) : ℂ) = z
    rw [hv, hs]
    dsimp [v]
    rw [← mul_assoc, hphase, one_mul]
    ring
  · exact hs

end Gluck.Discrete.NativeOppositePure
