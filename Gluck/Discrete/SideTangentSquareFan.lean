module

public import Gluck.Discrete.SideTangentFan

/-!
# A finite tangential fan approaching the labelled square

For four selected labels `0 < p < q < r < n`, perturb the four repeated normal
angles towards the regular n-gon angles. Every positive perturbation has strict
cyclic normal order and gaps below π. The original vertex labels are retained.
-/

@[expose] public section

open Set Filter
open scoped Topology InnerProductSpace BigOperators

namespace Gluck.Discrete.SideTangent

/-- The incoming normal levels for the four square sides. -/
def squareLevel (p q r k : ℕ) : ℕ :=
  if k = 0 then 0 else if k ≤ p then 1 else if k ≤ q then 2 else if k ≤ r then 3 else 4

lemma squareLevel_monotone (p q r : ℕ) : Monotone (squareLevel p q r) := by
  intro i j hij
  unfold squareLevel
  split_ifs <;> omega

lemma squareLevel_step_le {p q r : ℕ} (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (k : ℕ) : squareLevel p q r (k + 1) ≤ squareLevel p q r k + 1 := by
  unfold squareLevel
  split_ifs <;> omega

/-- Blend repeated square normals with a strictly ordered regular fan. -/
noncomputable def fanAngle (n p q r : ℕ) (η : ℝ) (k : ℕ) : ℝ :=
  (1 - η) * (squareLevel p q r k : ℝ) * (Real.pi / 2) +
    η * (2 * Real.pi * k / n)

lemma fanAngle_zero (n p q r : ℕ) (η : ℝ) : fanAngle n p q r η 0 = 0 := by
  simp [fanAngle, squareLevel]

lemma fanAngle_end {n p q r : ℕ} (hn : 0 < n) (hr : r < n) (hpq : p < q)
    (hqr : q < r) (η : ℝ) : fanAngle n p q r η n = 2 * Real.pi := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [fanAngle, squareLevel, hn.ne', show ¬n ≤ p by omega,
    show ¬n ≤ q by omega, show ¬n ≤ r by omega, hn']
  ring

lemma fanAngle_strictMono {n p q r : ℕ} (hn : 0 < n) {η : ℝ}
    (hη : 0 < η) (hη₁ : η ≤ 1) : StrictMono (fanAngle n p q r η) := by
  intro i j hij
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hij' : (i : ℝ) < j := by exact_mod_cast hij
  have hl : (squareLevel p q r i : ℝ) ≤ squareLevel p q r j := by
    exact_mod_cast squareLevel_monotone p q r hij.le
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hη₁)) (by positivity : 0 ≤ Real.pi / 2)
  have hg := mul_lt_mul_of_pos_left (div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_left hij' (by positivity : 0 < 2 * Real.pi)) hn') hη
  exact add_lt_add_of_le_of_lt hb hg

lemma fanAngle_step_lt_pi {n p q r : ℕ} (hn : 4 ≤ n) (hp : 0 < p)
    (hpq : p < q) (hqr : q < r) {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1) (k : ℕ) :
    fanAngle n p q r η (k + 1) - fanAngle n p q r η k < Real.pi := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn₄ : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : (squareLevel p q r (k + 1) : ℝ) - squareLevel p q r k ≤ 1 := by
    have h := squareLevel_step_le hp hpq hqr k
    exact_mod_cast (show (squareLevel p q r (k + 1) : ℤ) - squareLevel p q r k ≤ 1 by omega)
  have hb : ((squareLevel p q r (k + 1) : ℝ) - squareLevel p q r k) *
      (Real.pi / 2) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hg : 2 * Real.pi / n ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hn').mpr
    nlinarith [Real.pi_pos]
  have he : fanAngle n p q r η (k + 1) - fanAngle n p q r η k =
      (1 - η) * (((squareLevel p q r (k + 1) : ℝ) - squareLevel p q r k) *
        (Real.pi / 2)) + η * (2 * Real.pi / n) := by
    simp only [fanAngle, Nat.cast_add, Nat.cast_one]
    ring
  rw [he]
  have hbound := add_le_add (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hη₁))
    (mul_le_mul_of_nonneg_left hg hη)
  nlinarith [Real.pi_pos]

/-- The square corner or side contact approached by each original vertex label. -/
def squareTag (p q r k : ℕ) : Fin 8 :=
  if k = 0 then 0 else if k = p then 1 else if k = q then 2 else if k = r then 3
  else if k < p then 4 else if k < q then 5 else if k < r then 6 else 7

/-- Actual vertices formed by consecutive tangent lines in the perturbed fan. -/
noncomputable def fanVertex (n p q r : ℕ) (η : ℝ) (k : ℕ) : ℂ :=
  tangentIntersection (normal (fanAngle n p q r η k))
    (normal (fanAngle n p q r η (k + 1)))

lemma squareLevel_pair {p q r : ℕ} (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (k : ℕ) :
    (squareLevel p q r k, squareLevel p q r (k + 1)) =
      (![0, 1, 2, 3, 1, 2, 3, 4] (squareTag p q r k),
        ![1, 2, 3, 4, 1, 2, 3, 4] (squareTag p q r k)) := by
  unfold squareTag
  split_ifs <;> norm_num only [squareLevel, Matrix.cons_val, Prod.mk.injEq] <;>
    (try split_ifs) <;> norm_num <;> omega

lemma tangentIntersection_quarter_pair (k : Fin 8) :
    tangentIntersection (normal ((![0, 1, 2, 3, 1, 2, 3, 4] k : ℝ) * (Real.pi / 2)))
      (normal ((![1, 2, 3, 4, 1, 2, 3, 4] k : ℝ) * (Real.pi / 2))) = squareSite k := by
  fin_cases k <;> apply Complex.ext <;>
    simp only [tangentIntersection, Complex.smul_re, Complex.smul_im]
  all_goals norm_num [squareSite, Complex.inner, show 3 * (Real.pi / 2) =
    Real.pi + Real.pi / 2 by ring, show 2 * (Real.pi / 2) = Real.pi by ring,
    show 4 * (Real.pi / 2) = 2 * Real.pi by ring, Real.cos_add, Real.sin_add]

lemma fanVertex_zero {p q r : ℕ} (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (n k : ℕ) : fanVertex n p q r 0 k = squareSite (squareTag p q r k) := by
  have he := squareLevel_pair hp hpq hqr k
  have he₁ : squareLevel p q r k = ![0, 1, 2, 3, 1, 2, 3, 4] (squareTag p q r k) :=
    congrArg Prod.fst he
  have he₂ : squareLevel p q r (k + 1) = ![1, 2, 3, 4, 1, 2, 3, 4] (squareTag p q r k) :=
    congrArg Prod.snd he
  simp only [fanVertex, fanAngle, sub_zero, one_mul, zero_mul, add_zero, he₁, he₂]
  convert tangentIntersection_quarter_pair (squareTag p q r k) using 1
  generalize squareTag p q r k = t
  fin_cases t <;> norm_num

lemma continuous_fanAngle (n p q r k : ℕ) : Continuous (fun η ↦ fanAngle n p q r η k) := by
  unfold fanAngle
  fun_prop

lemma continuousAt_fanVertex_zero {n p q r : ℕ} (hn : 4 ≤ n) (hp : 0 < p)
    (hpq : p < q) (hqr : q < r) (k : ℕ) :
    ContinuousAt (fun η ↦ fanVertex n p q r η k) 0 := by
  have hg := fanAngle_step_lt_pi hn hp hpq hqr (η := 0) le_rfl zero_le_one k
  have ho : fanAngle n p q r 0 k ≤ fanAngle n p q r 0 (k + 1) := by
    simp only [fanAngle, sub_zero, one_mul, zero_mul, add_zero]
    have hl : (squareLevel p q r k : ℝ) ≤ squareLevel p q r (k + 1) := by
      exact_mod_cast squareLevel_monotone p q r (Nat.le_add_right k 1)
    exact mul_le_mul_of_nonneg_right hl (by positivity)
  have hc : ContinuousAt (fun η : ℝ ↦
      (normal (fanAngle n p q r η k), normal (fanAngle n p q r η (k + 1)))) 0 :=
    ((continuous_normal.comp (continuous_fanAngle n p q r k)).prodMk
      (continuous_normal.comp (continuous_fanAngle n p q r (k + 1)))).continuousAt
  exact ContinuousAt.comp (f := fun η : ℝ ↦
    (normal (fanAngle n p q r η k), normal (fanAngle n p q r η (k + 1)))) (x := 0)
    (continuousAt_tangentIntersection (normal_denominator_pos ho hg).ne') hc

lemma squareTag_corners {p q r : ℕ} (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (k : ℕ) :
    (squareTag p q r k = 0 ↔ k = 0) ∧ (squareTag p q r k = 1 ↔ k = p) ∧
      (squareTag p q r k = 2 ↔ k = q) ∧ (squareTag p q r k = 3 ↔ k = r) := by
  unfold squareTag
  split_ifs <;> norm_num <;> omega

lemma siteCoefficient_eq_of_fiber {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (tag : ι → Fin 8) (k : Fin 8) (i : ι) (hi : ∀ j, tag j = k ↔ j = i) :
    siteCoefficient c tag k = c i := by
  classical
  simp only [siteCoefficient, hi, Finset.sum_filter]
  simp

/-- Every nonincident tangent line strictly supports each finite perturbed vertex,
including the cyclic seam. Normals here are indexed by the incoming edge. -/
lemma fanVertex_strict_support {n p q r : ℕ} [NeZero n] (hn : 4 ≤ n) (hp : 0 < p)
    (hpq : p < q) (hqr : q < r) (hr : r < n) {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1)
    (i j : Fin n) (hji : j ≠ i) (hnext : j ≠ i + 1) :
    ⟪normal (fanAngle n p q r η j), fanVertex n p q r η i⟫_ℝ < 1 := by
  have hn₀ : 0 < n := by omega
  have h_one : (1 : Fin n).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hm := fanAngle_strictMono (p := p) (q := q) (r := r) hn₀ hη hη₁
  have hg := fanAngle_step_lt_pi hn hp hpq hqr hη.le hη₁ i
  have hend := fanAngle_end hn₀ hr hpq hqr η
  have hij : (j : ℕ) ≠ i := by exact fun he ↦ hji (Fin.ext he)
  have hijnext : (j : ℕ) ≠ (i : ℕ) + 1 := by
    intro he
    apply hnext
    apply Fin.ext
    rw [Fin.val_add, h_one, Nat.mod_eq_of_lt (by omega : (i : ℕ) + 1 < n)]
    exact he
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · apply normal_support_lt_of_wrapped (hm hlt) (hm (Nat.lt_succ_self _)) hg
    have hib : fanAngle n p q r η (i + 1) ≤ 2 * Real.pi := by
      rw [← hend]
      exact hm.monotone (by omega)
    by_cases hj₀ : (j : ℕ) = 0
    · have hil : (i : ℕ) + 1 < n := by
        by_contra h
        apply hnext
        apply Fin.ext
        rw [Fin.val_add, h_one, show (i : ℕ) + 1 = n by omega, Nat.mod_self]
        exact hj₀
      have hiθ := hm hil
      simpa only [hj₀, fanAngle_zero, zero_add, hend] using hiθ
    · have hjθ := hm (show 0 < (j : ℕ) by omega)
      rw [fanAngle_zero] at hjθ
      linarith
  · apply normal_support_lt_of_ordered (hm (Nat.lt_succ_self _)) hg (hm (by omega))
    have hjθ := hm j.isLt
    have hiθ := hm.monotone (Nat.zero_le (i : ℕ))
    rw [hend] at hjθ
    rw [fanAngle_zero] at hiθ
    linarith

/-- A positive finite perturbation has exact projective balance, with the original
coefficient at every label. The only sign conditions are the four chosen witnesses. -/
theorem exists_balanced_squareFan {n p q r : ℕ} (hn : 4 ≤ n) (hp : 0 < p)
    (hpq : p < q) (hqr : q < r) (hr : r < n) (c : Fin n → ℝ)
    (hsum : ∑ i, c i = 0)
    (h₀ : 0 < c ⟨0, by omega⟩) (h₁ : c ⟨p, by omega⟩ < 0)
    (h₂ : 0 < c ⟨q, by omega⟩) (h₃ : c ⟨r, hr⟩ < 0) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ a : ℂ, ∃ σ : ℝ,
      ‖a‖ < 1 ∧ 0 < σ ∧ σ ^ 2 + ‖a‖ ^ 2 = 1 ∧
        (∀ i : Fin n, 0 < ProjectiveBall.denominator a (fanVertex n p q r η i)) ∧
        ∑ i : Fin n, c i • ProjectiveBall.transform a σ (fanVertex n p q r η i) = 0 := by
  let tag : Fin n → Fin 8 := fun i ↦ squareTag p q r i
  have ht₀ : siteCoefficient c tag 0 = c ⟨0, by omega⟩ := by
    apply siteCoefficient_eq_of_fiber
    intro i
    simpa only [Fin.ext_iff] using (squareTag_corners hp hpq hqr i).1
  have ht₁ : siteCoefficient c tag 1 = c ⟨p, by omega⟩ := by
    apply siteCoefficient_eq_of_fiber
    intro i
    simpa only [Fin.ext_iff] using (squareTag_corners hp hpq hqr i).2.1
  have ht₂ : siteCoefficient c tag 2 = c ⟨q, by omega⟩ := by
    apply siteCoefficient_eq_of_fiber
    intro i
    simpa only [Fin.ext_iff] using (squareTag_corners hp hpq hqr i).2.2.1
  have ht₃ : siteCoefficient c tag 3 = c ⟨r, hr⟩ := by
    apply siteCoefficient_eq_of_fiber
    intro i
    simpa only [Fin.ext_iff] using (squareTag_corners hp hpq hqr i).2.2.2
  have hb := eventually_balance_near_square c tag hsum
    (ht₀.symm ▸ h₀) (ht₁.symm ▸ h₁) (ht₂.symm ▸ h₂) (ht₃.symm ▸ h₃)
  have hc : Tendsto (fun η : ℝ ↦ fun i : Fin n ↦ fanVertex n p q r η i)
      (𝓝 0) (𝓝 (fun i ↦ squareSite (tag i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hi := continuousAt_fanVertex_zero hn hp hpq hqr i
    rw [ContinuousAt, fanVertex_zero hp hpq hqr] at hi
    exact hi
  have hbη := (hc.eventually hb).filter_mono
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hη₀ : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  have hη₁ : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨η, hη₀, hη₁, hbalance⟩ := (hη₀.and (hη₁.and hbη)).exists
  exact ⟨η, hη₀, hη₁, hbalance⟩

end Gluck.Discrete.SideTangent
