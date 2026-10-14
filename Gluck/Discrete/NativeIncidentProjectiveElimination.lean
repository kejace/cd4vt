import Gluck.Discrete.NativeIncidentProjectivePolynomial

/-!
# Exact elimination of the one-sided physical projective chamber

The two turn equations are the original denominator-cleared tangent-addition
equations. Together with the original affine relation, they force the
quadratic branch and its physical interval, where the sign theorem gives a
contradiction. No resultant or external solver is trusted by this proof.
-/

namespace Gluck.Discrete.NativeIncidentProjective

def turnOne (p q B r k : ℝ) : ℝ :=
  q * (p - B) * (p * (1 - 2 * r) + (1 - 2 * k)) -
    (p + 1) * (q ^ 2 - p * B * (1 - 2 * r) * (1 - 2 * k))

def turnTwo (p q B r k T : ℝ) : ℝ :=
  (p * B - q ^ 2) * T * (T - 2 * k + p * (T - 2 * r)) -
    q * (p + 1) * (B * T ^ 2 - p * (T - 2 * k) * (T - 2 * r))

def affineRelation (p q r k T : ℝ) : ℝ :=
  -(p + 1) * (p - q) * (1 + T) + 2 * (p ^ 2 - q) * k -
    2 * p * (q - 1) * r

def projectiveD0 (p q r : ℝ) : ℝ := p * (p + 1) * r - (p ^ 2 - q)

def projectiveN (p q r : ℝ) : ℝ := (p + 1) * (p - q) + 2 * p * (q - 1) * r

def projectiveH (p q r k : ℝ) : ℝ := 2 * k * projectiveD0 p q r + projectiveN p q r

private def coeffOne (p q r k : ℝ) : ℝ :=
  -q * (p * (1 - 2 * r) + (1 - 2 * k)) +
    (p + 1) * p * (1 - 2 * r) * (1 - 2 * k)

private def constOne (p q r k : ℝ) : ℝ :=
  q * p * (p * (1 - 2 * r) + (1 - 2 * k)) - (p + 1) * q ^ 2

private def coeffTwo (p q r k T : ℝ) : ℝ :=
  p * T * (T - 2 * k + p * (T - 2 * r)) - q * (p + 1) * T ^ 2

private def constTwo (p q r k T : ℝ) : ℝ :=
  -q ^ 2 * T * (T - 2 * k + p * (T - 2 * r)) +
    q * (p + 1) * p * (T - 2 * k) * (T - 2 * r)

private noncomputable def affineT (p q r k : ℝ) : ℝ :=
  (2 * (p ^ 2 - q) * k - 2 * p * (q - 1) * r - (p + 1) * (p - q)) /
    ((p + 1) * (p - q))

/-- Exact cleared identity behind the three resultant factors. -/
private theorem elimination_identity {p q : ℝ} (hp : p + 1 ≠ 0) (hpq : p - q ≠ 0)
    (r k : ℝ) :
    (p + 1) * (p - q) *
      (coeffOne p q r k * constTwo p q r k (affineT p q r k) -
        constOne p q r k * coeffTwo p q r k (affineT p q r k)) =
      8 * p * q * (r - k) * (k * (p ^ 2 - q) + p ^ 2 * r * (q - 1)) *
        projectiveH p q r k := by
  unfold coeffOne constOne coeffTwo constTwo affineT projectiveH projectiveD0 projectiveN
  field_simp
  ring

theorem projectiveH_eq_zero {p q B r k T : ℝ}
    (hq : 1 < q) (hqp : q < p) (hr : 0 < r)
    (hk : 0 < k) (hTr : 2 * r < T)
    (hf1 : turnOne p q B r k = 0) (hf2 : turnTwo p q B r k T = 0)
    (haff : affineRelation p q r k T = 0) : projectiveH p q r k = 0 := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hp1 : 0 < p + 1 := by linarith
  have hpq : 0 < p - q := by linarith
  have hT : T = affineT p q r k := by
    apply (eq_div_iff (mul_ne_zero hp1.ne' hpq.ne')).mpr
    unfold affineRelation at haff
    nlinarith [haff]
  have hres : coeffOne p q r k * constTwo p q r k T -
      constOne p q r k * coeffTwo p q r k T = 0 := by
    unfold turnOne at hf1
    unfold turnTwo at hf2
    unfold coeffOne constOne coeffTwo constTwo
    linear_combination
      (-q * (p * (1 - 2 * r) + (1 - 2 * k)) +
        (p + 1) * p * (1 - 2 * r) * (1 - 2 * k)) * hf2 -
      (p * T * (T - 2 * k + p * (T - 2 * r)) - q * (p + 1) * T ^ 2) * hf1
  have hprod : 8 * p * q * (r - k) *
      (k * (p ^ 2 - q) + p ^ 2 * r * (q - 1)) * projectiveH p q r k = 0 := by
    rw [← elimination_identity hp1.ne' hpq.ne', ← hT, hres, mul_zero]
  have hrk : r - k ≠ 0 := by
    intro heq
    have hkr : k = r := by linarith
    have hid : affineRelation p q r r T = (p + 1) * (p - q) * (2 * r - 1 - T) := by
      unfold affineRelation
      ring
    rw [hkr, hid] at haff
    have ht : 2 * r - 1 - T = 0 :=
      (mul_eq_zero.mp haff).resolve_left (mul_ne_zero hp1.ne' hpq.ne')
    linarith
  have hbranch : 0 < k * (p ^ 2 - q) + p ^ 2 * r * (q - 1) := by
    have hpsq : 0 < p ^ 2 - q := by nlinarith
    exact add_pos (mul_pos hk hpsq) (mul_pos (mul_pos (sq_pos_of_pos hp0) hr) (by linarith))
  exact (mul_eq_zero.mp hprod).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp0.ne') hq0.ne') hrk)
      hbranch.ne')

/-- The surviving projective branch forces the simpler diagonal relation. -/
theorem projective_T_relation {p q r k T : ℝ} (hp : p + 1 ≠ 0)
    (haff : affineRelation p q r k T = 0) (hH : projectiveH p q r k = 0) :
    (p - q) * T = 2 * k * p * r := by
  have hid : (p + 1) * ((p - q) * T - 2 * k * p * r) +
      projectiveH p q r k + affineRelation p q r k T = 0 := by
    unfold projectiveH projectiveD0 projectiveN affineRelation
    ring
  rw [hH, haff, add_zero, add_zero] at hid
  exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left hp)

/-- The first original turn equation identifies the remaining factor C. -/
theorem projective_polyC_eq_zero {p q B r k : ℝ} (hp : p + 1 ≠ 0)
    (hf1 : turnOne p q B r k = 0) (hH : projectiveH p q r k = 0) :
    polyC p q B r = 0 := by
  have hid : projectiveD0 p q r * turnOne p q B r k + (p + 1) * polyC p q B r =
      (2 * B * p ^ 2 * r - B * p ^ 2 + 2 * B * p * r - B * p + B * q - p * q) *
        projectiveH p q r k := by
    unfold projectiveH projectiveD0 turnOne polyC polyD polyA projectiveN
    ring
  rw [hf1, hH, mul_zero, mul_zero, zero_add] at hid
  exact (mul_eq_zero.mp hid).resolve_left hp

/-- The original strict projective inequalities force the interval used by
the independent quadratic sign theorem. -/
theorem projective_forced_interval {p q r k T : ℝ}
    (hq : 1 < q) (hqp : q < p) (hr : 0 < r) (hk : 0 < k) (hkhalf : k < 1 / 2)
    (hTk : 2 * k < T) (hH : projectiveH p q r k = 0)
    (hT : (p - q) * T = 2 * k * p * r) :
    (p - q) / p < r ∧ r < (q - 1) / (p + 2 * q - 1) := by
  have hp : 0 < p := by linarith
  have hpq : 0 < p - q := by linarith
  have hden : 0 < p + 2 * q - 1 := by linarith
  have hN : 0 < projectiveN p q r := by
    unfold projectiveN
    exact add_pos (mul_pos (by linarith) hpq)
      (mul_pos (mul_pos (mul_pos (by norm_num) hp) (by linarith)) hr)
  have hD : projectiveD0 p q r < 0 := by
    unfold projectiveH at hH
    by_contra hn
    have := mul_nonneg (show 0 ≤ 2 * k by linarith) (le_of_not_gt hn)
    linarith
  constructor
  · have hscaled := mul_pos hpq (sub_pos.mpr hTk)
    have hprod : 0 < (2 * k) * (p * r - (p - q)) := by nlinarith [hT]
    have hpr : p - q < p * r := sub_pos.mp (pos_of_mul_pos_right hprod (by linarith))
    exact (div_lt_iff₀ hp).mpr (by nlinarith)
  · have hprod : (1 - 2 * k) * projectiveD0 p q r < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hD
    have hid : projectiveN p q r + projectiveD0 p q r =
        p * (r * (p + 2 * q - 1) - (q - 1)) := by
      unfold projectiveN projectiveD0
      ring
    have hsum : projectiveN p q r + projectiveD0 p q r < 0 := by
      unfold projectiveH at hH
      nlinarith
    rw [hid] at hsum
    have hinner : r * (p + 2 * q - 1) - (q - 1) < 0 :=
      neg_of_mul_neg_right hsum hp.le
    exact (lt_div_iff₀ hden).mpr (by linarith)

/-- No physical one-sided projective configuration satisfies the original
two turn equations and affine relation. -/
theorem not_projective_turn_solution {p q B r k T : ℝ}
    (hq : 1 < q) (hqp : q < p) (hB : 0 < B)
    (hr : 0 < r) (hk : 0 < k) (hkhalf : k < 1 / 2)
    (hTr : 2 * r < T) (hTk : 2 * k < T)
    (hf1 : turnOne p q B r k = 0) (hf2 : turnTwo p q B r k T = 0)
    (haff : affineRelation p q r k T = 0) : False := by
  have hp : p + 1 ≠ 0 := by linarith
  have hH := projectiveH_eq_zero hq hqp hr hk hTr hf1 hf2 haff
  have hT := projective_T_relation hp haff hH
  have hC := projective_polyC_eq_zero hp hf1 hH
  obtain ⟨hlo, hhi⟩ := projective_forced_interval hq hqp hr hk hkhalf hTk hH hT
  have hneg := polyC_neg_of_interval hq hqp hB hlo hhi
  rw [hC] at hneg
  exact lt_irrefl _ hneg

end Gluck.Discrete.NativeIncidentProjective
