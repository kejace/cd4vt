import Gluck.Discrete.Defs

/-!
# The discrete obstruction zoo

First theorems of the discrete (Menger) converse four-vertex program: the
obstructions separating the discrete problem from its smooth template.

* **Menger chord identity** — the exact chord-level consequence of the
  turning-angle law at `K = 0`: `κᵢ · mᵢ = 2 sin θᵢ` on the moderate-arc
  class.
* **N1 (positive-turning support)** — a realizable profile has at least
  three indices of positive curvature.
* **The killer example** — `κ = (M, -ε, M, -ε)` satisfies the discrete
  transport of the smooth four-vertex window yet is unrealizable for every
  `M, ε > 0`, in either orientation.
* **N0 (`n = 3` rigidity)** — at `n = 3` only constant profiles are
  realizable.

The sections that consume `Gluck.Discrete.Defs` (turning angles, moderate
arcs, developments) are stated against that interface; the scalar,
counting, and complex-closure cores below are Defs-independent and proved
directly from Mathlib.

-/

open Real

namespace Gluck.Discrete

/-! ## The sine addition square identity and the Menger scalar core -/

/-- Sine addition square identity:
`sin²(a+b) = sin²a + sin²b + 2 sin a sin b cos(a+b)`. Unconditional; pure
ring algebra after `sin_add`/`cos_add`. -/
theorem sin_sq_add_identity (a b : ℝ) :
    sin (a + b) ^ 2 =
      sin a ^ 2 + sin b ^ 2 + 2 * sin a * sin b * cos (a + b) := by
  have ha := sin_sq_add_cos_sq a
  have hb := sin_sq_add_cos_sq b
  rw [sin_add, cos_add]
  nlinarith [ha, hb]

/-- Squared-sine law for a sum of two arcsines: project-local because
Mathlib has no addition formulas at the `arcsin` level. -/
theorem sin_sq_arcsin_add_arcsin {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    sin (arcsin x + arcsin y) ^ 2 =
      x ^ 2 + y ^ 2 + 2 * x * y * cos (arcsin x + arcsin y) := by
  have h := sin_sq_add_identity (arcsin x) (arcsin y)
  rwa [sin_arcsin (abs_le.mp hx).1 (abs_le.mp hx).2,
    sin_arcsin (abs_le.mp hy).1 (abs_le.mp hy).2] at h

/-- Sine of a sum of two arcsines. The `√(1 - ·²)` factors are nonnegative,
which makes the sign of the result transparent in each κ-sign case. -/
theorem sin_arcsin_add_arcsin {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    sin (arcsin x + arcsin y) = x * sqrt (1 - y ^ 2) + y * sqrt (1 - x ^ 2) := by
  rw [sin_add, sin_arcsin (abs_le.mp hx).1 (abs_le.mp hx).2,
    sin_arcsin (abs_le.mp hy).1 (abs_le.mp hy).2, cos_arcsin, cos_arcsin]
  ring

/-- Scalar core of the Menger chord identity: for edge lengths `l₀, l₁ > 0`
inside the strict wall `|κ| · lⱼ/2 < 1`, the chord
`m = √(l₀² + l₁² + 2 l₀ l₁ cos θ)` of the turning angle
`θ = arcsin (κ l₀/2) + arcsin (κ l₁/2)` satisfies `κ · m = 2 sin θ`. -/
theorem mul_sqrt_chord_eq_two_sin {κ l₀ l₁ : ℝ}
    (h₀ : 0 < l₀) (h₁ : 0 < l₁)
    (w₀ : |κ| * (l₀ / 2) < 1) (w₁ : |κ| * (l₁ / 2) < 1) :
    κ * sqrt (l₀ ^ 2 + l₁ ^ 2 + 2 * l₀ * l₁ *
        cos (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2)))) =
      2 * sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) := by
  rcases eq_or_ne κ 0 with hκ | hκ
  · simp [hκ]
  · have hx1 : |κ * (l₀ / 2)| < 1 := by
      rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < l₀ / 2)]
    have hy1 : |κ * (l₁ / 2)| < 1 := by
      rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < l₁ / 2)]
    have hsq := sin_sq_arcsin_add_arcsin hx1.le hy1.le
    have hsin := sin_arcsin_add_arcsin hx1.le hy1.le
    have hsign : 0 ≤ 2 * sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) / κ := by
      rcases lt_or_gt_of_ne hκ with hneg | hpos
      · have hx0 : κ * (l₀ / 2) ≤ 0 := by nlinarith
        have hy0 : κ * (l₁ / 2) ≤ 0 := by nlinarith
        have hs : sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) ≤ 0 := by
          rw [hsin]
          have h1 := sqrt_nonneg (1 - (κ * (l₁ / 2)) ^ 2)
          have h2 := sqrt_nonneg (1 - (κ * (l₀ / 2)) ^ 2)
          nlinarith
        exact div_nonneg_of_nonpos (by linarith) hneg.le
      · have hx0 : 0 ≤ κ * (l₀ / 2) := by positivity
        have hy0 : 0 ≤ κ * (l₁ / 2) := by positivity
        have hs : 0 ≤ sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) := by
          rw [hsin]
          have h1 := sqrt_nonneg (1 - (κ * (l₁ / 2)) ^ 2)
          have h2 := sqrt_nonneg (1 - (κ * (l₀ / 2)) ^ 2)
          positivity
        positivity
    have key : κ ^ 2 * (l₀ ^ 2 + l₁ ^ 2 + 2 * l₀ * l₁ *
        cos (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2)))) =
        (2 * sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2)))) ^ 2 := by
      linear_combination (-4 : ℝ) * hsq
    have hrw : (2 * sin (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) / κ) ^ 2 =
        l₀ ^ 2 + l₁ ^ 2 + 2 * l₀ * l₁ *
          cos (arcsin (κ * (l₀ / 2)) + arcsin (κ * (l₁ / 2))) := by
      rw [div_pow, ← key, mul_div_cancel_left₀]
      exact pow_ne_zero 2 hκ
    rw [← hrw, sqrt_sq hsign]
    field_simp

/-! ## Counting core for N1 -/

/-- Counting core of the positive-turning-support obstruction: if the terms
outside `S` are nonpositive, the terms inside `S` are each `< π`, and the
total is at least `2π`, then `S` has at least three elements. Project-local:
the combination of a one-sided bound and a strict per-term cap has no
Mathlib counterpart. -/
theorem three_le_card_of_two_pi_le_sum {ι : Type*} [Fintype ι] {θ : ι → ℝ}
    {S : Finset ι}
    (h_nonpos : ∀ i ∉ S, θ i ≤ 0) (h_lt : ∀ i ∈ S, θ i < π)
    (hsum : 2 * π ≤ ∑ i, θ i) :
    3 ≤ S.card := by
  classical
  have hS : ∑ i, θ i ≤ ∑ i ∈ S, θ i := by
    rw [← Finset.sum_add_sum_compl S θ]
    have : ∑ i ∈ Sᶜ, θ i ≤ 0 :=
      Finset.sum_nonpos fun i hi => h_nonpos i (Finset.mem_compl.mp hi)
    linarith
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    simp only [Finset.sum_empty] at hS
    nlinarith [pi_pos]
  have hlt : ∑ i ∈ S, θ i < S.card * π := by
    calc ∑ i ∈ S, θ i < ∑ _i ∈ S, π := Finset.sum_lt_sum_of_nonempty hne h_lt
    _ = S.card * π := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : (2 : ℝ) < S.card := by nlinarith [pi_pos]
  have h2' : 2 < S.card := by exact_mod_cast h2
  omega

/-! ## Complex-closure core for the `n = 3` rigidity block -/

/-- Imaginary part of a rotated three-term closure equation: if three edge
vectors `lⱼ · exp(ψⱼ i)` sum to zero, then so does every rotation, giving
`∑ lⱼ sin (ψⱼ - φ) = 0` for all `φ`. Scalar core of the discrete law of
sines. -/
theorem sum_sin_of_closure {l₀ l₁ l₂ ψ₀ ψ₁ ψ₂ : ℝ}
    (h : (l₀ : ℂ) * Complex.exp (ψ₀ * Complex.I) + l₁ * Complex.exp (ψ₁ * Complex.I) +
      l₂ * Complex.exp (ψ₂ * Complex.I) = 0) (φ : ℝ) :
    l₀ * sin (ψ₀ - φ) + l₁ * sin (ψ₁ - φ) + l₂ * sin (ψ₂ - φ) = 0 := by
  have h2 := congrArg (fun z => (z * Complex.exp (-(φ : ℂ) * Complex.I)).im) h
  simp only [add_mul, mul_assoc, ← Complex.exp_add, zero_mul, Complex.zero_im] at h2
  have e : ∀ ψ : ℝ, (ψ : ℂ) * Complex.I + -(φ : ℂ) * Complex.I =
      ((ψ - φ : ℝ) : ℂ) * Complex.I := by
    intro ψ; push_cast; ring
  rw [e ψ₀, e ψ₁, e ψ₂] at h2
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.exp_ofReal_mul_I_im] at h2
  exact h2

/-- Norm-squared core of the law of cosines: from a three-term closure, the
middle length squared equals the law-of-cosines combination of the other
two. Scalar core of the `n = 3` vertex-chord/opposite-edge identity. -/
theorem sq_eq_of_closure {l₀ l₁ l₂ ψ₀ ψ₁ ψ₂ : ℝ}
    (h : (l₀ : ℂ) * Complex.exp (ψ₀ * Complex.I) + l₁ * Complex.exp (ψ₁ * Complex.I) +
      l₂ * Complex.exp (ψ₂ * Complex.I) = 0) :
    l₁ ^ 2 = l₀ ^ 2 + l₂ ^ 2 + 2 * l₀ * l₂ * cos (ψ₀ - ψ₂) := by
  have h1 : (l₁ : ℂ) * Complex.exp (ψ₁ * Complex.I) =
      -((l₀ : ℂ) * Complex.exp (ψ₀ * Complex.I) + l₂ * Complex.exp (ψ₂ * Complex.I)) := by
    linear_combination h
  have h2 := congrArg Complex.normSq h1
  rw [Complex.normSq_neg, Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_mul] at h2
  simp only [Complex.normSq_ofReal] at h2
  have habs : ∀ ψ : ℝ, Complex.normSq (Complex.exp (ψ * Complex.I)) = 1 := by
    intro ψ
    rw [Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    linear_combination cos_sq_add_sin_sq ψ
  rw [habs, habs, habs] at h2
  have harg : ((ψ₀ : ℂ)) * Complex.I + ((-ψ₂ : ℝ) : ℂ) * Complex.I =
      ((ψ₀ - ψ₂ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hre : ((l₀ : ℂ) * Complex.exp (ψ₀ * Complex.I) *
      (starRingEnd ℂ) ((l₂ : ℂ) * Complex.exp (ψ₂ * Complex.I))).re =
      l₀ * l₂ * cos (ψ₀ - ψ₂) := by
    rw [map_mul, ← Complex.exp_conj]
    have hconj : (starRingEnd ℂ) ((ψ₂ : ℂ) * Complex.I) = ((-ψ₂ : ℝ) : ℂ) * Complex.I := by
      simp [Complex.conj_ofReal]
    rw [hconj, Complex.conj_ofReal]
    have hprod : (l₀ : ℂ) * Complex.exp ((ψ₀ : ℂ) * Complex.I) *
        ((l₂ : ℂ) * Complex.exp (((-ψ₂ : ℝ) : ℂ) * Complex.I)) =
        ((l₀ * l₂ : ℝ) : ℂ) * Complex.exp (((ψ₀ - ψ₂ : ℝ) : ℂ) * Complex.I) := by
      rw [← harg, Complex.exp_add]
      push_cast
      ring
    rw [hprod, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  rw [hre] at h2
  nlinarith [h2]

/-! ## The killer profile -/

/-- The alternating two-value profile on `ℤ/4`: value `M` at `i ∈ {0, 2}`
and `-ε` at `i ∈ {1, 3}`. For `M, ε > 0` it satisfies the discrete
transport of the smooth four-vertex window yet is unrealizable. -/
def killerProfile (M ε : ℝ) : ZMod 4 → ℝ := fun i => if i = 0 ∨ i = 2 then M else -ε

lemma killerProfile_zero (M ε : ℝ) : killerProfile M ε 0 = M :=
  if_pos (Or.inl rfl)

lemma killerProfile_one (M ε : ℝ) : killerProfile M ε 1 = -ε :=
  if_neg (by decide)

lemma killerProfile_two (M ε : ℝ) : killerProfile M ε 2 = M :=
  if_pos (Or.inr rfl)

lemma killerProfile_three (M ε : ℝ) : killerProfile M ε 3 = -ε :=
  if_neg (by decide)

private lemma zmod4_cases (j : ZMod 4) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
  revert j; decide

/-- The positive set of the killer profile is exactly `{0, 2}`. -/
theorem killerProfile_pos_filter {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    (Finset.univ.filter fun i : ZMod 4 => 0 < killerProfile M ε i) = {0, 2} := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · rw [killerProfile_zero]
    exact iff_of_true hM (by decide)
  · rw [killerProfile_one]
    exact iff_of_false (by linarith) (by decide)
  · rw [killerProfile_two]
    exact iff_of_true hM (by decide)
  · rw [killerProfile_three]
    exact iff_of_false (by linarith) (by decide)

/-- The killer profile has exactly two indices of positive curvature. -/
theorem killerProfile_pos_card {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    (Finset.univ.filter fun i : ZMod 4 => 0 < killerProfile M ε i).card = 2 := by
  rw [killerProfile_pos_filter hM hε]
  decide

/-- The positive set of the reflected killer profile `i ↦ -killer M ε (-i)`
is exactly `{1, 3}`. -/
theorem killerProfile_reflected_pos_filter {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    (Finset.univ.filter fun i : ZMod 4 => 0 < -killerProfile M ε (-i)) = {1, 3} := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · rw [show -(0 : ZMod 4) = 0 by decide, killerProfile_zero]
    exact iff_of_false (by linarith) (by decide)
  · rw [show -(1 : ZMod 4) = 3 by decide, killerProfile_three]
    exact iff_of_true (by linarith) (by decide)
  · rw [show -(2 : ZMod 4) = 2 by decide, killerProfile_two]
    exact iff_of_false (by linarith) (by decide)
  · rw [show -(3 : ZMod 4) = 1 by decide, killerProfile_one]
    exact iff_of_true (by linarith) (by decide)

/-- The reflected killer profile has exactly two indices of positive
curvature. -/
theorem killerProfile_reflected_pos_card {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    (Finset.univ.filter fun i : ZMod 4 => 0 < -killerProfile M ε (-i)).card = 2 := by
  rw [killerProfile_reflected_pos_filter hM hε]
  decide

/-! ## The Menger chord identity -/

variable {n : ℕ}

/-- The vertex chord at `i` for data `(κ, ℓ)` at `K = 0`: the length of the
chord from `P (i-1)` to `P (i+1)` in any development, expressed through the
law of cosines at the exterior angle `θ i`. -/
noncomputable def vertexChord (κ ℓ : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  sqrt (ℓ (i - 1) ^ 2 + ℓ i ^ 2 + 2 * ℓ (i - 1) * ℓ i * cos (turningAngle 0 κ ℓ i))

/-- **Menger chord identity**: on the Euclidean moderate-arc domain,
`κ i · m i = 2 sin θ i` for every vertex `i`. -/
theorem menger_chord_identity {κ ℓ : ZMod n → ℝ} (h : ModerateArc 0 κ ℓ)
    (i : ZMod n) :
    κ i * vertexChord κ ℓ i = 2 * sin (turningAngle 0 κ ℓ i) := by
  have w₀ := h.wall_left i
  have w₁ := h.wall_right i
  rw [tK_zero] at w₀ w₁
  have key := mul_sqrt_chord_eq_two_sin (κ := κ i)
    (h.length_pos (i - 1)) (h.length_pos i) w₀ w₁
  simpa only [vertexChord, turningAngle, tK_zero] using key

/-! ## N1: positive-turning support -/

/-- **N1, turning form**: closed positively-oriented moderate-arc data has at
least three vertices of positive curvature. -/
theorem three_le_card_pos_of_turningSum [NeZero n] {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) (hT : turningSum κ ℓ = 2 * π) :
    3 ≤ (Finset.univ.filter fun i : ZMod n => 0 < κ i).card := by
  apply three_le_card_of_two_pi_le_sum (θ := turningAngle 0 κ ℓ)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    rcases hi.lt_or_eq with hlt | heq
    · exact (turningAngle_neg_of_neg h hlt).le
    · exact le_of_eq (turningAngle_eq_zero heq)
  · intro i _
    exact lt_of_abs_lt (abs_turningAngle_lt_pi h i)
  · rw [← hT]
    rfl

/-- **N1 for realizable profiles**: a realizable profile has at least three
indices of positive curvature. -/
theorem three_le_card_pos_of_realizes [NeZero n] {κ : ZMod n → ℝ}
    (h : RealizesR2 κ) :
    3 ≤ (Finset.univ.filter fun i : ZMod n => 0 < κ i).card := by
  obtain ⟨ℓ, hMA, -, hT, -⟩ := h
  exact three_le_card_pos_of_turningSum hMA hT

/-- **N1, reflected gauge**: closed negatively-oriented moderate-arc data has
at least three vertices of negative curvature. -/
theorem three_le_card_neg_of_turningSum_neg [NeZero n] {κ ℓ : ZMod n → ℝ}
    (h : ModerateArc 0 κ ℓ) (hT : turningSum κ ℓ = -(2 * π)) :
    3 ≤ (Finset.univ.filter fun i : ZMod n => κ i < 0).card := by
  have hMA : ModerateArc 0 (-κ) ℓ := by
    intro i
    obtain ⟨h1, h2, h3, h4, h5⟩ := h i
    exact ⟨h1, h2, h3, by simpa using h4, by simpa using h5⟩
  have hT' : turningSum (-κ) ℓ = 2 * π := by
    unfold turningSum
    simp only [turningAngle_neg, Finset.sum_neg_distrib]
    rw [show (∑ i : ZMod n, turningAngle 0 κ ℓ i) = turningSum κ ℓ from rfl, hT]
    ring
  have h3 := three_le_card_pos_of_turningSum hMA hT'
  have hfilter : (Finset.univ.filter fun i : ZMod n => 0 < (-κ) i) =
      (Finset.univ.filter fun i : ZMod n => κ i < 0) := by
    ext i
    simp
  rwa [hfilter] at h3

/-! ## The killer profile is unrealizable -/

/-- **The killer profile is unrealizable**: for all `M, ε > 0` the profile
`(M, -ε, M, -ε)` is unrealizable, and likewise its reflected orientation
`i ↦ -killer M ε (-i)` — despite satisfying the discrete transport of the
smooth four-vertex window. -/
theorem killerProfile_not_realizes {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ¬RealizesR2 (killerProfile M ε) ∧
      ¬RealizesR2 (fun i => -killerProfile M ε (-i)) := by
  constructor
  · intro h
    have h3 := three_le_card_pos_of_realizes h
    rw [killerProfile_pos_card hM hε] at h3
    omega
  · intro h
    have h3 := three_le_card_pos_of_realizes h
    rw [killerProfile_reflected_pos_card hM hε] at h3
    omega

/-! ## N0: rigidity at `n = 3` -/

private lemma zmod3_cases (j : ZMod 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  revert j; decide

private lemma sum_zmod3 (f : ZMod 3 → ℝ) : ∑ i : ZMod 3, f i = f 0 + f 1 + f 2 := by
  have h : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- The three-term closure equation of a triangle development, with
explicit headings `θ₀`, `θ₀+θ₁`, `θ₀+θ₁+θ₂`. -/
private lemma triangle_closure {κ ℓ : ZMod 3 → ℝ} (hE : closureGap κ ℓ = 0) :
    (ℓ 0 : ℂ) * Complex.exp ((turningAngle 0 κ ℓ 0 : ℝ) * Complex.I) +
      (ℓ 1 : ℂ) * Complex.exp
        ((turningAngle 0 κ ℓ 0 + turningAngle 0 κ ℓ 1 : ℝ) * Complex.I) +
      (ℓ 2 : ℂ) * Complex.exp
        ((turningAngle 0 κ ℓ 0 + turningAngle 0 κ ℓ 1 + turningAngle 0 κ ℓ 2 : ℝ) *
          Complex.I) = 0 := by
  have h0 : heading κ ℓ 0 = turningAngle 0 κ ℓ 0 := by
    simp [heading]
  have h1 : heading κ ℓ 1 = turningAngle 0 κ ℓ 0 + turningAngle 0 κ ℓ 1 := by
    simp [heading, Finset.sum_range_succ]
  have h2 : heading κ ℓ 2 =
      turningAngle 0 κ ℓ 0 + turningAngle 0 κ ℓ 1 + turningAngle 0 κ ℓ 2 := by
    simp [heading, Finset.sum_range_succ]
  have hE' : vertexR2 κ ℓ 3 = 0 := hE
  have e3 : vertexR2 κ ℓ 3 = vertexR2 κ ℓ 2 +
      (ℓ ((2 : ℕ) : ZMod 3) : ℂ) * Complex.exp ((heading κ ℓ 2 : ℂ) * Complex.I) :=
    vertexR2_succ κ ℓ 2
  have e2 : vertexR2 κ ℓ 2 = vertexR2 κ ℓ 1 +
      (ℓ ((1 : ℕ) : ZMod 3) : ℂ) * Complex.exp ((heading κ ℓ 1 : ℂ) * Complex.I) :=
    vertexR2_succ κ ℓ 1
  have e1 : vertexR2 κ ℓ 1 = vertexR2 κ ℓ 0 +
      (ℓ ((0 : ℕ) : ZMod 3) : ℂ) * Complex.exp ((heading κ ℓ 0 : ℂ) * Complex.I) :=
    vertexR2_succ κ ℓ 0
  have e0 : vertexR2 κ ℓ 0 = 0 := Finset.sum_range_zero _
  rw [e3, e2, e1, e0, zero_add, h0, h1, h2] at hE'
  simpa using hE'

/-- **All three turning angles are interior**: at `n = 3` with total turning
`2π`, each `θ i ∈ (0, π)`. -/
theorem triangle_turning_mem_Ioo {κ ℓ : ZMod 3 → ℝ} (h : ModerateArc 0 κ ℓ)
    (hT : turningSum κ ℓ = 2 * π) (i : ZMod 3) :
    turningAngle 0 κ ℓ i ∈ Set.Ioo 0 π := by
  have hsum : turningAngle 0 κ ℓ 0 + turningAngle 0 κ ℓ 1 + turningAngle 0 κ ℓ 2 =
      2 * π := by
    rw [← sum_zmod3 (turningAngle 0 κ ℓ)]
    exact hT
  have h0 := abs_lt.mp (abs_turningAngle_lt_pi h 0)
  have h1 := abs_lt.mp (abs_turningAngle_lt_pi h 1)
  have h2 := abs_lt.mp (abs_turningAngle_lt_pi h 2)
  rcases zmod3_cases i with rfl | rfl | rfl <;>
    exact ⟨by linarith, by linarith⟩

/-- **Discrete law of sines at `n = 3`**: from a closed, `2π`-turning
development, `ℓ₀ sin θ₀ = ℓ₁ sin θ₂`, `ℓ₁ sin θ₁ = ℓ₂ sin θ₀` and
`ℓ₂ sin θ₂ = ℓ₀ sin θ₁`. -/
theorem triangle_law_of_sines {κ ℓ : ZMod 3 → ℝ} (hE : closureGap κ ℓ = 0)
    (hT : turningSum κ ℓ = 2 * π) :
    ℓ 0 * sin (turningAngle 0 κ ℓ 0) = ℓ 1 * sin (turningAngle 0 κ ℓ 2) ∧
      ℓ 1 * sin (turningAngle 0 κ ℓ 1) = ℓ 2 * sin (turningAngle 0 κ ℓ 0) ∧
      ℓ 2 * sin (turningAngle 0 κ ℓ 2) = ℓ 0 * sin (turningAngle 0 κ ℓ 1) := by
  set θ0 := turningAngle 0 κ ℓ 0 with hθ0
  set θ1 := turningAngle 0 κ ℓ 1 with hθ1
  set θ2 := turningAngle 0 κ ℓ 2 with hθ2
  have hsum : θ0 + θ1 + θ2 = 2 * π := by
    rw [hθ0, hθ1, hθ2, ← sum_zmod3 (turningAngle 0 κ ℓ)]
    exact hT
  have hcl := triangle_closure hE
  refine ⟨?_, ?_, ?_⟩
  · -- rotate by ψ₂ = θ0+θ1+θ2 = 2π
    have hs := sum_sin_of_closure hcl (θ0 + θ1 + θ2)
    rw [show θ0 - (θ0 + θ1 + θ2) = θ0 - 2 * π from by rw [hsum],
      show θ0 + θ1 - (θ0 + θ1 + θ2) = (θ0 + θ1 + θ2) - θ2 - (θ0 + θ1 + θ2) from by ring,
      show (θ0 + θ1 + θ2) - θ2 - (θ0 + θ1 + θ2) = -θ2 from by ring,
      show θ0 + θ1 + θ2 - (θ0 + θ1 + θ2) = 0 from by ring,
      Real.sin_sub_two_pi, Real.sin_neg, Real.sin_zero] at hs
    linarith
  · -- rotate by ψ₀ = θ0
    have hs := sum_sin_of_closure hcl θ0
    rw [show θ0 - θ0 = 0 from by ring,
      show θ0 + θ1 - θ0 = θ1 from by ring,
      show θ0 + θ1 + θ2 - θ0 = 2 * π - θ0 from by linarith,
      Real.sin_zero, Real.sin_two_pi_sub] at hs
    linarith
  · -- rotate by ψ₁ = θ0 + θ1
    have hs := sum_sin_of_closure hcl (θ0 + θ1)
    rw [show θ0 - (θ0 + θ1) = -θ1 from by ring,
      show θ0 + θ1 - (θ0 + θ1) = 0 from by ring,
      show θ0 + θ1 + θ2 - (θ0 + θ1) = θ2 from by ring,
      Real.sin_neg, Real.sin_zero] at hs
    linarith

/-- **The vertex chord is the opposite edge**: at `n = 3`, `m i = ℓ (i+1)`
for every `i`. -/
theorem triangle_chord_eq_opposite {κ ℓ : ZMod 3 → ℝ} (h : ModerateArc 0 κ ℓ)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * π) (i : ZMod 3) :
    vertexChord κ ℓ i = ℓ (i + 1) := by
  set θ0 := turningAngle 0 κ ℓ 0 with hθ0
  set θ1 := turningAngle 0 κ ℓ 1 with hθ1
  set θ2 := turningAngle 0 κ ℓ 2 with hθ2
  have hsum : θ0 + θ1 + θ2 = 2 * π := by
    rw [hθ0, hθ1, hθ2, ← sum_zmod3 (turningAngle 0 κ ℓ)]
    exact hT
  have hcl := triangle_closure hE
  have key : ∀ j : ZMod 3,
      ℓ (j - 1) ^ 2 + ℓ j ^ 2 + 2 * ℓ (j - 1) * ℓ j * cos (turningAngle 0 κ ℓ j) =
        ℓ (j + 1) ^ 2 := by
    intro j
    rcases zmod3_cases j with rfl | rfl | rfl
    · -- vertex 0: chord ℓ₂,ℓ₀ ↦ opposite ℓ₁
      have hsq := sq_eq_of_closure hcl
      rw [show θ0 - (θ0 + θ1 + θ2) = θ0 - 2 * π from by rw [hsum],
        Real.cos_sub_two_pi] at hsq
      rw [show (0 : ZMod 3) - 1 = 2 from by decide,
        show (0 : ZMod 3) + 1 = 1 from by decide, ← hθ0]
      linarith [hsq]
    · -- vertex 1: chord ℓ₀,ℓ₁ ↦ opposite ℓ₂
      have hcl' : (ℓ 1 : ℂ) *
          Complex.exp ((θ0 + θ1 : ℝ) * Complex.I) +
          (ℓ 2 : ℂ) * Complex.exp ((θ0 + θ1 + θ2 : ℝ) * Complex.I) +
          (ℓ 0 : ℂ) * Complex.exp ((θ0 : ℝ) * Complex.I) = 0 := by
        linear_combination hcl
      have hsq := sq_eq_of_closure hcl'
      rw [show θ0 + θ1 - θ0 = θ1 from by ring] at hsq
      rw [show (1 : ZMod 3) - 1 = 0 from by decide,
        show (1 : ZMod 3) + 1 = 2 from by decide, ← hθ1]
      linarith [hsq]
    · -- vertex 2: chord ℓ₁,ℓ₂ ↦ opposite ℓ₀
      have hcl' : (ℓ 2 : ℂ) *
          Complex.exp ((θ0 + θ1 + θ2 : ℝ) * Complex.I) +
          (ℓ 0 : ℂ) * Complex.exp ((θ0 : ℝ) * Complex.I) +
          (ℓ 1 : ℂ) * Complex.exp ((θ0 + θ1 : ℝ) * Complex.I) = 0 := by
        linear_combination hcl
      have hsq := sq_eq_of_closure hcl'
      rw [show θ0 + θ1 + θ2 - (θ0 + θ1) = θ2 from by ring] at hsq
      rw [show (2 : ZMod 3) - 1 = 1 from by decide,
        show (2 : ZMod 3) + 1 = 0 from by decide, ← hθ2]
      linarith [hsq]
  rw [vertexChord, key i, sqrt_sq (h.length_pos (i + 1)).le]

/-- **N0: `n = 3` rigidity** — closed, `2π`-turning moderate-arc data at
`n = 3` forces a constant curvature profile. -/
theorem triangle_rigidity {κ ℓ : ZMod 3 → ℝ} (h : ModerateArc 0 κ ℓ)
    (hE : closureGap κ ℓ = 0) (hT : turningSum κ ℓ = 2 * π) :
    κ 0 = κ 1 ∧ κ 1 = κ 2 := by
  have hm : ∀ i : ZMod 3, κ i * ℓ (i + 1) = 2 * sin (turningAngle 0 κ ℓ i) := by
    intro i
    rw [← triangle_chord_eq_opposite h hE hT i]
    exact menger_chord_identity h i
  have hm0 := hm 0
  have hm1 := hm 1
  have hm2 := hm 2
  rw [show (0 : ZMod 3) + 1 = 1 from by decide] at hm0
  rw [show (1 : ZMod 3) + 1 = 2 from by decide] at hm1
  rw [show (2 : ZMod 3) + 1 = 0 from by decide] at hm2
  obtain ⟨-, hlos2, hlos3⟩ := triangle_law_of_sines hE hT
  have hl0 := h.length_pos 0
  have hl1 := h.length_pos 1
  have hl2 := h.length_pos 2
  constructor
  · -- κ0 ℓ1 ℓ2 = 2 sinθ0 ℓ2 = 2 ℓ1 sinθ1 = κ1 ℓ2 ℓ1
    have : κ 0 * (ℓ 1 * ℓ 2) = κ 1 * (ℓ 1 * ℓ 2) := by
      nlinarith [hm0, hm1, hlos2]
    exact mul_right_cancel₀ (by positivity) this
  · -- κ1 ℓ2 ℓ0 = 2 sinθ1 ℓ0 = 2 ℓ2 sinθ2 = κ2 ℓ0 ℓ2
    have : κ 1 * (ℓ 2 * ℓ 0) = κ 2 * (ℓ 2 * ℓ 0) := by
      nlinarith [hm1, hm2, hlos3]
    exact mul_right_cancel₀ (by positivity) this

end Gluck.Discrete
