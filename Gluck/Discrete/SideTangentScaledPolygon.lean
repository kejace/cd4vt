import Gluck.Discrete.SideTangentDFV
import Gluck.Discrete.SideTangentProjectiveFan
import Gluck.Discrete.StrictSupportSimplicity

/-!
# Closed positive edge scaling preserves strict polygonal support

Integrate a zero-sum cyclic edge list, then use the ordered one-turn heading of
an already strict polygon to prove support for its positive closed edge scaling.
The scaled polygon's simplicity is a conclusion, never an assumption.
-/

open scoped BigOperators InnerProductSpace

namespace Gluck.Discrete.SideTangent

variable {n : ℕ}

/-- Integrate cyclic edges from label zero to the chosen natural representative. -/
noncomputable def edgePrimitive [NeZero n] (e : ZMod n → ℂ) (i : ZMod n) : ℂ :=
  ∑ k ∈ Finset.range i.val, e (k : ZMod n)

/-- Exact integration includes the closing edge at the cyclic seam. -/
lemma edgePrimitive_succ [NeZero n] (e : ZMod n → ℂ) (hsum : ∑ i, e i = 0)
    (i : ZMod n) : edgePrimitive e (i + 1) - edgePrimitive e i = e i := by
  have hv : (i + 1).val = (i.val + 1) % n := by
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using
      (ZMod.val_natCast n (i.val + 1))
  by_cases hi : i.val + 1 < n
  · simp [edgePrimitive, hv, Nat.mod_eq_of_lt hi, Finset.sum_range_succ]
  · have hin : i.val + 1 = n := by have := i.val_lt; omega
    have hs : (∑ k ∈ Finset.range n, e (k : ZMod n)) = 0 := by
      simpa only [zero_add] using (sum_range_natCast_add e 0).trans hsum
    have he : (∑ k ∈ Finset.range i.val, e (k : ZMod n)) + e i = 0 := by
      simpa only [← hin, Finset.sum_range_succ, ZMod.natCast_zmod_val] using hs
    simpa only [edgePrimitive, hv, hin, Nat.mod_self, Finset.range_zero,
      Finset.sum_empty, zero_sub] using (neg_eq_iff_add_eq_zero.mpr he)

/-- Cyclic summation by parts identifies edge closure with the radius-difference balance. -/
lemma sum_scaled_edges [NeZero n] (ρ : ZMod n → ℝ) (Y : ZMod n → ℂ) :
    ∑ i, ρ i • (Y (i + 1) - Y i) = ∑ i, (ρ (i - 1) - ρ i) • Y i := by
  have he := Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
    (fun i ↦ ρ i • Y (i + 1)) (fun j ↦ ρ (j - 1) • Y j) (fun i ↦ by simp)
  simpa only [smul_sub, sub_smul, Finset.sum_sub_distrib] using
    congrArg (fun z : ℂ ↦ z - ∑ i, ρ i • Y i) he

/-- Telescoping the lifted polygon uses no simplicity assumption. -/
private lemma lifted_eq_sum_edges (P : ZMod n → ℂ) (j : ℕ) :
    cyclicVertex P j = cyclicVertex P 0 + ∑ m ∈ Finset.range j, cyclicEdge P m := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    unfold cyclicEdge
    ring

private lemma lifted_sub_eq_sum_edges (P : ZMod n → ℂ) {k j : ℕ} (hkj : k ≤ j) :
    cyclicVertex P j - cyclicVertex P k = ∑ m ∈ Finset.Ico k j, cyclicEdge P m := by
  rw [Finset.sum_Ico_eq_sub _ hkj]
  have hj := lifted_eq_sum_edges P j
  have hk := lifted_eq_sum_edges P k
  linear_combination hj - hk

/-- Left-distance telescoping for any supplied polar edge representation. -/
private lemma im_rot_of_polar (P : ZMod n → ℂ) (θ ℓ : ℕ → ℝ)
    (hpolar : ∀ m, (ℓ m : ℂ) * Complex.exp ((θ m : ℂ) * Complex.I) = cyclicEdge P m)
    {k j : ℕ} (hkj : k ≤ j) :
    (Complex.exp (((-θ k : ℝ) : ℂ) * Complex.I) *
        (cyclicVertex P j - cyclicVertex P k)).im =
      ∑ m ∈ Finset.Ico k j, ℓ m * Real.sin (θ m - θ k) := by
  rw [lifted_sub_eq_sum_edges P hkj, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [← hpolar m]
  have hexp : Complex.exp (((-θ k : ℝ) : ℂ) * Complex.I) *
      ((ℓ m : ℂ) * Complex.exp ((θ m : ℂ) * Complex.I)) =
        (ℓ m : ℂ) * Complex.exp (((θ m - θ k : ℝ) : ℂ) * Complex.I) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hexp, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma sin_neg_second_half {x : ℝ} (hπ : Real.pi < x)
    (h2π : x < 2 * Real.pi) : Real.sin x < 0 := by
  have hsub : Real.sin (2 * Real.pi - x) = -Real.sin x := Real.sin_two_pi_sub x
  have hpos := Real.sin_pos_of_pos_of_lt_pi (show 0 < 2 * Real.pi - x by linarith)
    (show 2 * Real.pi - x < Real.pi by linarith)
  rw [hsub] at hpos
  linarith

/-- Strict support follows from one ordered turn and closure, with no simplicity assumption. -/
private lemma support_pos_of_polar [NeZero n] (P : ZMod n → ℂ) (θ ℓ : ℕ → ℝ)
    (hℓ : ∀ k, 0 < ℓ k) (hmono : StrictMono θ)
    (hgap : ∀ k, θ (k + 1) < θ k + Real.pi)
    (hperiod : ∀ k, θ (k + n) = θ k + 2 * Real.pi)
    (hpolar : ∀ m, (ℓ m : ℂ) * Complex.exp ((θ m : ℂ) * Complex.I) = cyclicEdge P m)
    (k : ℕ) {j : ℕ} (hkj : k + 1 < j) (hjn : j < k + n) :
    0 < (Complex.exp (((-θ k : ℝ) : ℂ) * Complex.I) *
      (cyclicVertex P j - cyclicVertex P k)).im := by
  rw [im_rot_of_polar P θ ℓ hpolar (by omega : k ≤ j)]
  have hzero : ∑ m ∈ Finset.Ico k (k + n),
      ℓ m *
        Real.sin (θ m - θ k) = 0 := by
    have H := im_rot_of_polar P θ ℓ hpolar (Nat.le_add_right k n)
    rw [cyclicVertex_periodic, sub_self, mul_zero, Complex.zero_im] at H
    exact H.symm
  have hsplit :
      (∑ m ∈ Finset.Ico k j, ℓ m *
        Real.sin (θ m - θ k)) =
        -∑ m ∈ Finset.Ico j (k + n), ℓ m *
          Real.sin (θ m - θ k) := by
    have hc := Finset.sum_Ico_consecutive
      (fun m ↦ ℓ m *
        Real.sin (θ m - θ k))
      (by omega : k ≤ j) (by omega : j ≤ k + n)
    rw [hzero] at hc
    linarith
  by_cases hcross : ∀ m ∈ Finset.Ico k j,
      θ m - θ k ≤ Real.pi
  · apply Finset.sum_pos'
    · intro m hm
      rw [Finset.mem_Ico] at hm
      have hαnn : 0 ≤ θ m - θ k :=
        sub_nonneg.2 (hmono.monotone hm.1)
      exact mul_nonneg (hℓ m).le
        (Real.sin_nonneg_of_nonneg_of_le_pi hαnn
          (hcross m (Finset.mem_Ico.2 hm)))
    · refine ⟨k + 1, Finset.mem_Ico.2 ⟨Nat.le_add_right k 1, hkj⟩, ?_⟩
      exact mul_pos (hℓ (k + 1))
        (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr (hmono (Nat.lt_succ_self k)))
          (by have := hgap k; linarith))
  · push Not at hcross
    obtain ⟨m₀, hm₀mem, hm₀⟩ := hcross
    rw [Finset.mem_Ico] at hm₀mem
    rw [hsplit, neg_pos]
    apply Finset.sum_neg
    · intro m hm
      rw [Finset.mem_Ico] at hm
      have hm₀m : m₀ < m := lt_of_lt_of_le hm₀mem.2 hm.1
      have hαgt : Real.pi < θ m - θ k := by
        have h := hmono hm₀m
        linarith
      have hkm : k < m := lt_of_le_of_lt hm₀mem.1 hm₀m
      have hwin : θ k < θ m ∧
          θ m < θ k + 2 * Real.pi := by
        refine ⟨hmono hkm, ?_⟩
        have hw := hmono hm.2
        rw [hperiod] at hw
        exact hw
      exact mul_neg_of_pos_of_neg (hℓ m)
        (sin_neg_second_half hαgt (by linarith [hwin.2]))
    · exact ⟨j, Finset.mem_Ico.2 ⟨le_rfl, hjn⟩⟩

private lemma crossR2_polar_edge (A C : ℂ) (r ψ : ℝ) :
    crossR2 A (A + (r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) C =
      r * (Complex.exp (((-ψ : ℝ) : ℂ) * Complex.I) * (C - A)).im := by
  unfold crossR2
  simp only [add_sub_cancel_left, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  ring

/-- Any cyclic polygon with a positive ordered one-turn edge representation has strict support. -/
theorem strictSupport_of_polar [NeZero n] (P : ZMod n → ℂ) (θ ℓ : ℕ → ℝ)
    (hℓ : ∀ k, 0 < ℓ k) (hmono : StrictMono θ)
    (hgap : ∀ k, θ (k + 1) < θ k + Real.pi)
    (hperiod : ∀ k, θ (k + n) = θ k + 2 * Real.pi)
    (hpolar : ∀ m, (ℓ m : ℂ) * Complex.exp ((θ m : ℂ) * Complex.I) = cyclicEdge P m) :
    StrictConvexEdgeSupport P := by
  intro a c hca hca1
  set t := (c - a).val
  have hb : ((t : ℕ) : ZMod n) = c - a := ZMod.natCast_rightInverse (c - a)
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hb
    exact hca (sub_eq_zero.1 hb.symm)
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, Nat.cast_one] at hb
    exact hca1 (by linear_combination hb.symm)
  have htn : t < n := ZMod.val_lt (c - a)
  have hc : cyclicVertex P (a.val + t) = P c := by
    simp [cyclicVertex, t, Nat.cast_add]
  have hleft : 0 < (Complex.exp (((-θ a.val : ℝ) : ℂ) * Complex.I) * (P c - P a)).im := by
    rw [← hc, show P a = cyclicVertex P a.val by simp [cyclicVertex]]
    exact support_pos_of_polar P θ ℓ hℓ hmono hgap hperiod hpolar a.val (by omega) (by omega)
  have he : (ℓ a.val : ℂ) * Complex.exp ((θ a.val : ℂ) * Complex.I) = P (a + 1) - P a := by
    simpa [cyclicEdge, cyclicVertex, Nat.cast_add] using hpolar a.val
  have hp : P (a + 1) = P a + (ℓ a.val : ℂ) * Complex.exp ((θ a.val : ℂ) * Complex.I) := by
    linear_combination -he
  rw [hp, crossR2_polar_edge]
  exact mul_pos (hℓ a.val) hleft

/-- Strict support in a polygon with at least three labels gives positive local orientation. -/
lemma positiveOrientation_of_strictSupport [NeZero n] (hn : 3 ≤ n)
    {Y : ZMod n → ℂ} (hY : StrictConvexEdgeSupport Y) :
    ∀ i, 0 < crossR2 (Y (i - 1)) (Y i) (Y (i + 1)) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have h₁ : (1 : ZMod n) ≠ 0 := one_ne_zero
  have h₂ : (2 : ZMod n) ≠ 0 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 n).mp h)
    omega
  intro i
  have h := hY (i - 1) (i + 1)
    (fun he ↦ h₂ (by linear_combination he))
    (fun he ↦ h₁ (by linear_combination he))
  simpa only [sub_add_cancel] using h

/-- Positive closed edge scaling of a strict polygon preserves global strict support. -/
theorem strictSupport_of_positive_edge_scaling [NeZero n] (hn : 3 ≤ n)
    {P Y : ZMod n → ℂ} (hY : StrictConvexEdgeSupport Y) (ρ : ZMod n → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hedge : ∀ i, P (i + 1) - P i = ρ i • (Y (i + 1) - Y i)) :
    StrictConvexEdgeSupport P := by
  have hs := isSimplePolygon_of_strictConvexEdgeSupport hn hY
  have ho := positiveOrientation_of_strictSupport hn hY
  have ht := hasPositiveTurningNumberOne_of_simple_positiveOrientation hs ho
  refine strictSupport_of_polar P (cyclicEdgeHeading Y)
    (fun k ↦ ρ (k : ZMod n) * cyclicEdgeLength Y k)
    (fun k ↦ mul_pos (hρ _) (cyclicEdgeLength_pos hs k))
    (cyclicEdgeHeading_strictMono hs ho) (cyclicEdgeHeading_succ_lt_add_pi hs ho)
    (cyclicEdgeHeading_add_n ht) ?_
  intro k
  have he : cyclicEdge P k = ρ (k : ZMod n) • cyclicEdge Y k := by
    simpa [cyclicEdge, cyclicVertex, Nat.cast_add] using hedge (k : ZMod n)
  rw [he, ← cyclicEdge_length_mul_exp_heading hs k]
  simp only [Complex.ofReal_mul, Complex.real_smul, mul_assoc]

/-- An exactly balanced positive scaling integrates to a closed simple strict polygon. -/
theorem exists_strictPolygon_of_balanced_scaling [NeZero n] (hn : 3 ≤ n)
    {Y : ZMod n → ℂ} (hY : StrictConvexEdgeSupport Y) (ρ : ZMod n → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hbalance : ∑ i, (ρ (i - 1) - ρ i) • Y i = 0) :
    ∃ P : ZMod n → ℂ,
      (∀ i, P (i + 1) - P i = ρ i • (Y (i + 1) - Y i)) ∧
      StrictConvexEdgeSupport P ∧ IsSimplePolygon P := by
  have hclose : ∑ i, ρ i • (Y (i + 1) - Y i) = 0 :=
    (sum_scaled_edges ρ Y).trans hbalance
  let P := edgePrimitive (fun i ↦ ρ i • (Y (i + 1) - Y i))
  have hedge : ∀ i, P (i + 1) - P i = ρ i • (Y (i + 1) - Y i) :=
    edgePrimitive_succ _ hclose
  have hs := strictSupport_of_positive_edge_scaling hn hY ρ hρ hedge
  exact ⟨P, hedge, hs, isSimplePolygon_of_strictConvexEdgeSupport hn hs⟩

/-- The inverse relabeling also preserves the cyclic seam. -/
lemma cyclicLabelEquiv_symm_succ [NeZero n] (s i : ZMod n) :
    (cyclicLabelEquiv s).symm (i + 1) = (cyclicLabelEquiv s).symm i + 1 :=
  (cyclicLabelEquiv s).injective (by
    simp only [cyclicLabelEquiv_succ, Equiv.apply_symm_apply])

/-- A strict unit-incircle tangent fan on the original cyclic labels. -/
structure IsCyclicStrictTangentialFan [NeZero n] (U Y : ZMod n → ℂ) : Prop where
  unit_normal : ∀ i, ‖U i‖ = 1
  normal_cross_pos : ∀ i, 0 < crossR2 0 (U i) (U (i + 1))
  vertex_eq : ∀ i, Y i = tangentIntersection (U i) (U (i + 1))
  strict_support : ∀ i j, j ≠ i → j ≠ i + 1 → ⟪U j, Y i⟫_ℝ < 1
  contact_interior : ∀ i, U (i + 1) ∈ openSegment ℝ (Y i) (Y (i + 1))
  edge_pos : ∀ i, ∃ ℓ : ℝ, 0 < ℓ ∧ Y (i + 1) - Y i = ℓ • (Complex.I * U (i + 1))
  edge_ne : ∀ i, Y (i + 1) ≠ Y i
  cross_support : StrictConvexEdgeSupport Y

/-- Transport the whole finite tangency geometry through the exact cyclic label equivalence. -/
theorem isCyclicStrictTangentialFan_of_finite [NeZero n] (s : ZMod n)
    {U Y : Fin n → ℂ} (h : IsStrictTangentialFan U Y) :
    IsCyclicStrictTangentialFan (fun i ↦ U ((cyclicLabelEquiv s).symm i))
      (fun i ↦ Y ((cyclicLabelEquiv s).symm i)) := by
  refine ⟨fun i ↦ h.unit_normal _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [cyclicLabelEquiv_symm_succ] using h.normal_cross_pos ((cyclicLabelEquiv s).symm i)
  · intro i
    simpa only [cyclicLabelEquiv_symm_succ] using h.vertex_eq ((cyclicLabelEquiv s).symm i)
  · intro i j hji hjs
    apply h.strict_support
    · exact fun he ↦ hji ((cyclicLabelEquiv s).symm.injective he)
    · intro he
      apply hjs
      apply (cyclicLabelEquiv s).symm.injective
      simpa only [cyclicLabelEquiv_symm_succ] using he
  · intro i
    simpa only [cyclicLabelEquiv_symm_succ] using h.contact_interior ((cyclicLabelEquiv s).symm i)
  · intro i
    simpa only [cyclicLabelEquiv_symm_succ] using h.edge_pos ((cyclicLabelEquiv s).symm i)
  · intro i
    simpa only [cyclicLabelEquiv_symm_succ] using h.edge_ne ((cyclicLabelEquiv s).symm i)
  · intro i j hji hjs
    simp only [cyclicLabelEquiv_symm_succ]
    apply h.cross_support
    · exact fun he ↦ hji ((cyclicLabelEquiv s).symm.injective he)
    · intro he
      apply hjs
      apply (cyclicLabelEquiv s).symm.injective
      simpa only [cyclicLabelEquiv_symm_succ] using he

/-- Positive radii with the original cyclic DFV condition produce a closed simple strict
polygon by positive edge scaling of an actual balanced tangential fan. -/
theorem exists_sideTangent_scaledPolygon [NeZero n] (ρ : ZMod n → ℝ)
    (hρ : ∀ i, 0 < ρ i) (h : DFV (radiusDifference ρ) 0) :
    ∃ U Y P : ZMod n → ℂ, IsCyclicStrictTangentialFan U Y ∧
      (∀ i, P (i + 1) - P i = ρ i • (Y (i + 1) - Y i)) ∧
      StrictConvexEdgeSupport P ∧ IsSimplePolygon P := by
  obtain ⟨s, p, q, r, hp, hpq, hqr, hr, h₀, h₁, h₂, h₃⟩ :=
    exists_ordered_shift_of_dfv h
  have hn := four_le_of_dfv h
  obtain ⟨U, Y, hfan, hbalance⟩ := exists_balanced_strictTangentialFan hn hp hpq hqr hr
    (fun i ↦ radiusDifference ρ (cyclicLabelEquiv (s : ZMod n) i))
    ((sum_cyclicLabelEquiv (s : ZMod n) (radiusDifference ρ)).trans (sum_radiusDifference ρ))
    (by simpa only [cyclicLabelEquiv_apply, Nat.cast_zero, add_zero] using h₀)
    (by simpa only [cyclicLabelEquiv_apply, Nat.cast_add] using h₁)
    (by simpa only [cyclicLabelEquiv_apply, Nat.cast_add] using h₂)
    (by simpa only [cyclicLabelEquiv_apply, Nat.cast_add] using h₃)
  let U' : ZMod n → ℂ := fun i ↦ U ((cyclicLabelEquiv (s : ZMod n)).symm i)
  let Y' : ZMod n → ℂ := fun i ↦ Y ((cyclicLabelEquiv (s : ZMod n)).symm i)
  have hf : IsCyclicStrictTangentialFan U' Y' := isCyclicStrictTangentialFan_of_finite _ hfan
  have hb : ∑ i, (ρ (i - 1) - ρ i) • Y' i = 0 := by
    calc
      ∑ i, (ρ (i - 1) - ρ i) • Y' i =
          ∑ i : Fin n, radiusDifference ρ (cyclicLabelEquiv (s : ZMod n) i) •
            Y' (cyclicLabelEquiv (s : ZMod n) i) :=
        (sum_cyclicLabelEquiv (s : ZMod n) (fun i ↦ radiusDifference ρ i • Y' i)).symm
      _ = 0 := by simpa only [Y', Equiv.symm_apply_apply] using hbalance
  obtain ⟨P, hedge, hsupport, hsimple⟩ :=
    exists_strictPolygon_of_balanced_scaling (by omega) hf.cross_support ρ hρ hb
  exact ⟨U', Y', P, hf, hedge, hsupport, hsimple⟩

end Gluck.Discrete.SideTangent
