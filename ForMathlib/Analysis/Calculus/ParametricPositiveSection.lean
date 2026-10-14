import ForMathlib.Analysis.Calculus.ParametricConstraintCorrection

/-!
# Positive local sections from a regular boundary solution

A nonnegative solution of finitely many smooth constraints admits a local
positive section in its parameters if the derivative is onto using only
directions supported on its positive coordinates. Additional open constraints
are preserved. The section need not pass through the boundary solution.
-/

open Filter Set
open scoped Topology ContDiff

variable {P F ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype ι]

/-- An onto derivative supported away from the zero coordinates gives a `C¹`
local family of strictly positive solutions, retaining any prescribed open
condition on the parameter and unknown together. -/
theorem ContDiffAt.exists_localSection_pos_of_active_surjective
    {f : P × (ι → ℝ) → F} {p₀ : P} {x₀ : ι → ℝ}
    (hf : ContDiffAt ℝ 1 f (p₀, x₀)) (hx₀ : ∀ i, 0 ≤ x₀ i)
    (hactive : ∀ y : F, ∃ b : ι → ℝ,
      (fderiv ℝ f (p₀, x₀) ∘L ContinuousLinearMap.inr ℝ P (ι → ℝ)) b = y ∧
        ∀ i, x₀ i = 0 → b i = 0)
    {V : Set (P × (ι → ℝ))} (hV : IsOpen V) (hV₀ : (p₀, x₀) ∈ V) :
    ∃ (U : Set P) (s : P → (ι → ℝ)), IsOpen U ∧ p₀ ∈ U ∧
      ContDiffOn ℝ 1 s U ∧
      ∀ p ∈ U, (p, s p) ∈ V ∧ (∀ i, 0 < s p i) ∧ f (p, s p) = f (p₀, x₀) := by
  classical
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  let D : Submodule ℝ (ι → ℝ) :=
    { carrier := {b | ∀ i, x₀ i = 0 → b i = 0}
      zero_mem' := by simp
      add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
      smul_mem' := by intro c b hb i hi; simp [hb i hi] }
  let A := fderiv ℝ f (p₀, x₀) ∘L ContinuousLinearMap.inr ℝ P (ι → ℝ)
  let B : D →L[ℝ] F := A ∘L D.subtypeL
  have hB : B.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨b, hb, hbs⟩ := hactive y
    exact ⟨⟨b, hbs⟩, hb⟩
  obtain ⟨g, hg⟩ := B.exists_rightInverse_of_surjective hB
  let R : F →L[ℝ] (ι → ℝ) := D.subtypeL ∘L g
  have hR : A ∘L R = ContinuousLinearMap.id ℝ F := by
    rw [show A ∘L R = B ∘L g from rfl]
    exact hg
  obtain ⟨Q, hQcd, hQ₀, hQrange, hQeq, -⟩ :=
    hf.exists_parametricConstraintCorrection one_ne_zero R hR
  have hfixed : ∀ q i, x₀ i = 0 → Q q i = q.2 i := by
    intro q i hi
    obtain ⟨a, ha⟩ := hQrange q
    have hz : (R a) i = 0 := (g a).property i hi
    have hai : R a i = Q q i - q.2 i := congrFun ha i
    exact sub_eq_zero.mp (hai.symm.trans hz)
  have hQpair : ContinuousAt (fun q : P × (ι → ℝ) => (q.1, Q q)) (p₀, x₀) :=
    continuousAt_fst.prodMk hQcd.continuousAt
  have hQV : ∀ᶠ q in 𝓝 (p₀, x₀), (q.1, Q q) ∈ V := by
    apply hQpair.preimage_mem_nhds
    simpa [hQ₀] using hV.mem_nhds hV₀
  have hQpos : ∀ᶠ q in 𝓝 (p₀, x₀), ∀ i, x₀ i ≠ 0 → 0 < Q q i := by
    apply eventually_all.mpr
    intro i
    by_cases hi : x₀ i = 0
    · exact Filter.Eventually.of_forall (by simp [hi])
    · have hp : 0 < Q (p₀, x₀) i := by rw [hQ₀]; exact lt_of_le_of_ne (hx₀ i) (Ne.symm hi)
      have hc := (continuous_apply i).continuousAt.comp hQcd.continuousAt
      exact (hc.eventually (isOpen_Ioi.mem_nhds hp)).mono (fun _ h _ => h)
  have hgood : ∀ᶠ q in 𝓝 (p₀, x₀), ContDiffAt ℝ 1 Q q ∧
      (q.1, Q q) ∈ V ∧ (∀ i, x₀ i ≠ 0 → 0 < Q q i) ∧
        f (q.1, Q q) = f (p₀, x₀) := by
    filter_upwards [hQcd.eventually (by norm_num), hQV, hQpos, hQeq] with q h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨W, hWgood, hWopen, hW₀⟩ := mem_nhds_iff.mp hgood
  let d : ι → ℝ := fun i => if x₀ i = 0 then 1 else 0
  have ht : Tendsto (fun t : ℝ => (p₀, x₀ + t • d)) (𝓝 0) (𝓝 (p₀, x₀)) := by
    have hc : Continuous (fun t : ℝ => (p₀, x₀ + t • d)) := by fun_prop
    simpa using hc.tendsto 0
  have hw : ∀ᶠ t in 𝓝 (0 : ℝ), (p₀, x₀ + t • d) ∈ W :=
    ht.eventually (hWopen.mem_nhds hW₀)
  have hw' : ∀ᶠ t in 𝓝[>] (0 : ℝ), (p₀, x₀ + t • d) ∈ W :=
    hw.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, htW, htpos⟩ := (hw'.and hpos).exists
  let x₁ := x₀ + t • d
  let U := (fun p : P => (p, x₁)) ⁻¹' W
  refine ⟨U, fun p => Q (p, x₁), hWopen.preimage (by fun_prop), htW, ?_, ?_⟩
  · intro p hp
    exact ((hWgood hp).1.comp p (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  · intro p hp
    obtain ⟨_, hV', hpos, heq⟩ := hWgood hp
    refine ⟨hV', fun i => ?_, heq⟩
    by_cases hi : x₀ i = 0
    · change 0 < Q (p, x₁) i
      rw [hfixed _ i hi]
      simpa [x₁, d, hi] using htpos
    · exact hpos i hi
