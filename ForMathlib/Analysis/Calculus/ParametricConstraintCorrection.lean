import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Parametric correction of regular constraints

Near a regular solution of a parameter-dependent equation, a fixed continuous
linear right inverse of the partial derivative determines a smooth correction.
The correction changes the unknown only in the range of that right inverse
and fixes points which already satisfy the equation.

This is an application of Mathlib's implicit function theorem, not a new
implicit function theorem. No project-specific declarations are imported.
-/

open Filter Set
open scoped Topology ContDiff

section

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A smooth local correction of a parameter-dependent regular constraint.
The correction preserves the parameter, changes the unknown in `range R`,
and fixes every nearby solution of the original level equation. -/
theorem ContDiffAt.exists_parametricConstraintCorrection
    {n : ℕ∞ω} {f : P × E → F} {p₀ : P} {x₀ : E}
    (hf : ContDiffAt ℝ n f (p₀, x₀)) (hn : n ≠ 0)
    (R : F →L[ℝ] E)
    (hR : (fderiv ℝ f (p₀, x₀) ∘L ContinuousLinearMap.inr ℝ P E) ∘L R =
      ContinuousLinearMap.id ℝ F) :
    ∃ Q : P × E → E,
      ContDiffAt ℝ n Q (p₀, x₀) ∧ Q (p₀, x₀) = x₀ ∧
      (∀ q, Q q - q.2 ∈ R.range) ∧
      (∀ᶠ q in 𝓝 (p₀, x₀), f (q.1, Q q) = f (p₀, x₀)) ∧
      (∀ᶠ q in 𝓝 (p₀, x₀), f q = f (p₀, x₀) → Q q = q.2) := by
  let L : (P × E) × F →L[ℝ] P × E :=
    ContinuousLinearMap.fst ℝ (P × E) F +
      ContinuousLinearMap.inr ℝ P E ∘L R ∘L ContinuousLinearMap.snd ℝ (P × E) F
  have hL : ∀ q a, L (q, a) = (q.1, q.2 + R a) := by
    intro q a
    ext <;> simp [L]
  have hL₀ : L ((p₀, x₀), 0) = (p₀, x₀) := by simp [hL]
  have hG : ContDiffAt ℝ n (fun v => f (L v)) ((p₀, x₀), (0 : F)) := by
    exact (hL₀ ▸ hf).comp _ L.contDiff.contDiffAt
  have hd : fderiv ℝ (fun v => f (L v)) ((p₀, x₀), (0 : F)) =
      fderiv ℝ f (p₀, x₀) ∘L L := by
    have hf' : HasStrictFDerivAt f (fderiv ℝ f (p₀, x₀)) (L ((p₀, x₀), 0)) := by
      simpa only [hL₀] using hf.hasStrictFDerivAt hn
    have h := hf'.comp ((p₀, x₀), (0 : F))
      L.hasStrictFDerivAt
    exact h.hasFDerivAt.fderiv
  have hinr : (fderiv ℝ f (p₀, x₀) ∘L L) ∘L
      ContinuousLinearMap.inr ℝ (P × E) F = ContinuousLinearMap.id ℝ F := by
    rw [← hR]
    ext a
    simp [L]
  have hinv : (fderiv ℝ (fun v => f (L v)) ((p₀, x₀), (0 : F)) ∘L
      ContinuousLinearMap.inr ℝ (P × E) F).IsInvertible := by
    rw [hd, hinr]
    exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  let ψ := hG.implicitFunction hn hinv
  have hψ₀ : ψ (p₀, x₀) = 0 := hG.implicitFunction_apply_self hn hinv
  have hψcd : ContDiffAt ℝ n ψ (p₀, x₀) := hG.contDiffAt_implicitFunction hn hinv
  refine ⟨fun q => q.2 + R (ψ q), contDiffAt_snd.add (R.contDiff.contDiffAt.comp _ hψcd),
    by simp [hψ₀], ?_, ?_, ?_⟩
  · intro q
    exact ⟨ψ q, by simp⟩
  · filter_upwards [hG.eventually_apply_implicitFunction hn hinv] with q hq
    change f (L (q, ψ q)) = f (L ((p₀, x₀), 0)) at hq
    rw [hL, hL₀] at hq
    exact hq
  · have ht : Tendsto (fun q : P × E => (q, (0 : F)))
        (𝓝 (p₀, x₀)) (𝓝 ((p₀, x₀), 0)) := continuousAt_id.prodMk continuousAt_const
    have he := ht.eventually (hG.eventually_apply_eq_iff_implicitFunction hn hinv)
    filter_upwards [he] with q hq
    intro hsol
    have hz : ψ q = 0 := hq.mp (by simpa [hL] using hsol)
    simp [hz]

end

section DenseCorrectionDirections

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A surjection onto a finite-dimensional space has a continuous linear right
inverse with image in any prescribed dense linear subspace of its domain. -/
theorem ContinuousLinearMap.exists_rightInverse_range_subset_of_dense
    (A : E →L[ℝ] F) (hA : Function.Surjective A)
    {D : Submodule ℝ E} (hD : Dense (D : Set E)) :
    ∃ R : F →L[ℝ] E, A ∘L R = ContinuousLinearMap.id ℝ F ∧
      ∀ y, R y ∈ D := by
  let B : D →L[ℝ] F := A ∘L D.subtypeL
  have hB : B.range = ⊤ := by
    have hclosed : IsClosed (B.range : Set F) := Submodule.closed_of_finiteDimensional _
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨x, rfl⟩ := hA y
    have hmem : A x ∈ closure (B.range : Set F) :=
      map_mem_closure A.continuous (hD x) fun z hz => ⟨⟨z, hz⟩, rfl⟩
    rwa [hclosed.closure_eq] at hmem
  obtain ⟨g, hg⟩ := B.exists_rightInverse_of_surjective hB
  refine ⟨D.subtypeL ∘L g, ?_, fun y => (g y).2⟩
  rw [← ContinuousLinearMap.comp_assoc]
  exact hg

end DenseCorrectionDirections

section LocalSection

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A local `C¹` family of exact solutions through a regular solution lying in
a dense linear subspace. Every selected solution remains in that subspace.
The family is `C¹` on a single open neighborhood, not just at the base point. -/
theorem ContDiffAt.exists_localSection_mem_submodule
    {f : P × E → F} {p₀ : P} {x₀ : E}
    (hf : ContDiffAt ℝ 1 f (p₀, x₀))
    (hA : Function.Surjective
      (fderiv ℝ f (p₀, x₀) ∘L ContinuousLinearMap.inr ℝ P E))
    {D : Submodule ℝ E} (hD : Dense (D : Set E)) (hx₀ : x₀ ∈ D) :
    ∃ (U : Set P) (s : P → E), IsOpen U ∧ p₀ ∈ U ∧
      ContDiffOn ℝ 1 s U ∧ s p₀ = x₀ ∧
      (∀ p ∈ U, f (p, s p) = f (p₀, x₀)) ∧ (∀ p, s p ∈ D) := by
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨R, hR, hRD⟩ := ContinuousLinearMap.exists_rightInverse_range_subset_of_dense
    (fderiv ℝ f (p₀, x₀) ∘L ContinuousLinearMap.inr ℝ P E) hA hD
  obtain ⟨Q, hQcd, hQ₀, hQrange, hQeq, -⟩ :=
    hf.exists_parametricConstraintCorrection one_ne_zero R hR
  let s : P → E := fun p => Q (p, x₀)
  have hscd : ContDiffAt ℝ 1 s p₀ :=
    hQcd.comp p₀ (contDiffAt_id.prodMk contDiffAt_const)
  have ht : Tendsto (fun p : P => (p, x₀)) (𝓝 p₀) (𝓝 (p₀, x₀)) :=
    continuousAt_id.prodMk continuousAt_const
  have hgood : ∀ᶠ p in 𝓝 p₀, ContDiffAt ℝ 1 s p ∧ f (p, s p) = f (p₀, x₀) :=
    (hscd.eventually (by norm_num)).and (ht.eventually hQeq)
  obtain ⟨U, hUgood, hUopen, hp₀⟩ := mem_nhds_iff.mp hgood
  refine ⟨U, s, hUopen, hp₀, fun p hp => (hUgood hp).1.contDiffWithinAt,
    hQ₀, fun p hp => (hUgood hp).2, ?_⟩
  intro p
  obtain ⟨a, ha⟩ := hQrange (p, x₀)
  have hmem : s p - x₀ ∈ D := by rw [← ha]; exact hRD a
  simpa using D.add_mem hmem hx₀

end LocalSection
