/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import ForMathlib.Analysis.Complex.WindingNumber
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Subpath

/-!
# Winding comparison in pointwise open half-planes

The separating linear functional may change discontinuously with the parameter.
Only the two loops themselves need to be continuous.
-/

@[expose] public section

open scoped unitInterval

namespace Path

/-- A pointwise predicate on every constituent path also holds on their concatenation. -/
theorem forall_concat {X : Type*} [TopologicalSpace X] {n : ℕ}
    (p : Fin (n + 1) → X) (F : (k : Fin n) → Path (p k.castSucc) (p k.succ))
    {P : X → Prop} (h0 : P (p 0)) (hF : ∀ k t, P (F k t)) :
    ∀ t, P (concat p F t) := by
  induction n with
  | zero => simpa only [concat_zero, refl_apply] using fun _ : I ↦ h0
  | succ n ih =>
    have hfirst := ih (p ∘ Fin.castSucc) (fun k ↦ F k.castSucc) h0
      (fun k ↦ hF k.castSucc)
    have hboth := Set.union_subset (Set.range_subset_iff.mpr hfirst)
      (Set.range_subset_iff.mpr (hF (Fin.last n)))
    have htrans : Set.range
        ((concat (p ∘ Fin.castSucc) (fun k ↦ F k.castSucc)).trans (F (Fin.last n))) ⊆ P :=
      (trans_range (concat (p ∘ Fin.castSucc) (fun k ↦ F k.castSucc))
        (F (Fin.last n))).symm ▸ hboth
    exact (concat_succ p F).symm ▸ Set.range_subset_iff.mp htrans

end Path

namespace Complex

/-- Two closed loops have equal winding when their values at each parameter lie in a
common open half-plane through the origin. -/
theorem windingNumberAt_eq_of_common_halfPlane (γ η : C(I, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hη : ∀ t, η t ≠ 0)
    (hγloop : γ 0 = γ 1) (hηloop : η 0 = η 1)
    (hcone : ∀ t, ∃ L : ℂ →ₗ[ℝ] ℝ, 0 < L (γ t) ∧ 0 < L (η t)) :
    windingNumberAt 0 γ hγ = windingNumberAt 0 η hη := by
  let H : C(I × I, ℂ) :=
    ⟨fun st ↦ (1 - (st.1 : ℝ)) • γ st.2 + (st.1 : ℝ) • η st.2, by fun_prop⟩
  refine windingNumberAt_eq_of_homotopy 0 γ η hγ hη H ?_
    (by simp [H]) (by simp [H]) (by simp [H, hγloop, hηloop])
  intro st hzero
  obtain ⟨L, hLγ, hLη⟩ := hcone st.2
  have hpos : 0 < L (H st) :=
    (convex_halfSpace_gt L.isLinear 0) hLγ hLη
      (sub_nonneg.mpr st.1.property.2) st.1.property.1 (sub_add_cancel _ _)
  simp [hzero] at hpos

/-- The unit-valued loop associated to a continuous real phase. -/
noncomputable def phaseCurve (φ : C(I, ℝ)) : C(I, ℂ) :=
  ⟨fun t ↦ exp ((φ t : ℂ) * Complex.I), by fun_prop⟩

/-- A phase curve never passes through the origin. -/
theorem phaseCurve_ne_zero (φ : C(I, ℝ)) (t : I) : phaseCurve φ t ≠ 0 :=
  exp_ne_zero _

/-- An arbitrary continuous phase computes the winding, whether or not it is linear. -/
theorem windingNumberAt_phaseCurve (φ : C(I, ℝ)) :
    windingNumberAt 0 (phaseCurve φ) (phaseCurve_ne_zero φ) =
      (φ 1 - φ 0) / (2 * Real.pi) := by
  apply windingNumberAt_eq_div_of_lift _ φ
  simp [phaseCurve, norm_exp_ofReal_mul_I]

/-- A nonzero boundary winding forces a zero inside any convex domain containing the loop.
The loop need not be a circular parametrization of the boundary. -/
theorem exists_zero_of_windingNumberAt_ne_zero_on_convex
    {S : Set ℂ} (hS : Convex ℝ S) (a : ℂ) (ha : a ∈ S)
    (F : ℂ → ℂ) (hF : ContinuousOn F S) (γ : C(I, ℂ))
    (hγ : ∀ t, γ t ∈ S) (hloop : γ 0 = γ 1) (havoid : ∀ t, F (γ t) ≠ 0)
    (hw : windingNumberAt 0 ⟨F ∘ γ, hF.comp_continuous γ.continuous hγ⟩ havoid ≠ 0) :
    ∃ x ∈ S, F x = 0 := by
  by_contra hnone
  push Not at hnone
  let A : C(I × I, ℂ) :=
    ⟨fun st ↦ (1 - (st.1 : ℝ)) • γ st.2 + (st.1 : ℝ) • a, by fun_prop⟩
  have hA : ∀ st, A st ∈ S := fun st ↦
    hS (hγ st.2) ha (sub_nonneg.mpr st.1.property.2) st.1.property.1
      (sub_add_cancel _ _)
  let H : C(I × I, ℂ) := ⟨F ∘ A, hF.comp_continuous A.continuous hA⟩
  have heq := windingNumberAt_eq_of_homotopy 0
    ⟨F ∘ γ, hF.comp_continuous γ.continuous hγ⟩ (ContinuousMap.const I (F a))
    havoid (fun _ ↦ hnone a ha) H (fun st ↦ hnone _ (hA st))
    (by simp [H, A, Function.comp_def]) (by simp [H, A, Function.comp_def])
    (by simp [H, A, Function.comp_def, hloop])
  exact hw (heq.trans (windingNumberAt_const 0 (F a) (fun _ ↦ hnone a ha)))

end Complex
