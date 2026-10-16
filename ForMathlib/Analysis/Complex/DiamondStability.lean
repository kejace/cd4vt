module

public import ForMathlib.Analysis.Complex.DiamondWinding
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Persistence of diamond sign conditions

Joint continuity near a compact diamond transports strict boundary signs to all
nearby parameters. This supplies actual zeros after finite vertex perturbations.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Complex

/-- The closed coordinate diamond is compact. -/
theorem isCompact_diamond (r : ℝ) : IsCompact (diamond r) := by
  apply (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset
    (isClosed_le (by fun_prop) continuous_const)
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (norm_le_abs_re_add_abs_im z).trans hz

/-- A closed slice of the diamond boundary cut out by a continuous scalar function. -/
def diamondFace (r : ℝ) (g : ℂ → ℝ) : Set ℂ :=
  {z | |z.re| + |z.im| = r ∧ 0 ≤ g z}

lemma isCompact_diamondFace (r : ℝ) {g : ℂ → ℝ} (hg : Continuous g) :
    IsCompact (diamondFace r g) := by
  exact (isCompact_diamond r).of_isClosed_subset
    ((isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_le continuous_const hg)) (fun _ hz ↦ hz.1.le)

/-- Strict signs on a compact boundary slice persist near the parameter. -/
lemma eventually_pos_on_diamondFace {A : Type*} [TopologicalSpace A]
    {F : A → ℂ → ℂ} {a : A} {r : ℝ}
    (hF : ∀ z ∈ diamond r, ContinuousAt (fun p : A × ℂ ↦ F p.1 p.2) (a, z))
    (L : ℂ →L[ℝ] ℝ) {g : ℂ → ℝ} (hg : Continuous g)
    (hsign : ∀ z ∈ diamondFace r g, 0 < L (F a z)) :
    ∀ᶠ b in 𝓝 a, ∀ z ∈ diamondFace r g, 0 < L (F b z) := by
  apply (isCompact_diamondFace r hg).eventually_forall_of_forall_eventually
  intro z hz
  exact (L.continuous.continuousAt.comp (hF z hz.1.le))
    (Ioi_mem_nhds (hsign z hz))

/-- All four strict diamond signs persist under a jointly continuous perturbation. -/
theorem eventually_diamondSigns {A : Type*} [TopologicalSpace A]
    {F : A → ℂ → ℂ} {a : A} {r : ℝ}
    (hF : ∀ z ∈ diamond r, ContinuousAt (fun p : A × ℂ ↦ F p.1 p.2) (a, z))
    (hs : DiamondSigns (F a) r) :
    ∀ᶠ b in 𝓝 a, DiamondSigns (F b) r := by
  have ht := eventually_pos_on_diamondFace hF reCLM
    (g := fun z ↦ z.im - |z.re|) (by fun_prop)
    (fun z hz ↦ hs.top z hz.1 (sub_nonneg.mp hz.2))
  have hl := eventually_pos_on_diamondFace hF (-imCLM)
    (g := fun z ↦ -z.re - |z.im|) (by fun_prop)
    (fun z hz ↦ neg_pos.mpr (hs.left z hz.1 (sub_nonneg.mp hz.2)))
  have hb := eventually_pos_on_diamondFace hF (-reCLM)
    (g := fun z ↦ -z.im - |z.re|) (by fun_prop)
    (fun z hz ↦ neg_pos.mpr (hs.bottom z hz.1 (sub_nonneg.mp hz.2)))
  have hr := eventually_pos_on_diamondFace hF imCLM
    (g := fun z ↦ z.re - |z.im|) (by fun_prop)
    (fun z hz ↦ hs.right z hz.1 (sub_nonneg.mp hz.2))
  filter_upwards [ht, hl, hb, hr] with b ht hl hb hr
  exact ⟨fun z he hz ↦ ht z ⟨he, sub_nonneg.mpr hz⟩,
    fun z he hz ↦ neg_pos.mp (hl z ⟨he, sub_nonneg.mpr hz⟩),
    fun z he hz ↦ neg_pos.mp (hb z ⟨he, sub_nonneg.mpr hz⟩),
    fun z he hz ↦ hr z ⟨he, sub_nonneg.mpr hz⟩⟩

end Complex
