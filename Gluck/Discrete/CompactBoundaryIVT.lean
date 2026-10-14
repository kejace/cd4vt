import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

/-!
# An inward intermediate-value argument on a compact physical strip

This is the topological step in the native first-pair construction. The
physical predicate is open, and the original scalar residual is continuous
there. A negative left endpoint and a positive right endpoint persist on an
inward nearby slice. A positive inward-coordinate derivative handles a zero
boundary value without an unproved strict-sign premise.
-/

open Set Filter
open scoped Topology

namespace Gluck.Discrete.CompactBoundaryIVT

/-- A positive derivative puts nearby points on the left strictly below the
value at the differentiation point. -/
theorem eventually_lt_left_of_hasDerivAt_pos {f : ℝ → ℝ} {a d : ℝ}
    (hd : HasDerivAt f d a) (hdpos : 0 < d) :
    ∀ᶠ x in 𝓝[<] a, f x < f a := by
  have hfilter : 𝓝[<] a ≤ 𝓝[≠] a :=
    nhdsWithin_mono a (fun x hx ↦ ne_of_lt hx)
  have hslope : ∀ᶠ x in 𝓝[<] a, 0 < slope f a x :=
    ((hd.tendsto_slope.mono_left hfilter).eventually (eventually_gt_nhds hdpos))
  filter_upwards [hslope, eventually_mem_nhdsWithin] with x hs hx
  have hxa : x < a := hx
  rw [slope_def_field] at hs
  have hm := mul_neg_of_pos_of_neg hs (sub_neg.mpr hxa)
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_lt hxa))] at hm
  exact sub_neg.mp hm

/-- An open physical strip with opposite endpoint signs contains a zero on
an inward nearby slice, with both parameters strictly inside their bounds. -/
theorem exists_inward_zero
    {F : ℝ → ℝ → ℝ} {P : ℝ → ℝ → Prop} {a amin lo hi : ℝ}
    (hamin : amin < a) (hlohi : lo < hi)
    (hopen : IsOpen {z : ℝ × ℝ | P z.1 z.2})
    (hphysical : ∀ y ∈ Icc lo hi, P a y)
    (hcontinuous : ContinuousOn (Function.uncurry F) {z : ℝ × ℝ | P z.1 z.2})
    (hleft : ∀ᶠ x in 𝓝[<] a, F x lo < 0)
    (hright : 0 < F a hi) :
    ∃ x ∈ Ioo amin a, ∃ y ∈ Ioo lo hi, P x y ∧ F x y = 0 := by
  have hstrip : ∀ᶠ x in 𝓝 a, ∀ y ∈ Icc lo hi, P x y :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (fun y hy ↦ hopen.mem_nhds (hphysical y hy))
  have hcontRight : ContinuousAt (fun x ↦ F x hi) a :=
    (hcontinuous.continuousAt (hopen.mem_nhds (hphysical hi (right_mem_Icc.mpr hlohi.le)))).comp
      (continuousAt_id.prodMk continuousAt_const)
  have hpositive : ∀ᶠ x in 𝓝 a, 0 < F x hi :=
    hcontRight.eventually (eventually_gt_nhds hright)
  have hamin' : ∀ᶠ x in 𝓝 a, amin < x := eventually_gt_nhds hamin
  let : NeBot (𝓝[<] a) := nhdsWithin_Iio_neBot (le_refl a)
  have hchoose : ∀ᶠ x in 𝓝[<] a,
      amin < x ∧ x < a ∧ F x lo < 0 ∧ 0 < F x hi ∧
        ∀ y ∈ Icc lo hi, P x y := by
    filter_upwards [hamin'.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin, hleft,
      hpositive.filter_mono nhdsWithin_le_nhds,
      hstrip.filter_mono nhdsWithin_le_nhds] with x hx0 hx1 hxlo hxhi hxP
    exact ⟨hx0, hx1, hxlo, hxhi, hxP⟩
  obtain ⟨x, hx0, hx1, hxlo, hxhi, hxP⟩ := hchoose.exists
  have hcontSlice : ContinuousOn (F x) (Icc lo hi) :=
    hcontinuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y hy ↦ hxP y hy)
  obtain ⟨y, hy, hyzero⟩ := intermediate_value_Icc hlohi.le hcontSlice ⟨hxlo.le, hxhi.le⟩
  have hlo : lo < y := lt_of_le_of_ne hy.1 (by
    intro heq
    subst y
    linarith)
  have hhi : y < hi := lt_of_le_of_ne hy.2 (by
    intro heq
    subst y
    linarith)
  exact ⟨x, ⟨hx0, hx1⟩, y, ⟨hlo, hhi⟩, hxP y hy, hyzero⟩

/-- A weak boundary sign suffices if its zero case has a positive derivative
in the inward coordinate. All physical inequalities are kept in `P`. -/
theorem exists_inward_zero_of_boundary_derivative
    {F : ℝ → ℝ → ℝ} {P : ℝ → ℝ → Prop} {a amin lo hi : ℝ}
    (hamin : amin < a) (hlohi : lo < hi)
    (hopen : IsOpen {z : ℝ × ℝ | P z.1 z.2})
    (hphysical : ∀ y ∈ Icc lo hi, P a y)
    (hcontinuous : ContinuousOn (Function.uncurry F) {z : ℝ × ℝ | P z.1 z.2})
    (hleft : F a lo ≤ 0) (hright : 0 < F a hi)
    (hderiv : F a lo = 0 → ∃ d > 0, HasDerivAt (fun x ↦ F x lo) d a) :
    ∃ x ∈ Ioo amin a, ∃ y ∈ Ioo lo hi, P x y ∧ F x y = 0 := by
  apply exists_inward_zero hamin hlohi hopen hphysical hcontinuous ?_ hright
  rcases lt_or_eq_of_le hleft with hneg | heq
  · have hc : ContinuousAt (fun x ↦ F x lo) a :=
      (hcontinuous.continuousAt (hopen.mem_nhds
        (hphysical lo (left_mem_Icc.mpr hlohi.le)))).comp
          (continuousAt_id.prodMk continuousAt_const)
    exact (hc.eventually (eventually_lt_nhds hneg)).filter_mono nhdsWithin_le_nhds
  · obtain ⟨d, hdpos, hd⟩ := hderiv heq
    simpa only [heq] using eventually_lt_left_of_hasDerivAt_pos hd hdpos

end Gluck.Discrete.CompactBoundaryIVT
