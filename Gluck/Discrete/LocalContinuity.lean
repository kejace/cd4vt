module

public import ForMathlib.Analysis.Calculus.ParametricPositiveSection
public import Gluck.Discrete.ProfileLengthSmoothness
public import Gluck.Discrete.TabachnikovFourActive

/-!
# Local continuous choice of coherent discrete realizations

Every positive strict-DFV profile has a `C¹` local choice of coherent realizing
polygons, for arbitrary polygon size. An existing regular four-active anchor
supplies the derivative; the parametric positive-section theorem opens its
dormant edges and corrects closure while varying the original curvature data.

The input and output topologies are the usual finite-dimensional topologies
on labelled curvature vectors, edge lengths, and complex vertex tuples.
The family is defined on a full open neighborhood in the input vector space.
This is an existence of a local choice, not a canonical or global selector,
and does not assert passage through an arbitrary given polygon. Constant
profiles are not covered by this local theorem.
-/

@[expose] public section

namespace Gluck.Discrete

open Filter Set
open scoped Topology

variable {n : ℕ} [NeZero n]

/-- A local family in the literal geometry of `RealizesR2`. The same length
function supplies exact closure, a full turn, and the simple polygon. -/
structure LocalDiscreteRealizationFamily (κ₀ : ZMod n → ℝ) where
  neighborhood : Set (ZMod n → ℝ)
  isOpen_neighborhood : IsOpen neighborhood
  base_mem : κ₀ ∈ neighborhood
  lengths : (ZMod n → ℝ) → (ZMod n → ℝ)
  contDiffOn_lengths : ContDiffOn ℝ 1 lengths neighborhood
  positive : ∀ κ ∈ neighborhood, ∀ i, 0 < κ i
  moderate : ∀ κ ∈ neighborhood, ModerateArc 0 κ (lengths κ)
  closure : ∀ κ ∈ neighborhood, closureGap κ (lengths κ) = 0
  fullTurn : ∀ κ ∈ neighborhood, turningSum κ (lengths κ) = 2 * Real.pi
  simple : ∀ κ ∈ neighborhood, IsSimplePolygon (polygonR2 κ (lengths κ))
  contDiffOn_vertices : ContDiffOn ℝ 1 (fun κ => polygonR2 κ (lengths κ)) neighborhood

namespace LocalDiscreteRealizationFamily

variable {κ₀ : ZMod n → ℝ} (S : LocalDiscreteRealizationFamily κ₀)

/-- Every member realizes its own, unmodified prescribed curvature word. -/
theorem realizesR2 {κ : ZMod n → ℝ} (hκ : κ ∈ S.neighborhood) : RealizesR2 κ :=
  ⟨S.lengths κ, S.moderate κ hκ, S.closure κ hκ, S.fullTurn κ hκ, S.simple κ hκ⟩

/-- Continuity refers to all labelled vertices simultaneously. -/
theorem continuousOn_vertices :
    ContinuousOn (fun κ => polygonR2 κ (S.lengths κ)) S.neighborhood :=
  S.contDiffOn_vertices.continuousOn

/-- The signed Menger curvature belongs to the very same continuously
selected polygon, rather than to a separately chosen realization. -/
theorem menger_curvature {κ : ZMod n → ℝ} (hκ : κ ∈ S.neighborhood) (i : ZMod n) :
    signedMengerR2 (polygonR2 κ (S.lengths κ) (i - 1))
      (polygonR2 κ (S.lengths κ) i) (polygonR2 κ (S.lengths κ) (i + 1)) = κ i := by
  let k := (i - 1).val
  have hk : (k : ZMod n) = i - 1 := ZMod.natCast_rightInverse _
  have h := signedMengerR2_development (S.moderate κ hκ) k
  simpa only [vertexR2_eq_polygon (S.closure κ hκ) (S.fullTurn κ hκ),
    Nat.cast_add, Nat.cast_one, hk, sub_add_cancel] using h

/-- Strict convexity in the oriented supporting-line form: every other
vertex lies strictly to the left of each oriented polygon edge. -/
theorem strict_support {κ : ZMod n → ℝ} (hκ : κ ∈ S.neighborhood)
    (a c : ZMod n) (hca : c ≠ a) (hca₁ : c ≠ a + 1) :
    0 < crossR2 (polygonR2 κ (S.lengths κ) a)
      (polygonR2 κ (S.lengths κ) (a + 1)) (polygonR2 κ (S.lengths κ) c) :=
  crossR2_polygonR2_edge_vertex_pos (S.moderate κ hκ) (S.positive κ hκ)
    (S.closure κ hκ) (S.fullTurn κ hκ) a c hca hca₁

end LocalDiscreteRealizationFamily

/-- A regular nonnegative anchor with active-supported corrections produces
a local family of strictly positive coherent polygons. -/
theorem nonempty_localDiscreteRealizationFamily_of_active_surjective
    (hn : 3 ≤ n) {κ₀ ℓ₀ : ZMod n → ℝ}
    (hκ₀ : ∀ i, 0 < κ₀ i)
    (hℓ₀ : ∀ i, 0 ≤ ℓ₀ i ∧ ℓ₀ i < edgeCap κ₀ i)
    (hzero : closureMapR3 (κ₀, ℓ₀) = 0)
    (hactive : ∀ y : ℂ × ℝ, ∃ b : ZMod n → ℝ,
      fderiv ℝ (fun L => closureMapR3 (κ₀, L)) ℓ₀ b = y ∧
        ∀ i, ℓ₀ i = 0 → b i = 0) :
    Nonempty (LocalDiscreteRealizationFamily κ₀) := by
  let V : Set ((ZMod n → ℝ) × (ZMod n → ℝ)) :=
    {p | ∀ i, 0 < p.1 i ∧
      |p.1 i * (p.2 (i - 1) / 2)| < 1 ∧ |p.1 i * (p.2 i / 2)| < 1}
  have hV : IsOpen V := by
    have hVe : V = ⋂ i : ZMod n, {p : (ZMod n → ℝ) × (ZMod n → ℝ) |
      0 < p.1 i ∧ |p.1 i * (p.2 (i - 1) / 2)| < 1 ∧
        |p.1 i * (p.2 i / 2)| < 1} := by ext p; simp [V]
    rw [hVe]
    apply isOpen_iInter_of_finite
    intro i
    have hk : Continuous (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) => p.1 i) := by fun_prop
    have hl : Continuous (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) =>
        |p.1 i * (p.2 (i - 1) / 2)|) := by fun_prop
    have hr : Continuous (fun p : (ZMod n → ℝ) × (ZMod n → ℝ) =>
        |p.1 i * (p.2 i / 2)|) := by fun_prop
    exact (isOpen_lt continuous_const hk).inter
      ((isOpen_lt hl continuous_const).inter (isOpen_lt hr continuous_const))
  have hw := strict_arc_walls_of_nonneg_lt_edgeCap hκ₀ hℓ₀
  have hpartial := fderiv_closureMapR3_inr hw
  obtain ⟨U, s, hUopen, hU₀, hscd, hgood⟩ :=
    (contDiffAt_closureMapR3_joint (r := 1) hw).exists_localSection_pos_of_active_surjective
      (fun i => (hℓ₀ i).1) (by simpa only [hpartial] using hactive) hV
      (fun i => ⟨hκ₀ i, hw i⟩)
  have hpos : ∀ κ ∈ U, ∀ i, 0 < κ i := fun κ hκ i => (hgood κ hκ).1 i |>.1
  have hmod : ∀ κ ∈ U, ModerateArc 0 κ (s κ) := by
    intro κ hκ
    apply moderateArc_zero_iff.mpr
    intro i
    have hi := (hgood κ hκ).1 i
    have hl := (hgood κ hκ).2.1
    refine ⟨hl i, ?_, ?_⟩
    · simpa only [abs_mul, abs_of_pos (half_pos (hl (i - 1)))] using hi.2.1
    · simpa only [abs_mul, abs_of_pos (half_pos (hl i))] using hi.2.2
  have heq : ∀ κ ∈ U, closureMapR3 (κ, s κ) = 0 :=
    fun κ hκ => (hgood κ hκ).2.2.trans hzero
  have hclose : ∀ κ ∈ U, closureGap κ (s κ) = 0 :=
    fun κ hκ => congrArg Prod.fst (heq κ hκ)
  have hturn : ∀ κ ∈ U, turningSum κ (s κ) = 2 * Real.pi := by
    intro κ hκ
    have ht := congrArg Prod.snd (heq κ hκ)
    exact sub_eq_zero.mp ht
  refine ⟨⟨U, hUopen, hU₀, s, hscd, hpos, hmod, hclose, hturn,
    fun κ hκ => isSimplePolygon_of_turningPositive hn (hmod κ hκ) (hpos κ hκ)
      (hclose κ hκ) (hturn κ hκ), ?_⟩⟩
  intro κ hκ
  exact (contDiffAt_polygonR2_joint (fun i => ((hgood κ hκ).1 i).2)).comp_contDiffWithinAt κ
    (contDiffWithinAt_id.prodMk (hscd κ hκ))

/-- The existing four-active anchor yields a local family without needing
the anchor-selection rule to vary continuously with the profile. -/
theorem RegularFourAnchor.nonempty_localDiscreteRealizationFamily
    {κ₀ : ZMod n → ℝ} (A : RegularFourAnchor κ₀) (hκ₀ : ∀ i, 0 < κ₀ i) :
    Nonempty (LocalDiscreteRealizationFamily κ₀) := by
  have hb := A.frame.lengths_nonneg_lt_edgeCap κ₀ A.halfLengths hκ₀
    A.positive A.start_lt A.finish_lt
  have hzero : closureMapR3 (κ₀, A.frame.lengths A.halfLengths) = 0 := by
    unfold closureMapR3
    rw [A.frame.closureGap_eq_controller, A.frame.turningSum_eq_controller, A.zero]
    simp
  have h01 := A.frame.strictMono (show (0 : Fin 4) < 1 by decide)
  have h12 := A.frame.strictMono (show (1 : Fin 4) < 2 by decide)
  have h23 := A.frame.strictMono (show (2 : Fin 4) < 3 by decide)
  have h3n := A.frame.lt_n 3
  exact nonempty_localDiscreteRealizationFamily_of_active_surjective (by omega)
    hκ₀ hb hzero (A.frame.active_surj_of_controller_regular hκ₀ A.positive hb A.zero A.regular)

/-- Local continuous (indeed `C¹`) coherent realization for every positive
strict-DFV word, including repeated readings and constant runs. -/
theorem localContinuousRealization_of_dfv
    {κ₀ : ZMod n → ℝ} {c : ℝ} (hκ₀ : ∀ i, 0 < κ₀ i) (hdfv : DFV κ₀ c) :
    Nonempty (LocalDiscreteRealizationFamily κ₀) := by
  obtain ⟨A⟩ := nonempty_regularFourAnchor_of_dfv hκ₀ hdfv
  exact A.nonempty_localDiscreteRealizationFamily hκ₀

/-- The local-continuity strengthening of the nonconstant part of
`TabachnikovProblem2`, at every `n ≥ 4`, with no producer or rank assumption. -/
theorem tabachnikovProblem2_local_continuity (_hn : 4 ≤ n)
    {κ₀ : ZMod n → ℝ} (hκ₀ : DiscreteFourVertexPos κ₀)
    (hnonconstant : ¬ ∃ c, ∀ i, κ₀ i = c) :
    Nonempty (LocalDiscreteRealizationFamily κ₀) := by
  obtain ⟨hp, hc | ⟨c, _, hd⟩⟩ := hκ₀
  · exact (hnonconstant hc).elim
  · exact localContinuousRealization_of_dfv hp hd

end Gluck.Discrete
