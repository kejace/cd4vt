import Gluck.Forward.Kernel
import Gluck.Discrete.TangentChord

namespace Gluck.Forward

def DahlbergRegularAt (A B C : ℂ) : Prop :=
  (Gluck.Discrete.crossR2 A B C = 0 ∧ B ∈ segment ℝ A C) ∨
    ∃ O R, CircumcircleR2 A B C O R ∧ InVertexCone A B C O

/-- Every vertex of a cyclic Euclidean polygon is regular in Dahlberg's sense. -/
def DahlbergRegular {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i, DahlbergRegularAt (v (i - 1)) (v i) (v (i + 1))

/-- All vertices lie on one Euclidean circle. -/
def Concyclic {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∃ O R, 0 < R ∧ ∀ i, dist O (v i) = R

/-- Project concyclicity is containment in a bundled sphere whose radius is
strictly positive. The positivity hypothesis is essential for constant families. -/
theorem concyclic_iff_exists_pos_sphere {n : ℕ} {v : ZMod n → ℂ} :
    Concyclic v ↔ ∃ s : EuclideanGeometry.Sphere ℂ,
      0 < s.radius ∧ Set.range v ⊆ (s : Set ℂ) := by
  constructor
  · rintro ⟨O, R, hR, h⟩
    refine ⟨⟨O, R⟩, hR, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact EuclideanGeometry.mem_sphere'.mpr (h i)
  · rintro ⟨s, hs, hsub⟩
    refine ⟨s.center, s.radius, hs, fun i ↦ ?_⟩
    exact EuclideanGeometry.mem_sphere'.mp (hsub (Set.mem_range_self i))

/-- A project-concyclic family is cospherical in mathlib's radius-unrestricted sense. -/
theorem Concyclic.cospherical {n : ℕ} {v : ZMod n → ℂ} (h : Concyclic v) :
    EuclideanGeometry.Cospherical (Set.range v) := by
  obtain ⟨s, _hs, hsub⟩ := concyclic_iff_exists_pos_sphere.mp h
  exact EuclideanGeometry.cospherical_iff_exists_sphere.mpr ⟨s, hsub⟩

/-- A vertex lies in the closed Euclidean disk with centre `O` and radius `R`.
Compatibility alias for mathlib's closed ball. -/
abbrev InClosedDiskR2 (O : ℂ) (R : ℝ) (P : ℂ) : Prop :=
  P ∈ Metric.closedBall O R

/-- A cyclic Euclidean polygon lies in a closed disk. -/
abbrev PolygonInClosedDiskR2 {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) : Prop :=
  ∀ i, v i ∈ Metric.closedBall O R

/-- A polygon is contained in a closed disk exactly when its range is a subset
of the corresponding metric closed ball. -/
theorem polygonInClosedDiskR2_iff_range_subset {n : ℕ} {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} :
    PolygonInClosedDiskR2 v O R ↔ Set.range v ⊆ Metric.closedBall O R := by
  rw [Set.range_subset_iff]

/-- An indexed family lies in a closed ball of least nonnegative radius.
The conjunction order deliberately preserves the established projection API. -/
def IsMinimalEnclosingBall {ι α : Type*} [PseudoMetricSpace α]
    (v : ι → α) (O : α) (R : ℝ) : Prop :=
  0 ≤ R ∧ (∀ i, v i ∈ Metric.closedBall O R) ∧
    ∀ O' R', 0 ≤ R' → (∀ i, v i ∈ Metric.closedBall O' R') → R ≤ R'

/-- A closed disk of least radius enclosing all vertices of a cyclic Euclidean
polygon.  This is the object denoted `Δ` in Dahlberg's proof of DFV. -/
abbrev MinimalEnclosingDiskR2 {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) : Prop :=
  IsMinimalEnclosingBall v O R

/-- The vertices lying on the boundary of a chosen enclosing disk.  Dahlberg
calls this boundary set `E` in the final proof of DFV. -/
abbrev OnDiskBoundaryR2 {n : ℕ} (v : ZMod n → ℂ) (O : ℂ) (R : ℝ) (i : ZMod n) :
    Prop := v i ∈ Metric.sphere O R

/-- A minimal enclosing disk has nonnegative radius. -/
theorem radius_nonneg_of_minimalEnclosingDiskR2 {n : ℕ} {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} (hΔ : MinimalEnclosingDiskR2 v O R) :
    0 ≤ R := by
  exact hΔ.1

/-- A minimal enclosing disk contains every polygon vertex. -/
theorem polygonInClosedDiskR2_of_minimalEnclosingDiskR2 {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) :
    PolygonInClosedDiskR2 v O R := by
  exact hΔ.2.1

/-- The radius of a minimal enclosing disk is bounded above by the radius of
any other enclosing disk. -/
theorem minimalEnclosingDiskR2_le_of_polygonInClosedDiskR2 {n : ℕ}
    {v : ZMod n → ℂ} {O O' : ℂ} {R R' : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R) (hR' : 0 ≤ R')
    (hcontains : PolygonInClosedDiskR2 v O' R') :
    R ≤ R' := by
  exact hΔ.2.2 O' R' hR' hcontains

/-- A minimal enclosing disk for a simple cyclic polygon has positive radius:
two adjacent distinct vertices are contained in the disk, so the radius cannot
be zero. -/
theorem radius_pos_of_minimalEnclosingDiskR2_of_isSimplePolygon {n : ℕ}
    [NeZero n] {v : ZMod n → ℂ} {O : ℂ} {R : ℝ}
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hsimple : Gluck.Discrete.IsSimplePolygon v) :
    0 < R := by
  rcases lt_or_eq_of_le hΔ.1 with hRpos | hRzero
  · exact hRpos
  · have hdist₀ : dist O (v 0) = 0 := by
      exact le_antisymm
        (by simpa only [Metric.mem_closedBall', hRzero] using hΔ.2.1 (0 : ZMod n))
        dist_nonneg
    have hdist₁ : dist O (v ((0 : ZMod n) + 1)) = 0 := by
      exact le_antisymm
        (by simpa only [Metric.mem_closedBall', hRzero] using hΔ.2.1 ((0 : ZMod n) + 1))
        dist_nonneg
    have hO₀ : O = v 0 := dist_eq_zero.mp hdist₀
    have hO₁ : O = v ((0 : ZMod n) + 1) := dist_eq_zero.mp hdist₁
    exact False.elim ((hsimple.1 (0 : ZMod n)) (hO₀.symm.trans hO₁))

/-- A boundary vertex of a disk is, in particular, contained in that disk. -/
theorem inClosedDiskR2_of_onDiskBoundaryR2 {n : ℕ} {v : ZMod n → ℂ}
    {O : ℂ} {R : ℝ} {i : ZMod n}
    (hboundary : OnDiskBoundaryR2 v O R i) :
    InClosedDiskR2 O R (v i) := by
  exact Metric.mem_closedBall'.mpr (Metric.mem_sphere'.mp hboundary).le

/-- A boundary vertex of a minimal enclosing disk has maximal distance from
the disk centre among the polygon vertices. -/
theorem dist_le_boundary_dist_of_minimalEnclosingDiskR2 {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ} {i j : ZMod n}
    (hΔ : MinimalEnclosingDiskR2 v O R)
    (hboundary : OnDiskBoundaryR2 v O R i) :
    dist O (v j) ≤ dist O (v i) := by
  rw [Metric.mem_sphere'.mp hboundary]
  exact Metric.mem_closedBall'.mp (hΔ.2.1 j)

/-- A strictly interior vertex is not on the disk boundary. -/
theorem not_onDiskBoundaryR2_of_dist_lt {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ} {i : ZMod n}
    (hinterior : dist O (v i) < R) :
    ¬ OnDiskBoundaryR2 v O R i := by
  intro hboundary
  exact (ne_of_lt hinterior) (Metric.mem_sphere'.mp hboundary)

/-- A boundary vertex and a strictly interior vertex of the same disk are
distinct. -/
theorem ne_of_onDiskBoundaryR2_of_dist_lt {n : ℕ}
    {v : ZMod n → ℂ} {O : ℂ} {R : ℝ} {i j : ZMod n}
    (hboundary : OnDiskBoundaryR2 v O R i)
    (hinterior : dist O (v j) < R) :
    i ≠ j := by
  intro hij
  subst j
  exact (not_onDiskBoundaryR2_of_dist_lt hinterior) hboundary

/-- The signed-Menger curvature profile of a cyclic Euclidean polygon. -/
noncomputable def SignedMengerProfile {n : ℕ} (v : ZMod n → ℂ) : ZMod n → ℝ :=
  fun i => Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1))

/-- The signed-Menger profile unfolds to the signed curvature of the adjacent
vertex triple. -/
theorem SignedMengerProfile_apply {n : ℕ} (v : ZMod n → ℂ) (i : ZMod n) :
    SignedMengerProfile v i =
      Gluck.Discrete.signedMengerR2 (v (i - 1)) (v i) (v (i + 1)) := rfl

/-- Reverse the cyclic order of a polygonal vertex map. -/
def ReverseCyclicPolygon {n : ℕ} (v : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i => v (-i)

/-- Every consecutive vertex triple has positive orientation.  This is the
local orientation/strict-convexity interface used by the Euclidean convex
discrete four-vertex reduction. -/
def PositivePolygonOrientation {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i, 0 < Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1))

/-- Every consecutive vertex triple has negative orientation. -/
def NegativePolygonOrientation {n : ℕ} (v : ZMod n → ℂ) : Prop :=
  ∀ i, Gluck.Discrete.crossR2 (v (i - 1)) (v i) (v (i + 1)) < 0

/-- In the stereographic/Poincaré models, a Euclidean circumcircle `(c,r)` has
space-form geodesic curvature
`(1 + ε (‖c‖²-r²))/(2r)`, with orientation supplied by the triple. -/
def ConformalMenger (ε : ℝ) (A B C : ℂ) (κ : ℝ) : Prop :=
  ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ dist c A = r ∧ dist c B = r ∧
    dist c C = r ∧
    κ = (if 0 < Gluck.Discrete.crossR2 A B C then 1 else -1) *
      (1 + ε * (‖c‖ ^ 2 - r ^ 2)) / (2 * r)

/-- A cyclic model polygon realizes a space-form signed Menger profile. -/
def RealizesConformalMenger {n : ℕ} (ε : ℝ) (v : ZMod n → ℂ)
    (κ : ZMod n → ℝ) : Prop :=
  ∀ i, ConformalMenger ε (v (i - 1)) (v i) (v (i + 1)) (κ i)

end Gluck.Forward
