/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
import Mathlib.Analysis.Complex.RealDeriv
import Gluck.Discrete.CurvatureLinkage
import Gluck.Discrete.MonotoneCuts

/-!
# Trace constraints for monotone-run compression

The product identities in `MonotoneCuts` compress the *ratios* along a
monotone run.  They do not compress its Euclidean linkage trace.  This file
records the first obstruction in the concrete `LinkageAffine` model.

For endpoint radii `r,s`, the first-order translation coefficient of the
vertex transfer is the harmonic quantity

`c(r,s) = 2*r*s/(r+s)`.

If one rigidly replaces a small endpoint cell by three cells and distributes
its total angle with asymptotic nonnegative weights of sum one, equality of
the first-order translations requires `c(r₀,r₃)` to be the corresponding
convex combination of the three adjacent coefficients.  The radius word
`(2, 1/5, 1/5, 2)` violates this condition: the endpoint coefficient is `2`,
whereas all adjacent coefficients are at most `4/11`.

This is only a no-go theorem for rigid local compression.  It does not rule
out a relative construction in which the complementary polygon moves.  Such
a construction must be phrased as an intersection or degree statement for
`LinkageAffine` endpoint traces rather than as an equality obtained from
telescoping curvature ratios.
-/

namespace Gluck.Discrete

open scoped BigOperators

/-! ## The concrete finite-run trace -/

/-- The ordered product of the vertex-frame transfers along a run with `p`
edges and `p+1` prescribed radii. -/
noncomputable def vertexRunTrace {p : ℕ}
    (r : Fin (p + 1) → ℝ) (y : Fin p → ℂ) : LinkageAffine :=
  LinkageAffine.product <|
    List.ofFn fun j : Fin p ↦
      vertexTransfer (r j.castSucc) (r j.succ) (y j)

/-- The run trace parameterized by real lifted edge angles. -/
noncomputable def vertexRunTraceAtAngles {p : ℕ}
    (r : Fin (p + 1) → ℝ) (delta : Fin p → ℝ) : LinkageAffine :=
  vertexRunTrace r fun j ↦ unitPhase (delta j)

/-- The run trace parameterized by its physical chord lengths. -/
noncomputable def vertexRunTraceAtLengths {p : ℕ}
    (r : Fin (p + 1) → ℝ) (ell : Fin p → ℝ) : LinkageAffine :=
  vertexRunTraceAtAngles r fun j ↦
    linkageAngle (r j.castSucc) (r j.succ) (ell j)

/-- Strict positivity and the moderate-cell wall for every edge of a finite
radius run. -/
def AdmissibleRunLengths {p : ℕ}
    (r : Fin (p + 1) → ℝ) (ell : Fin p → ℝ) : Prop :=
  (∀ i, 0 < r i) ∧
    ∀ j, 0 < ell j ∧
      ell j < 2 / max (r j.castSucc)⁻¹ (r j.succ)⁻¹

/-- The exact endpoint-trace image of the strict physical run.  A relative
run-lifting theorem should assert an intersection or degree statement for
this set and the trace image of the complementary carrier. -/
noncomputable def admissibleVertexRunTraceSet {p : ℕ}
    (r : Fin (p + 1) → ℝ) : Set LinkageAffine :=
  {g | ∃ ell, AdmissibleRunLengths r ell ∧ vertexRunTraceAtLengths r ell = g}

/-- The strict physical run-trace image in one fixed total-angle fiber.  This
is the source object needed by a whole-run outer-heavy lifting theorem. -/
noncomputable def admissibleVertexRunTraceFiber {p : ℕ}
    (r : Fin (p + 1) → ℝ) (D : ℝ) : Set LinkageAffine :=
  {g | ∃ ell, AdmissibleRunLengths r ell ∧
    (∑ j, linkageAngle (r j.castSucc) (r j.succ) (ell j)) = D ∧
    vertexRunTraceAtLengths r ell = g}

/-- Forgetting the total-angle equation maps a trace fiber into the full
admissible run-trace image. -/
theorem admissibleVertexRunTraceFiber_subset {p : ℕ}
    (r : Fin (p + 1) → ℝ) (D : ℝ) :
    admissibleVertexRunTraceFiber r D ⊆ admissibleVertexRunTraceSet r := by
  rintro g ⟨ell, hell, _hsum, htrace⟩
  exact ⟨ell, hell, htrace⟩

/-- The single-cell trace joining the two endpoint radii with total lifted
angle `D`.  This is the tempting compressed target; matching it is an extra
translation constraint, not a consequence of ratio telescoping. -/
noncomputable def compressedVertexTrace {p : ℕ}
    (r : Fin (p + 1) → ℝ) (D : ℝ) : LinkageAffine :=
  vertexTransfer (r 0) (r (Fin.last p)) (unitPhase D)

@[simp] theorem vertexRunTrace_linear {p : ℕ}
    (r : Fin (p + 1) → ℝ) (y : Fin p → ℂ) :
    (vertexRunTrace r y).linear = ∏ j, y j := by
  rw [vertexRunTrace, LinkageAffine.product_linear, List.map_ofFn,
    List.prod_ofFn]
  rfl

/-- The rotation part of a run trace only remembers the sum of its lifted
angles.  All geometric difficulty in compression is therefore in the
translation part (together with positivity and wall conditions). -/
theorem vertexRunTraceAtAngles_linear {p : ℕ}
    (r : Fin (p + 1) → ℝ) (delta : Fin p → ℝ) :
    (vertexRunTraceAtAngles r delta).linear = unitPhase (∑ j, delta j) := by
  rw [vertexRunTraceAtAngles, vertexRunTrace_linear]
  classical
  have hphase : ∀ s : Finset (Fin p),
      unitPhase (∑ j ∈ s, delta j) = ∏ j ∈ s, unitPhase (delta j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [unitPhase]
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, unitPhase_add, ih]
  exact (hphase Finset.univ).symm

theorem vertexRunTraceAtLengths_linear {p : ℕ}
    (r : Fin (p + 1) → ℝ) (ell : Fin p → ℝ) :
    (vertexRunTraceAtLengths r ell).linear =
      unitPhase (∑ j,
        linkageAngle (r j.castSucc) (r j.succ) (ell j)) := by
  exact vertexRunTraceAtAngles_linear r _

/-- The run translation required to close against a complementary affine
trace at total run turn `D`. -/
noncomputable def complementaryTraceTarget (D : ℝ) (complement : LinkageAffine) : ℂ :=
  -(unitPhase D * complement.shift)

/-- Affine closure identifies the run translation with the complementary
trace target. -/
theorem shift_eq_complementary_trace_target_of_comp_eq_one
    {run complement : LinkageAffine} {D : ℝ}
    (hlinear : run.linear = unitPhase D)
    (hclose : LinkageAffine.comp run complement = LinkageAffine.one) :
    run.shift = complementaryTraceTarget D complement := by
  have h := congrArg LinkageAffine.shift hclose
  change run.shift + run.linear * complement.shift = 0 at h
  unfold complementaryTraceTarget
  rw [hlinear] at h
  linear_combination h

/-- A matching complementary translation and closing rotation imply affine
closure. -/
theorem comp_eq_one_of_shift_eq_complementary_trace_target
    {run complement : LinkageAffine} {D : ℝ}
    (hrun : run.linear = unitPhase D)
    (hlinear : run.linear * complement.linear = 1)
    (hshift : run.shift = complementaryTraceTarget D complement) :
    LinkageAffine.comp run complement = LinkageAffine.one := by
  ext
  · simpa [LinkageAffine.comp, LinkageAffine.one] using hlinear
  · change run.shift + run.linear * complement.shift = 0
    rw [hshift, hrun]
    simp [complementaryTraceTarget]

/-- For two lifted run traces whose total angle is `2π`, affine closure is
equivalent to their one remaining complex translation equation. -/
theorem vertex_run_trace_at_angles_comp_eq_one_iff_shift
    {p q : ℕ} (r : Fin (p + 1) → ℝ) (delta : Fin p → ℝ)
    (s : Fin (q + 1) → ℝ) (theta : Fin q → ℝ)
    (htotal : (∑ j, delta j) + ∑ j, theta j = 2 * Real.pi) :
    LinkageAffine.comp (vertexRunTraceAtAngles r delta)
        (vertexRunTraceAtAngles s theta) = LinkageAffine.one ↔
      (vertexRunTraceAtAngles r delta).shift =
        complementaryTraceTarget (∑ j, delta j)
          (vertexRunTraceAtAngles s theta) := by
  have hrun :=
    vertexRunTraceAtAngles_linear r delta
  have hlinear :
      (vertexRunTraceAtAngles r delta).linear *
          (vertexRunTraceAtAngles s theta).linear = 1 := by
    rw [vertexRunTraceAtAngles_linear, vertexRunTraceAtAngles_linear,
      ← unitPhase_add, htotal]
    simp [unitPhase]
  constructor
  · exact shift_eq_complementary_trace_target_of_comp_eq_one hrun
  · exact comp_eq_one_of_shift_eq_complementary_trace_target hrun hlinear

/-- Every trace in the fixed-total-angle fiber has the prescribed rotation
part.  Only its translation remains to be matched to a complementary
carrier trace. -/
theorem mem_admissibleVertexRunTraceFiber_linear {p : ℕ}
    {r : Fin (p + 1) → ℝ} {D : ℝ} {g : LinkageAffine}
    (hg : g ∈ admissibleVertexRunTraceFiber r D) :
    g.linear = unitPhase D := by
  obtain ⟨ell, _hell, hsum, rfl⟩ := hg
  rw [vertexRunTraceAtLengths_linear, hsum]

/-- Every angle used by an admissible physical run lies in its strict
single-edge chart image. -/
theorem AdmissibleRunLengths.angle_mem_chartImage {p : ℕ}
    {r : Fin (p + 1) → ℝ} {ell : Fin p → ℝ}
    (h : AdmissibleRunLengths r ell) (j : Fin p) :
    linkageAngle (r j.castSucc) (r j.succ) (ell j) ∈
      chartMap (r j.castSucc)⁻¹ (r j.succ)⁻¹ ''
        Set.Ioo (0 : ℝ) (2 / max (r j.castSucc)⁻¹ (r j.succ)⁻¹) := by
  exact linkageAngle_mem_chartImage (h.1 j.castSucc) (h.1 j.succ)
    (h.2 j).1 (h.2 j).2

@[simp] theorem compressedVertexTrace_linear {p : ℕ}
    (r : Fin (p + 1) → ℝ) (D : ℝ) :
    (compressedVertexTrace r D).linear = unitPhase D := by
  rfl

/-- Once the real angle sums agree, exact rigid run compression is equivalent
to the one remaining complex translation equation. -/
theorem vertexRunTraceAtAngles_eq_compressed_iff_shift {p : ℕ}
    (r : Fin (p + 1) → ℝ) (delta : Fin p → ℝ) (D : ℝ)
    (hsum : ∑ j, delta j = D) :
    vertexRunTraceAtAngles r delta = compressedVertexTrace r D ↔
      (vertexRunTraceAtAngles r delta).shift =
        (compressedVertexTrace r D).shift := by
  constructor
  · exact fun h ↦ congrArg LinkageAffine.shift h
  · intro hshift
    ext
    · rw [vertexRunTraceAtAngles_linear, compressedVertexTrace_linear, hsum]
    · exact hshift

/-- Membership of the tempting compressed trace in a strict fixed-angle run
fiber is exactly one complex translation equation, once the angle sum is
imposed.  This does not assert that such a match always exists. -/
theorem compressedVertexTrace_mem_fiber_iff {p : ℕ}
    (r : Fin (p + 1) → ℝ) (D : ℝ) :
    compressedVertexTrace r D ∈ admissibleVertexRunTraceFiber r D ↔
      ∃ ell, AdmissibleRunLengths r ell ∧
        (∑ j, linkageAngle (r j.castSucc) (r j.succ) (ell j)) = D ∧
        (vertexRunTraceAtLengths r ell).shift =
          (compressedVertexTrace r D).shift := by
  constructor
  · rintro ⟨ell, hell, hsum, htrace⟩
    exact ⟨ell, hell, hsum, congrArg LinkageAffine.shift htrace⟩
  · rintro ⟨ell, hell, hsum, hshift⟩
    refine ⟨ell, hell, hsum, ?_⟩
    apply (vertexRunTraceAtAngles_eq_compressed_iff_shift
      r (fun j ↦ linkageAngle (r j.castSucc) (r j.succ) (ell j)) D hsum).2
    exact hshift

/-! ## The first-order rigid-compression obstruction -/

/-- The coefficient of the linear imaginary translation of a small-angle
vertex transfer between circles of radii `r` and `s`. -/
noncomputable def vertexTraceSlope (r s : ℝ) : ℝ :=
  2 * r * s / (r + s)

/-- The exact algebraic factorization from which `vertexTraceSlope` is read
at phase one. -/
lemma vertexCoeff_factor (r s : ℝ) (y : ℂ) :
    vertexCoeff r s y =
      (y - 1) * (((r * s : ℝ) : ℂ) * (y + 1) / linkageDen r s y) := by
  simp only [vertexCoeff]
  ring

/-- At phase one, the residual factor in `vertexCoeff_factor` is the real
number `vertexTraceSlope r s`, provided the two radii do not cancel. -/
lemma vertexCoeff_residual_one {r s : ℝ} (hrs : r + s ≠ 0) :
    (((r * s : ℝ) : ℂ) * ((1 : ℂ) + 1) / linkageDen r s 1) =
      (vertexTraceSlope r s : ℝ) := by
  rw [show linkageDen r s 1 = ((r + s : ℝ) : ℂ) by
    simp [linkageDen, add_comm]]
  simp only [vertexTraceSlope]
  rw [show (((r * s : ℝ) : ℂ) * ((1 : ℂ) + 1)) =
      (((2 * r * s : ℝ) : ℂ)) by push_cast; ring]
  apply (div_eq_iff (Complex.ofReal_ne_zero.mpr hrs)).2
  norm_cast
  field_simp [hrs]

/-- The vertex coefficient varies continuously away from its denominator pole. -/
lemma continuousWithinAt_vertexCoeff {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {y : X → ℂ} {s : Set X} {x : X}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
    (hy : ContinuousWithinAt y s x) (hden : linkageDen (f x) (g x) (y x) ≠ 0) :
    ContinuousWithinAt (fun z ↦ vertexCoeff (f z) (g z) (y z)) s x := by
  have hden' : (g x : ℂ) + (f x : ℂ) * y x ≠ 0 := hden
  unfold vertexCoeff linkageDen
  apply ContinuousWithinAt.div
  · fun_prop
  · fun_prop
  · exact hden'

/-- The unit complex phase preserves continuity within a set. -/
@[fun_prop] lemma continuousWithinAt_unitPhase {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {s : Set X} {x : X} (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun z ↦ unitPhase (f z)) s x := by
  unfold unitPhase
  exact ((Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt hf).mul
    continuousWithinAt_const).cexp

/-- Complexified small-angle path through one vertex transfer.  Restricting
`z` to the real axis recovers the physical phase `exp(i*z)`. -/
noncomputable def vertexCoeffAlongAngle (r s : ℝ) (z : ℂ) : ℂ :=
  vertexCoeff r s (Complex.exp (z * Complex.I))

/-- The real-angle derivative of the unit complex phase. -/
theorem hasDerivAt_unitPhase (delta : ℝ) :
    HasDerivAt (fun x : ℝ ↦ unitPhase x) (unitPhase delta * Complex.I) delta := by
  have hcomplex := ((hasDerivAt_id (𝕜 := ℂ) (delta : ℂ)).mul_const Complex.I).cexp
  simpa [unitPhase] using hcomplex.comp_ofReal

/-- The angle derivative of one vertex coefficient, expressed at its complex phase. -/
noncomputable def vertexCoeffAngleDerivative (r s : ℝ) (y : ℂ) : ℂ :=
  Complex.I * ((r * s : ℝ) : ℂ) * y *
    ((r : ℂ) * y ^ 2 + 2 * (s : ℂ) * y + r) / linkageDen r s y ^ 2

/-- Exact complex angle derivative of one vertex coefficient away from its pole. -/
theorem hasDerivAt_vertexCoeffAlongAngle {r s : ℝ} {z : ℂ}
    (hden : linkageDen r s (Complex.exp (z * Complex.I)) ≠ 0) :
    HasDerivAt (vertexCoeffAlongAngle r s)
      (vertexCoeffAngleDerivative r s (Complex.exp (z * Complex.I))) z := by
  unfold vertexCoeffAlongAngle
  let y : ℂ → ℂ := fun w ↦ Complex.exp (w * Complex.I)
  have hy : HasDerivAt y (y z * Complex.I) z := by
    have hz := (hasDerivAt_id (𝕜 := ℂ) z).mul_const Complex.I
    simpa [y] using hz.cexp
  have hnum : HasDerivAt
      (fun w ↦ ((r * s : ℝ) : ℂ) * (y w ^ 2 - 1))
      (((r * s : ℝ) : ℂ) * (2 * y z * (y z * Complex.I))) z := by
    simpa using HasDerivAt.const_mul (((r * s : ℝ) : ℂ)) ((hy.pow 2).sub_const 1)
  have hd : HasDerivAt (fun w ↦ (s : ℂ) + (r : ℂ) * y w)
      ((r : ℂ) * (y z * Complex.I)) z := by
    have hd' : HasDerivAt (fun w ↦ (r : ℂ) * y w + (s : ℂ))
        ((r : ℂ) * (y z * Complex.I)) z :=
      (HasDerivAt.const_mul (r : ℂ) hy).add_const (s : ℂ)
    simpa only [add_comm] using hd'
  have hden' : (s : ℂ) + (r : ℂ) * y z ≠ 0 := by
    simpa [linkageDen, y] using hden
  change HasDerivAt (fun w ↦ ((r * s : ℝ) : ℂ) * (y w ^ 2 - 1) /
    ((s : ℂ) + (r : ℂ) * y w))
      (vertexCoeffAngleDerivative r s (Complex.exp (z * Complex.I))) z
  apply (hnum.div hd hden').congr_deriv
  unfold vertexCoeffAngleDerivative linkageDen
  dsimp [y]
  simp only [linkageDen] at hden
  field_simp [hden]
  ring

/-- Exact real-angle derivative of one vertex coefficient away from its pole. -/
theorem hasDerivAt_vertexCoeff_unitPhase {r s delta : ℝ}
    (hden : linkageDen r s (unitPhase delta) ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ vertexCoeff r s (unitPhase x))
      (vertexCoeffAngleDerivative r s (unitPhase delta)) delta := by
  have hcomplex := hasDerivAt_vertexCoeffAlongAngle (z := (delta : ℂ)) (by
    simpa [unitPhase] using hden)
  simpa [vertexCoeffAlongAngle, unitPhase] using hcomplex.comp_ofReal

/-- The harmonic coefficient is the actual first derivative of the local
vertex translation at the collapsed cell. -/
theorem hasDerivAt_vertexCoeffAlongAngle_zero {r s : ℝ} (hrs : r + s ≠ 0) :
    HasDerivAt (vertexCoeffAlongAngle r s)
      (Complex.I * (vertexTraceSlope r s : ℝ)) 0 := by
  have hden : linkageDen r s (Complex.exp ((0 : ℂ) * Complex.I)) ≠ 0 := by
    simpa [linkageDen, add_comm] using Complex.ofReal_ne_zero.mpr hrs
  have hrs' : (r : ℂ) + (s : ℂ) ≠ 0 := by
    simpa using Complex.ofReal_ne_zero.mpr hrs
  apply (hasDerivAt_vertexCoeffAlongAngle hden).congr_deriv
  simp [vertexCoeffAngleDerivative, vertexTraceSlope, linkageDen]
  field_simp [hrs', add_comm]
  ring

/-- First-order coefficient matching for an arbitrary rigid finite run.  The
weights are the limiting nonnegative fractions of the total small angle
assigned to its edges. -/
def FirstOrderRunMatch {p : ℕ}
    (r : Fin (p + 1) → ℝ) (lambda : Fin p → ℝ) : Prop :=
  (∀ j, 0 ≤ lambda j) ∧ (∑ j, lambda j) = 1 ∧
    vertexTraceSlope (r 0) (r (Fin.last p)) =
      ∑ j, lambda j * vertexTraceSlope (r j.castSucc) (r j.succ)

/-- A convex combination of finitely many quantities bounded by `M` is
bounded by `M`. -/
private lemma weighted_sum_le {p : ℕ} {lambda c : Fin p → ℝ} {M : ℝ}
    (hlambda : ∀ j, 0 ≤ lambda j) (hsum : (∑ j, lambda j) = 1)
    (hc : ∀ j, c j ≤ M) :
    (∑ j, lambda j * c j) ≤ M := by
  calc
    (∑ j, lambda j * c j) ≤ ∑ j, lambda j * M := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (hc j) (hlambda j)
    _ = (∑ j, lambda j) * M := by rw [Finset.sum_mul]
    _ = M := by rw [hsum, one_mul]

/-- A strict upper separator between the endpoint coefficient and all
adjacent coefficients rules out first-order matching for a run of any
length. -/
theorem not_firstOrderRunMatch_of_adjacent_le {p : ℕ}
    {r : Fin (p + 1) → ℝ} {M : ℝ}
    (hadj : ∀ j : Fin p,
      vertexTraceSlope (r j.castSucc) (r j.succ) ≤ M)
    (hend : M < vertexTraceSlope (r 0) (r (Fin.last p))) :
    ¬∃ lambda, FirstOrderRunMatch r lambda := by
  rintro ⟨lambda, hlambda, hsum, heq⟩
  have hle := weighted_sum_le hlambda hsum hadj
  rw [← heq] at hle
  exact (not_lt_of_ge hle) hend

/-- First-order coefficient matching for a three-cell rigid subdivision.
The weights are the limiting fractions of the total small angle assigned to
the three new cells. -/
def FirstOrderThreeCellMatch
    (r₀ r₁ r₂ r₃ lambda₀ lambda₁ lambda₂ : ℝ) : Prop :=
  0 ≤ lambda₀ ∧ 0 ≤ lambda₁ ∧ 0 ≤ lambda₂ ∧
    lambda₀ + lambda₁ + lambda₂ = 1 ∧
    vertexTraceSlope r₀ r₃ =
      lambda₀ * vertexTraceSlope r₀ r₁ +
        lambda₁ * vertexTraceSlope r₁ r₂ +
          lambda₂ * vertexTraceSlope r₂ r₃

/-- A convex combination of three quantities bounded by `M` is bounded by
`M`.  This is the abstract separation step used by the rigid-compression
obstruction. -/
private lemma weighted_three_le
    {lambda₀ lambda₁ lambda₂ c₀ c₁ c₂ M : ℝ}
    (hlambda₀ : 0 ≤ lambda₀) (hlambda₁ : 0 ≤ lambda₁)
    (hlambda₂ : 0 ≤ lambda₂)
    (hsum : lambda₀ + lambda₁ + lambda₂ = 1)
    (hc₀ : c₀ ≤ M) (hc₁ : c₁ ≤ M) (hc₂ : c₂ ≤ M) :
    lambda₀ * c₀ + lambda₁ * c₁ + lambda₂ * c₂ ≤ M := by
  have h₀ := mul_le_mul_of_nonneg_left hc₀ hlambda₀
  have h₁ := mul_le_mul_of_nonneg_left hc₁ hlambda₁
  have h₂ := mul_le_mul_of_nonneg_left hc₂ hlambda₂
  calc
    lambda₀ * c₀ + lambda₁ * c₁ + lambda₂ * c₂
        ≤ lambda₀ * M + lambda₁ * M + lambda₂ * M :=
          add_le_add (add_le_add h₀ h₁) h₂
    _ = (lambda₀ + lambda₁ + lambda₂) * M := by ring
    _ = M := by rw [hsum, one_mul]

/-- If the compressed endpoint coefficient is larger than a common upper
bound for all adjacent coefficients, no nonnegative first-order angle
allocation can match it. -/
theorem not_firstOrderThreeCellMatch_of_adjacent_le
    {r₀ r₁ r₂ r₃ M : ℝ}
    (h₀ : vertexTraceSlope r₀ r₁ ≤ M)
    (h₁ : vertexTraceSlope r₁ r₂ ≤ M)
    (h₂ : vertexTraceSlope r₂ r₃ ≤ M)
    (hend : M < vertexTraceSlope r₀ r₃) :
    ¬∃ lambda₀ lambda₁ lambda₂,
      FirstOrderThreeCellMatch r₀ r₁ r₂ r₃ lambda₀ lambda₁ lambda₂ := by
  rintro ⟨lambda₀, lambda₁, lambda₂, hmatch⟩
  rcases hmatch with ⟨hlambda₀, hlambda₁, hlambda₂, hsum, heq⟩
  have hle := weighted_three_le hlambda₀ hlambda₁ hlambda₂ hsum h₀ h₁ h₂
  rw [← heq] at hle
  exact (not_lt_of_ge hle) hend

@[simp] lemma vertexTraceSlope_two_one_fifth :
    vertexTraceSlope 2 (1 / 5) = 4 / 11 := by
  norm_num [vertexTraceSlope]

@[simp] lemma vertexTraceSlope_one_fifth_self :
    vertexTraceSlope (1 / 5) (1 / 5) = 1 / 5 := by
  norm_num [vertexTraceSlope]

@[simp] lemma vertexTraceSlope_one_fifth_two :
    vertexTraceSlope (1 / 5) 2 = 4 / 11 := by
  norm_num [vertexTraceSlope]

@[simp] lemma vertexTraceSlope_two_self : vertexTraceSlope 2 2 = 2 := by
  norm_num [vertexTraceSlope]

/-- The exact radius word `(2,1/5,1/5,2)` cannot rigidly replace its endpoint
cell to first order, regardless of how its small total angle is split among
the three positive or dormant subcells. -/
theorem no_firstOrderThreeCellMatch_two_one_fifth :
    ¬∃ lambda₀ lambda₁ lambda₂,
      FirstOrderThreeCellMatch 2 (1 / 5) (1 / 5) 2 lambda₀ lambda₁ lambda₂ := by
  apply not_firstOrderThreeCellMatch_of_adjacent_le (M := 4 / 11)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end Gluck.Discrete
