# Side-tangent-circle converse: complete

Recorded 2026-09-30 UTC in `gluck-circumedge`, branch `proof/circumedge`.
The theorem below and its geometric certificate have passed Lean. The local
continuity/nonsingularity bonus remains a separate, unproved task.

## Exact endpoint

```lean
Gluck.Discrete.SideTangent.sideTangentConverse
  {n : ℕ} [NeZero n] (hn : 4 ≤ n) (ρ : ZMod n → ℝ)
  (h : Gluck.Discrete.SideTangent.SideTangentAdmissible ρ) :
  Gluck.Discrete.SideTangent.RealizesSideTangent ρ
```

`SideTangentAdmissible ρ` means all radii are positive and either the profile
is constant, or `DFV (radiusDifference ρ) 0` holds, where
`radiusDifference ρ i = ρ (i - 1) - ρ i`. The latter predicate gives four
cyclically ordered, distinct labels with signs `+,-,+,-`. Thus zeros in the
difference list do not count as strict sign changes. Every original label
and every exact radius is retained, including repeated adjacent radii and
long constant runs. The constant case has its own actual regular-fan producer.

The nonconstant endpoint `sideTangentConverse_of_dfv` needs only positivity
and this DFV hypothesis; `4 ≤ n` follows from the four witnesses.

The statement matches the mathematical target in `circumeedge.plan`; it
adds neither a genericity hypothesis nor a missing fan/balance producer.
This completion record makes no separate literature-novelty claim.

## What the geometric certificate proves

`RealizesSideTangent ρ` supplies labelled vertices `P`, outward unit edge
normals `N`, and circle centers `C` satisfying `IsSideTangentRealization`:

- `P` is simple and has strict convex edge support. Every edge is a positive
  multiple of `I * N i`, so all edges have positive length and consistent
  counterclockwise orientation.
- Every polygon vertex is in the inward closed half-plane of each
  supporting line: `⟪N i, P j - P i⟫ ≤ 0`.
- `C i` has inward signed distance `ρ i` from the supporting lines of edges
  `i - 1`, `i`, and `i + 1`. The center and signed radius solving these three
  equations are unique.
- The central contact `C i + ρ i • N i` lies in the **open** segment from
  `P i` to `P (i + 1)`.

The previous-line equation is initially based at `P i`, which belongs to
the preceding edge's line. `normal_edge_orthogonal` and
`circle_line_distance` explicitly transport it to that edge's own basepoint
`P (i - 1)`; this is not left to an indexing convention.

The metric bridge `IsSideTangentRealization.tangent_sphere` further proves,
for each `k = i - 1`, `k = i`, or `k = i + 1`,

```lean
Metric.sphere (C i) (ρ i) ∩ supportingLine P N k
  = {C i + ρ i • N k}
```

Consequently these are actual circles tangent to the three actual lines,
not merely a named algebraic predicate. Neighboring contacts may lie on
line extensions. Global containment of each circle in the polygon is not
asserted. Nor is a condition excluding a circle shared by four arbitrary
supporting lines asserted. These are the conventions of the preserved plan.

## Construction and dependency map

The original radius data are never perturbed. A finite positive geometric
perturbation resolves a four-corner limiting fan while retaining every
coefficient, including all zero and unselected coefficients. Boundary signs
on an inset diamond produce an actual zero of the rational balance field.
Projective disk normalization produces a strict tangential fan `Y` with
`∑ i, (ρ (i - 1) - ρ i) • Y i = 0`.

The desired polygon is the cyclic primitive of
`ρ i • (Y (i + 1) - Y i)`. Summation by parts proves exact closure. Positive
edge scaling preserves the ordered direction fan. A supporting-half-plane
argument proves strict convexity of the new polygon; its simplicity is then
a conclusion, never an input assumption. Finally,

```text
N i = U (i + 1)
C i = P i - ρ i • Y i
```

gives the three exact circle equations and open central contact.

The new modules are arranged as follows (arrows mean mathematical supply):

```text
SideTangentField + DiamondWinding
  → SideTangentPerturbation + DiamondStability + ProjectiveBalance
  → SideTangentSquareLabels
  → SideTangentFan → SideTangentSquareFan → SideTangentDFV

SideTangentFan → SideTangentContact → SideTangentCircle
SideTangentSquareFan + SideTangentCircle + ProjectiveOrientation
  → SideTangentProjectiveFan → SideTangentRegularFan

SideTangentDFV + SideTangentProjectiveFan + StrictSupportSimplicity
  → SideTangentScaledPolygon
SideTangentScaledPolygon + SideTangentRegularFan
  → SideTangentConverse
```

`ProjectiveBall` supplies the projective disk formulas;
`ProjectiveSegments` supplies line/segment transport. Existing
`PolygonConvexity` supplies the one-turn heading of the *auxiliary* simple
polygon. Existing `Converse` supplies the original DFV vocabulary; no
circumradius converse is being invoked as an unproved polarity shortcut.
The manifest records the exact full local import closure (31 modules), not
only this abbreviated dependency diagram.

Key unconditional producer and assembly endpoints:

| Declaration | Result |
| --- | --- |
| `exists_balanced_cyclicFan_of_radiusDFV` | Original-label exact projective balance from radius DFV |
| `exists_balanced_strictTangentialFan` | Actual positive finite strict tangential fan and balance |
| `exists_strictTangentialFan_of_four_le` | Actual regular strict tangential fan for the constant branch |
| `exists_sideTangent_scaledPolygon` | Original-label simple strict polygon with exact scaled edges |
| `realizesSideTangent_of_scaledFan` | Exact, unique inward circles and open central contacts |
| `sideTangentConverse` | Full constant-or-DFV endpoint |
| `IsSideTangentRealization.tangent_sphere` | Exact metric tangency to all three supporting lines |

## Build and trust audit

Commands, all with one Lean worker:

```sh
LEAN_NUM_THREADS=1 lake build +Gluck.Discrete.SideTangentConverse
LEAN_NUM_THREADS=1 lake env lean research/side_tangent_20260929/ConverseAudit.lean
LEAN_NUM_THREADS=1 lake env lean research/side_tangent_20260929/ConverseIndependentAudit.lean
```

- The targeted build completed successfully: **3533 jobs**. Existing dependency
  deprecation warnings were replayed; no warnings were emitted by the three
  assembly modules.
- `ConverseAudit.lean` audits all **44 public declarations** of
  `SideTangentDFV`, `SideTangentScaledPolygon`, and `SideTangentConverse`.
  Every result has only `propext`, `Classical.choice`, and `Quot.sound`.
- `ConverseIndependentAudit.lean` preserves the separate reviewer's endpoint
  audit; it rechecks the final converse, nonconstant converse, scaled-polygon
  producer, and metric tangency theorem. It has the same clean result.
- Lean's `#print axioms` is transitive through theorem dependencies.
  In particular **no `sorryAx`, invented axiom, or other admission is reachable
  from the endpoint or metric tangency theorem**, including via imports.
  This is a dependency audit, not a claim about unrelated declarations that
  happen to exist elsewhere in imported source files.
- The independent semantic review checked the original plan, circle sign,
  previous-line basepoint, exact radii, central contact, and lack of an added
  producer or regularity hypothesis; it found no mismatch.

Durable evidence: `converse_build.log`, `converse_axioms.log`,
`converse_independent_axioms.log`, and `converse_sources.json`.
The JSON records the base commit, commands, complete local source hashes,
configuration hashes, declaration results, and evidence-file hashes. Source
hashes were rechecked after the audits. Existing theorem files, protected
statements, and prior status documents were not edited for this assembly.
Nothing was staged, committed, pushed, or merged by this task.

## Local continuity and nonsingularity: read-only feasibility assessment

**Status: not proved by the completed converse.** The present zero-existence
argument does not choose its zero continuously and supplies no Jacobian rank.
A nonzero boundary degree can have only singular interior zeros; degree
alone is not a regular-value theorem. Strict polygon geometry and uniqueness
of the three-line circle do not establish nonsingularity of the balancing
parameter map.

A concrete next target is: for every positive nonconstant admissible base
profile `ρ₀`, construct an open neighborhood in the finite-dimensional space
of labelled radii and a `C¹` family `(P(ρ), N(ρ), C(ρ))` whose members satisfy
`IsSideTangentRealization ρ`. This would be an existence of a local family,
not a canonical/global choice or continuation through every prechosen polygon.
The four strict sign witnesses and positivity persist on a sufficiently small
open neighborhood, even when other differences vanish at the base profile.

A direct route freezes the cyclic labels, four selected witnesses, and a
strict finite fan parameter `η`, and considers the actual rational field

```text
F(ρ, a) = Σ_i c_i(ρ) X_i / (1 - <a, X_i>),
c_i(ρ) = ρ_(i-1) - ρ_i,
X_i = fanVertex(n,p,q,r,η,i).
```

The following mathematical derivative is the quantity to formalize:

```text
D_a F(ρ,a)[h] = Σ_i c_i(ρ) <h,X_i> X_i / (1 - <a,X_i>)².
```

It is a real two-dimensional linear operator, represented by a symmetric
2-by-2 matrix. Its coefficients have mixed signs; positive denominators do
not make it positive definite. The present result establishes an interior
zero, but does not establish that this operator is invertible at any chosen
zero, or that some regular zero exists for every admissible profile.

If a regular zero is supplied, the remaining route is concrete:

1. Prove joint `ContDiffAt` of `F` on its open positive-denominator domain.
   The existing `continuousAt_projectiveField` is only a continuity theorem
   with coefficients fixed, so the joint smoothness statement must be added.
2. Apply existing
   `ContDiffAt.exists_parametricConstraintCorrection` or
   `ContDiffAt.exists_localSection_mem_submodule` with the inverse/right
   inverse of the parameter derivative to obtain a local section `a(ρ)`.
3. Compose with `σ(ρ) = sqrt(1 - ‖a(ρ)‖²)`, the explicit projective transform,
   finite cyclic edge sums, and `C_i = P_i - ρ_i Y_i`. Positive denominators,
   positive gaps, strict support, and interior-contact inequalities persist
   after shrinking the neighborhood. Fix `P_0 = 0` and the label convention
   to remove irrelevant translation/relabelling choices.
4. Package a local family in the literal `IsSideTangentRealization` geometry,
   including continuity of the same labelled vertices, centers, and contacts.
   Reuse the established radius-identification and tangency results.

The substantive missing producer is a regular balancing solution for each
nonconstant admissible profile. Possible research routes are a quantitative
regular four-corner solution stable under finite fan perturbation, or a
larger family of normal-angle controls with a proved surjective derivative.
A generic-perturbation assertion would require proof that it preserves the
exact radius data and produces a regular solution; simply citing genericity
would leave the main gap unchanged. Allowing more angle controls asks for
surjectivity onto the two closure equations, not invertibility of an
unspecified square matrix.

The existing Menger result
`Gluck.Discrete.tabachnikovProblem2_local_continuity` in `LocalContinuity.lean`
is a useful interface/model: it obtains an unconditional `C¹` local family
from a proved regular four-active anchor. Its derivative producer concerns
Menger closure and turning, so it does not automatically supply the new
side-tangent rank theorem.

Constant profiles require separate scope. Here `c_i = 0` and `F` is
identically zero, so its derivative in `a` is zero: this particular implicit
chart cannot prove nonsingularity there. Scaling a fixed regular tangential
polygon gives a smooth family along the one-dimensional positive-constant
locus. Selection through general nearby admissible nonconstant profiles is
a different question, not covered by that observation or by the completed
existence theorem. No global selection or global obstruction claim for the
side-tangent problem follows from this audit.
