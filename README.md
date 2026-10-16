# A converse to the discrete four-vertex theorem

Paper and Lean 4 / Mathlib formalization answering Tabachnikov's Problem 2
([arXiv:0710.5902](https://arxiv.org/abs/0710.5902)).
Website: <https://kejace.github.io/cd4vt/>.

Every cyclic sequence of positive numbers `r₁, …, rₙ` (`n ≥ 4`) with at least
two local maxima and two local minima, with extrema counted as plateaus, is the
sequence of radii of the circles through consecutive vertex triples of a
convex polygon whose circumcenters lie inside the corresponding vertex angles
(a *coherent* convex polygon). By Dahlberg's discrete four-vertex theorem the
condition is also necessary for nonconstant sequences, so this is a
characterization. The polygon can be chosen to depend `C¹` on the data near
every nonconstant admissible sequence, but not globally: an explicit path of
admissible hexagon data admits no continuous choice of realizing polygons. The
paper also proves the corresponding characterization for circles tangent to
three consecutive supporting lines.

## Contents

| Path | |
|---|---|
| `paper/tabachnikov-converse.tex`, `paper/tabachnikov/` | paper source, figures, bibliography |
| `paper/tabachnikov-converse.pdf` | built paper |
| `Gluck/` | the formalization (library `Gluck`) |
| `ForMathlib/` | self-contained generalisations, Mathlib-only imports, staged for upstreaming |
| `scripts/axioms.lean` | `#print axioms` for the paper's displayed theorems |
| `formalization.yaml` | project metadata in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format |
| `comparator/` | [Comparator](https://github.com/leanprover/comparator) statement/axiom/kernel audit |
| `scripts/build-paper`, `scripts/package-arxiv-discrete` | paper build and arXiv packaging |
| `site/`, `scripts/build-site` | website (GitHub Pages): construction overview, playground, proof map, blueprint |
| `tools/discrete_playground/` | playground solver source and the paper's figure generators |

## Main formal statements

The Lean appendix of the paper displays each statement in full.

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 1.1 (realization) | `Gluck.Discrete.tabachnikov_converse_geometric` | `Gluck/Discrete/TabachnikovConverse.lean` |
| Corollary 1.2 (characterization) | `Gluck.Discrete.tabachnikov_radius_characterization` | `Gluck/Discrete/TabachnikovCharacterization.lean` |
| Theorem 8.2 (side-tangent converse) | `Gluck.Discrete.SideTangent.sideTangentConverse` | `Gluck/Discrete/SideTangentConverse.lean` |
| Corollary 8.6 (side-tangent characterization) | `Gluck.Discrete.SideTangent.realizesSideTangent_iff_admissible` | `Gluck/Discrete/SideTangentForward.lean` |
| Theorem 7.1 (local `C¹` continuity) | `Gluck.Discrete.localContinuousRealization_of_dfv` | `Gluck/Discrete/LocalContinuity.lean` |
| Theorem 7.2 (no global continuous choice) | `Gluck.Discrete.GlobalContinuity.no_continuous_regular_hexagon_path` | `Gluck/Discrete/GlobalContinuity/EnclosingCircleObstruction.lean` |

The umbrella theorem `Gluck.Discrete.tabachnikovProblem2_all`
(`Gluck/Discrete/TabachnikovFourActive.lean`) states Problem 2 for every `n ≥ 4`.
The development contains no `sorry` and no `axiom`; every theorem above
depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Building

Lean `v4.35.0-rc2`, Mathlib `v4.35.0-rc2`.

```bash
lake exe cache get        # prebuilt Mathlib
lake build
lake env lean scripts/axioms.lean
```

The paper needs pdfLaTeX and BibTeX:

```bash
scripts/build-paper        # writes paper/tabachnikov-converse.pdf
scripts/build-paper --check  # two builds, byte-identical PDF
scripts/package-arxiv-discrete  # arXiv source archive under paper/arxiv/
```

## License

Apache 2.0; see `LICENSE`.
