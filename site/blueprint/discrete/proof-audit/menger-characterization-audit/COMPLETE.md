# Corollary 1.2: formalized

`Gluck.Discrete.tabachnikov_radius_characterization` proves exactly the paper's
nonconstant positive-radius characterization: for `n ≥ 4`, a radius sequence is
realized by a coherent strictly convex polygon iff it has two distinct plateau
maxima and two distinct plateau minima. No nondegeneracy or no-plateau hypothesis
has been added.

The new geometric bridges produce Dahlberg regularity from coherence, positive
orientation from strict edge support, and the exact inverse-radius relation.
`Gluck.Forward.Discrete.PlateauBridge` proves that the forward theorem's
alternating plateau extrema yield a strict level window, then uses the existing
window-to-distinct-runs theorem. Thus the differing plateau encodings are proved
equivalent in the direction needed by the paper, rather than identified by fiat.

Build: `LEAN_NUM_THREADS=1 lake build Gluck.Discrete.TabachnikovCharacterization`
passed (3,773 jobs), recorded in `build.log`. `Audit.lean` / `axioms.log` audit all
10 new declarations transitively; only `propext`, `Classical.choice`, and
`Quot.sound` occur. Exact file hashes and source provenance are in `sources.json`.

The isolated checkout `/tmp/gluck-forward-main-20260930` was clean before creating
branch `proof/discrete-characterization`. Prerequisites copied from the active
web checkout are `TabachnikovConverse.lean` and the additive coherence section in
`LocalRegularity.lean`; the existing main forward proof was reused unchanged.
The `TabachnikovReduction.lean` web differences were comments only and were not
copied. No commits or pushes were made by this proof lane.

This theorem concerns Menger vertex circumcircles. The separate supporting-line
circle characterization requires its own Wegner necessity proof.
