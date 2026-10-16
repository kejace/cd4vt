# Comparator audit

[Comparator](https://github.com/leanprover/comparator) (pinned at
`e3dcf3083fc53d44b27a4431fabf7d43181583f5`, release `v4.35.0`) checks a
candidate library against a trusted statement: same theorem statements and
statement dependencies, only the permitted axioms, and acceptance of the proofs
by the Lean kernel.

This checking project compares the six theorems displayed in the Lean appendix
of `paper/tabachnikov-converse.tex` (`config.json`):

* **Challenge** is the trusted statement, written out in Lean and importing only
  Mathlib. `Challenge.lean` states the six theorems with `sorry`;
  `Challenge/**` holds the 37 project definitions and structures they depend on,
  copied from the library, one file per library module. Review these files
  against the paper.
* **Solution** is `import Gluck` from this checkout.
* Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.

Comparator compares the elaborated terms, so the challenge must reproduce the
library's definitions exactly, including instance paths and the names of
auto-generated auxiliary proofs. That is why the challenge imports seven
specific Mathlib modules rather than all of Mathlib (which resolves the topology
on `ℂ` through a C*-algebra instance), and why it follows the library's module
boundaries. Like the library, every challenge file uses the module system
(`module`, `public import`, `@[expose] public section`). If a library definition changes, update its copy here; Comparator
reports any definition or statement that no longer matches.

## Running

From the repository root, with
[landrun](https://github.com/Zouuup/landrun) and a `systemd --user` session
available:

```bash
lake build                              # the candidate; read-only in the sandbox
lake build comparator lean4export       # the pinned tools
(cd comparator && lake build)           # prebuild both roots
COMPARATOR_LANDRUN=/path/to/landrun bash comparator/run.sh
```

A successful run ends with `Your solution is okay!`. The log is written to
`comparator/evidence/comparator.log`.

Changing any definition in `Challenge/**` makes the run fail: with the first
entry of `bandProfile` changed from `14` to `15`, Comparator reports
`Const does not match between challenge and target
'Gluck.Discrete.GlobalContinuity.bandProfile'`.
