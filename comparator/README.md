# Comparator audit

[Comparator](https://github.com/leanprover/comparator) (pinned at
`32bd61da1d68fbaa310234964e9b820b03a0f82f`, release `v4.35.0-rc2`) checks a
candidate library against a trusted statement: same theorem statements and
statement dependencies, only the permitted axioms, and acceptance of the proofs
by the Lean kernel.

This checking project compares the six theorems displayed in the Lean appendix
of `paper/tabachnikov-converse.tex` (`config.json`):

* **Challenge** is the import closure of the modules stating those theorems,
  copied byte for byte from a trusted git revision under the module prefix
  `Challenge.` (`prepare_challenge.py`). Only internal import lines are
  rewritten; namespaces and declarations are unchanged.
* **Solution** is `import Gluck` from this checkout.
* Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Running

From the repository root, with
[landrun](https://github.com/Zouuup/landrun) and a `systemd --user` session
available:

```bash
lake build                              # the candidate; read-only in the sandbox
lake build comparator lean4export       # the pinned tools
python3 comparator/prepare_challenge.py <trusted-rev>   # e.g. a release tag
(cd comparator && lake build)           # optional: prebuild both roots
COMPARATOR_LANDRUN=/path/to/landrun bash comparator/run.sh
```

A successful run ends with `Your solution is okay!`. The log is written to
`comparator/evidence/comparator.log`.

When the candidate is this checkout itself, the challenge only freezes the
statements at the chosen revision; the comparison is meaningful for later
revisions, or when the trusted revision is reviewed independently.
