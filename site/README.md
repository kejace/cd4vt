# Website

Static pages published to GitHub Pages by `.github/workflows/deploy-site.yml`.

| Path | |
|---|---|
| `index.html` | home: the construction, the playground and the proof map on one page |
| `discrete-playground/` | numerical curvature playground; the WASM solver is built from `tools/discrete_playground/solver.c` (`build.py`) |
| `discrete-proof-map/` | curated map of the construction cases (`graph.json`); not a compiled dependency extraction |
| `blueprint/` | hgraph blueprint reader with the discrete book (`blueprint/discrete/`) |
| `figures/` | paper figures as SVG, used by the blueprint reader |

Pages link to each other through root-absolute `/web/…` routes and to the paper
through `/paper/…`. Build and preview:

```sh
scripts/build-paper                      # paper/tabachnikov-converse.pdf
scripts/build-site --out _site
python3 -m http.server -d _site 8000
```

The blueprint book under `blueprint/` is generated output, extracted from the
gluck project's website build. Its provenance files (`blueprint/discrete/*provenance*.json`,
`blueprint/discrete/proof-audit/`) record the gluck revisions and audits it was
built from. One link to a declaration outside this library
(`Gluck.Hyperbolic.poincareMiranda_rect`) was removed.
