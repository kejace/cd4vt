# Discrete curvature playground

Open `/web/discrete-playground/` on the preview server. It supports 4–24 labelled
vertices, editable positive curvature readings, an immediately updated polygon,
DFV witnesses, Menger circles and JSON export. Each colored circle passes through
the corresponding vertex and its two neighbors. Circles are clipped to the view;
the polygon alone controls the scale. A checkbox toggles them without reframing. All solving runs locally in a WebAssembly worker.
There is no numerical server, installation at page load, or Lean execution.

This is a **numerical companion**, using IEEE double arithmetic. It derives its
coordinates and construction strategy from the Lean proof; it does not extract
an executable from Lean or produce a formal certificate. The bounded root search
can fail for admissible data. The accepted input range is 10^-6 to 10^6 and a
maximum curvature ratio of 10,000; it is a numerical limit, not a theorem limit.

## Original geometry

The definitions in `Gluck/Discrete/Defs.lean`, the endpoint bookkeeping in
`FourActiveSlotEmbedding.lean`, and the completed construction in
`TabachnikovFourActive.lean` supply the mathematical model. The files
`RegularDormantOpening.lean` and `LocalContinuity.lean` explain why opening zero
edges and making local corrections are possible at a suitable regular anchor.
`docs/discrete/LOCAL_CONTINUITY.md` records the local theorem's precise scope.
All these library sources are unchanged by this playground.

Write h_i = ell_i / 2 for the half-length of edge i, from vertex i to i+1.
The strict cap is h_i < 1 / max(k_i, k_(i+1)). Define

```
A_i = asin(k_i h_i)           B_i = asin(k_(i+1) h_i)
theta_0 = 0                  theta_i = sum_(j<i) (B_j + A_(j+1))
E = sum_i h_i exp(i theta_i)  T = sum_i (A_i + B_i).
```

The three equations are Re E = Im E = 0 and T = 2 pi. Once solved, the vertices
are partial sums of 2 h_i exp(i theta_i). Labels retain their original order.
Signed Menger curvature at i is measured from the cyclic triple (i-1,i,i+1),
using 2 cross(u,v) / (|u| |v| |u+v|).

## Numerical construction

1. Detect the constant case or four strict cyclic high/low witnesses. A constant
   input starts with a regular polygon.
2. Normalize max curvature to one. Use fractions q_i of the strict edge caps as
   coordinates. Record the original indices at the boundaries of constant runs.
3. Enumerate four-edge frames from the two incident edge pairs at nonadjacent
   vertices of the reduced word. Discard frames whose maximum turn is too small.
   Keep dormant edges zero and solve on the four active coordinates.
4. Try small positive fractions on the dormant edges, correcting only the four
   active coordinates. Restore the original scale and check the full polygon.
5. During edits, continue from the previous lengths through an adaptive linear
   interpolation of the curvature readings. Correct all lengths; bound each
   accepted step's change in log lengths. Failed steps are subdivided. A failed
   continuation returns a distinct status and never automatically runs a new
   initialization. The user can explicitly request a fresh starting point.

The corrector uses a damped minimum-norm Newton step, an analytic Jacobian,
a 3 by 3 linear system, backtracking, and explicit iteration and start budgets.
The existence proof's case-specific topological producers are **not** translated
into a guaranteed terminating numerical algorithm. Here they motivate a bounded
multistart search over four-edge frames. Numerical rank and convergence are not
formalized by this implementation.

Near a constant profile the raw three-equation Jacobian loses rank. For normalized
curvature, the circular half-closure contribution is

```
C = sin(T/2) exp(i (T/2 - A_0)).
```

At a constant normalized profile E = C identically. At T = 2 pi, C = 0.
For a nonconstant profile the corrector therefore uses (E-C)/(1-min k),
further divided by sum h, together with (T-2 pi)/(2 pi). This removes the
leading circular cancellation while retaining the same exact zero set. The
analytic derivative is tested by independent central differences. Tolerances
account for the remaining floating-point cancellation very near constants.

The final check always recomputes the **original** closure and turning equations,
not just this transformed residual. It also reconstructs all cyclic triples,
checks every strict supporting half-plane and verifies:

| Quantity | Acceptance threshold |
| --- | --- |
| Closure / perimeter | < 2e-10 |
| Absolute turn error in radians | < 3e-10 |
| Maximum relative signed curvature error | < 2e-6 |
| Smallest endpoint cap margin, 1 - k h | > 2e-10 |
| Shortest / longest edge | > 2e-8 |
| All nonincident supporting cross products | strictly positive |

`validate.py` independently reconstructs and checks the geometry in Python/NumPy,
including the vertices returned by the kernel. These are floating-point checks,
not interval arithmetic, exact certificates or machine-checked existence claims.

## What would connect the numerics to Lean?

This is authentic to our four-active-edge proof strategy, with numerical search
in place of its anchor existence arguments. It is not a verified execution of
that proof. A quantitative local theorem would fix a regular anchor, an opening,
and a correction slice, then bound errors in the original closure/turn equations
and resulting vertices. The Lean existence theorem does not specify a canonical
polygon for the solver to approach. See the
[shared convergence discussion](../smooth_playground/DAHLBERG.md#the-discrete-solvers-relationship-to-our-proof)
for the distinction between numerical refinement, dormant opening, and global
continuation. No new convergence theorem or certificate is claimed here.

## Continuity and failure behavior

The UI attempts a numerical local continuation. The local C1 theorem guarantees
a choice around each nonconstant admissible profile, not a section through every
preassigned polygon or a globally continuous selector. The implementation cannot
certify branch identity, regularity, or the location of a singularity.

The exposed obstruction path is
`[14, 11, 10+3s, 5, 7-3s, 3]`, 0 <= s <= 1. Its mathematical obstruction is
recorded in `docs/discrete/GLOBAL_CONTINUITY.md`. Every point is admissible,
but no continuous coherent realization exists over the whole path. A numerical
stop is solver-dependent and is not a certified location of the obstruction.

When input is invalid or a solve fails, the previous polygon is faded and
explicitly labelled as belonging to the old profile. Current metrics and export
are disabled. A latest-request queue coalesces pointer events and rejects stale
display results. The worker keeps numerical searches off the UI thread.

## Build and reproduce

The checked-in `solver.mjs` and `solver.wasm` are ready to serve. Rebuild with an
installed C compiler / Emscripten:

```sh
python3 tools/discrete_playground/build.py
python3 tools/discrete_playground/build.py --native /tmp/gluck-dfv-solver.so
```

`site/discrete-playground/build.json` records the compiler, exact flags and hashes.
This build used installed Emscripten 3.1.6; no new toolchain was installed.
The module uses Emscripten's documented
[modularized ES module output](https://emscripten.org/docs/compiling/Modularized-Output.html)
and [exported C functions and typed memory](https://emscripten.org/docs/porting/connecting_cpp_and_javascript/Interacting-with-code.html).

Run numerical probes through the workspace CAS launcher, respecting its thread
budget. In this machine's environment `/opt/cas-venv` is absent; the existing
`/home/kejace/.venvs/cas` environment contains NumPy and Playwright. For example:

```sh
CAS_VENV=/home/kejace/.venvs/cas CAS_WORKERS=1 ../gluck-physical/tools/cas/run python tools/discrete_playground/validate.py --native /tmp/gluck-dfv-solver.so --report /tmp/validation-native.json
CAS_VENV=/home/kejace/.venvs/cas /home/kejace/.venvs/cas/bin/python scripts/check-discrete-playground --cas ../gluck-physical/tools/cas/run --report /tmp/validation-browser.json
```

Start `python3 scripts/serve-web --port 8788` for the browser checks. The wrapper starts Chromium outside the CAS process address-space cap: V8
reserves more virtual memory than that cap, even with a small resident footprint.
The validation process still runs through CAS with one worker. The tests
require NumPy and an installed Playwright Chromium; the product does not.

The deterministic suite (PCG64 seed 194211) includes constants, repeated maxima,
constant runs, random admissible words, contrasts down to 1e-7, rescaling and
cyclic relabelling; 200 consecutive edits for each n; a recorded obstruction
trace and explicit restart; invalid inputs; and an independent Jacobian check.
The browser checks run the actual WASM worker against the same numerical suite,
then exercise all 39 preset/size combinations, mouse dragging, keyboard editing,
number inputs, paste, JSON export, invalid/stale states, branch stopping/reseeding,
loading failure, navigation and 390/320-pixel layouts. Results are in
`validation-native.json` and `validation-browser.json` beside this file.

## Recorded results (2026-09-28)

Both native and browser WASM passed all 167 cold profiles and the 1,600-step edit
suite. Two continuation attempts needed explicit cold restarts; these are recorded
as stops, not counted as successful continuous steps. The obstruction trace stopped
at s = 0.374 (fine numerical steps), and the UI trace at s = 0.37 (coarser edits);
both restarted successfully when explicitly requested. These locations depend on
the numerical path and tolerances.

In Chromium 151, WASM cold initialization took 0.30 ms median, 1.54 ms at the
95th percentile and 171.1 ms maximum on this machine. For each size, continuation
medians were at or below the browser timer's approximately 0.1 ms resolution;
the largest per-size 95th percentile was 1.11 ms and the overall maximum 1.90 ms.
These measure the solver in the worker, excluding UI rendering and message latency.
Timing values recorded as zero mean below the timer's resolution.

The browser timings above were measured when the playground supported 4–11
vertices. With the range raised to 24, the native suite (`validation-native.json`)
passes all 440 cold cases for n = 4–24 (median 0.46 ms, maximum 129 ms) and
4,200 continuation edits.

All 39 preset/size combinations, real exported geometry, pointer and keyboard
editing, invalid profiles, stale-result handling, obstruction/restart behavior,
engine-load failure, eight navigation bars and mobile layouts passed. The native
analytic-Jacobian check differed from central differences by at most 1.45e-10.
The reports pin the C and WASM hashes; this is empirical coverage, not a universal
convergence claim.

## Kernel ABI

The worker serializes calls into one fixed-memory module. `input_buffer` has 36
float64 values: new k[0:12], previous k[12:24], previous full lengths[24:36].
`solve(n, mode, seed)` uses mode zero for initialization and one for continuation.
Seed 17 starts with a balanced frame; explicit restarts use seeded random starts.
`output_buffer` contains lengths[0:12], interleaved vertices[12:36], then closure,
turn error, curvature error, cap margin, min/max length, evaluation count, start
count, method, active-edge mask and strict support margin in slots 36 through 45.

Status 1 means checked success, -1 unsupported size, -2 unsupported numerical
range, -3 failed DFV hypothesis, -4 continuation stopped, and 0 exhausted cold
search. Output geometry must only be consumed after status 1. `evaluate(n)`
exposes residuals and the analytic Jacobian solely for validation.
