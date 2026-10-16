#!/usr/bin/env python3
"""Independent geometry validation and deterministic native/WASM benchmark suite."""
import argparse
import ctypes
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
SEED = 194211
N, MAXN = 25, 24  # buffer stride and largest polygon, as in solver.c


def dfv(k):
    k = np.asarray(k, dtype=float)
    if np.all(k == k[0]):
        return True
    values = np.unique(k)
    return any(np.count_nonzero((k > c) != np.roll(k > c, 1)) >= 4
               for c in (values[:-1] + values[1:]) / 2)


def geometry(k, lengths, vertices=None):
    """Recompute original equations, signed Menger curvature and strict support."""
    k, ell = np.asarray(k, dtype=float), np.asarray(lengths, dtype=float)
    assert len(k) == len(ell) and np.all(np.isfinite(ell)) and np.all(ell > 0)
    cap_product = ell * np.maximum(k, np.roll(k, -1)) / 2
    assert np.all(cap_product < 1)
    turns = np.arcsin(k * np.roll(ell, 1) / 2) + np.arcsin(k * ell / 2)
    headings = np.r_[0., np.cumsum(turns[1:])]
    steps = ell * np.exp(1j * headings)
    v = np.r_[0j, np.cumsum(steps)[:-1]]
    u = v - np.roll(v, 1)
    w = np.roll(v, -1) - v
    curvature = 2 * np.imag(np.conj(u) * w) / (abs(u) * abs(w) * abs(u + w))
    support = min(np.imag(np.conj(w[i]) * (v[j] - v[i])) / ell.sum()**2
                  for i in range(len(k)) for j in range(len(k))
                  if j not in (i, (i + 1) % len(k)))
    # Recompute the actual cyclic edges from the returned coordinates as well.
    edge_error = max(abs(abs(w) / ell - 1))
    result = dict(closure=float(abs(steps.sum()) / ell.sum()),
                  turn=float(abs(turns.sum() - 2 * np.pi)),
                  curvature=float(max(abs(curvature / k - 1))),
                  wall=float(min(1 - cap_product)),
                  minLength=float(min(ell) / max(ell)), support=float(support),
                  edgeError=float(edge_error))
    assert result['closure'] < 2e-10, result
    assert result['turn'] < 3e-10, result
    assert result['curvature'] < 2e-6, result
    assert result['wall'] > 2e-10 and result['minLength'] > 2e-8 and support > 0, result
    if vertices is not None:
        actual = np.asarray(vertices)
        assert actual.shape == (len(k), 2) and np.all(np.isfinite(actual))
        assert max(abs(actual[:, 0] + 1j * actual[:, 1] - v)) / ell.sum() < 2e-11
    return result


def fixtures():
    rng = np.random.default_rng(SEED)
    rows, bases = [], {}
    for n in range(4, MAXN + 1):
        cases = [('constant', np.ones(n)), ('repeated', np.array([3, 1, 3, 1] + [1] * (n - 4), float))]
        for _ in range(12):
            while True:
                k = np.exp(rng.uniform(0, 2.3, n))
                if dfv(k):
                    break
            bases.setdefault(n, k.copy())
            cases.append(('random', k))
        for eps in [1e-2, 1e-5, 1e-7]:
            while True:
                k = 1 + eps * rng.random(n)
                if dfv(k):
                    break
            cases.append(('nearconstant', k))
        if n > 4:
            cases.append(('constant-runs', np.array([4, 4, 1, 3, 1] + [1] * (n - 5), float)))
        for scale in [1e-5, 1e4]:
            cases.append(('scaled', bases[n] * scale))
        cases.append(('cyclic-relabeling', np.roll(bases[n], 1)))
        rows.extend((kind, k.tolist()) for kind, k in cases)
    return rows, bases


def summary(times):
    return dict(p50_ms=float(np.median(times)), p95_ms=float(np.percentile(times, 95)), max_ms=max(times))


def run_suite(solve):
    cases, bases = fixtures()
    cold = []
    worst_curvature = 0
    for kind, k in cases:
        result = solve(k)
        assert result['status'] == 1, (kind, k, result)
        metrics = geometry(k, result['lengths'], result['vertices'])
        worst_curvature = max(worst_curvature, metrics['curvature'])
        cold.append(dict(n=len(k), kind=kind, milliseconds=result['milliseconds'], curvature=metrics['curvature']))
    print(f'Cold initialization: {len(cold)}/{len(cases)} checked.', flush=True)
    continuation = []
    for n, base in bases.items():
        previous = solve(base.tolist())
        times, stops, max_error = [], [], 0
        for step in range(1, 201):
            k = base * (1 + .025 * np.sin(step / 25 + np.arange(n)))
            assert dfv(k)
            result = solve(k.tolist(), previous)
            times.append(result['milliseconds'])
            if result['status'] != 1:
                assert result['status'] == -4
                stops.append(step)
                # Explicit benchmark restart, recorded separately. The UI never auto-reseeds.
                result = solve(k.tolist())
                assert result['status'] == 1
            metrics = geometry(k, result['lengths'], result['vertices'])
            max_error = max(max_error, metrics['curvature'])
            previous = result
        continuation.append(dict(n=n, steps=200, explicit_restarts=stops,
                                 max_curvature_error=max_error, **summary(times)))
    initial = [14., 11., 10., 5., 7., 3.]
    previous = solve(initial)
    assert previous['status'] == 1
    obstruction = None
    for step in range(1, 501):
        s = step / 500
        k = [14., 11., 10 + 3 * s, 5., 7 - 3 * s, 3.]
        assert dfv(k)
        result = solve(k, previous)
        if result['status'] == -4:
            restart = solve(k, seed=18)
            assert restart['status'] == 1
            geometry(k, restart['lengths'], restart['vertices'])
            obstruction = dict(numerical_stop=s, restart_status=restart['status'],
                               note='Solver-dependent stopping point; not a certified singularity.')
            break
        assert result['status'] == 1
        geometry(k, result['lengths'], result['vertices'])
        previous = result
    assert obstruction is not None, 'Expected the checked obstruction trace to stop.'
    invalid = [([1., 2., 3.], -1), ([1.] * (MAXN + 1), -1), ([1., 2., 3., 4.], -3),
               ([1., 0., 2., 0.], -2), ([1., -1., 2., 1.], -2),
               ([1e-7, 2e-7, 1e-7, 2e-7], -2), ([1., 10001., 1., 10001.], -2)]
    for k, status in invalid:
        assert solve(k)['status'] == status, (k, status)
    # Cold constants are regular; an explicit seed changes the nonconstant start.
    base = bases[8].tolist()
    a, b = solve(base), solve(base, seed=18)
    assert a['status'] == b['status'] == 1
    geometry(base, b['lengths'], b['vertices'])
    assert np.max(np.abs(np.array(a['lengths']) - b['lengths'])) > 1e-7
    report = dict(timestamp=datetime.now(timezone.utc).isoformat(), seed=SEED,
                  source_sha256=hashlib.sha256((ROOT / 'tools/discrete_playground/solver.c').read_bytes()).hexdigest(),
                  numpy=np.__version__, cold_cases=len(cold), cold_passed=len(cold),
                  cold_timing=summary([r['milliseconds'] for r in cold]), max_cold_curvature_error=worst_curvature,
                  continuation=continuation, obstruction=obstruction, rejected_inputs=len(invalid), cases=cold)
    print(f'Continuation: {200 * len(bases):,} edits checked, explicit restarts =', sum(len(r['explicit_restarts']) for r in continuation), flush=True)
    print('Obstruction trace:', obstruction, flush=True)
    return report


class Native:
    def __init__(self, path):
        self.lib = ctypes.CDLL(str(Path(path).resolve()))
        self.lib.input_buffer.restype = self.lib.output_buffer.restype = ctypes.POINTER(ctypes.c_double)
        self.lib.solve.argtypes = [ctypes.c_int] * 3
        self.input = np.ctypeslib.as_array(self.lib.input_buffer(), shape=(3 * N,))
        self.output = np.ctypeslib.as_array(self.lib.output_buffer(), shape=(3 * N + 10,))

    def solve(self, k, previous=None, seed=17):
        n = len(k)
        self.input.fill(0)
        self.input[:min(n, N)] = k[:N]
        if previous:
            self.input[N:N+n] = previous['k']
            self.input[2*N:2*N+n] = previous['lengths']
        start = time.perf_counter()
        code = self.lib.solve(n, int(previous is not None), seed)
        ms = 1000 * (time.perf_counter() - start)
        return dict(k=k, status=code, milliseconds=ms, lengths=self.output[:n].tolist(),
                    vertices=self.output[N:N+2*n].reshape(n, 2).tolist())

    def jacobian_check(self):
        k = np.array([1., .4, .85, .2, .8, .3, .7, .6])
        q = np.linspace(.21, .76, len(k))
        def evaluate(x):
            self.input[:len(k)] = k
            self.input[N:N+len(k)] = x
            assert self.lib.evaluate(len(k)) == 1
            return self.output[:3].copy(), self.output[3:3+3*N].reshape(3, N)[:, :len(k)].copy()
        _, jac = evaluate(q)
        fd = np.zeros_like(jac)
        for j in range(len(k)):
            shift = np.eye(len(k))[j] * 1e-6
            fd[:, j] = (evaluate(q + shift)[0] - evaluate(q - shift)[0]) / 2e-6
        error = float(np.max(abs(jac - fd)))
        assert error < 2e-7, error
        assert self.solve([float('nan'), 2, 1, 2])['status'] == -2
        assert self.solve([float('inf'), 2, 1, 2])['status'] == -2
        return error


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native', required=True, type=Path)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    native = Native(args.native)
    report = run_suite(native.solve)
    report['backend'] = 'native IEEE double'
    report['jacobian_max_error'] = native.jacobian_check()
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ['cold_cases', 'cold_timing', 'jacobian_max_error']}, indent=2))
