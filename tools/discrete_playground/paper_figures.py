#!/usr/bin/env python3
"""Figures for paper/tabachnikov-converse.tex from the native discrete solver.

Build the solver and render (matplotlib is not a repository dependency):

    gcc -O3 -std=c99 -fPIC -shared tools/discrete_playground/solver.c -lm -o solver.so
    uv run --with numpy --with scipy --with matplotlib \
        python tools/discrete_playground/paper_figures.py --native solver.so

Every polygon is re-checked by validate.geometry before plotting. The figures
are numerical illustrations, not certificates.
"""
import argparse
import ctypes
import itertools
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt

from validate import geometry, ROOT

OUT = ROOT / 'paper/tabachnikov/figures'
N = 12
plt.rcParams.update({'pdf.fonttype': 42, 'svg.hashsalt': 'gluck', 'font.size': 8})


def solver(path):
    lib = ctypes.CDLL(str(path))
    lib.input_buffer.restype = lib.output_buffer.restype = ctypes.POINTER(ctypes.c_double)
    inp = np.ctypeslib.as_array(lib.input_buffer(), shape=(48,))
    out = np.ctypeslib.as_array(lib.output_buffer(), shape=(48,))

    def solve(k):
        status = None
        for seed in (0, 17, 18, 3, 5, 7):
            inp[:] = 0
            inp[:len(k)] = k
            status = lib.solve(len(k), 0, seed)
            if status == 1:
                ell = out[:len(k)].copy()
                v = out[N:N + 2 * len(k)].reshape(len(k), 2).copy()
                geometry(k, ell, v)
                return ell, v[:, 0] + 1j * v[:, 1]
        raise RuntimeError(f'solver failed for {k}: status {status}')
    return solve


def develop(k, ell):
    turns = np.arcsin(k * np.roll(ell, 1) / 2) + np.arcsin(k * ell / 2)
    headings = np.r_[0., np.cumsum(turns[1:])]
    steps = ell * np.exp(1j * headings)
    return turns, np.r_[0j, np.cumsum(steps)[:-1]], steps.sum()


def residual(k, x):
    turns, _, gap = develop(k, x)
    return np.array([gap.real, gap.imag, turns.sum() - 2 * np.pi])


def project(k, x):
    """Minimum-norm Newton steps back onto closure = 0, total turn = 2*pi."""
    for _ in range(50):
        with np.errstate(invalid='ignore'):
            f = residual(k, x)
        if not np.all(np.isfinite(f)) or np.any(x <= 0):
            return None
        if np.max(abs(f)) < 1e-14 * max(1, x.sum()):
            break
        h = 1e-7 * max(1e-3, x.mean())
        with np.errstate(invalid='ignore'):
            J = np.column_stack([(residual(k, x + h * e) - residual(k, x - h * e)) / (2 * h)
                                 for e in np.eye(len(x))])
        if not np.all(np.isfinite(J)):
            return None
        x = x - np.linalg.pinv(J) @ f
    return x


def spread(k, ell, steps=80):
    """Move inside the realization family towards larger min(log ell), by small
    trust-region steps, each projected back onto the exact equations. Every
    accepted polygon is re-validated. Display only."""
    from scipy.optimize import minimize
    k = np.asarray(k, float)
    cap = np.maximum(k, np.roll(k, -1)) / 2
    x = np.asarray(ell, float)
    for _ in range(steps):
        lo = np.maximum(x * 0.8, 1e-9)
        hi = np.maximum(np.minimum(x * 1.25 + 0.02 * x.max(), 0.999 / cap), x)
        cons = [dict(type='eq', fun=lambda y: residual(k, y))]
        res = minimize(lambda y: -np.log(y).sum(), x, bounds=list(zip(lo, hi)),
                       constraints=cons, method='SLSQP', options=dict(maxiter=200))
        y = project(k, np.clip(res.x, lo, hi))
        if y is not None and np.all(y > 0) and np.all(y * cap < 0.9995) and np.max(abs(residual(k, y))) < 1e-12:
            if np.log(y).sum() <= np.log(x).sum() + 1e-9:
                break
            x = y
        else:
            break
    geometry(k, x)
    return x, develop(k, x)[1]


def circumcircle(a, b, c):
    d = 2 * (a.real * (b.imag - c.imag) + b.real * (c.imag - a.imag) + c.real * (a.imag - b.imag))
    ux = (abs(a)**2 * (b.imag - c.imag) + abs(b)**2 * (c.imag - a.imag)
          + abs(c)**2 * (a.imag - b.imag)) / d
    uy = (abs(a)**2 * (c.real - b.real) + abs(b)**2 * (a.real - c.real)
          + abs(c)**2 * (b.real - a.real)) / d
    o = ux + 1j * uy
    return o, abs(a - o)


def min_enclosing(pts):
    """Smallest enclosing circle by brute force over pairs and triples."""
    best = None
    candidates = [((a + b) / 2, abs(a - b) / 2) for a, b in itertools.combinations(pts, 2)]
    candidates += [circumcircle(a, b, c) for a, b, c in itertools.combinations(pts, 3)
                   if abs(np.imag(np.conj(b - a) * (c - a))) > 1e-14]
    for o, r in candidates:
        if all(abs(p - o) <= r * (1 + 1e-12) for p in pts) and (best is None or r < best[1]):
            best = (o, r)
    return best


def draw_polygon(ax, v, k, circles=True, label=True):
    n = len(v)
    cyc = np.r_[v, v[0]]
    if circles:
        cmap = plt.get_cmap('viridis')
        for i in range(n):
            o, r = circumcircle(v[i - 1], v[i], v[(i + 1) % n])
            color = cmap(i / max(1, n - 1))
            ax.add_patch(plt.Circle((o.real, o.imag), r, fill=False, lw=0.6, alpha=0.7, color=color))
            ax.plot(o.real, o.imag, '.', ms=2.5, color=color)
    ax.plot(cyc.real, cyc.imag, '-', color='black', lw=1.2)
    ax.plot(v.real, v.imag, 'o', color='black', ms=3)
    if label:
        c = v.mean()
        scale = max(abs(v - c))
        for i in range(n):
            d = (v[i] - c) / abs(v[i] - c)
            p = v[i] + 0.1 * d * scale
            ax.annotate(f'{k[i]:g}', (p.real, p.imag), ha='center', va='center', fontsize=7,
                        annotation_clip=False)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.margins(0.12)


def figure_example(solve):
    k = [3.0, 1.2, 2.2, 0.8, 2.6, 1.0, 1.6, 0.7]
    ell, _ = solve(k)
    _, v = spread(k, ell)
    fig, axes = plt.subplots(1, 2, figsize=(7.0, 3.3))
    draw_polygon(axes[0], v, k, circles=False)
    axes[0].set_title('realized octagon, curvature at each vertex')
    draw_polygon(axes[1], v, k, circles=True, label=False)
    axes[1].set_title('circles through consecutive triples')
    fig.tight_layout()
    fig.savefig(OUT / 'example.pdf', metadata={'CreationDate': None})
    plt.close(fig)
    return k


def figure_hexagon(solve):
    fig, axes = plt.subplots(1, 3, figsize=(7.2, 2.6), gridspec_kw=dict(width_ratios=[1.15, 1, 1]))
    ax = axes[0]
    s = np.linspace(0, 1, 201)
    ax.fill_between(s, 5, 7 - 3 * s, where=7 - 3 * s > 5, color='tab:blue', alpha=0.35, lw=0)
    ax.fill_between(s, 11, 10 + 3 * s, where=10 + 3 * s > 11, color='tab:orange', alpha=0.35, lw=0)
    ax.axhline(9, color='gray', ls='--', lw=0.8)
    ax.set_xlabel('$s$')
    ax.set_ylabel('window level $c$')
    ax.set_ylim(3, 15)
    ax.set_title(r'four-vertex levels of $\kappa^s$')
    radii = {}
    for ax, sv in zip(axes[1:], (0.0, 1.0)):
        k = [14, 11, 10 + 3 * sv, 5, 7 - 3 * sv, 3]
        ell, _ = solve(k)
        _, v = spread(k, ell)
        o, r = min_enclosing(list(v))
        radii[sv] = 1 / r
        ax.add_patch(plt.Circle((o.real, o.imag), r, fill=False, lw=0.9, color='tab:red'))
        draw_polygon(ax, v, k, circles=False)
        ax.set_title(f'$s={sv:g}$,  $1/R = {1 / r:.2f}$')
        ax.set_xlim(o.real - 1.2 * r, o.real + 1.2 * r)
        ax.set_ylim(o.imag - 1.2 * r, o.imag + 1.2 * r)
    fig.tight_layout()
    fig.savefig(OUT / 'hexagon.pdf', metadata={'CreationDate': None})
    plt.close(fig)
    return radii


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native', required=True, type=Path)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    solve = solver(args.native.resolve())
    print('example profile', figure_example(solve))
    print('enclosing levels 1/R', figure_hexagon(solve))
