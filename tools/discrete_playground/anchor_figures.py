#!/usr/bin/env python3
"""Illustrations of regular anchors for paper/tabachnikov-converse.tex.

    uv run --no-project --with numpy --with scipy --with matplotlib \
        python tools/discrete_playground/anchor_figures.py

Each figure is computed, not drawn by hand: the four active edges are chosen
by the rule of the paper (repeated maximum, first transition, or both flags
negative), the four-length system Phi(L) = 0 is solved numerically (with
orthogonal diagonals for the orthogonal constructions), the Jacobian rank is
checked, the dormant edges are opened by a Newton correction of the active
lengths, and every polygon is re-validated by validate.geometry. Numerical
illustrations only; the proofs are in the paper and in Lean.
"""
import numpy as np
from scipy.optimize import least_squares
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt
from matplotlib.patches import Arc

from validate import geometry, ROOT
from paper_figures import spread, develop

OUT = ROOT / 'paper/tabachnikov/figures'
plt.rcParams.update({'pdf.fonttype': 42, 'font.size': 8})
BLUE, ORANGE, GREY = '#1f5fa8', '#d9731a', '#9a9a9a'


# ---------------------------------------------------------------- the model

def sigma(h, l):
    return np.sqrt((1 - l * l) / (h * h - l * l))


def flag(p, q, h, l):
    s = sigma(h, l)
    return np.arcsin(p) + np.arcsin(q * s) - np.arcsin(s) - np.pi / 2


def turns(L, s, f):
    return np.array([np.arcsin(f[(j - 1) % 4] * L[(j - 1) % 4]) + np.arcsin(s[j] * L[j])
                     for j in range(4)])


def quad(L, s, f):
    """Vertices Q_0..Q_3 of the collapsed quadrilateral (edge j = 2 L_j)."""
    b = turns(L, s, f)
    heads = np.r_[0, np.cumsum(b[1:])]
    steps = 2 * L * np.exp(1j * heads)
    return np.r_[0j, np.cumsum(steps)[:-1]], steps.sum(), b.sum() - 2 * np.pi


def controller(L, s, f):
    _, gap, turn = quad(L, s, f)
    return np.array([gap.real / 2, gap.imag / 2, turn])


def orth(L, s, f):
    Q, _, _ = quad(L, s, f)
    d1, d2 = Q[2] - Q[0], Q[3] - Q[1]
    return (np.conj(d1) * d2).real / (abs(d1) * abs(d2))


def jac(fun, L, h=1e-7):
    return np.column_stack([(fun(L + h * e) - fun(L - h * e)) / (2 * h) for e in np.eye(len(L))])


def solve_anchor(s, f, orthogonal, seed=1):
    rng = np.random.default_rng(seed)
    cap = 1 / np.maximum(s, f)
    best = None
    for _ in range(400):
        x0 = cap * rng.uniform(0.2, 0.95, 4)
        res = (lambda L: np.r_[controller(L, s, f), orth(L, s, f)]) if orthogonal else \
              (lambda L: np.r_[controller(L, s, f), 0.0])
        try:
            r = least_squares(res, x0, bounds=(1e-9, cap * (1 - 1e-9)), xtol=1e-15, ftol=1e-15, gtol=1e-15)
        except ValueError:
            continue
        L = r.x
        if np.max(abs(controller(L, s, f))) < 1e-12 and (not orthogonal or abs(orth(L, s, f)) < 1e-10) \
                and np.all(L > 1e-4 * cap) and np.all(L * np.maximum(s, f) < 1 - 1e-6):
            sv = np.linalg.svd(jac(lambda y: controller(y, s, f), L), compute_uv=False)
            if sv[-1] > 1e-3 and (best is None or min(L / cap) > min(best / cap)):
                best = L
    if best is None:
        raise RuntimeError('no regular anchor found')
    return best


def frame_readings(k, e):
    n = len(k)
    return np.array([k[j] for j in e]), np.array([k[(j + 1) % n] for j in e])


def open_anchor(k, e, L, eps):
    """Give each dormant edge half-length eps and re-solve closure and turn with
    the active half-lengths (minimum-norm Newton), keeping every reading."""
    n = len(k)
    k = np.asarray(k, float)
    h = np.full(n, eps)
    h[list(e)] = L

    def F(act):
        hh = h.copy()
        hh[list(e)] = act
        t, _, gap = develop(k, 2 * hh)
        return np.array([gap.real, gap.imag, t.sum() - 2 * np.pi])
    act = np.array(L, float)
    for _ in range(60):
        r = F(act)
        if np.max(abs(r)) < 1e-14:
            break
        J = jac(F, act)
        act = act - np.linalg.pinv(J) @ r
    h[list(e)] = act
    geometry(k, 2 * h)
    return 2 * h


# ---------------------------------------------------------------- selection

def mountain_transition(mu, H):
    """Least i on the rising leg to H with flag(p, mu_i, mu_{i+1}, l) >= 0."""
    n = len(mu)
    p, l = mu[1], mu[-1]
    a = H
    while mu[(a - 1) % n] < mu[a % n] and (a - 1) % n != 0:
        a -= 1
    for i in range(max(a, 1), H):
        t, q, h = mu[i - 1], mu[i], mu[i + 1]
        if q > 1 and h > q and flag(p, q, h, l) >= 0:
            return i
    raise ValueError('no transition')


def classify(k):
    """Return (case, shift, mu, frame) following the paper's case split."""
    k = np.asarray(k, float)
    n = len(k)
    M = k.max()
    tops = np.flatnonzero(k == M)
    if len(tops) > 1:
        H0 = tops[0]
        mu = np.roll(k, -H0) / M
        J = int(np.flatnonzero(mu == 1)[1])
        return 'R', H0, mu, (0, J - 1, J, n - 1)
    H0 = int(np.argmax(k))
    peaks = [i for i in range(n) if k[i] > k[i - 1] and k[i] > k[(i + 1) % n] and i != H0]
    q = max(peaks, key=lambda i: k[i])
    mu = np.roll(k, -q) / k[q]
    H = (H0 - q) % n
    Fp = flag(mu[1], mu[H - 1], mu[H], mu[-1])
    Fm = flag(mu[-1], mu[(H + 1) % n], mu[H], mu[1])
    if Fp >= 0:
        i = mountain_transition(mu, H)
        return 'F', q, mu, (0, i - 1, i, n - 1)
    if Fm >= 0:
        return 'F-', q, mu, None
    return 'N', q, mu, (0, H - 1, H, n - 1)


# ---------------------------------------------------------------- drawing

def chord_arc(ax, A, B, kappa, color, lw=0.9, alpha=0.9):
    """Minor arc of curvature kappa through A and B, bulging outward (to the
    right of A->B); its circle has its centre on the polygon side."""
    c = abs(B - A) / 2
    r = 1 / kappa
    d = np.sqrt(max(r * r - c * c, 0))
    u = (B - A) / abs(B - A)
    O = (A + B) / 2 + 1j * u * d
    ta, tb = np.angle(A - O), np.angle(B - O)
    sweep = (ta - tb) % (2 * np.pi)          # from B counterclockwise to A
    if sweep > np.pi:                        # take the minor arc (outer side)
        tb, sweep = ta, 2 * np.pi - sweep
    t = tb + np.linspace(0, sweep, 60)
    z = O + r * np.exp(1j * t)
    ax.plot(z.real, z.imag, color=color, lw=lw, alpha=alpha)
    return z


def blocks(n, e):
    """Vertex indices collapsed into each corner Q_j (block before edge e_j)."""
    out = []
    for j in range(4):
        start = (e[j - 1] + 1) if j > 0 else (e[3] + 1)
        idx = [(v % n) for v in range(start, e[j] + 1 + (n if j == 0 else 0))]
        out.append(idx)
    return out


def draw_anchor(ax, mu, e, L, names, orthogonal, readings=True):
    n = len(mu)
    s, f = frame_readings(mu, e)
    Q, _, _ = quad(L, s, f)
    cyc = np.r_[Q, Q[0]]
    drawn = [Q]
    for j in range(4):
        A, B = Q[j], Q[(j + 1) % 4]
        drawn.append(chord_arc(ax, A, B, s[j], BLUE))
        drawn.append(chord_arc(ax, A, B, f[j], ORANGE))
    ax.plot(cyc.real, cyc.imag, '-', color='black', lw=1.4)
    if orthogonal:
        for a, b in ((0, 2), (1, 3)):
            ax.plot([Q[a].real, Q[b].real], [Q[a].imag, Q[b].imag], ls=(0, (3, 2)), color=GREY, lw=0.7)
    ctr = Q.mean()
    scale = max(abs(Q - ctr))
    for j, idx in enumerate(blocks(n, e)):
        d = (Q[j] - ctr) / abs(Q[j] - ctr)
        p = Q[j] + 0.2 * scale * d
        lab = names[j]
        ax.plot(Q[j].real, Q[j].imag, 'o', color='black', ms=4 if len(idx) == 1 else 6,
                mfc='white' if len(idx) > 1 else 'black')
        ax.annotate(lab, (p.real, p.imag), ha='center', va='center', fontsize=7.5, annotation_clip=False)
        drawn.append(np.array([p]))
    for j in range(4 if readings else 0):
        A, B = Q[j], Q[(j + 1) % 4]
        u = (B - A) / abs(B - A)
        nrm = -1j * u
        for frac, val, col, nm in ((0.2, s[j], BLUE, 's'), (0.8, f[j], ORANGE, 'f')):
            p = A + frac * (B - A) + 0.11 * scale * nrm
            ax.annotate(f'${nm}_{j}$', (p.real, p.imag), ha='center', va='center', fontsize=7, color=col,
                        annotation_clip=False)
            drawn.append(np.array([p]))
    ax.set_aspect('equal')
    ax.axis('off')
    pts = np.concatenate(drawn)
    pad = 0.12 * scale
    ax.set_xlim(pts.real.min() - pad, pts.real.max() + pad)
    ax.set_ylim(pts.imag.min() - pad, pts.imag.max() + pad)
    return Q


def zoom_window(mu, e, ell, zoom_block):
    mu = np.asarray(mu, float)
    _, v, _ = develop(mu, ell)
    pts = v[blocks(len(mu), e)[zoom_block]]
    ctr = pts.mean()
    span = max(np.ptp(pts.real), np.ptp(pts.imag), 1e-9)
    return v, ctr, 1.5 * span


def draw_opened(ax, mu, e, ell, zoom_block):
    """The opened polygon; the zoom region is boxed."""
    v, ctr, w = zoom_window(mu, e, ell, zoom_block)
    cyc = np.r_[v, v[0]]
    ax.plot(cyc.real, cyc.imag, '-', color='black', lw=1.2)
    ax.plot(v.real, v.imag, 'o', color='black', ms=2.5)
    ax.add_patch(plt.Rectangle((ctr.real - w, ctr.imag - w), 2 * w, 2 * w, fill=False,
                               ec='#888888', lw=0.7))
    ax.set_aspect('equal')
    ax.axis('off')
    ax.margins(0.08)


def draw_zoom(ax, mu, e, ell, zoom_block):
    """Magnified view of one formerly collapsed block: its short dormant edges
    (orange) between the two active edges, each vertex labelled i: kappa_i."""
    mu = np.asarray(mu, float)
    n = len(mu)
    v, ctr, w = zoom_window(mu, e, ell, zoom_block)
    cyc = np.r_[v, v[0]]
    ax.plot(cyc.real, cyc.imag, '-', color='black', lw=1.2)
    for i in range(n):
        if i not in set(e):
            a, b = v[i], v[(i + 1) % n]
            ax.plot([a.real, b.real], [a.imag, b.imag], '-', color=ORANGE, lw=2.4)
    ax.plot(v.real, v.imag, 'o', color='black', ms=3.5)
    idx = blocks(n, e)[zoom_block]
    for m, i in enumerate(idx):
        tan = v[(i + 1) % n] - v[i - 1]
        nrm = -1j * tan / abs(tan)             # outward for a ccw polygon
        side = 1 if m % 2 == 0 else -1
        p = v[i] + side * (0.17 + 0.17 * ((m // 2) % 2)) * w * nrm
        ax.annotate(f'{i}: {mu[i]:.2f}', (p.real, p.imag), ha='center', va='center', fontsize=6.5,
                    annotation_clip=False)
    ax.set_xlim(ctr.real - w, ctr.real + w)
    ax.set_ylim(ctr.imag - w, ctr.imag + w)
    ax.set_aspect('equal')
    ax.set_xticks([])
    ax.set_yticks([])
    for sp in ax.spines.values():
        sp.set_color('#888888')
        sp.set_linewidth(0.7)


def draw_word(ax, k, e, highlight=True):
    n = len(k)
    idx = np.arange(n)
    active_ends = set()
    for j in e:
        active_ends |= {j, (j + 1) % n}
    for i in idx:
        col = 'black' if i in active_ends else GREY
        ax.vlines(i, 0, k[i], color=col, lw=1.6 if i in active_ends else 1.0)
        ax.plot(i, k[i], 'o', color=col, ms=3.5)
    for j, ej in enumerate(e):
        a, b = ej, (ej + 1) % n
        if b == 0:
            b = n
        ax.axvspan(a - 0.15, b + 0.15 if b != n else n - 0.5, color='#e8eef8', zorder=-1)
        ax.annotate(f'$e_{j}$', ((a + (b if b != n else n - 0.5)) / 2, max(k) * 1.08),
                    ha='center', fontsize=7)
    ax.set_xticks(idx)
    ax.set_xticklabels([str(i) for i in idx], fontsize=6.5)
    ax.set_yticks([])
    for sp in ('top', 'right', 'left'):
        ax.spines[sp].set_visible(False)
    ax.set_xlim(-0.6, n - 0.4)
    ax.set_ylim(0, max(k) * 1.2)


def draw_polygon(ax, v, color='black', lw=1.2, ms=3):
    cyc = np.r_[v, v[0]]
    ax.plot(cyc.real, cyc.imag, '-', color=color, lw=lw)
    ax.plot(v.real, v.imag, 'o', color=color, ms=ms)
    ax.set_aspect('equal')
    ax.axis('off')


def block_names(mu, e, fmt):
    n = len(mu)
    names = []
    for idx in blocks(n, e):
        if len(idx) == 1:
            names.append(fmt(idx[0]))
        else:
            names.append(f'{{{fmt(idx[0])},…,{fmt(idx[-1])}}}')
    return names


# ---------------------------------------------------------------- figures

def build(k, expect):
    case, shift, mu, e = classify(k)
    assert case == expect, (case, expect, k)
    s, f = frame_readings(mu, e)
    orthogonal = case in ('R', 'N') or (case == 'F' and s[1] > f[0])
    L = solve_anchor(s, f, orthogonal)
    return case, shift, mu, e, L, orthogonal


def figure_anchor_and_method(k):
    case, shift, mu, e, L, orthogonal = build(k, 'F')
    n = len(mu)
    names = block_names(mu, e, lambda i: f'{i}')
    # anchor figure
    fig, ax = plt.subplots(figsize=(3.6, 3.1))
    draw_anchor(ax, mu, e, L, names, False)
    fig.tight_layout()
    fig.savefig(OUT / 'anchor.pdf', metadata={'CreationDate': None})
    plt.close(fig)
    # method figure
    fig = plt.figure(figsize=(7.0, 4.3))
    gs = fig.add_gridspec(2, 4, height_ratios=[0.75, 1.6])
    ax0 = fig.add_subplot(gs[0, :])
    draw_word(ax0, mu, e)
    ax0.set_title('(a) the curvature word; four active edges $e_0,\\dots,e_3$ and their eight endpoint readings',
                  fontsize=8)
    ax1 = fig.add_subplot(gs[1, 0])
    draw_anchor(ax1, mu, e, L, names, False, readings=False)
    ax1.set_title('(b) regular anchor: dormant\nedges have length zero', fontsize=8)
    ell_open = open_anchor(mu, e, L, eps=0.05 * L.mean())
    _, v_open, _ = develop(np.asarray(mu), ell_open)
    ax2 = fig.add_subplot(gs[1, 1])
    zb = int(np.argmax([len(b) for b in blocks(n, e)]))
    draw_opened(ax2, mu, e, ell_open, zb)
    ax2.set_title('(c) dormant edges opened\n(implicit function theorem)', fontsize=8)
    axz = fig.add_subplot(gs[1, 2])
    draw_zoom(axz, mu, e, ell_open, zb)
    blk = blocks(n, e)[zb]
    axz.set_title(f'(c) zoom: block {{{blk[0]},…,{blk[-1]}}}', fontsize=8)
    _, v_fin = spread(list(mu), ell_open)
    ax3 = fig.add_subplot(gs[1, 3])
    draw_polygon(ax3, v_fin)
    ax3.set_title('(d) the same curvatures,\nanother realization', fontsize=8)
    fig.tight_layout()
    fig.savefig(OUT / 'method.pdf', metadata={'CreationDate': None})
    plt.close(fig)
    return mu, e, L


def with_dormant(k, expect):
    """Insert one monotone reading inside each collapsed block of two or more
    vertices. Such readings create no new extremum and are not endpoint
    readings, so the case, the eight endpoint readings and the anchor are
    unchanged (the dormant invariance of the four-length system)."""
    case, shift, mu, e = classify(k)
    assert case == expect
    s0, f0 = frame_readings(mu, e)
    out = []
    n = len(mu)
    inner = set()
    for idx in blocks(n, e):
        if len(idx) >= 2:
            inner.add(idx[0])
    for i in range(n):
        out.append(mu[i])
        if i in inner:
            out.append((mu[i] + mu[(i + 1) % n]) / 2)
    case2, shift2, mu2, e2 = classify(out)
    s2, f2 = frame_readings(mu2, e2)
    assert case2 == expect and np.allclose(s2, s0) and np.allclose(f2, f0), (case2, s2, s0, f2, f0)
    return out


def figure_construction(k, expect, name, title):
    k = with_dormant(k, expect)
    case, shift, mu, e, L, orthogonal = build(k, expect)
    n = len(mu)
    ell_open = open_anchor(mu, e, L, eps=0.03 * L.mean())
    sizes = [len(b) for b in blocks(n, e)]
    zb = int(np.argmax(sizes))
    fig = plt.figure(figsize=(7.0, 4.3))
    gs = fig.add_gridspec(2, 3, height_ratios=[0.8, 1.5])
    ax0 = fig.add_subplot(gs[0, :])
    draw_word(ax0, mu, e)
    ax0.set_title(title, fontsize=8)
    ax1 = fig.add_subplot(gs[1, 0])
    draw_anchor(ax1, mu, e, L, block_names(mu, e, lambda i: f'{i}'), orthogonal, readings=False)
    ax1.set_title('regular anchor', fontsize=8)
    ax2 = fig.add_subplot(gs[1, 1])
    draw_opened(ax2, mu, e, ell_open, zb)
    ax2.set_title('dormant edges opened', fontsize=8)
    ax3 = fig.add_subplot(gs[1, 2])
    draw_zoom(ax3, mu, e, ell_open, zb)
    ax3.set_title(f'zoom: block {{{blocks(n, e)[zb][0]},…,{blocks(n, e)[zb][-1]}}}', fontsize=8)
    fig.tight_layout()
    fig.savefig(OUT / f'construct-{name}.pdf', metadata={'CreationDate': None})
    plt.close(fig)
    return mu, e, L


if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    print('method/anchor', figure_anchor_and_method([0.7, 2.8, 3.0, 2.0, 0.9, 0.8, 1.6, 1.5, 1.0]))
    print('R', figure_construction([2.3, 1.3, 1.9, 2.3, 1.2, 2.0], 'R', 'R',
                                   'repeated maximum: edges around both maxima'))
    print('F', figure_construction([1.1, 2.3, 2.2, 1.8, 2.9, 3.0], 'F', 'F',
                                   'forward flag $\\geq 0$: first transition on the rising leg'))
    print('N', figure_construction([2.4, 2.3, 1.6, 2.5, 1.8, 2.2], 'N', 'N',
                                   'both flags negative: edges around the two peaks'))
