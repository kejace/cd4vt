#!/usr/bin/env python3
"""Exact rational examples for the side-tangent supplement to the discrete paper.

No solver is used. All geometric assertions use fractions.Fraction before any
coordinates are converted for rendering. The pictures illustrate one example;
the general theorem is proved in Lean, not by this generator.

Run through the repository CAS resource launcher. If /opt/cas-venv is absent,
a temporary CAS_VENV with bin/python pointing to the installed python3 suffices:
this script uses only the Python standard library, pdflatex and pdftocairo.

    CAS_VENV=/tmp/gluck-figure-cas CAS_WORKERS=1 \
      ../gluck-physical/tools/cas/run python \
      tools/discrete_playground/side_tangent_figures.py
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
from tempfile import TemporaryDirectory
import hashlib
import json
import platform
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'paper/tabachnikov/figures'
SITE = ROOT / 'site/figures'
ZERO = (Q(0), Q(0))


def add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def sub(x, y):
    return tuple(a - b for a, b in zip(x, y))


def scale(a, x):
    return tuple(a * b for b in x)


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def cross(x, y):
    return x[0] * y[1] - x[1] * y[0]


def solve3(rows, rhs):
    """Independent exact linear-system check of each center and radius."""
    a = [list(row) + [b] for row, b in zip(rows, rhs)]
    pivots = []
    for j in range(3):
        k = next(k for k in range(j, 3) if a[k][j])
        a[j], a[k] = a[k], a[j]
        v = a[j][j]
        pivots.append(v)
        a[j] = [x / v for x in a[j]]
        for k in range(3):
            if k != j:
                v = a[k][j]
                a[k] = [x - v*y for x, y in zip(a[k], a[j])]
    return [a[j][3] for j in range(3)], pivots


def exact_example():
    u = [(Q(1), Q(0)), (Q(3, 5), Q(4, 5)),
         (Q(0), Q(1)), (Q(-4, 5), Q(3, 5))]
    u += [scale(-1, v) for v in u]
    y = [scale(1 / (1 + dot(u[i], u[(i+1) % 8])),
               add(u[i], u[(i+1) % 8])) for i in range(8)]
    radii = [Q(1), Q(2), Q(1), Q(3, 2)] * 2
    coeff = [radii[i-1] - radii[i] for i in range(8)]
    edges = [scale(radii[i], sub(y[(i+1) % 8], y[i])) for i in range(8)]
    p = [ZERO]
    for edge in edges:
        p.append(add(p[-1], edge))
    assert p.pop() == p[0]
    normal = [u[(i+1) % 8] for i in range(8)]
    centers = [sub(p[i], scale(radii[i], y[i])) for i in range(8)]
    return u, y, radii, coeff, edges, p, normal, centers


def verify(data):
    u, y, radii, coeff, edges, p, normal, centers = data
    n = len(p)
    assert all(r > 0 for r in radii)
    assert sum(coeff) == 0
    assert all(coeff[i] * coeff[(i+1) % n] < 0 for i in range(n))
    balance = tuple(sum(coeff[i] * y[i][k] for i in range(n)) for k in range(2))
    closure = tuple(sum(e[k] for e in edges) for k in range(2))
    assert balance == closure == ZERO
    assert len(set(p)) == n
    support_margins, contact_parameters, pivots = [], [], []
    for i in range(n):
        j = (i+1) % n
        assert dot(u[i], u[i]) == 1
        assert cross(u[i], u[j]) > 0
        assert dot(u[i], y[i]) == dot(u[j], y[i]) == 1
        assert sub(p[j], p[i]) == edges[i]
        assert dot(normal[i], edges[i]) == 0
        assert cross(normal[i], edges[i]) > 0
        for k in range(n):
            if k not in (i, j):
                margin = cross(edges[i], sub(p[k], p[i]))
                assert margin > 0
                support_margins.append(margin)
                assert dot(u[k], y[i]) < 1
        ks = [(i-1) % n, i, j]
        sol, ps = solve3([(*normal[k], Q(1)) for k in ks],
                         [dot(normal[k], p[k]) for k in ks])
        assert tuple(sol[:2]) == centers[i] and sol[2] == radii[i]
        pivots.append(ps)
        params = []
        for k in ks:
            assert dot(normal[k], sub(p[k], centers[i])) == radii[i]
            foot = add(centers[i], scale(radii[i], normal[k]))
            assert dot(normal[k], sub(foot, p[k])) == 0
            assert dot(sub(foot, centers[i]), sub(foot, centers[i])) == radii[i] ** 2
            t = dot(sub(foot, p[k]), edges[k]) / dot(edges[k], edges[k])
            assert add(p[k], scale(t, edges[k])) == foot
            if k == i:
                assert 0 < t < 1
            params.append(t)
        contact_parameters.append(params)
    assert contact_parameters[1] == [Q(1, 5), Q(2, 5), Q(6, 5)]
    def encoded(values):
        if isinstance(values, (tuple, list)):
            return [encoded(x) for x in values]
        return str(values)
    return {
        'description': 'Exact rational illustrative octagon; not an extracted Lean witness.',
        'arithmetic': 'Python standard-library fractions.Fraction; no numerical solver',
        'solver_used': False,
        'normals_u': encoded(u), 'tangential_vertices_y': encoded(y),
        'radii': encoded(radii), 'radius_differences': encoded(coeff),
        'scaled_vertices_p': encoded(p), 'circle_centers': encoded(centers),
        'balance_sum': encoded(balance), 'edge_closure_sum': encoded(closure),
        'minimum_strict_support_cross': str(min(support_margins)),
        'contact_edge_parameters_previous_central_next': encoded(contact_parameters),
        'three_line_system_nonzero_elimination_pivots': encoded(pivots),
        'checks': {'positive_radii': True, 'alternating_nonzero_differences': True,
                   'unit_normals': True, 'strict_convex_support': True,
                   'exact_balance_and_closure': True, 'exact_edge_scaling': True,
                   'all_three_inward_signed_distances': True,
                   'all_contact_squared_distances': True,
                   'all_central_contacts_in_open_edges': True,
                   'independent_three_line_system_solutions': True,
                   'selected_neighbor_contact_beyond_endpoint': True},
    }


PREAMBLE = r'''\documentclass[border=3pt]{standalone}
\usepackage{amsmath,amssymb,tikz}
\usetikzlibrary{arrows.meta}
\pdfinfoomitdate=1
\pdftrailerid{}
\definecolor{ink}{HTML}{242E2C}
\definecolor{teal}{HTML}{386F79}
\definecolor{gold}{HTML}{A76C27}
\definecolor{slate}{HTML}{69798A}
\definecolor{berry}{HTML}{99606C}
\definecolor{quiet}{HTML}{9AA3A1}
\begin{document}
'''


def xy(point):
    return '(' + ','.join(f'{float(x):.9f}' for x in point) + ')'


def coords(name, points):
    return '\n'.join(r'\coordinate (' + name + str(i) + ') at ' + xy(p) + ';'
                     for i, p in enumerate(points))


def circle_figure(data):
    _, _, radii, _, edges, p, normals, centers = data
    i = 1
    c = centers[i]
    feet = [add(c, scale(radii[i], normals[k])) for k in (0, 1, 2)]
    parts = [PREAMBLE, r'\begin{tikzpicture}[x=1.8cm,y=1.8cm,font=\small,text=ink]',
             r'\path[use as bounding box] (-3.78,-3.62) rectangle (0.82,1.02);',
             coords('p', p), r'\coordinate (c) at ' + xy(c) + ';', coords('f', feet),
             r'\fill[ink!5] (p0)--(p1)--(p2)--(p3)--(p4)--(p5)--(p6)--(p7)--cycle;']
    for k, lo, hi in [(0, Q(-4, 5), Q(2)), (1, Q(-2, 5), Q(7, 5)),
                      (2, Q(-3, 5), Q(11, 5))]:
        a, b = add(p[k], scale(lo, edges[k])), add(p[k], scale(hi, edges[k]))
        parts += [r'\draw[quiet,densely dashed,line width=.55pt] ' + xy(a) + '--' + xy(b) + ';']
    parts += [r'\draw[teal,line width=1pt] (c) circle[radius=2];',
              r'\draw[ink,line width=1pt] (p0)--(p1)--(p2)--(p3)--(p4)--(p5)--(p6)--(p7)--cycle;',
              r'\draw[teal,line width=1.65pt] (p1)--(p2);',
              r'\draw[gold,line width=1.05pt,densely dashed] (p3)--(f2);',
              r'\draw[teal,line width=.65pt] (c)--(f1);',
              r'\draw[teal!65,line width=.5pt,densely dotted] (c)--(f0) (c)--(f2);']
    for k, f in enumerate(feet):
        tangent = (-normals[k][1], normals[k][0])
        inward = scale(-Q(7, 100), normals[k])
        along = scale(Q(7, 100), tangent)
        mark = [add(f, along), add(add(f, along), inward), add(f, inward)]
        parts += [r'\draw[teal,line width=.5pt] ' + '--'.join(xy(a) for a in mark) + ';',
                  r'\fill[teal] ' + xy(f) + ' circle[radius=1.4pt];']
    parts += [r'\foreach \j in {0,...,7} \fill[ink] (p\j) circle[radius=1pt];',
              r'\fill[teal] (c) circle[radius=1.5pt];',
              r'\node[above right=2pt] at (p1) {$P_i$};',
              r'\node[above left=2pt] at (p2) {$P_{i+1}$};',
              r'\node[above=3pt,text=teal] at (f1) {$F_i$};',
              r'\node[right=3pt] at (-1.333333,-.57) {$\rho_i=2$};',
              r'\node[below right=2pt,text=teal] at (c) {$C_i$};',
              r'\node at (.27,.66) {$\ell_i$};',
              r'\node at (.60,-.25) {$\ell_{i-1}$};',
              r'\node at (-3.49,-.63) {$\ell_{i+1}$};',
              r'\node[text=gold,font=\footnotesize,align=center,fill=ink!5,inner sep=1pt] (note) at (-2.25,-.85) {extension\\contact};',
              r'\draw[gold,-{Stealth[length=3pt]},line width=.45pt] (note.north west) to[bend right=12] (f2);',
              r'\end{tikzpicture}', r'\end{document}']
    return '\n'.join(parts) + '\n'


def construction_figure(data):
    _, y, radii, coeff, edges, p, _, _ = data
    pc = scale(Q(1, 8), tuple(sum(v[k] for v in p) for k in range(2)))
    pp = [add(sub(v, pc), (Q(9, 2), Q(0))) for v in p]
    colors = ['teal', 'gold', 'slate', 'berry'] * 2
    parts = [PREAMBLE, r'\begin{tikzpicture}[x=1.75cm,y=1.75cm,font=\small,text=ink]',
             r'\path[use as bounding box] (-1.60,-2.15) rectangle (6.15,1.82);',
             coords('y', y), coords('p', pp),
             r'\fill[ink!3] (y0)--(y1)--(y2)--(y3)--(y4)--(y5)--(y6)--(y7)--cycle;',
             r'\fill[ink!3] (p0)--(p1)--(p2)--(p3)--(p4)--(p5)--(p6)--(p7)--cycle;',
             r'\draw[quiet,line width=.6pt] (0,0) circle[radius=1];',
             r'\fill[quiet] (0,0) circle[radius=1pt];',
             r'\node[text=quiet,font=\footnotesize] at (0,-.15) {unit circle};']
    for i, color in enumerate(colors):
        j = (i+1) % 8
        parts += [rf'\draw[{color},line width=1.3pt] (y{i})--(y{j});',
                  rf'\draw[{color},line width=1.3pt] (p{i})--(p{j});']
        # Exact affine positions for a short arrow on each corresponding edge.
        for vs in (y, pp):
            e = sub(vs[j], vs[i])
            a, b = add(vs[i], scale(Q(2, 5), e)), add(vs[i], scale(Q(3, 5), e))
            parts += [rf'\draw[{color},-{{Stealth[length=3pt]}},line width=.65pt] {xy(a)}--{xy(b)};']
        sign = '+' if coeff[i] > 0 else '-'
        sign_pt = scale(Q(6, 5), y[i])
        parts += [r'\node[font=\footnotesize,text=' + ('teal' if sign == '+' else 'berry')
                  + '] at ' + xy(sign_pt) + ' {$' + sign + '$};']
    parts += [r'\node at (0,1.64) {Tangential fan $Y$};',
              r'\node at (4.5,1.64) {Scaled polygon $P$};',
              r'\draw[ink!65,-{Stealth[length=5pt]},line width=.7pt] (1.57,.08)--(2.64,.08);',
              r'\node[align=center,font=\footnotesize] at (2.10,.52) {multiply edge $i$\\by $\rho_i>0$};',
              r'\node[align=center,font=\footnotesize,text=ink!75] at (2.10,-.39) {same directions\\exact closure};',
              r'\node[above=2pt,text=gold] at (-.083333,1) {$e_1$};',
              r'\node[above=2pt,text=gold] at (4.416667,1.208333) {$2e_1$};',
              r'\node[text=berry,left=3pt,font=\footnotesize] at (5.916667,.083333) {$\tfrac32 e_7$};',
              r'\node[align=center,font=\footnotesize] at (0,-1.63) {$c_i=\rho_{i-1}-\rho_i$\\$\sum_i c_iY_i=0$};',
              r'\node[align=center,font=\footnotesize] at (4.5,-1.63)',
              r'  {$P_{i+1}-P_i=\rho_i(Y_{i+1}-Y_i)$\\$\sum_i(P_{i+1}-P_i)=0$};',
              r'\node[font=\footnotesize] at (2.26,-2.03)',
              r'  {$\rho=(1,2,1,\tfrac32,1,2,1,\tfrac32)$; signs at the $Y_i$ are those of $c_i$.};',
              r'\end{tikzpicture}', r'\end{document}']
    return '\n'.join(parts) + '\n'


def render(name, tex, description):
    PAPER.mkdir(parents=True, exist_ok=True)
    SITE.mkdir(parents=True, exist_ok=True)
    stem = 'side-tangent-' + name
    (PAPER / (stem + '.tex')).write_text(tex)
    with TemporaryDirectory(prefix='gluck-side-tangent-') as tmp:
        tmp = Path(tmp)
        source = tmp / (stem + '.tex')
        source.write_text(tex)
        run = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                              '-output-directory', str(tmp), str(source)],
                             text=True, capture_output=True)
        if run.returncode:
            raise RuntimeError(run.stdout[-9000:] + run.stderr)
        pdf = tmp / (stem + '.pdf')
        shutil.copyfile(pdf, PAPER / pdf.name)
        svg = tmp / (stem + '.svg')
        subprocess.run(['pdftocairo', '-svg', str(pdf), str(svg)], check=True)
        contents = svg.read_text()
        where = contents.index('>', contents.index('<svg')) + 1
        contents = (contents[:where] + '\n<title>' + description + '</title>'
                    + '\n<desc>Rendered from the same verified rational coordinates as the paper PDF.</desc>'
                    + contents[where:])
        (SITE / ('tabachnikov-' + stem + '.svg')).write_text(contents)


def main():
    started = time.perf_counter()
    data = exact_example()
    built = time.perf_counter()
    report = verify(data)
    checked = time.perf_counter()
    render('circle', circle_figure(data),
           'One circle tangent inward to three consecutive supporting lines')
    render('construction', construction_figure(data),
           'Balanced tangential octagon and polygon with positively scaled edges')
    report['generator_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['environment'] = {'python': platform.python_version(),
                             'executable': sys.executable,
                             'optional_cas_venv_used': False,
                             'note': 'CAS resource launcher; standard-library exact rationals; no optional CAS backend.'}
    report['artifacts_sha256'] = {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for name in ('circle', 'construction')
        for p in (PAPER / ('side-tangent-' + name + '.tex'),
                  PAPER / ('side-tangent-' + name + '.pdf'),
                  SITE / ('tabachnikov-side-tangent-' + name + '.svg'))}
    (PAPER / 'side-tangent-data.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Exact construction {built-started:.4f}s; exact checking {checked-built:.4f}s; '
          f'vector rendering {time.perf_counter()-checked:.3f}s; solver: none.')
    print('All 8 circles, 24 contacts, strict supports and closure checked exactly.')


if __name__ == '__main__':
    main()
