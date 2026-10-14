#!/usr/bin/env python3
"""Build the two-panel illustration of Definition 3.1.

Uses only the Python standard library and pdflatex. Coordinates follow the
paper's development equations; the highlighted circumcircle is independently
checked before rendering. The picture is an illustration, not a proof.

Run with the shared CAS resource launcher, as for side_tangent_figures.py:
    CAS_VENV=/tmp/gluck-figure-cas CAS_WORKERS=1 \
      ../gluck-physical/tools/cas/run python \
      tools/discrete_playground/development_figure.py

The fallback environment above only points at the system Python; use the
installed /opt/cas-venv without CAS_VENV when available.
"""
import os
import shutil
import subprocess
from tempfile import TemporaryDirectory

from math import asin, sin, cos, pi
from pathlib import Path

root=Path(__file__).resolve().parents[2]
k=[.85,1.1,.8,1.25,.9,1.15]
h=[.4,.38,.45,.36,.43,.34]
n=len(k)
t=[asin(k[i]*h[i-1])+asin(k[i]*h[i]) for i in range(n)]
heads=[];p=[0j];angle=0
for j in range(n):
    angle+=t[j];heads.append(angle)
    p.append(p[-1]+2*h[j]*complex(cos(angle),sin(angle)))
assert all(0<k[j]*h[j-1]<1 and 0<k[j]*h[j]<1 for j in range(n))
# Check the selected triple independently using its circumcircle.
i=3
X,Y=asin(k[i]*h[i-1]),asin(k[i]*h[i])
tangent=heads[i-1]+X
center=p[i]+complex(-sin(tangent),cos(tangent))/k[i]
assert max(abs(abs(p[j]-center)-1/k[i]) for j in (i-1,i,i+1))<1e-12
assert abs(heads[-1]-sum(t))<1e-12
assert abs(p[-1])>.2 and abs(sum(t)-2*pi)>.2

def pt(z):return f'({z.real:.9f},{z.imag:.9f})'
def arrow(a,b,color='ink',width='1.0pt'):
    u=a+.43*(b-a);v=a+.61*(b-a)
    return rf'\draw[{color},line width={width}] {pt(a)}--{pt(b)};'+ '\n'+rf'\draw[{color},line width={width},-{{Stealth[length=3.2pt,width=3.1pt]}}] {pt(u)}--{pt(v)};'

s=[r'''% Definition 3.1: one figure with local and global views.
% The right panel is the defining development for
% kappa=(.85,1.1,.8,1.25,.9,1.15), h=(.4,.38,.45,.36,.43,.34).
% The left panel magnifies its triple P_2,P_3,P_4 (i=3) and rotates its
% positively oriented circle tangent to horizontal. No closure is imposed.
% Compile: pdflatex -output-directory=<scratch> development.tex
\documentclass[border=2pt]{standalone}
\usepackage{amsmath,amssymb,tikz}
\usetikzlibrary{arrows.meta,calc}
\pdfinfoomitdate=1
\pdftrailerid{}
\definecolor{ink}{HTML}{242E2C}
\definecolor{teal}{HTML}{386F79}
\definecolor{gold}{HTML}{A76C27}
\definecolor{berry}{HTML}{99606C}
\definecolor{quiet}{HTML}{9AA3A1}
\begin{document}
\begin{tikzpicture}[x=1cm,y=1cm,font=\small,text=ink,
    labelbg/.style={fill=white,inner sep=1.5pt}]
\path[use as bounding box] (0,0) rectangle (15.8,6.05);
\node[anchor=west] at (.1,5.8) {(a) The turn at one vertex};
\node[anchor=west] at (8.2,5.8) {(b) The developed edges};
\draw[quiet!35,line width=.4pt] (7.75,.05)--(7.75,5.45);
''']
# Left panel: the same local triple, rotated and enlarged.
B=complex(2.9,1.9);R=1.4;O=B+R*1j
A=O+R*complex(-sin(2*X),-cos(2*X))
C=O+R*complex(sin(2*Y),-cos(2*Y))
s += [rf'\coordinate (A) at {pt(A)};\coordinate (B) at {pt(B)};\coordinate (C) at {pt(C)};\coordinate (O) at {pt(O)};',
rf'\draw[quiet!70,line width=.65pt] (O) circle[radius={R}];',
rf'\draw[quiet,line width=.6pt,densely dashed,-{{Stealth[length=3pt]}}] {pt(B-.35)}--{pt(B+2.95)};',
rf'\draw[quiet,line width=.6pt,densely dashed] (B)--{pt(B+1.62*complex(cos(X),-sin(X)))};',
rf'\draw[quiet,line width=.6pt] (B)--(O);',
rf'\draw[quiet,line width=.5pt] {pt(B+.12j)}--{pt(B+.12+.12j)}--{pt(B+.12)};',
arrow(A,B,'gold','1.35pt'),arrow(B,C,'teal','1.35pt'),
rf'\draw[gold,line width=.8pt,-{{Stealth[length=2.3pt]}}] {pt(B+.64*complex(cos(X),-sin(X)))} arc[start angle={-X*180/pi:.9f},end angle=0,radius=.64];',
rf'\draw[teal,line width=.8pt,-{{Stealth[length=2.3pt]}}] {pt(B+.64)} arc[start angle=0,end angle={Y*180/pi:.9f},radius=.64];',
rf'\draw[ink,line width=.55pt,-{{Stealth[length=2.3pt]}}] {pt(B+1.10*complex(cos(X),-sin(X)))} arc[start angle={-X*180/pi:.9f},end angle={Y*180/pi:.9f},radius=1.10];',
r'\foreach \v in {A,B,C} \fill[ink] (\v) circle[radius=1.5pt];',
r'\fill[quiet] (O) circle[radius=1.3pt];',
r'\node[left=3pt] at (A) {$P_{i-1}$};',
r'\node[below left=3pt] at (B) {$P_i$};',
r'\node[right=4pt] at (C) {$P_{i+1}$};',
r'\node[above right=2pt] at (O) {$O_i$};',
r'\node[labelbg,anchor=east] at (2.77,3.03) {$1/\kappa_i$};',
r'\node[text=gold] at (2.05,2.10) {$2h_{i-1}$};',
r'\node[text=teal] at (3.48,2.61) {$2h_i$};',
r'\node[text=gold,labelbg] at (3.67,1.64) {$X$};',
r'\node[text=teal,labelbg] at (3.69,2.10) {$Y$};',
r'\node[labelbg] at (4.23,1.46) {$\theta_i$};',
r'\node[anchor=west,font=\footnotesize] at (5.02,2.12) {tangent at $P_i$};',
r'\node at (3.8,.78) {$\theta_i=X+Y$};',
r'\node[font=\footnotesize] at (3.8,.22) {$X=\arcsin(\kappa_i h_{i-1}),\qquad Y=\arcsin(\kappa_i h_i)$};']
# Right panel: translate and uniformly scale; keep the definition's angle zero.
q=[complex(12.0,1.60)+1.75*z for z in p]
for j,z in enumerate(q):s.append(rf'\coordinate (p{j}) at {pt(z)};')
for j in range(n):s.append(arrow(q[j],q[j+1], 'gold' if j==2 else 'teal' if j==3 else 'ink', '1.35pt' if j in (2,3) else '1.0pt'))
s += [rf'\draw[quiet,line width=.55pt,densely dashed,-{{Stealth[length=3pt]}}] {pt(q[0]-.60)}--{pt(q[0]+1.52)};',
rf'\draw[ink,line width=.7pt,-{{Stealth[length=2.3pt]}}] {pt(q[0]+.58)} arc[start angle=0,end angle={heads[0]*180/pi:.9f},radius=.58];',
r'\node[anchor=west,font=\footnotesize] at (13.59,1.60) {$\operatorname{Re}$};',
r'\node[labelbg] at (13.55,1.98) {$\psi_0=\theta_0$};',
rf'\draw[berry,line width=1.1pt,-{{Stealth[length=4pt,width=4pt]}}] (p0)--(p6);',
r'\node[text=berry,labelbg,align=center] at (10.98,1.64) {$\mathcal G=P_6$};',
r'\node[labelbg] at (13.65,3.10) {$2h_1$};',
# A representative exterior turn at P3, matching the left panel.
rf'\draw[quiet,line width=.5pt,densely dashed] (p3)--{pt(q[3]+.68*complex(cos(heads[2]),sin(heads[2])))};',
rf'\draw[ink,line width=.65pt,-{{Stealth[length=2.3pt]}}] {pt(q[3]+.38*complex(cos(heads[2]),sin(heads[2])))} arc[start angle={heads[2]*180/pi:.9f},end angle={heads[3]*180/pi:.9f},radius=.38];',
r'\node[labelbg] at (11.67,5.23) {$\theta_3$};',
r'\foreach \j in {0,...,5} \fill[ink] (p\j) circle[radius=1.4pt];',
r'\draw[berry,fill=white,line width=.9pt] (p6) circle[radius=2pt];',
r'\node[below right=3pt] at (p0) {$P_0=0$};',
r'\node[right=3pt] at (p1) {$P_1$};',
r'\node[right=3pt] at (p2) {$P_2$};',
r'\node[above right=3pt] at (p3) {$P_3$};',
r'\node[left=3pt] at (p4) {$P_4$};',
r'\node[left=3pt] at (p5) {$P_5$};',
r'\node[left=4pt,text=berry] at (p6) {$P_6$};',
r'\node at (11.95,.78) {$\psi_j=\sum_{m=0}^{j}\theta_m$};',
r'\node[font=\footnotesize] at (11.95,.22) {$\mathcal T=\sum_{i=0}^{5}\theta_i=\psi_5\simeq 4.915\ne 2\pi$};',
r'\end{tikzpicture}',r'\end{document}']
(root/'paper/tabachnikov/figures/development.tex').write_text('\n'.join(s)+'\n')
print('Wrote source; checked moderate bounds and highlighted circumcircle.')
print('Total turn:',sum(t),'gap:',p[-1])

figure_dir=root/'paper/tabachnikov/figures'
with TemporaryDirectory(prefix='gluck-development-figure-') as scratch:
    env=dict(os.environ, SOURCE_DATE_EPOCH='0', FORCE_SOURCE_DATE='1')
    result=subprocess.run(
        ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
         f'-output-directory={scratch}', str(figure_dir/'development.tex')],
        env=env, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(result.stdout[-6000:]+'\n'+result.stderr)
    log=(Path(scratch)/'development.log').read_text()
    if any(marker in log for marker in ('Overfull', 'Missing character')):
        raise RuntimeError('Figure layout warning: '+log)
    shutil.copyfile(Path(scratch)/'development.pdf', figure_dir/'development.pdf')
print('Wrote', figure_dir/'development.pdf')
