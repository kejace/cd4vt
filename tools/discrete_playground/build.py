#!/usr/bin/env python3
"""Build the same numerical kernel for the browser or native validation."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'tools/discrete_playground/solver.c'
OUT = ROOT / 'site/discrete-playground'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--native', type=Path, help='Build a native shared object at this path instead.')
args = parser.parse_args()
if args.native:
    subprocess.run(['cc', '-O3', '-std=c99', '-Wall', '-Wextra', '-Werror', '-fPIC', '-shared', str(SOURCE), '-lm', '-o', str(args.native)], check=True)
else:
    OUT.mkdir(exist_ok=True)
    flags = ['-O3', '-std=c99', '-Wall', '-Wextra', '-Werror', '-sMODULARIZE=1', '-sEXPORT_ES6=1', '-sENVIRONMENT=web,worker', '-sFILESYSTEM=0', '-sASSERTIONS=0', "-sEXPORTED_FUNCTIONS=['_solve','_input_buffer','_output_buffer','_evaluate']"]
    subprocess.run(['emcc', str(SOURCE), *flags, '-o', str(OUT/'solver.mjs')], check=True)
    module = OUT / 'solver.mjs'
    module.write_text('\n'.join(line.rstrip() for line in module.read_text().splitlines()) + '\n')
    (OUT / 'solver.wasm').chmod(0o644)
    metadata = {'compiler': subprocess.check_output(['emcc','--version'], text=True).splitlines()[0], 'flags': flags, 'source':'tools/discrete_playground/solver.c', 'sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(), 'artifacts': {name:hashlib.sha256((OUT/name).read_bytes()).hexdigest() for name in ['solver.mjs','solver.wasm']}}
    (OUT/'build.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print('Built solver.mjs and solver.wasm from the checked numerical source.')
