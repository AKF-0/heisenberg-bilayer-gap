#!/usr/bin/env python3
"""Run the unchanged clean-project build driver on this source-only distribution."""
from pathlib import Path
import argparse
import subprocess
import sys
sys.dont_write_bytecode = True
from verify_sources import verify

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--mathlib', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--preflight-only', action='store_true')
    args = parser.parse_args()
    verify()
    root = Path(__file__).resolve().parents[1] / 'lean'
    digest = (root / 'MANIFEST.sha256').read_text().split()[0]
    command = [sys.executable, str(root / 'reproduction/clean_build_cached.py'),
               '--snapshot', str(root), '--manifest-sha256', digest,
               '--lean', str(args.lean.resolve()), '--mathlib', str(args.mathlib.resolve()),
               '--output', str(args.output.resolve())]
    if args.preflight_only:
        command.append('--preflight-only')
    return subprocess.call(command)

if __name__ == '__main__':
    raise SystemExit(main())
