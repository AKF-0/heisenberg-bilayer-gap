#!/usr/bin/env python3
"""Build the English manuscript with an existing TeX installation.

This script does not install packages or modify Lean sources. It requires
latexmk, pdflatex, BibTeX, and the packages declared in paper/preamble.tex.
"""
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
OUTPUT = ROOT / "output" / "pdf"
BUILD = ROOT / "build" / "paper"


def main() -> int:
    for tool in ("latexmk", "pdflatex", "bibtex"):
        if shutil.which(tool) is None:
            print(f"Missing required existing tool: {tool}", file=sys.stderr)
            return 2
    OUTPUT.mkdir(parents=True, exist_ok=True)
    BUILD.mkdir(parents=True, exist_ok=True)
    command = [
        "latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
        "-file-line-error", f"-outdir={BUILD}",
        "-jobname=heisenberg-bilayer-gap", "paper-en.tex",
    ]
    result = subprocess.run(command, cwd=PAPER, check=False)
    if result.returncode:
        return result.returncode
    pdf = BUILD / "heisenberg-bilayer-gap.pdf"
    if not pdf.is_file() or pdf.stat().st_size == 0:
        print("TeX returned success without the expected PDF.", file=sys.stderr)
        return 3
    destination = OUTPUT / pdf.name
    shutil.copy2(pdf, destination)
    print(destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
