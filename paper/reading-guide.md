# Reading the derivation

[Read the mathematical manuscript](../output/pdf/heisenberg-bilayer-gap.pdf) · [LaTeX entrypoint](paper-en.tex) · [Proof-to-Lean map](../docs/proof-map.md) · [Mathematical sources](../CITATIONS.md)

## Result

For the standard spin-1/2 square-lattice bilayer, with rung coupling one and intralayer coupling `0 ≤ g ≤ 1/10`, every even periodic square of side `L ≥ 256` has a unique ground state and spectral gap strictly greater than `log(200/13)/1024`.

The Hamiltonian includes the gap-invariant constant `3/4` per rung. Eigenvalues are counted with multiplicities. This is a finite-volume uniform statement, not a claim about uniqueness of an infinite-volume GNS ground state or the entire dimer phase.

## Suggested route

1. **Sections 1–3:** the precise model, exact Pauli-to-rung basis maps, finite occupation embedding, and an elementary finite Jacobi comparison. All reference spaces are finite-dimensional.
2. **Sections 4–6:** the explicit cubic trial kernel, its complete signed residual of creation degrees 0, 2, 4 and 6, and the finite graph certificates. The four-site matching coefficients are collected with their signs before taking absolute values.
3. **Section 7:** the actual Rayleigh/Temple energy bounds and the three physical seed ratios on the `4×4`, `8×4` and `8×8` rung tori.
4. **Sections 8–10:** real symmetric spatial-transfer approximants, legitimate even-power probability moments, six ordered unequal-error updates, and interpolation to every even `L ≥ 256`.
5. **Appendices:** further exact constants, a compact formal correspondence, and the source/reproduction trust boundary.

The paper states the inequalities that make the finite certificates sufficient. Large integer coefficient arrays are machine-readable appendices in the Lean source, not numerically assumed inputs. The [proof map](../docs/proof-map.md) identifies their actual graph-membership, interval-bound and aggregate checks separately.

## Build the PDF

From the repository root, with an existing TeX installation:

```sh
python3 scripts/build_paper.py
```

The script invokes `latexmk`, `pdflatex` and BibTeX and writes `output/pdf/heisenberg-bilayer-gap.pdf`. It neither installs software nor runs Lean. Formal reproduction is documented separately in [VERIFICATION.md](../VERIFICATION.md).
