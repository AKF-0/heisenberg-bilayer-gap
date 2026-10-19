# Heisenberg Bilayer Spectral Gap

A mathematical derivation and Lean 4 proof for the spin-1/2 Heisenberg model on two coupled periodic square lattices.

## Result

With the interlayer coupling set to 1, the proof covers intralayer coupling from 0 to 0.1 and every even lattice side length of at least 256.

The finite system has a unique ground state. Its spectral gap is greater than `log(200/13) / 1024`, approximately 0.0026693. Here `log` is the natural logarithm.

## Read the project

- [Paper (PDF)](output/pdf/heisenberg-bilayer-gap.pdf)
- [Paper source](paper/paper-en.tex)
- [Lean theorem](lean/Dressed/CubicPhysicalGap.lean)
- [Proof map](docs/proof-map.md)
- [Verification and scope](VERIFICATION.md)
- [Reproduction instructions](docs/reproducibility.md)
- [References](CITATIONS.md)

Detailed formulas and derivations are in the paper. The result concerns finite periodic systems; it does not assert uniqueness of an infinite-volume ground state.
