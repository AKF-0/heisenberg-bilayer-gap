# Mathematical sources and attribution

The manuscript distinguishes the general purity method, model-specific finite certificates, and classical weak-coupling context. These sources are mathematical references, not external certifications of this project.

## Spatial moments and purity propagation

**OpenAI, _The periodic spin-one Haldane gap_**, manuscript dated September 24, 2026.

- [Pinned manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-periodic-spin-one-Haldane-gap-September-24-2026/paper.pdf)
- [Pinned source directory](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-periodic-spin-one-Haldane-gap-September-24-2026)
- Relevant locations: Proposition 3.1; Lemmas 4.1–4.2; Proposition 4.3; finite initializations in Section 5.

The real spatial-moment representation and purity-squaring strategy provide the methodological starting point. The bilayer proof constructs its own finite spatial-transfer approximants, three-coordinate propagation, all-even-size interpolation, and physical seed. It does not assume the one-dimensional gap theorem or import its numerical seed. The pinned revision is `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Product-state stability context

**D. A. Yarotsky, _Quasi-particles in weak perturbations of non-interacting quantum lattice systems_** (2004).

- [Primary arXiv record](https://arxiv.org/abs/math-ph/0411042)
- [Primary PDF](https://arxiv.org/pdf/math-ph/0411042)
- Relevant location: Theorem 1, PDF page 3.

The theorem supplies uniform weak-perturbation stability in a general product-state setting. Its existential smallness constants are not, by themselves, a numerical certification of the interval `0 ≤ g ≤ 1/10` in the normalization used here.

**S. Del Vecchio, J. Fröhlich, A. Pizzo and S. Rossi, _Local iterative block-diagonalization of gapped Hamiltonians: a new tool in singular perturbation theory_**, Journal of Mathematical Physics **63**, 073503 (2022).

- [Primary arXiv record](https://arxiv.org/abs/2007.07667)
- [Primary PDF, version 2](https://arxiv.org/pdf/2007.07667v2)
- [Published article](https://doi.org/10.1063/5.0084552)
- Relevant location: Theorem 5.3, arXiv version 2, PDF page 41.

This higher-dimensional block-diagonalization result gives a volume-independent small-coupling interval and a positive gap under its hypotheses. The cited theorem is contextual; the project does not derive its explicit bilayer interval merely by quoting that theorem.

## Scope of the comparison

The cited statements and theorem locations were checked in their primary manuscripts. This is a targeted comparison, not an exhaustive priority survey. No claim of a best-known threshold, a new general nonperturbative phase theorem, or external peer review follows from the formal verification.

The earlier narrower certificates in the vendored `first_project_v2` directory concern the same bilayer Hamiltonian. The directory name is retained for source compatibility and does not designate a different physical model. Current model-specific certificates are in `lean/Dressed/`.

BibTeX entries are in [paper/references.bib](paper/references.bib).
