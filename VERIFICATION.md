# Verification scope

## Accepted source and build

The distribution contains 556 local Lean source files: 510 `Dressed` modules and 46 pinned `Gap` support modules. Every source byte matches the input to the successful clean build completed on 19 October 2026. The final theorem's transitive local import closure contains 550 modules; the other six are retained support modules, not additional theorem assumptions.

The [build receipt](verification/build-receipt.json) records compilation of all 556 modules into a previously nonexistent output directory. No historical project `.olean` was reused. The [source checker](scripts/verify_sources.py) verifies every selected source against both the original input manifest and the successful receipt, and verifies the normalized review's source/object correspondence.

The distribution manifest is derived for this repository layout. It is **not** the identical manifest used by the historical build: non-build historical material has been omitted. The mapping is exact: an original source path `p` is distributed at `lean/p`; the internal module names and complete build order are unchanged. See [source provenance](docs/source-provenance.md).

## Declaration audit

The [audit program](verification/AllLocalDeclarationsAudit.lean) selects constants by their declaring module, including private and generated declarations. Its recorded result covers:

- 556 imported local modules;
- 554 modules with declaring origins and two import-only modules;
- 77,040 constants, including 50,494 theorem constants;
- the axiom union `propext`, `Classical.choice`, and `Quot.sound` only.

The two import-only modules are `Dressed.CubicResidualSeedCoefficients` and `Dressed.CubicQuarticEnvelopeCertificates`. The [compact terminal result](verification/audit-result.txt) and [normalized audit summary](verification/audit-summary.json) identify the full audit log by SHA-256. The rebuild command regenerates that log. The [headline check](verification/headline-checks.txt) records the final theorem type and its axiom list.

A separate mechanical review rechecked all 556 source/object/log pairs, the exact object-file set, the topological build order, dependency revisions, and the generated audit source. Its normalized results are included; this is not external human mathematical peer review.

## Trusted inputs and limitations

The accepted run used Lean 4.24.0 at commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b` and mathlib at commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, with the exact package revisions in [the dependency lock file](verification/dependencies.lock.json). The pinned Lean executable, mathlib/package compiled caches, operating system, hardware, Python build driver, and cryptographic hash implementations remain trusted inputs. This is a clean **project** rebuild, not a bootstrap of Lean or all upstream dependencies, an independent kernel implementation, or a verified build system.

Lean acceptance establishes the formal propositions under this trust boundary. The identification of those definitions with the intended physical Hamiltonian should be read alongside the [mathematical manuscript](output/pdf/heisenberg-bilayer-gap.pdf) and [proof map](docs/proof-map.md). No infinite-volume uniqueness, phase-boundary determination, near-critical estimate, numerical optimality, or novelty claim follows from the audit counts.
