# Source provenance and reproducibility correction

## Accepted source identity

The original corrected input manifest has SHA-256

`cbe4e29cf66b6a3a161e5ecac13b25c0c5465d32454966c1b2760c617844ae2b`.

The successful terminal build receipt has SHA-256

`a263b39d7de182a238a68afb6d81763cfe21c5d978b539f1369e5ed4eacb0eb1`.

Both original files are retained without modification in [the provenance manifest](../verification/provenance/original-manifest.json) and [build receipt](../verification/build-receipt.json). The original manifest was frozen before compilation and therefore contains historical pending-status fields; the terminal receipt, not those historical fields, records the outcome.

Every selected Lean source is copied byte-for-byte from that input. The source-only manifest [lean/MANIFEST.json](../lean/MANIFEST.json) explicitly derives from it, retaining all 556 module paths, hashes, and build order. The only prefix change is from an original path `p` to repository path `lean/p`. No proof source was reformatted or edited during repository reorganization. The checked source distribution also agrees byte-for-byte with the independently checked complete archival package, SHA-256 `ad195354bbe31819941e854d23ce54c4d099a87bbaa8ef1e8b03a1fe70abe463`.

## Correction to earlier reproduction evidence

An earlier fresh-build attempt stopped after 158 of 556 modules because `MeanTrialCertificate.lean` placed a documentation comment before `omit ... in`, where Lean rejected it. An earlier incremental check had retained an old compiled object after that failed source compilation; it therefore did not establish a source-to-object correspondence for the edited file. The source provenance of two generated files, `Dressed.QuarticIntegerMembership16.Dictionary` and `Dressed.CubicQuarticEnvelopes.Batch00`, also required a fresh reconstruction rather than reliance on pre-existing objects.

The corrected input moved the unchanged documentation comment inside the `omit` block without changing the non-comment token stream. The complete 556-module project was then rebuilt into a new output directory, and all source/object pairs and the origin-based audit were rechecked. The successful receipt above supersedes the incomplete reproduction evidence; it does not retroactively validate the failed attempt.

For historical identification, the failed receipt has SHA-256 `14c2ff65f2ceb7e17d9bff4d228adc93ba3025bfb35cde9727270458b8646076`. The original correction note has SHA-256 `10fc1f26ac231fc0ec2bc58db875ac8a5f6dca37cc7987fd4b55b05356d6185b`. The separate terminal review has SHA-256 `8df0c0b5d26e29175ceb47c0c35890b48013047d915ea5bc29d7f38f929cb5c1`; [audit-summary.json](../verification/audit-summary.json) is a normalized extraction, not that original byte stream.

## Preserved scope

The historical weak-coupling and enlarged-interval material concerns two proof stages of the same two-dimensional bilayer model. The current repository presents the enlarged-interval theorem coherently; earlier repository contents remain accessible through ordinary Git parent history.
