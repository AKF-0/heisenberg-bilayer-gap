# Reproducing the formal result

All commands below are run from the repository root. Python 3 and its standard library are sufficient for static source verification. A full rebuild additionally requires the pinned Lean executable and an already prepared mathlib checkout, including its compiled package caches. The scripts do not download or install dependencies.

## 1. Check the distribution

```sh
python3 scripts/verify_sources.py
python3 -B lean/reproduction/test_clean_build_cached.py
```

The first command verifies source bytes, the original input manifest, the complete 556-module import order, all 46 vendored support sources, the 550-module final-theorem closure, and the binding to the successful build receipt. It does not invoke Lean. The second command runs the build driver's non-compiling safety tests.

## 2. Prepare the pinned upstream dependencies

Required versions:

- Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
- mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`;
- package revisions specified in [dependencies.lock.json](../verification/dependencies.lock.json), matching mathlib's `lake-manifest.json`.

Use the official [Lean releases](https://github.com/leanprover/lean4/releases/tag/v4.24.0) and [mathlib repository](https://github.com/leanprover-community/mathlib4/tree/f897ebcf72cd16f89ab4577d0c826cd14afaafc7). Prepare the dependency caches according to mathlib's own instructions. The driver checks repository revisions, tracked-file cleanliness, compiler identity, cache availability, import closure, and absence of selected project objects in the dependency caches. It fails rather than substituting an unpinned dependency.

The repository does not vendor upstream compiler or mathlib sources. The `lean/vendor/first_project_v2/` directory contains only the pinned local support library used by this proof. Its historical directory name and module names are retained to preserve the successful build inputs exactly.

## 3. Preflight

Choose an absolute output path that does not yet exist:

```sh
python3 scripts/reproduce.py \
  --lean /absolute/path/to/lean \
  --mathlib /absolute/path/to/mathlib \
  --output /absolute/path/to/new-build \
  --preflight-only
```

Preflight reads the selected compiler's version and dependency metadata but does not compile any Lean source or create the output directory. A successful preflight is not a successful rebuild.

## 4. Clean build and audit

Repeat the same command without `--preflight-only`:

```sh
python3 scripts/reproduce.py \
  --lean /absolute/path/to/lean \
  --mathlib /absolute/path/to/mathlib \
  --output /absolute/path/to/new-build
```

The unchanged build driver compiles all 556 modules in the frozen topological order, generating fresh project objects and per-module logs. It then compiles and runs an origin-based all-declaration axiom audit. `BUILD_RECEIPT.json` in the new output directory records the terminal status and source/object hashes. A failed or interrupted run is not accepted, and the driver has no resume or old-project-cache fallback mode. Use another nonexistent output path for a subsequent clean attempt.

This is computationally substantial and is intentionally not an automatic push workflow. The recorded successful run took approximately three hours on its original machine; runtime and resource needs may differ elsewhere. Reproduction on a different machine is not claimed merely from the recorded run.

## Source distribution versus historical build input

`lean/MANIFEST.json` lists only files required for this source distribution and build driver. The original successful input manifest is retained in [verification/provenance/original-manifest.json](../verification/provenance/original-manifest.json). Its additional historical files are not required by this derived distribution and are deliberately not shipped. Source entries and the complete build order are unchanged. The new run records the derived manifest hash; the historical successful receipt remains bound to the original manifest hash.
