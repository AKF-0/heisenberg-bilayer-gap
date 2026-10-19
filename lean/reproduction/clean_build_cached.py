#!/usr/bin/env python3
"""Cached-origin-audit successor to clean_build.py (same build safety gates).

Fail-fast clean PROJECT rebuild of a pinned, normalized source snapshot.

No downloads, dependency installation, project-cache reuse, or resume mode.
Mathlib and its package caches must already exist at their exact revisions.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone

LEAN_VERSION = "4.24.0"
LEAN_COMMIT = "797c613eb9b6d4ec95db23e3e00af9ac6657f24b"
MATHLIB_COMMIT = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
VENDOR_MANIFEST = "6ed3b7c48d412f7d7e3eb34299dce2033e1b1cf279a66421179f362a47242a5e"
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_read(args: list[str], cwd: Path | None = None) -> str:
    return subprocess.run(args, cwd=cwd, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.strip()


def inside(root: Path, relative: str) -> Path:
    p = (root / relative).resolve()
    require(p.is_relative_to(root), f"Path escapes snapshot: {relative}")
    require(p.is_file(), f"Missing file: {relative}")
    return p


def without_comments(text: str) -> str:
    """Preserve newlines and strings while removing nested Lean comments."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        c, pair = text[i], text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif quoted:
            out.append(c)
            i += 1
            if c == "\\" and i < len(text):
                out.append(text[i])
                i += 1
            elif c == '"':
                quoted = False
        elif pair == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(c)
            quoted = c == '"'
            i += 1
    require(depth == 0, "Unterminated Lean comment")
    return "".join(out)


def imports(path: Path) -> list[str]:
    """Snapshot headers use explicit one-line import declarations."""
    result = []
    for line in without_comments(path.read_text()).splitlines():
        line = line.strip()
        if not line or line == "prelude":
            continue
        if not line.startswith("import "):
            break
        names = line.removeprefix("import ").split()
        require(bool(names) and all(MODULE.fullmatch(n) for n in names),
                f"Unsupported import syntax in {path}: {line}")
        result.extend(names)
    return result


def checked_repository(path: Path, revision: str) -> None:
    require(run_read(["git", "-C", str(path), "rev-parse", "HEAD"]) == revision,
            f"Wrong repository revision: {path}")
    require(not run_read(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"]),
            f"Modified tracked dependency files: {path}")


def audit_source(modules: list[str], declaration_modules: list[str]) -> str:
    # Origin-module filtering includes private and generated constants, unlike a
    # namespace-only scan. Every imported local module is explicitly checked.
    header = "\n".join("import " + m for m in modules)
    names = ", ".join("`" + m for m in modules)
    declaring = ", ".join("`" + m for m in declaration_modules)
    return header + f"""
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let localModules : List Name := [{names}]
  let declaringModules : List Name := [{declaring}]
  for m in localModules do
    unless (env.getModuleIdx? m).isSome do
      throwError m!"Missing audited module: {{m}}"
  let mut selected : Array Bool := Array.replicate moduleNames.size false
  for m in localModules do
    if let some idx := env.getModuleIdx? m then
      unless idx.toNat < moduleNames.size do
        throwError m!"Invalid imported module index: {{m}}"
      selected := selected.set! idx.toNat true
  let mut counts : Array Nat := Array.replicate moduleNames.size 0
  let mut entries : List (Name × ConstantInfo) := []
  let mut thms := 0
  for (n, c) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      unless idx.toNat < moduleNames.size do
        throwError m!"Invalid constant origin index: {{n}}"
      if selected[idx.toNat]! then
        entries := (n, c) :: entries
        counts := counts.set! idx.toNat (counts[idx.toNat]! + 1)
        match c with
        | .thmInfo _ => thms := thms + 1
        | _ => pure ()
  let names := entries.reverse.map Prod.fst
  if names.isEmpty then
    throwError "Empty local constant audit"
  for m in localModules do
    let some idx := env.getModuleIdx? m
      | throwError m!"Missing audited module during final count: {{m}}"
    let count := counts[idx.toNat]!
    liftIO <| IO.println s!"AUDIT_MODULE={{m}} CONSTANTS={{count}}"
    if declaringModules.contains m && count == 0 then
      throwError m!"No origin constants found for declaring module: {{m}}"
  liftIO <| IO.println s!"LOCAL_CONSTANT_COUNT={{names.length}}"
  liftIO <| IO.println s!"LOCAL_THEOREM_COUNT={{thms}}"
  for n in names do
    liftIO <| IO.println s!"AUDIT_CONSTANT={{n}}"
  let (_, state) := ((names.forM Lean.CollectAxioms.collect).run env).run {{}}
  liftIO <| IO.println s!"AXIOM_UNION={{state.axioms.toList}}"
  for a in state.axioms do
    unless ([`propext, `Classical.choice, `Quot.sound] : List Name).contains a do
      throwError m!"Unapproved axiom: {{a}}"
  liftIO <| IO.println "ALL_LOCAL_DECLARATIONS_STANDARD_AXIOMS_PASS"
"""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", type=Path, required=True)
    parser.add_argument("--manifest", default="MANIFEST.json")
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True,
                        help="Must not exist, even as an empty directory")
    parser.add_argument("--preflight-only", action="store_true")
    args = parser.parse_args()
    root, lean, mathlib, output = (p.resolve() for p in
                                 (args.snapshot, args.lean, args.mathlib, args.output))
    require(not output.exists(), "Output already exists; refusing cache reuse or deletion")
    require(not output.is_relative_to(root), "Output may not be inside the immutable snapshot")
    require(not output.is_relative_to(mathlib), "Output may not be inside mathlib")
    require(not output.is_relative_to(lean.parent.parent), "Output may not be inside the Lean toolchain")
    manifest_path = inside(root, args.manifest)
    require(sha(manifest_path) == args.manifest_sha256.lower(), "Snapshot manifest hash mismatch")
    manifest = json.loads(manifest_path.read_text())
    require(manifest["lean"] == LEAN_VERSION, "Snapshot Lean version mismatch")
    require(manifest["mathlib_commit"] == MATHLIB_COMMIT, "Snapshot mathlib pin mismatch")
    files = {f["path"]: f for f in manifest["files"]}
    require(len(files) == len(manifest["files"]), "Duplicate manifest file path")
    for name, data in files.items():
        path = inside(root, name)
        require(sha(path) == data["sha256"], f"Snapshot source/evidence hash mismatch: {name}")
        require(path.stat().st_size == data["bytes"], f"Snapshot byte count mismatch: {name}")
    vendor = root / "vendor/first_project_v2"
    require(sha(vendor / "PINNED_SHA256.txt") == VENDOR_MANIFEST, "First-project v2 manifest mismatch")
    pins = (vendor / "PINNED_SHA256.txt").read_text().splitlines()
    require(len(pins) == 46, "Expected all 46 first-project v2 files")
    for line in pins:
        expected, name = line.split(maxsplit=1)
        require(sha(inside(vendor, name.strip())) == expected, f"Vendor source mismatch: {name}")

    entries = manifest["build_order"]
    sources = {e["module"]: e["path"] for e in entries}
    require(len(sources) == len(entries), "Duplicate local module")
    require(all(MODULE.fullmatch(m) for m in sources), "Invalid local module name")
    require(all(p in files for p in sources.values()), "Build source absent from file manifest")
    deps = {m: imports(inside(root, p)) for m, p in sources.items()}
    for m, ds in deps.items():
        for d in ds:
            require(not d.startswith(("Dressed.", "Gap.")) or d in sources,
                    f"Unclosed project import: {m} imports {d}")
    order, active, complete = [], set(), set()
    def visit(m: str) -> None:
        require(m not in active, f"Local import cycle at {m}")
        if m in complete:
            return
        active.add(m)
        for d in deps[m]:
            if d in sources:
                visit(d)
        active.remove(m)
        complete.add(m)
        order.append(m)
    for m in sources:
        visit(m)

    require(run_read([str(lean), "--short-version"]) == LEAN_VERSION, "Lean version mismatch")
    require(run_read([str(lean), "--githash"]) == LEAN_COMMIT, "Lean compiler commit mismatch")
    checked_repository(mathlib, MATHLIB_COMMIT)
    library_paths = [mathlib / ".lake/build/lib/lean"]
    packages = json.loads((mathlib / "lake-manifest.json").read_text())
    package_pins = []
    for package in packages["packages"]:
        require(package["type"] == "git", "Only pinned git dependency packages are supported")
        directory = mathlib / packages["packagesDir"] / package["name"]
        checked_repository(directory, package["rev"])
        cache = directory / ".lake/build/lib/lean"
        # Some pinned packages are build-tool-only dependencies. Their absent
        # library cache is harmless unless an actual source import needs it.
        if cache.is_dir():
            library_paths.append(cache)
        package_pins.append({"name": package["name"], "revision": package["rev"],
                             "library_cache_present": cache.is_dir()})
    require(library_paths[0].is_dir(), "The prebuilt mathlib cache is missing")
    for ds in deps.values():
        for d in ds:
            if d not in sources and not d.startswith(("Init", "Lean")):
                rel = Path(*d.split(".")).with_suffix(".olean")
                require(any((p / rel).is_file() for p in library_paths), f"Missing dependency olean: {d}")
    print(f"PREFLIGHT_PASS files={len(files)} modules={len(order)}; no project compiler invoked", flush=True)
    if args.preflight_only:
        return

    output.mkdir(parents=True, exist_ok=False)
    lib, logs = output / "lib/lean", output / "logs"
    lib.mkdir(parents=True)
    logs.mkdir()
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN_SETUP"):
        env.pop(key, None)
    env["LEAN_PATH"] = os.pathsep.join(map(str, [lib] + library_paths))
    receipt = {"status": "building", "started_utc": datetime.now(timezone.utc).isoformat(),
               "driver_sha256": sha(Path(__file__).resolve()), "python_version": sys.version,
               "manifest_sha256": args.manifest_sha256.lower(), "lean_commit": LEAN_COMMIT,
               "mathlib_commit": MATHLIB_COMMIT, "dependency_packages": package_pins,
               "project_old_oleans_reused": False, "dependencies_rebuilt": False,
               "module_order": order, "completed": []}
    receipt_path = output / "BUILD_RECEIPT.json"
    def save() -> None:
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    save()
    try:
        for m in order:
            source = inside(root, sources[m])
            require(sha(source) == files[sources[m]]["sha256"], f"Source changed during build: {m}")
            rel = Path(*m.split(".")).with_suffix(".lean")
            require(str(source).endswith(str(rel)), f"Source path does not match module: {m}")
            source_root = source
            for _ in rel.parts:
                source_root = source_root.parent
            target = (lib / Path(*m.split("."))).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            print(f"BUILD {m}", flush=True)
            with (logs / (m + ".log")).open("w") as log:
                subprocess.run([str(lean), "--root=" + str(source_root), "-o", str(target), str(source)],
                               cwd=source_root, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
            require(sha(source) == files[sources[m]]["sha256"], f"Source changed while compiling: {m}")
            receipt["completed"].append({"module": m, "source_sha256": sha(source),
                                         "olean_sha256": sha(target)})
            save()
        declaration_modules = [m for m in order if re.search(
            r"\b(?:def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|axiom)\s",
            without_comments(inside(root, sources[m]).read_text()))]
        audit = output / "AllLocalDeclarationsAudit.lean"
        audit.write_text(audit_source(order, declaration_modules))
        with (logs / "ALL_LOCAL_DECLARATIONS_AUDIT.log").open("w") as log:
            subprocess.run([str(lean), "--root=" + str(output), str(audit)], cwd=output, env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        for m in order:
            require(sha(inside(root, sources[m])) == files[sources[m]]["sha256"],
                    f"Compiled source changed before final verification: {m}")
        receipt["status"] = "project_clean_build_and_all_declaration_audit_pass"
        receipt["audit_source_sha256"] = sha(audit)
        receipt["audit_log_sha256"] = sha(logs / "ALL_LOCAL_DECLARATIONS_AUDIT.log")
    except BaseException:
        receipt["status"] = "failed_or_interrupted_not_a_complete_build"
        raise
    finally:
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
    print("PROJECT_CLEAN_BUILD_AND_ALL_DECLARATION_AUDIT_PASS", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError, OSError, KeyError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
