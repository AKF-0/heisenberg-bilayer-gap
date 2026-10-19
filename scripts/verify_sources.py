#!/usr/bin/env python3
"""Verify source identity and import closure without invoking any Lean compiler."""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys
sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / 'lean'
ORIGIN_HASH = 'cbe4e29cf66b6a3a161e5ecac13b25c0c5465d32454966c1b2760c617844ae2b'
DRIVER_HASH = 'ee896d08d089510ca40ee87bd44c0c9c76b007dc26ea521b58f2ad11e81644db'

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())

def verify():
    origin_path = ROOT / 'verification/provenance/original-manifest.json'
    require(sha(origin_path) == ORIGIN_HASH, 'Original corrected manifest mismatch')
    origin = read(origin_path)
    manifest_path = FORMAL / 'MANIFEST.json'
    expected, filename = (FORMAL / 'MANIFEST.sha256').read_text().split()
    require(filename == 'MANIFEST.json' and sha(manifest_path) == expected,
            'Publication manifest digest mismatch')
    manifest = read(manifest_path)
    require(manifest['origin_manifest_sha256'] == ORIGIN_HASH, 'Wrong source origin')
    require(manifest['build_order'] == origin['build_order'], 'Module order or path changed')
    require(len(manifest['build_order']) == 556, 'Expected 556 modules')
    old = {entry['path']: entry for entry in origin['files']}
    new = {entry['path']: entry for entry in manifest['files']}
    require(len(new) == len(manifest['files']), 'Duplicate publication file')
    source_paths = {entry['path'] for entry in manifest['build_order']}
    require(source_paths == {str(p.relative_to(FORMAL)) for p in FORMAL.rglob('*.lean')},
            'Missing or unselected Lean source')
    for name, entry in new.items():
        path = (FORMAL / name).resolve()
        require(path.is_relative_to(FORMAL.resolve()) and path.is_file(), 'Invalid path: '+name)
        require(path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256'],
                'Publication file mismatch: '+name)
        require(name in old and entry == old[name], 'File differs from original snapshot: '+name)
    require(set(new) == source_paths | {'vendor/first_project_v2/PINNED_SHA256.txt', 'lean-toolchain',
                                      'reproduction/clean_build_cached.py', 'reproduction/test_clean_build_cached.py'},
            'Unexpected source-distribution manifest selection')
    driver_path = FORMAL / 'reproduction/clean_build_cached.py'
    require(sha(driver_path) == DRIVER_HASH, 'Unchanged fail-fast driver mismatch')
    spec = importlib.util.spec_from_file_location('driver', driver_path)
    driver = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(driver)
    modules = {entry['module']: entry['path'] for entry in manifest['build_order']}
    require(len(modules) == 556, 'Duplicate module')
    seen = set()
    for module, name in modules.items():
        for dependency in driver.imports(FORMAL / name):
            if dependency.startswith(('Dressed.', 'Gap.')):
                require(dependency in modules, 'Unclosed import: '+dependency)
                require(dependency in seen, 'Non-topological source order: '+dependency)
        seen.add(module)
    pins = FORMAL / 'vendor/first_project_v2/PINNED_SHA256.txt'
    require(sha(pins) == driver.VENDOR_MANIFEST, 'Pinned vendor manifest mismatch')
    lines = pins.read_text().splitlines()
    require(len(lines) == 46, 'Expected 46 pinned vendor sources')
    for line in lines:
        digest, name = line.split(maxsplit=1)
        require(sha(pins.parent / name.strip()) == digest, 'Vendor source mismatch: '+name)
    require(not list(ROOT.rglob('*.olean')), 'Project objects must not be distributed')
    receipt_path = ROOT / 'verification/build-receipt.json'
    require(sha(receipt_path) == 'a263b39d7de182a238a68afb6d81763cfe21c5d978b539f1369e5ed4eacb0eb1',
            'Successful build receipt digest mismatch')
    receipt = read(receipt_path)
    require(receipt['status'] == 'project_clean_build_and_all_declaration_audit_pass', 'Incomplete build')
    require(receipt['manifest_sha256'] == ORIGIN_HASH, 'Receipt binds another input')
    require(receipt['project_old_oleans_reused'] is False, 'Old project objects were reused')
    require(receipt['module_order'] == list(modules), 'Receipt module order mismatch')
    require(len(receipt['completed']) == 556, 'Incomplete receipt coverage')
    for entry, completed in zip(manifest['build_order'], receipt['completed']):
        require(entry['module'] == completed['module'] and
                new[entry['path']]['sha256'] == completed['source_sha256'],
                'Successful receipt source mismatch: ' + entry['path'])
    release = read(ROOT / 'verification/release.json')
    require(release['source_manifest_sha256'] == sha(manifest_path), 'Release source manifest mismatch')
    require(release['build_receipt_sha256'] == sha(receipt_path), 'Release build receipt mismatch')
    audit_path = ROOT / 'verification/audit-summary.json'
    require(release['audit_summary_sha256'] == sha(audit_path), 'Audit summary digest mismatch')
    audit = read(audit_path)
    require(audit['source_record_sha256'] == release['independent_review_sha256'] ==
            '8df0c0b5d26e29175ceb47c0c35890b48013047d915ea5bc29d7f38f929cb5c1', 'Review origin mismatch')
    require(audit['build_receipt_sha256'] == sha(receipt_path) and
            audit['original_manifest_sha256'] == ORIGIN_HASH and
            audit['audit_log_sha256'] == receipt['audit_log_sha256'], 'Audit provenance mismatch')
    require(audit['module_count'] == 556 and audit['constants_including_private_generated'] == 77040 and
            audit['theorem_constants'] == 50494, 'Audit coverage mismatch')
    require(set(audit['axiom_union']) == {'propext', 'Classical.choice', 'Quot.sound'}, 'Unexpected axiom union')
    require(sha(ROOT / 'verification/AllLocalDeclarationsAudit.lean') == receipt['audit_source_sha256'],
            'Audit source mismatch')
    require(len(audit['modules']) == 556, 'Audit module coverage mismatch')
    require(sum(e['origin_constants'] for e in audit['modules']) == 77040, 'Origin constant total mismatch')
    require(sum(e['origin_constants'] > 0 for e in audit['modules']) == 554, 'Declaring origin count mismatch')
    require({e['module'] for e in audit['modules'] if not e['origin_constants']} ==
            {'Dressed.CubicResidualSeedCoefficients', 'Dressed.CubicQuarticEnvelopeCertificates'},
            'Import-only module set mismatch')
    for entry, checked, completed in zip(manifest['build_order'], audit['modules'], receipt['completed']):
        require(entry['path'] == checked['source_path'] and
                entry['module'] == checked['module'] == completed['module'] and
                new[entry['path']]['sha256'] == checked['source_sha256'] == completed['source_sha256'] and
                checked['olean_sha256'] == completed['olean_sha256'], 'Review/receipt mismatch')
    closure = set()
    def visit(module):
        if module in closure: return
        closure.add(module)
        for dependency in driver.imports(FORMAL / modules[module]):
            if dependency in modules: visit(dependency)
    visit('Dressed.CubicPhysicalGap')
    require(len(closure) == 550, 'Final theorem transitive closure differs')
    require(release['theorem_closure_module_count'] == len(closure), 'Closure summary mismatch')
    print('SOURCE_IDENTITY_PASS: 556 exact sources; 550-module theorem closure; successful build receipt bound; no compiler invoked')
    return manifest, origin

if __name__ == '__main__':
    verify()
