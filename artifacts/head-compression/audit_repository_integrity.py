#!/usr/bin/env python3
"""Check the saved research inventory and immutable proof/certificate links.

This checks packaging and recorded validation, not the universal conjecture.
It does not replace the exact certificate verifiers or Lean's kernel.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'artifacts/head-compression'
BASELINE = 'f4781edee561d9a1d1d020cea43d4f81058f4a24'
SOURCE_SHA = '392541fa481bca85bb658c414e5cba202eaef03206e1b2c29fd906db916a2db2'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    inventory = json.loads((BASE / 'audit-inventory.json').read_text())
    results = inventory['lean_results']
    names = [name for r in results for name in
             [r['main_declaration'], *r.get('companion_declarations', [])]]
    assert len(names) == len(set(names))
    files = sorted({r['file'] for r in results})
    imports = (ROOT / 'formalization/HeadComplexity/Results/All.lean').read_text()
    for f in files:
        assert (ROOT/f).is_file(), f
        module = f.removeprefix('formalization/').removesuffix('.lean').replace('/', '.')
        assert re.search(r'^import\s+' + re.escape(module) + r'\s*$', imports, re.M), module
    axiom_text = (BASE/'validation/lean-all-research-final-axioms.log').read_text()
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axiom_text)
    assert len(reports) == len(names), (len(reports), len(names))
    assert {name for name, _ in reports} == set(names)
    for name, axioms in reports:
        assert {a.strip() for a in axioms.split(',') if a.strip()} <= ALLOWED, (name, axioms)
    build = (ROOT/inventory['validation']['build_log']).read_text()
    jobs = inventory['validation']['build_jobs']
    assert f'Build completed successfully ({jobs} jobs).' in build
    cert_dir = BASE/'certificates'
    certs = json.loads((cert_dir/'manifest.json').read_text())['certificates']
    audit_count = 0
    for cert in certs:
        p = cert_dir/cert['file']
        assert digest(p) == cert['sha256'], p
        if 'audit' in cert:
            a = json.loads((cert_dir/cert['audit']).read_text())
            assert a['input_sha256'] == cert['sha256'], cert['file']
            assert a['all_target_signs_certified'] and a['whole_cube_denominator_admissibility']
            assert a['negative_margins_certified'] == a['unseparated_margins'] == 0
            audit_count += 1
    checkpoint_dir = BASE/'checkpoints'
    checkpoints = json.loads((checkpoint_dir/'manifest.json').read_text())['checkpoints']
    for c in checkpoints:
        assert digest(checkpoint_dir/c['file']) == c['sha256'], c['file']
    json_count = 0
    for p in BASE.rglob('*.json'):
        json.loads(p.read_text())
        json_count += 1
    tex_count = 0
    for p in BASE.rglob('*.tex'):
        s = p.read_text()
        assert '\u2014' not in s, p
        stack = []
        for kind, env in re.findall(r'\\(begin|end)\{([^}]+)\}', s):
            if kind == 'begin':
                stack.append(env)
            else:
                assert stack and stack.pop() == env, (p, kind, env)
        assert not stack, (p, stack)
        tex_count += 1
    changed = subprocess.check_output(['git', 'diff', '--name-status', BASELINE,
                                      '--', 'formalization'], cwd=ROOT, text=True)
    for line in changed.splitlines():
        status, filename = line.split('\t', 1)
        assert status == 'A' or filename == 'formalization/HeadComplexity/Results/All.lean', line
    assert digest(Path('/out/attachments/version-5.tex')) == SOURCE_SHA
    subprocess.run(['git', 'diff', '--check', BASELINE, '--',
                    'artifacts/head-compression', 'formalization'], cwd=ROOT, check=True)
    full = json.loads((cert_dir/'random-n14-anchored-h292.json').read_text())['labels']
    lo = json.loads((cert_dir/'random-n14-lower-face-n13-confluent-h146.json').read_text())['labels']
    hi = json.loads((cert_dir/'random-n14-upper-face-n13-anchored-h147-compact.json').read_text())['labels']
    glued = json.loads((cert_dir/'random-n14-glued-h293.json').read_text())['labels']
    assert full == lo + hi == glued
    report = {
        'lean_modules': len(files), 'listed_declarations': len(names),
        'all_imported': True, 'all_listed_axiom_audits_checked': True,
        'allowed_axioms': sorted(ALLOWED), 'successful_full_build_jobs': jobs,
        'certificate_manifest_hashes_checked': len(certs),
        'checkpoint_manifest_hashes_checked': len(checkpoints),
        'research_json_files_parsed': json_count, 'all_research_json_parsed': True,
        'tex_files_checked': tex_count, 'tex_environments_balanced': True,
        'no_em_dashes_in_tex': True, 'original_model_files_unchanged': True,
        'manuscript_unchanged': True, 'manuscript_sha256': SOURCE_SHA,
        'target_proved': False, 'full_and_concatenated_original_face_labels_equal': True,
        'hash_matched_large_certificate_audit_reports': audit_count,
        'scope': 'Inventory, hashes, imports, logged build/axiom checks, and static formatting only; no new mathematical theorem or certificate verification is inferred.'}
    (BASE/'diagnostics/final-repository-integrity.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
