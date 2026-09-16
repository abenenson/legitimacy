#!/usr/bin/env python3
"""Exercise documentation gates against relocated content and hostile edits."""
# Copyright (c) 2026 Adam Benenson. MIT OR Apache-2.0.
# BID: au-ajfvy.166.10.1
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
GATES = [
    'check-readme-theorem-spine-citations.sh', 'check-spine-rooted.sh',
    'check-cited-theorem-identifiers.sh', 'check-claim-ledger-anchors.sh',
    'check-public-surface.sh', 'check-doc-alignment.sh',
]

def main():
    # Only three document copies and the gate scripts are mutable. Source and
    # fixture paths are read-only references; no builds or Git mutations occur.
    with tempfile.TemporaryDirectory(prefix='legitimacy-reader-gates-') as directory:
        root = Path(directory)
        for source in ROOT.iterdir():
            if source.name not in {'.git', '.lake', 'target', '.worktrees', 'docs', 'scripts', 'README.md'}:
                (root / source.name).symlink_to(source)
        (root / 'docs').mkdir()
        (root / 'scripts').mkdir()
        for source in (ROOT / 'docs').iterdir():
            if source.name not in {'formal-overview.md', 'claim-ledger.md'}:
                (root / 'docs' / source.name).symlink_to(source)
        documents = ['README.md', 'docs/formal-overview.md', 'docs/claim-ledger.md']
        pristine = {name: (ROOT / name).read_bytes() for name in documents}
        for name, content in pristine.items():
            (root / name).write_bytes(content)
        for source in (ROOT / 'scripts').iterdir():
            if source.name not in GATES:
                (root / 'scripts' / source.name).symlink_to(source)
        for gate in GATES:
            shutil.copy2(ROOT / 'scripts' / gate, root / 'scripts' / gate)
        # Fixed CLI-help fixture isolates document validation. The normal
        # check-public-surface gate separately checks the actual executable.
        (root / 'bin').mkdir()
        cargo = root / 'bin/cargo'
        cargo.write_text('#!/bin/sh\nprintf "%s\\n" "extract audit-graph compile paradox certify protocol init measure activate status audit"\n')
        cargo.chmod(0o755)
        env = {**os.environ, 'PATH': str(root / 'bin') + os.pathsep + os.environ['PATH']}
        def run(gate, expected, label):
            result = subprocess.run(['bash', str(root / 'scripts' / gate)], cwd=root,
                                    env=env, capture_output=True, text=True, timeout=60)
            assert (result.returncode == 0) == expected, (label, result.stdout, result.stderr)
            print(f'PASS {label}')
        for gate in GATES:
            run(gate, True, 'baseline ' + gate)
        cases = [
            ('check-readme-theorem-spine-citations.sh', 'docs/formal-overview.md',
             'Capacity/CriticalCapability.lean:55', 'Capacity/CriticalCapability.lean:56', 'moved citation drift'),
            ('check-spine-rooted.sh', 'docs/formal-overview.md',
             '| `LegitimacyKernel` |', '| `MissingKernel` |', 'moved spine declaration mismatch'),
            ('check-cited-theorem-identifiers.sh', 'docs/formal-overview.md',
             '| `LegitimacyKernel` |', '| `MissingKernel` |', 'moved theorem identifier missing'),
            ('check-claim-ledger-anchors.sh', 'docs/formal-overview.md',
             '## Theorem Spine', '## Renamed Spine', 'ledger destination heading drift'),
            ('check-public-surface.sh', 'docs/formal-overview.md',
             '--review-overlay', '--missing-overlay', 'moved workflow fragment missing'),
            ('check-public-surface.sh', 'docs/formal-overview.md',
             'docs/audit-bundle-schema.md', 'docs/nonexistent-evidence.md', 'moved path missing'),
        ]
        for obligation in ['CERTIFIABLE', 'GOVERNANCE-OBSERVABLE', 'CORRIGIBLE',
                           'COMPOSITIONAL SAFETY', 'NON-VACUOUS']:
            cases.append(('check-doc-alignment.sh', 'docs/formal-overview.md',
                          obligation, 'REMOVED OBLIGATION', 'missing ' + obligation))
        cases.append(('check-doc-alignment.sh', 'docs/formal-overview.md',
                      'proofs of five obligations', 'proofs of Four axioms',
                      'legacy four-axiom count'))
        for gate, name, old, new, label in cases:
            text = pristine[name].decode()
            assert old in text, (label, old)
            try:
                (root / name).write_text(text.replace(old, new))
                run(gate, False, label)
            finally:
                (root / name).write_bytes(pristine[name])
        (root / 'docs/formal-overview.md').unlink()
        run('check-public-surface.sh', False, 'missing overview fails closed')
        run('check-doc-alignment.sh', False, 'missing kernel overview fails closed')

if __name__ == '__main__':
    main()
