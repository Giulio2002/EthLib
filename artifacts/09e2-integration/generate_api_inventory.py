#!/usr/bin/env python3
"""Compare written declarations in each historical child with the checkout.

Run from the repository root: python3 artifacts/09e2-integration/generate_api_inventory.py
This is a lexical inventory, not a Lean parser or a proof of type equality.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

SHAS = [
    '81d4251173bee3884861eb90903090a7a9f994dc',
    '5629dc3cec1903df275e8562cf70e55b5d83aee3',
    '217c2028afc1dfe260990e7e2bd088dab5f8df7e',
    'afb03ca43019d4a6b721e65f65022f561674ae1c',
]
DECL = re.compile(
    r'(?m)^(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
    r'(?:def|theorem|lemma|abbrev|inductive|structure|class)\s+'
    r'([\w.\u0080-\uffff]+)\b'
)
ADDED = re.compile(
    r'^\+\s*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*'
    r'(?:def|theorem|lemma|abbrev|inductive|structure|class)\s+'
    r'([\w.\u0080-\uffff]+)'
)
DELIMITER = re.compile(r'\s(?::=|where)(?:\s|$)|\n[ \t]+\|')
OUTPUT = Path('artifacts/09e2-integration/api-inventory.json')


def git(*args):
    return subprocess.check_output(['git', *args], text=True)


def headers(source):
    """Extract every matched header, including terminal equation-style definitions."""
    matches = list(DECL.finditer(source))
    result = {}
    for index, match in enumerate(matches):
        name = match.group(1)
        if name in result:
            raise ValueError(f'duplicate declaration name: {name}')
        end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        declaration = source[match.start():end]
        delimiter = DELIMITER.search(declaration)
        if delimiter is None:
            raise ValueError(f'no header delimiter for declaration: {name}')
        result[name] = ' '.join(declaration[:delimiter.start()].split())
    return result


def settle_definition(source):
    """Return the complete final settle definition without the namespace end."""
    match = re.search(r'(?ms)^def settle\b.*?(?=^end EthLib\.EVM\.Frame\s*$)', source)
    if match is None:
        raise ValueError('Frame.settle definition or namespace end not found')
    return match.group(0)


def main():
    children = []
    authored = []
    settle_checks = []
    for sha in SHAS:
        files = git('diff-tree', '--no-commit-id', '--name-only', '-r', sha,
                    '--', 'EthLib/EVM', 'EthLib/EVM.lean').splitlines()
        comparisons = []
        additions = []
        for name in files:
            path = Path(name)
            if not name.endswith('.lean'):
                continue
            if not path.is_file():
                raise FileNotFoundError(f'{sha}: missing candidate file {name}')
            before = git('show', f'{sha}:{name}')
            now = path.read_text()
            old_headers = headers(before)
            new_headers = headers(now)
            changed = [
                {'name': key, 'at_child': value, 'at_head': new_headers.get(key)}
                for key, value in old_headers.items() if new_headers.get(key) != value
            ]
            imports_before = [line for line in before.splitlines()
                              if re.match(r'^(public )?import ', line)]
            imports_now = [line for line in now.splitlines()
                           if re.match(r'^(public )?import ', line)]
            comparisons.append({
                'file': name,
                'declarations_compared': len(old_headers),
                'changed_or_missing_headers': changed,
                'child_imports_missing_at_head': [line for line in imports_before
                                                   if line not in imports_now],
            })
            diff = git('diff', f'{sha}^', sha, '--', name)
            for line in diff.splitlines():
                match = ADDED.match(line)
                if match:
                    decl = match.group(1)
                    additions.append({'file': name, 'declaration': decl,
                                      'present_at_head': decl in new_headers})
            if name == 'EthLib/EVM/Frame.lean':
                old_settle = settle_definition(before)
                new_settle = settle_definition(now)
                settle_checks.append({
                    'commit': sha, 'file': name,
                    'child_header': old_headers['settle'],
                    'candidate_header': new_headers['settle'],
                    'definition_sha256_child': hashlib.sha256(old_settle.encode()).hexdigest(),
                    'definition_sha256_candidate': hashlib.sha256(new_settle.encode()).hexdigest(),
                    'definition_byte_identical': old_settle == new_settle,
                })
        children.append({'commit': sha, 'files': comparisons})
        authored.append({'commit': sha, 'authored_declarations': additions,
                         'missing': [item for item in additions if not item['present_at_head']]})
    if len(settle_checks) != len(SHAS):
        raise ValueError('Frame.settle was not compared in every child')
    output = {
        'method': 'Diff each exact child against its parent and enumerate added declaration names in EthLib/EVM; compare against the same path in the working tree. Name-presence is not semantic API equivalence.',
        'commits': authored,
        'roots': {'ordinary': 'EthLib/EVM.lean', 'proof': 'EthLib/EVM/Proofs.lean'},
        'constructor': 'Environment.Context fields appended in successive children: 09e2a seven block fields, 09e2b1 blobVersionedHashes, 09e2b2 excessBlobGas before blobVersionedHashes, 09e2c blockHashes. Current constructor must supply all 15 fields.',
        'linear_ancestry': SHAS,
        'all_declaration_header_comparison': {
            'method': 'Compare matched top-level declaration headers and import lines in every Lean file changed by each child against the working tree. The extractor handles :=, where, and equation-style declarations, including at end of file. This is lexical, not elaborated type equality; constructor-and-roots.diff records structure fields and import changes.',
            'children': children,
            'interpretation': 'Review changed headers and missing imports below. Structure and rule constructors gained fields or cases; see constructor-and-roots.diff.',
            'terminal_equation_checks': settle_checks,
        },
    }
    OUTPUT.write_text(json.dumps(output, indent=2) + '\n')
    print('authored declarations:', sum(len(c['authored_declarations']) for c in authored))
    print('authored missing:', sum(len(c['missing']) for c in authored))
    print('header counts:', [sum(f['declarations_compared'] for f in c['files']) for c in children])
    print('settle definitions byte-identical:', sum(c['definition_byte_identical'] for c in settle_checks), '/', len(SHAS))


if __name__ == '__main__':
    main()
