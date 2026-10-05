#!/usr/bin/env python3
"""Validate the public import boundary and export only explicitly approved files."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = 'publication/public-manifest.json'


def lean_code(text):
    """Mask nested comments and strings, preserving newlines for command parsing."""
    result = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                result[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                result[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': result[i] = ' '
                i += 1
        elif quoted:
            char = text[i]
            if char != '\n': result[i] = ' '
            if char == '\\' and i + 1 < len(text):
                if text[i+1] != '\n': result[i+1] = ' '
                i += 2
            else:
                quoted = char != '"'; i += 1
        elif text.startswith('/-', i):
            result[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            result[i:end] = ' ' * (end - i); i = end
        elif text[i] == '"':
            result[i] = ' '; quoted = True; i += 1
        else:
            i += 1
    if depth or quoted:
        raise ValueError('Unterminated Lean comment or string')
    return ''.join(result)


def imports(path):
    code = lean_code(path.read_text())
    return [name for match in re.finditer(r'^\s*import\s+(?:all\s+)?([^\n]+)', code, re.M)
            for name in match[1].split()]


def safe_path(root, value):
    relative = Path(value)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('Unsafe manifest path: ' + value)
    path = root / relative
    if path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError('Export path leaves the source tree: ' + value)
    return path


def check(root=ROOT, public_tree=False):
    manifest = json.loads((root / MANIFEST).read_text())
    allowed = set(manifest['modules'])
    if len(allowed) != len(manifest['modules']):
        raise ValueError('Duplicate module in the public manifest')
    seen, stack = set(), list(manifest['roots'])
    external = set()
    while stack:
        module = stack.pop()
        if module in seen: continue
        if module not in allowed:
            raise ValueError('Public import reaches an unapproved module: ' + module)
        path = safe_path(root, module.replace('.', '/') + '.lean')
        if not path.is_file(): raise ValueError('Missing public module: ' + module)
        seen.add(module)
        code = lean_code(path.read_text())
        if re.search(r'\b(?:sorry|admit|native_decide|implemented_by)\b|^\s*(?:axiom|opaque|unsafe)\b', code, re.M):
            raise ValueError('Proof shortcut in public module: ' + module)
        for dependency in imports(path):
            if dependency == 'GraphPuzzlesResearch' or dependency.startswith('GraphPuzzles.') or dependency == 'GraphPuzzles':
                stack.append(dependency)
            elif dependency == 'Mathlib' or dependency.startswith(('Mathlib.', 'CDCLean.', 'Lean.', 'Std.', 'Batteries.')):
                external.add(dependency)
            else:
                raise ValueError('Unapproved external import: ' + dependency)
    if seen != allowed:
        raise ValueError('Public manifest has unreachable modules: ' + ', '.join(sorted(allowed - seen)))
    targets = set()
    for item in manifest['files']:
        source = safe_path(root, item['target'] if public_tree else item['source'])
        safe_path(root, item['target'])
        if item['target'] in targets: raise ValueError('Duplicate export target: ' + item['target'])
        targets.add(item['target'])
        if not source.is_file(): raise ValueError('Missing export file: ' + str(source))
        if source.suffix == '.lean':
            for dependency in imports(source):
                if dependency == 'GraphPuzzlesResearch' or (dependency.startswith('GraphPuzzles.') and dependency not in allowed):
                    raise ValueError('Exported Lean file imports private work: ' + item['target'])
    expected = {m.replace('.', '/') + '.lean' for m in allowed}
    if not expected <= targets: raise ValueError('Module absent from export files')
    if public_tree:
        actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()
                  and not any(part in {'.git', '.lake', '__pycache__'} for part in p.relative_to(root).parts)
                  and p.name != '.DS_Store'}
        if actual != targets:
            raise ValueError('Public tree differs from allowlist: ' + ', '.join(sorted(actual ^ targets)))
    return manifest, {'modules': len(seen), 'files': len(targets), 'external_imports': sorted(external)}


def export(destination, root=ROOT):
    manifest, summary = check(root)
    if destination.exists():
        raise ValueError('Export destination must not exist; export to a fresh directory and review the diff')
    if destination.resolve().is_relative_to(root.resolve()):
        raise ValueError('Export destination must be outside the private source tree')
    destination.mkdir(parents=True)
    for item in manifest['files']:
        target = safe_path(destination, item['target'])
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(safe_path(root, item['source']), target)
    # Independently verify the resulting file tree, not just the copy inputs.
    check(destination, public_tree=True)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    validate = sub.add_parser('check')
    validate.add_argument('--public-tree', action='store_true')
    emit = sub.add_parser('export')
    emit.add_argument('destination', type=Path)
    args = parser.parse_args()
    try:
        summary = check(public_tree=args.public_tree)[1] if args.command == 'check' else export(args.destination)
    except (ValueError, OSError, KeyError) as error:
        print('Publication check failed:', error, file=sys.stderr)
        raise SystemExit(1)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
