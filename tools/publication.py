#!/usr/bin/env python3
"""Validate the public import boundary and export only explicitly approved files."""
import argparse
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


def check(root=ROOT, public_tree=False, manifest_path=MANIFEST):
    manifest = json.loads(safe_path(root, manifest_path).read_text())
    sources = {}
    for item in manifest['files']:
        source = safe_path(root, item['target'] if public_tree else item['source'])
        safe_path(root, item['target'])
        if item['target'] in sources:
            raise ValueError('Duplicate export target: ' + item['target'])
        if not source.is_file():
            raise ValueError('Missing export file: ' + str(source))
        sources[item['target']] = source
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
        target = module.replace('.', '/') + '.lean'
        if target not in sources:
            raise ValueError('Module absent from export files: ' + module)
        path = sources[target]
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
    targets = set(sources)
    for target, source in sources.items():
        if source.suffix == '.lean':
            for dependency in imports(source):
                if dependency == 'GraphPuzzlesResearch' or (dependency.startswith('GraphPuzzles.') and dependency not in allowed):
                    raise ValueError('Exported Lean file imports private work: ' + target)
    expected = {m.replace('.', '/') + '.lean' for m in allowed}
    if not expected <= targets: raise ValueError('Module absent from export files')
    if public_tree:
        actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()
                  and not any(part in {'.git', '.lake', '__pycache__'} for part in p.relative_to(root).parts)
                  and p.name != '.DS_Store'}
        if actual != targets:
            raise ValueError('Public tree differs from allowlist: ' + ', '.join(sorted(actual ^ targets)))
    return manifest, {'modules': len(seen), 'files': len(targets), 'external_imports': sorted(external)}


def export(destination, root=ROOT, manifest_path=MANIFEST):
    manifest, summary = check(root, manifest_path=manifest_path)
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
    exported_manifest, _ = check(destination, public_tree=True)
    if exported_manifest != manifest:
        raise ValueError('Exported manifest differs from the selected manifest')
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    validate = sub.add_parser('check')
    validate.add_argument('--public-tree', action='store_true')
    validate.add_argument('--manifest', default=MANIFEST,
                          help='Explicit draft allowlist; the default approved scope is unchanged')
    emit = sub.add_parser('export')
    emit.add_argument('destination', type=Path)
    emit.add_argument('--manifest', default=MANIFEST)
    args = parser.parse_args()
    try:
        summary = (check(public_tree=args.public_tree, manifest_path=args.manifest)[1]
                   if args.command == 'check' else
                   export(args.destination, manifest_path=args.manifest))
    except (ValueError, OSError, KeyError) as error:
        print('Publication check failed:', error, file=sys.stderr)
        raise SystemExit(1)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
