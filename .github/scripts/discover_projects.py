"""Discover every tracked Lean project; fail if its build configuration is missing."""
import json
import subprocess

paths = set(subprocess.check_output(
    ['git', 'ls-tree', '-r', '--name-only', 'HEAD'], text=True
).splitlines())
projects = sorted(path.removesuffix('/lean-toolchain') for path in paths
                  if path.endswith('/lean-toolchain'))
if not projects:
    raise SystemExit('No Lean projects found')
for project in projects:
    if not any(f'{project}/{name}' in paths for name in ('lakefile.toml', 'lakefile.lean')):
        raise SystemExit(f'Missing Lake configuration: {project}')
    if f'{project}/lake-manifest.json' not in paths:
        raise SystemExit(f'Missing pinned dependency manifest: {project}')
print(json.dumps({'project': projects}))
