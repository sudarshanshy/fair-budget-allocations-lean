#!/usr/bin/env python3
"""Check selected modules using the pinned compiler and existing Lake dependencies."""
import json
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'lake-manifest.json').read_text())
paths = [root / '.lake/packages' / p['name'] / '.lake/build/lib/lean'
         for p in manifest['packages']]
paths.append(root / '.lake/build/lib/lean')
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)))
for argument in sys.argv[1:]:
    source = Path(argument)
    target = root / '.lake/build/lib/lean' / source.with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(['lean', '-j1', '-o', str(target), str(source)],
                            cwd=root, env=env)
    if result.returncode:
        sys.exit(result.returncode)
