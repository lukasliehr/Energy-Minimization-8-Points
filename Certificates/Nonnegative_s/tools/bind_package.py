"""Write integrity bindings after preparing a release; not a proof checker."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

cells = root / 'finite/cells.json'
manifest = json.loads(cells.read_text())
manifest['checker_sha256'] = {str(p.relative_to(root / 'finite')): sha(p)
                            for p in sorted((root / 'finite').rglob('*.py'))}
cells.write_text(json.dumps(manifest, indent=2) + '\n')
files = {}
for p in sorted(root.rglob('*')):
    name = str(p.relative_to(root))
    if (p.is_file() and name != 'MANIFEST.json' and '__pycache__' not in p.parts
            and '.git' not in p.parts and p.name != '.DS_Store'
            and not p.name.startswith('._')):
        files[name] = {'bytes': p.stat().st_size, 'sha256': sha(p)}
(root / 'MANIFEST.json').write_text(json.dumps({'schema_version': 1, 'files': files}, indent=2) + '\n')
print('Bound', len(files), 'release files')
