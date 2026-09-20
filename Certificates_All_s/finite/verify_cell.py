"""Decode one compact proposal and recompute its complete uniform certificate."""
import argparse
import json
import os
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from replay import dimensions, digest, read_json, require, witness_audit, write_json

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('cell', type=Path)
p.add_argument('report', type=Path)
a = p.parse_args()
require(__debug__ and sys.flags.optimize == 0, 'Run Python without -O')
cell = read_json(a.cell)
os.environ.update(N8_DEG_HALF=str(cell['degree'] // 2),
                  N8_TAYLOR_ORDER=str(cell['order']), N8_TARGET_BALANCE=cell['balance'])
sys.path.insert(0, str(HERE / 'kernel'))
import codec
import recipe
import structure
from verify_interval import verify
import exact_mm

asset = cell['witness']
source = (HERE.parent / asset['path']).resolve()
require(source.is_relative_to((HERE.parent / 'certificates/finite').resolve()),
        'Witness path outside certificate directory')
require(digest(source) == asset['compressed_sha256'], 'Witness byte hash mismatch')
started = time.monotonic()
record = codec.load(source, asset['semantic_sha256'], limits=codec.RECIPE_LIMITS)
record, expansion = recipe.expand_record(record, structure)
metadata = witness_audit(record, cell, dimensions(cell))
expansion.update(source_sha256=digest(source), semantic_sha256=asset['semantic_sha256'],
                 metadata=metadata, elapsed_seconds=time.monotonic() - started)
write_json(a.report.parent / 'EXPANSION.json', expansion)
verify(cell['center'], cell['halfwidth'], out=a.report,
       minorant=cell['profile'], record=record)
write_json(a.report.parent / 'ARITHMETIC.json', {
    **exact_mm.STATS, 'scope': 'Parent-process diagnostic counters; forked child work excluded.'})
