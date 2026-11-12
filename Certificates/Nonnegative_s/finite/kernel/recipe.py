"""Untrusted numerical proposal decoder; never a proof/arithmetic premise.

The returned binary64 matrix is the proposed exact dyadic C. This is not the
exact real matrix A_ref^T K, and no correctness claim about that formula is
used by the rigorous checker. Every generated C requires complete validation.
"""
import gzip
import hashlib
import json
import math
from pathlib import Path
import numpy as np

def expand(path, structure):
    with gzip.open(Path(path), 'rt') as fh:
        rec = json.load(fh)
    return expand_record(rec, structure)

def expand_record(record, structure):
    rec = dict(record)
    recipe = rec.pop('correction_recipe')
    kind = recipe['kind']
    if kind not in ('reference_coefficient_transpose_v1', 'reference_active_coefficient_transpose_v2'):
        raise ValueError('Unknown proposal recipe')
    rows = np.asarray(rec['rows'], dtype=np.int64)
    r = len(structure.EXPS)-2
    if rows.shape != (r,) or len(set(rows.tolist())) != r or min(rows) < 0 or max(rows) >= r+2:
        raise ValueError('Invalid retained rows')
    data = structure.raw_data()
    stored_blocks = recipe['reference_bases'] if kind.endswith('_v1') else recipe['reference_active_rows']
    if len(stored_blocks) != len(data):
        raise ValueError('Wrong reference block count')
    blocks = []
    for raw, stored, rb in zip(data, stored_blocks, rec['basis_records']):
        expected_rows = raw['raw'].shape[1]
        expected_cols = expected_rows-(1 if raw['name'].startswith('F') else 21)
        if kind.endswith('_v1'):
            B = np.asarray(stored, dtype=np.float64)
        else:
            free = rb['free']
            active = [rb['pivot']] if raw['name'].startswith('F') else rb['pivots']
            if sorted(free+active) != list(range(expected_rows)):
                raise ValueError('Invalid reference row partition')
            J = np.asarray(rb['change_of_basis'], dtype=np.float64)
            active_values = np.asarray(stored, dtype=np.float64)
            if J.shape != (expected_cols,expected_cols) or active_values.shape != (len(active),expected_cols):
                raise ValueError('Invalid active reference dimensions')
            B = np.empty((expected_rows,expected_cols))
            B[free,:] = J
            B[active,:] = active_values
        if B.shape != (expected_rows, expected_cols) or not np.isfinite(B).all():
            raise ValueError('Invalid reference matrix')
        tensor = raw['raw'][rows].astype(float)/raw['den']
        M = B.T @ (tensor @ B)
        ii = np.triu_indices(B.shape[1])
        factor = np.where(ii[0] == ii[1], 1., math.sqrt(2))
        blocks.append(M[:, ii[0], ii[1]]*factor)
    Aref = np.concatenate(blocks, axis=1)
    K = np.asarray(recipe['right_factor'], dtype=np.float64)
    if K.shape != (r,r) or not np.isfinite(K).all():
        raise ValueError('Invalid right factor')
    C = Aref.T @ K
    additive = recipe.get('additive_correction')
    if additive is not None:
        U = np.asarray(additive['left'], dtype=np.float64)
        V = np.asarray(additive['right'], dtype=np.float64)
        if (U.ndim != 2 or V.ndim != 2 or U.shape[0] != C.shape[0]
                or not 1 <= U.shape[1] <= 8 or V.shape != (U.shape[1],r)
                or not np.isfinite(U).all() or not np.isfinite(V).all()):
            raise ValueError('Invalid low-rank correction proposal')
        C = C + U @ V
    if not np.isfinite(C).all():
        raise ValueError('Nonfinite generated correction')
    rec['right_inverse'] = C
    if kind.endswith('_v2'):
        if 'left_preconditioner' in rec:
            raise ValueError('V2 derives the left preconditioner from its right factor')
        rec['left_preconditioner'] = K.T.copy()
    digest = hashlib.sha256(C.astype('<f8', copy=False).tobytes(order='C')).hexdigest()
    return rec, {'generated_C_shape': list(C.shape), 'generated_C_sha256_le_f64': digest,
        'decoder_semantics': 'untrusted numerical generation; actual finite output entries denote exact dyadics'}
