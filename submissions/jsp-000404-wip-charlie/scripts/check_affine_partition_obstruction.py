"""Check the rational affine-partition obstruction, independently of the search.

This verifies exact finite arithmetic. The general geometric trace inequality
and angle/argument deductions are documented in AFFINE_PARTITION_OBSTRUCTION.md.
It is not a Lean proof of that geometric counterexample.
"""

import argparse
import hashlib
import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

from check_full_band_phase_counterexample import PI, atan_nonnegative
from check_unweighted_thresholds import mat, det, dot_adj


def check_average(points, triples):
    assert len(triples) in (2, 3)
    values = [mat(points, triple) for triple in triples]
    assert all(det(value) == F(-1, 4) for value in values)
    if len(values) == 2:
        weights = (F(1, 2), F(1, 2))
    else:
        base = values[0]
        u, v = [tuple(y-x for x, y in zip(base, other)) for other in values[1:]]
        a, b, c = dot_adj(u, u), dot_adj(u, v), dot_adj(v, v)
        d, e = -dot_adj(base, u), -dot_adj(base, v)
        denominator = a*c-b*b
        assert denominator
        p, q = (c*d-b*e)/denominator, (a*e-b*d)/denominator
        weights = (1-p-q, p, q)
    assert min(weights) >= 0 and sum(weights) == 1
    matrix = tuple(sum(w*value[h] for w, value in zip(weights, values)) for h in range(3))
    assert matrix[0] > 0 and 4*det(matrix) > F(3, 4)


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path, nargs='?', default=Path(
        'verification/affine-partition-20261105/cover.json'))
    args = ap.parse_args()
    raw = args.certificate.read_bytes()
    data = json.loads(raw)
    points = [tuple(p) for p in data['points']]
    assert data['parent_t'] == '23/5' and data['child_t'] == '18/5'
    assert len(points) == len(set(points)) == 20
    assert all(len(p) == 2 and all(type(x) is int for x in p) for p in points)
    angles = 0
    for j, (x, y) in enumerate(points):
        for i, k in combinations([h for h in range(20) if h != j], 2):
            u, v = points[i][0]-x, points[i][1]-y
            s, t = points[k][0]-x, points[k][1]-y
            cross, product = abs(u*t-v*s), u*s+v*t
            assert cross > 0
            if product < 0:
                assert atan_nonnegative(F(cross, -product))[0] > 5*PI[1]/23
            angles += 1
    assert angles == 3420
    assert atan_nonnegative(F(7, 6))[1] < 5*PI[0]/18
    assert F(36, 49) < F(3, 4)
    masks = set()
    for certificate in data['certificates']:
        triples = certificate['triples']
        assert all(len(set(triple)) == 3 and all(0 <= i < 20 for i in triple)
                   for triple in triples)
        check_average(points, triples)
        carrier = set(i for triple in triples for i in triple)
        mask = sum(1 << i for i in carrier)
        assert mask == certificate['mask'] and mask not in masks
        masks.add(mask)
    remaining = list(range(0, 1 << 20, 2))
    for mask in sorted(masks):
        remaining = [color for color in remaining if color & mask not in (0, mask)]
    assert not remaining
    print('SHA-256', hashlib.sha256(raw).hexdigest())
    print('PASS: 20 integer points; all 3420 triple angles strictly below 18*pi/23.')
    print(f'PASS: {len(masks)} rational positive-matrix certificates with 4*det(C)>3/4.')
    print('PASS: all 524288 complementary colouring classes contain a monochromatic certificate.')
    print('Every bipartition has a part whose every nonsingular affine image has an angle >13*pi/18.')
    print('Scope: exact executable arithmetic and written geometry; not a Lean theorem.')


if __name__ == '__main__':
    main()
