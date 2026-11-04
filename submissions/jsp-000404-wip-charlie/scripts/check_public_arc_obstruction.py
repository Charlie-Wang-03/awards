"""Independently check one published abstract arc obstruction using fractions.

Input: the unmodified 2026-11-04 jerrylijize1224-star research snapshot.
No code from the archive is imported or executed. No planar witness follows.
"""

import argparse
import hashlib
import json
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
from zipfile import ZipFile


ARCHIVE_SHA = '34839c6043eedccec8b383823aeb65f7479ec5496e2d230d4e715a8c6d12e9b0'
MODEL = 'jsp404-twentyseven-exact-20261104/research/logs/jsp404-mixed144-9-12-20261022.json'
PERIOD = 18


def normalized(intervals):
    """All translates intersecting [0,18], with coincident pieces merged."""
    lifted = []
    for a, b in intervals:
        assert a <= b
        for k in range(-int(b // PERIOD), int((PERIOD - a) // PERIOD) + 1):
            l, r = max(F(0), a + PERIOD*k), min(F(PERIOD), b + PERIOD*k)
            if l <= r:
                lifted.append((l,r))
    out = []
    for l,r in sorted(lifted):
        if out and l <= out[-1][1]:
            out[-1] = (out[-1][0], max(r, out[-1][1]))
        else:
            out.append((l,r))
    return out


def antipodal_options(lhs, rhs):
    opp = normalized([(a-9,b-9) for a,b in rhs])
    return normalized([(max(a,c),min(b,e)) for (a,b),(c,e) in product(lhs,opp)
                       if max(a,c) <= min(b,e)])


def main():
    if not __debug__:
        raise RuntimeError('Run without -O: the rational checks use assertions.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('archive', type=Path)
    p = ap.parse_args().archive
    assert hashlib.sha256(p.read_bytes()).hexdigest() == ARCHIVE_SHA
    with ZipFile(p) as z:
        raw = z.read(MODEL)
    data = json.loads(raw)
    d = F(data['diameter'])
    assert d == F(43,6) < F(36,5) < 9
    single = [F(a) for a in data['starts_one']]
    triple = [tuple(map(F, row)) for row in data['starts_three']]
    assert len(single) == 9 and len(triple) == 12
    arcs = [[(a,a+d)] for a in single]
    for a,b,c in triple:
        assert a < b < c < a + PERIOD
        arcs.append([(a,c+d-PERIOD), (b,a+d), (c,b+d)])
    rows = [normalized(row) for row in arcs]
    for row in rows:
        assert row
        for (a,b),(c,e) in product(row,repeat=2):
            # The whole difference interval [c-b,e-a] must fit in one
            # period translate of [-d,d]. Normalized differences are in [-18,18].
            assert any(PERIOD*k-d <= c-b and e-a <= PERIOD*k+d for k in (-1,0,1))
    options = {(i,j): antipodal_options(rows[i],rows[j])
               for i,j in combinations(range(len(rows)),2)}
    assert len(options) == 210 and all(options.values())
    u,v,w = (options[pair] for pair in ((7,9),(7,10),(9,10)))
    assert len(u) == len(v) == len(w) == 1
    assert w[0][1] < u[0][0] and u[0][1] < v[0][0] and v[0][1]-w[0][0] < 9
    print('SOURCE jerrylijize1224-star/jsp404-lean-partial@09b2ee9cab2da6ca977f682f1c8359b5e90d13d0')
    print('ARCHIVE_SHA256', ARCHIVE_SHA)
    print('MODEL_SHA256', hashlib.sha256(raw).hexdigest())
    print('PASS: 21 rows of circular diameter <= 43/6 < 36/5 (period 18).')
    print('PASS: all 210 pairs have a nonempty antipodal intersection.')
    print('EXACT INTERVALS (7,9), (7,10), (9,10):',u,v,w)
    print('PASS: w<u<v and v-w<9 for every choice; neither triangle orientation is possible.')
    print('This excludes a pairwise-only capacity proof, not the original planar theorem.')


if __name__ == '__main__':
    main()
