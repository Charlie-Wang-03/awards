"""Exact checks accompanying the ordinary-point threshold notes; no Lean replay."""

import argparse
import hashlib
import json
from bisect import bisect_left
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
from zipfile import ZipFile

from check_full_band_phase_counterexample import (
    MASS_POINTS, PI, POINTS, atan_nonnegative,
)
from check_public_arc_obstruction import (
    ARCHIVE_SHA, MODEL, PERIOD, antipodal_options, normalized,
)


def mat(p, triple):
    i, j, k = triple
    x, y = (p[i][h] - p[j][h] for h in (0, 1))
    v, w = (p[k][h] - p[j][h] for h in (0, 1))
    area = abs(x*w - y*v)
    assert area
    return (F(-x*v, area), F(-x*w-y*v, 2*area), F(-y*w, area))


def det(a):
    return a[0]*a[2] - a[1]**2


def dot_adj(a, b):
    return a[2]*b[0] - 2*a[1]*b[1] + a[0]*b[2]


def verify_affine(name, p, support):
    # Solve tr(adj(C)(B_i-B_0))=0 for the two independent weights of
    # the selected support. The all-angle upper check below, not this
    # support selection, certifies optimality.
    active = [mat(p, t) for t in support]
    s, t = [tuple(y-x for x, y in zip(active[0], b)) for b in active[1:]]
    a, b, d = dot_adj(s, s), dot_adj(s, t), dot_adj(t, t)
    e, f = -dot_adj(active[0], s), -dot_adj(active[0], t)
    denom = a*d - b*b
    assert denom
    u, v = (d*e-b*f)/denom, (a*f-b*e)/denom
    weights = (1-u-v, u, v)
    assert min(weights) > 0 and sum(weights) == 1
    c = tuple(sum(w*m[h] for w, m in zip(weights, active)) for h in range(3))
    dc = det(c)
    assert dc > 0 and c[0] > 0
    assert all(dot_adj(c, m) == 2*dc for m in active)
    count = 0
    for j in range(len(p)):
        for i, k in combinations((h for h in range(len(p)) if h != j), 2):
            angle = mat(p, (i, j, k))
            assert det(angle) == F(-1, 4)
            assert dot_adj(c, angle) <= 2*dc
            count += 1
    print(f'{name}: {count} primal inequalities; 3 dual angles; optimum squared = {4*dc}')
    return 4*dc


def ordered_binary_test():
    # Four levels in directions 0, 45, 90, 135 degrees. The coarse
    # bit separates two sets of eight for the aperture assertion at n=4.
    p = [(10**6*b0+10**4*b1-b3, 10**4*b1+100*b2+b3)
         for b0, b1, b2, b3 in product((0, 1), repeat=4)]
    assert len(set(p)) == 16
    assert atan_nonnegative(F(9, 10))[0] > 2*PI[1]/9
    angles = 0
    for j, (x, y) in enumerate(p):
        for i, k in combinations((h for h in range(16) if h != j), 2):
            u, v = p[i][0]-x, p[i][1]-y
            s, t = p[k][0]-x, p[k][1]-y
            dot, cross = u*s+v*t, abs(u*t-v*s)
            assert cross > 0
            if dot < 0:
                assert 10*cross > 9*(-dot)
            angles += 1
    assert angles == 1680
    for observer, group, sign in ((p[0], p[8:], 1), (p[8], p[:8], -1)):
        assert len(group) == 8
        for x, y in group:
            dx, dy = sign*(x-observer[0]), y-observer[1]
            assert 0 <= dy and 50*dy < dx
    # Each view is on one side of a horizontal ray, width < atan(1/50).
    assert F(1, 50) < PI[0]/9
    print('A(4) narrow views: 16 integer points, 1680 strict angle checks, two views of 8.')


def check_sector_64():
    # Independently visit every prescribed local side and use the actual
    # nearest incident/splitting line on the projective circle. This
    # checks the finite angular data, not all triples of 74,304 points.
    n = 64
    k = n//4
    m = 3*n*(2*n+1)
    period = lcm(2*m, 8, 4*(k-1), 6, n)
    step, w, lam = period//m, period//n, 2*period//(2*n+1)
    d = lam+step
    assert 3*step == w-lam and 2*step+d == w and d % 2 == 0
    roots = [(period//2 + i*2*period//3) % period for i in range(3)]
    size = [0]*3
    axes = []

    def nearest(x, ds):
        # ds sorted and lifted one period at both ends.
        y = x % period
        p = bisect_left(ds, y)
        return min(ds[p]-y, y-ds[p-1])

    def lifts(ds):
        core = sorted(s % period for s in ds)
        return [core[-1]-period]+core+[core[0]+period]

    for t in roots:
        ext = [t-period//3, t+period//3]
        splits = [t+3*period//8+i*(period//(4*(k-1))) for i in range(k)]
        assert all(nearest(b, lifts(ext)) >= w for b in splits)
        assert all(nearest(b, lifts(splits[i+1:])) >= w for i, b in enumerate(splits[:-1]))
        axes.append(lifts(ext+splits))
    for j in range(m):
        mid = j*step
        ids = [i for i, t in enumerate(roots) if (mid-t+period//6) % period < period//3]
        assert len(ids) == 1
        i, = ids
        size[i] += 1
        assert all(nearest(mid+shift, axes[i]) >= w for shift in (-d//2, 0, d//2))
    assert size == [8256]*3 and max(size) <= 2**k
    assert F(32, 100*n*(2*n+1)) < PI[0]*F(w-lam, period)
    print('Sector n=64: 24,768 local triangles, all side directions and 3 sets of axes; explicit scale margin.')


def check_cycles(archive):
    assert hashlib.sha256(archive.read_bytes()).hexdigest() == ARCHIVE_SHA
    with ZipFile(archive) as z:
        data = json.loads(z.read(MODEL))
    d = F(data['diameter'])
    assert PERIOD == 18 and d == F(43, 6) < F(36, 5)
    arcs = [[(F(a), F(a)+d)] for a in data['starts_one']]
    for a, b, c in (map(F, row) for row in data['starts_three']):
        assert a < b < c < a+PERIOD
        arcs.append([(a, c+d-PERIOD), (b, a+d), (c, b+d)])
    rows = [normalized(row) for row in arcs]
    assert len(rows) == 21

    def opts(i, j):
        out = antipodal_options(rows[i], rows[j])
        assert out
        return out

    cycles = [(3, 15, 17), (7, 9, 10), (7, 12, 16), (9, 12, 20), (1, 11, 19, 13)]
    for cyc, start in zip(cycles, (3, F(53, 7), F(19, 2), 2, 7)):
        for i, j in zip(cyc, cyc[1:] + cyc[:1]):
            assert all(any(start < l+h and r+h < start+9 for h in (0, 18))
                       for l, r in opts(i, j))
    witness = {
        (1, 11, 13): (F(143, 15), F(17, 3), F(899, 60)),
        (1, 11, 19): (F(143, 15), F(106, 15), F(199, 12)),
        (1, 13, 19): (F(17, 3), F(7, 3), F(179, 15)),
        (11, 13, 19): (F(57, 5), F(163, 60), F(241, 15)),
    }
    assert set(witness) == set(combinations(sorted(cycles[-1]), 3))
    for cyc, values in witness.items():
        for i, j, q in zip(cyc, cyc[1:] + cyc[:1], values):
            assert any(l <= q <= r for l, r in opts(i, j))
        a, b, c = sorted(q % 18 for q in values)
        assert max(b-a, c-b, a+18-c) < 9
    first, *middle, last = map(set, cycles)
    assert first.isdisjoint(last)
    assert (first | last).isdisjoint(set.union(*middle))
    assert not set.intersection(*middle)
    print('21-row archive:', ARCHIVE_SHA)
    print('5 forced positive cycles; all four triples of the quartet realizable; at most 17 rows survive.')


def main():
    if not __debug__:
        raise RuntimeError('Use Python without -O; assertions verify the certificates.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('archive', type=Path, nargs='?', help='Optional pinned public 21-row ZIP')
    args = ap.parse_args()
    four = ((-10, 0), (10, 0), (0, 5), (0, 6))
    assert verify_affine('four-centre', four, ((0, 2, 1), (0, 2, 3), (1, 2, 3))) == F(1, 3)
    for name, pts in (('six-point phase', POINTS), ('six-point mass', MASS_POINTS)):
        verify_affine(name, pts, ((0, 1, 2), (2, 3, 4), (0, 5, 4)))
    five = ((-10297, -505), (-10303, -495), (-9697, 495), (-9703, 505), (9703, -505))
    verify_affine('five-point width drop', five, ((0, 1, 3), (1, 2, 4), (3, 2, 4)))
    ordered_binary_test()
    check_sector_64()
    if args.archive:
        check_cycles(args.archive)


if __name__ == '__main__':
    main()
