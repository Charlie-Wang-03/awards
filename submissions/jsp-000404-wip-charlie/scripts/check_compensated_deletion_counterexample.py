"""Certify the historical four-point witness at the fixed scale t=17/5.

The exact-maximum normalization in the historical note is a different claim.
This certificate uses only the AngleCap hypothesis needed by fixed-t deletion.
It is an exact rational computation, not a Lean geometric theorem.
"""

from fractions import Fraction as Q
from itertools import combinations

import check_full_band_phase_counterexample as interval


POINTS = ((7, -4), (19, -8), (3, 11), (-3, -11))
T = Q(17, 5)
LAM = interval.scale(interval.PI, 1 / T)


def profile(indices):
    rows = []
    for i in indices:
        angles = sorted(interval.projective_angle(interval.vector(i, j, POINTS))
                        for j in indices if i != j)
        assert all(angles[k][1] < angles[k + 1][0] for k in range(len(angles) - 1))
        gaps = [interval.sub(angles[k + 1], angles[k]) for k in range(len(angles) - 1)]
        gaps.append(interval.add(interval.sub(angles[0], angles[-1]), interval.PI))
        quotients = []
        for gap in gaps:
            lower, upper = gap[0] / LAM[1], gap[1] / LAM[0]
            a, b = lower.numerator // lower.denominator, upper.numerator // upper.denominator
            assert a == b
            quotients.append(a)
        rows.append((i, quotients, sum(max(q - 1, 0) for q in quotients)))
    return rows


def weight(rows):
    return sum(2 ** exponent for _, _, exponent in rows)


if __name__ == "__main__":
    assert 3 < T < Q(7, 2) and len(set(POINTS)) == 4
    checked = 0
    for centre in range(4):
        for a, b in combinations((i for i in range(4) if i != centre), 2):
            u, v = interval.vector(centre, a, POINTS), interval.vector(centre, b, POINTS)
            dot = u[0] * v[0] + u[1] * v[1]
            det = abs(u[0] * v[1] - u[1] * v[0])
            assert det > 0
            if dot < 0:
                assert interval.atan_nonnegative(Q(det, -dot))[0] > LAM[1]
            checked += 1
    assert checked == 12
    root = profile(tuple(range(4)))
    assert weight(root) == 7
    print("root:", root, "weight=7")
    for deleted in range(4):
        child = profile(tuple(i for i in range(4) if i != deleted))
        assert weight(child) == 6 < weight(root)
        print(f"delete {deleted}:", child, "weight=6")
    print("PASS: 12 strict angle checks and every root/child quotient enclosure.")
    print("Scope: fixed-t AngleCap counterexample; NOT a Lean geometric theorem.")
