"""Exact rational interval certificate for the common-phase counterexample.

No floating-point operations, third-party packages, or numerical trig calls
are used.  This is a reproducible mathematical certificate, not a Lean proof.
The alternating arctan series and Machin's identity supply all angle bounds.
"""

from fractions import Fraction as Q
from itertools import combinations


POINTS = ((105, 13), (69, 69), (-72, 67), (-102, 1), (-47, -92), (48, -83))
T = Q(349, 100)
TERMS = 24


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return (a[0] - b[1], a[1] - b[0])


def scale(a, c):
    x, y = a[0] * c, a[1] * c
    return (min(x, y), max(x, y))


def atan_small(r):
    """Enclose arctan(r), 0 <= r <= 1/2, by alternating partial sums."""
    assert Q(0) <= r <= Q(1, 2)
    total = sum(((-1) ** k * r ** (2 * k + 1) / (2 * k + 1)
                 for k in range(TERMS)), Q(0))
    next_sum = total + (-1) ** TERMS * r ** (2 * TERMS + 1) / (2 * TERMS + 1)
    return (min(total, next_sum), max(total, next_sum))


# Machin: pi = 16 arctan(1/5) - 4 arctan(1/239).
PI = sub(scale(atan_small(Q(1, 5)), 16), scale(atan_small(Q(1, 239)), 4))
LAM = scale(PI, 1 / T)


def atan_nonnegative(r):
    assert r >= 0
    if r > 1:
        return sub(scale(PI, Q(1, 2)), atan_nonnegative(1 / r))
    if r > Q(1, 2):
        return sub(scale(PI, Q(1, 4)), atan_small((1 - r) / (1 + r)))
    return atan_small(r)


def projective_angle(vector):
    """Angle in [0, pi) of the unoriented integer vector."""
    x, y = vector
    assert x or y
    if y < 0 or (y == 0 and x < 0):
        x, y = -x, -y
    if x == 0:
        return scale(PI, Q(1, 2))
    if x > 0:
        return atan_nonnegative(Q(y, x))
    return sub(PI, atan_nonnegative(Q(y, -x)))


def mod_pi(a):
    # A proposed period is selected rationally; the two strict inequalities
    # then prove that it works for every real value in both enclosures.
    middle_ratio = (a[0] + a[1]) / (PI[0] + PI[1])
    period = middle_ratio.numerator // middle_ratio.denominator
    result = sub(a, scale(PI, period))
    assert 0 < result[0] <= result[1] < PI[0], (period, result)
    return result


def vector(a, b):
    return (POINTS[b][0] - POINTS[a][0], POINTS[b][1] - POINTS[a][1])


def check_angle_cap():
    checked = 0
    for centre in range(6):
        for a, b in combinations((i for i in range(6) if i != centre), 2):
            u, v = vector(centre, a), vector(centre, b)
            dot = u[0] * v[0] + u[1] * v[1]
            det = abs(u[0] * v[1] - u[1] * v[0])
            assert det > 0  # Also certifies that no triple is collinear.
            if dot < 0:
                # angle = pi - arctan(|det| / -dot) < pi - lambda.
                assert atan_nonnegative(Q(det, -dot))[0] > LAM[1]
            else:
                # The angle is <= pi/2, and lambda < pi/2 since T>2.
                assert T > 2
            checked += 1
    assert checked == 60
    return checked


def check_phase_cells():
    edges = list(combinations(range(6), 2))
    angles = {e: projective_angle(vector(*e)) for e in edges}
    events = [(mod_pi(sub(angles[e], scale(LAM, j))), e, j)
              for e in edges for j in range(4)]
    events.sort(key=lambda row: row[0][0])
    assert len(events) == 60
    assert all(events[k][0][1] < events[k + 1][0][0] for k in range(59))

    full_sets = []
    for k, (bounds, edge, boundary) in enumerate(events):
        # The last cell crosses phase zero.  Its part below pi suffices,
        # since there is no event at zero and all bins are pi-periodic.
        right = events[k + 1][0][0] if k + 1 < len(events) else PI[0]
        phase = (bounds[1] + right) / 2
        masks = [0] * 6
        for e in edges:
            angle = mod_pi(sub(angles[e], (phase, phase)))
            lower, upper = angle[0] / LAM[1], angle[1] / LAM[0]
            lo_bin = lower.numerator // lower.denominator
            hi_bin = upper.numerator // upper.denominator
            assert lo_bin == hi_bin and 0 <= lo_bin <= 3
            for v in e:
                masks[v] |= 1 << lo_bin
        full = tuple(v for v, mask in enumerate(masks) if mask == 15)
        assert len(full) >= 2
        full_sets.append(full)
        print(f"{k + 1:02d} event={edge[0]}{edge[1]}:{boundary} "
              f"full_after={''.join(map(str, full))}")

    # At an isolated event theta_e - phase = j*lambda (mod pi), the
    # half-open bin at the event equals the bin immediately BEFORE it:
    # j for j=1,2,3, and 0 for j=0 (the wrap 0 -> 3).  All other edges
    # stay fixed because event enclosures are disjoint.  Thus endpoint
    # full sets are exactly those of the preceding open cells.
    return len(events), min(map(len, full_sets)), max(map(len, full_sets))


if __name__ == "__main__":
    assert len(set(POINTS)) == 6 and 3 < T < Q(7, 2)
    angles_checked = check_angle_cap()
    cells, minimum, maximum = check_phase_cells()
    print(f"PASS: {angles_checked} strict angle checks; {cells} disjoint event "
          f"enclosures; full counts {minimum}..{maximum} in every open cell.")
    print("Every event inherits its preceding cell by the half-open convention.")
    print("Scope: exact rational interval certificate, NOT a Lean theorem.")
