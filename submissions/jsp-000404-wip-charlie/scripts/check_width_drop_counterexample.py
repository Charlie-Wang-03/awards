"""Exact integer certificate for WIDTH_DROP_PARTITION_COUNTEREXAMPLE.md.

This is a diagnostic certificate checker, not a Lean proof or the main theorem.
Only Python's integer arithmetic is used.
"""

from itertools import combinations, product


POINTS = [
    (-10297, -505),
    (-10303, -495),
    (-9697, 495),
    (-9703, 505),
    (9703, -505),
]

WITNESS_VERTEX = [1, 1, 0, 2, 2, 3, 2, 2, 3, 2]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def certificate():
    assert len(set(POINTS)) == 5
    triples = list(combinations(range(5), 3))
    for triple, j in zip(triples, WITNESS_VERTEX):
        i, k = [index for index in triple if index != j]
        u = tuple(POINTS[i][q] - POINTS[j][q] for q in (0, 1))
        v = tuple(POINTS[k][q] - POINTS[j][q] for q in (0, 1))
        d, uu, vv = dot(u, v), dot(u, u), dot(v, v)
        assert uu > 0 and vv > 0 and d < 0
        assert 4 * uu * vv < 25 * d * d
        assert 49 * d * d < 16 * uu * vv
        print("".join(map(str, triple)), j, d, uu, vv)

    assert 5 * 49**2 < 117**2
    assert 5 * 5**2 < 13**2
    assignments = list(product((0, 1), repeat=5))
    for colours in assignments:
        assert any(len({colours[i] for i in triple}) == 1 for triple in triples)
    print("PASS: 10 exact angle certificates; all 32 partitions have a bad triple.")
    print("Not a Lean proof and not a solution of JSP-000404.")


if __name__ == "__main__":
    certificate()
