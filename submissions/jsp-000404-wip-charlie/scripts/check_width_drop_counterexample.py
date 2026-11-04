"""Exact integer certificate for WIDTH_DROP_PARTITION_COUNTEREXAMPLE.md.

This is a diagnostic certificate checker, not a Lean proof or the main theorem.
Only Python's integer arithmetic is used. The final check concerns the
four-bit colouring obstruction; its Euclidean realization is proved in
the companion document, not by this program.
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
        # Stronger lower bound on the obtuse angle, used at t=15/4.
        assert 81 * uu * vv < 400 * d * d
        assert 49 * d * d < 16 * uu * vv
        print("".join(map(str, triple)), j, d, uu, vv)

    assert 5 * 49**2 < 117**2
    assert 5 * 5**2 < 13**2
    assignments = list(product((0, 1), repeat=5))
    for colours in assignments:
        assert any(len({colours[i] for i in triple}) == 1 for triple in triples)
    print("PASS: 10 exact angle certificates; all 32 partitions have a bad triple.")
    print("The strengthened cosine bound also certifies the upper-strip witness at t=15/4.")


def four_bit_partition_certificate():
    def first_difference(x, y):
        assert x != y
        return 4 - (x ^ y).bit_length()

    bad_masks = []
    for a, b, c in combinations(range(16), 3):
        levels = sorted({first_difference(a, b), first_difference(a, c),
                         first_difference(b, c)})
        assert len(levels) == 2
        if levels in ([0, 1], [2, 3]):
            bad_masks.append((1 << a) | (1 << b) | (1 << c))
    assert len(bad_masks) == 272
    for colouring in range(1 << 16):
        assert any((colouring & edge) in (0, edge) for edge in bad_masks), colouring
    # The explicit algebraic instance uses angular error < 1/49 < pi/68,
    # where the last inequality follows from pi > 3 and this integer check.
    assert 68 < 3 * 49
    print("PASS: 272 designated four-bit triples; all 65536 partitions have a bad triple.")
    print("The angle bounds and the family for every t>4 are written proofs, not numerical tests.")


if __name__ == "__main__":
    certificate()
    four_bit_partition_certificate()
    print("Not a Lean proof and not a solution of JSP-000404.")
