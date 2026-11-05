"""Exact finite checks for the 21-row half-grid coherence obstruction.

Integer geometry uses one angular unit of twenty degrees. The continuous
epsilon argument is written in DIRECTION_ORDER_RESEARCH.md.
"""

from itertools import combinations, permutations, product


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    period = 18
    a = {1, 2, 7, 8, 13, 14}
    b = {3, 4, 9, 10, 15, 16}
    c = {0, 5, 6, 11, 12, 17}
    satellite = {1, 5, 6, 7, 8, 12}

    def rotated(row, amount):
        return {(x + amount) % period for x in row}

    rows = [a, b, c] + [rotated(satellite, 2*r) for r in range(9)]
    rows += [{(1 + 2*r + j) % period for j in range(8)} for r in range(9)]
    assert len(rows) == len({tuple(sorted(row)) for row in rows}) == 21
    assert all(min((x-y) % period, (y-x) % period) <= 7
               for row in rows for x, y in combinations(row, 2))
    options = {(i, j): rows[i] & rotated(rows[j], 9)
               for i, j in permutations(range(21), 2)}
    assert all(options.values())

    def largest_gap(values):
        x, y, z = sorted(values)
        return max(y-x, z-y, x+period-z)

    assert all(min(largest_gap(values) for values in
                   product(options[i, j], options[j, k], options[k, i])) <= 9
               for i, j, k in combinations(range(21), 3))
    inner_choices = list(product(options[0, 1], options[1, 2], options[2, 0]))
    valid = {values for values in inner_choices if largest_gap(values) < 9}
    assert len(inner_choices) == 27 and len(valid) == 9
    assert all(largest_gap(values) >= 10 for values in inner_choices if values not in valid)
    orbit = set()
    values = (1, 3, 11)
    for rotation in range(9):
        orbit.add(values)
        first, second, third = rotation % 3, (rotation+1) % 3, (rotation+2) % 3
        observer = 3+rotation
        cycle = [observer, first, second, third, observer]
        bearings = [(value + 2*rotation) % period for value in (5, 1, 3, 17)]
        assert options[observer, first] == {bearings[0]}
        assert options[third, observer] == {bearings[3]}
        assert bearings[1] in options[first, second] and bearings[2] in options[second, third]
        axis = (2+2*rotation) % period
        assert all(min((value-axis) % period, (axis-value) % period) <= 3 for value in bearings)
        assert len(set(cycle[:-1])) == 4
        values = ((values[2]+2) % period, (values[0]+2) % period, (values[1]+2) % period)
    assert orbit == valid and values == (1, 3, 11)

    for cut in range(period):
        edges = {(i, j) for (i, j), values in options.items()
                 if all(0 < ((2*value-(2*cut+1)) % 36) < 18 for value in values)}
        remaining = set(range(21))
        while remaining:
            sources = {i for i in remaining if all((j, i) not in edges for j in remaining)}
            assert sources
            remaining -= sources
    print('PASS: 21 integer rows, diameter <=7, and all 210 antipodal pair conditions.')
    print('PASS: every triple has a cyclic bearing choice with maximal gap <=9.')
    print('PASS: 27 inner choices split into 18 semicircle obstructions and nine conditional four-cycles.')
    print('PASS: all 18 unconditional forced-projection graphs are acyclic.')
    print('Continuous conclusion: individually realizable triples but no joint realization after any')
    print('row-run expansion by epsilon with 0<epsilon<10 degrees. Full Lean geometry is pending.')


if __name__ == '__main__':
    main()
