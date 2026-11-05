"""Exclude projection-separated width-drop retimings of the retained twenty-point order.

The checker constructs the actual rational projection sweep. Each excluded
child has an explicit negative cycle for its cyclic difference constraints.
An unrestricted two-colour partition is also checked to remain feasible.
"""

import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

from check_cyclic_wire_retiming import feasible, wire_graph


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    points = json.loads(Path('verification/affine-partition-20261105/cover.json').read_text())['points']
    initial, pairs, parent_arcs = wire_graph(points)
    assert len(points) == 20
    parent, _ = feasible(len(pairs), parent_arcs, 9, 2)
    assert parent is not None
    scale = 1 + 2 * max(abs(y) for _, y in points)
    rotated = [(scale * x + y, -x + scale * y) for x, y in points]
    coordinates = [rotated[i] for i in initial]
    slopes = [Fraction(coordinates[j][1] - coordinates[i][1],
                       coordinates[j][0] - coordinates[i][0]) for i, j in pairs]
    event_order = sorted(range(len(pairs)), key=lambda event: (slopes[event], pairs[event]))
    rank = {event: i for i, event in enumerate(event_order)}
    full = (1 << 20) - 1
    permutation, partitions = list(range(20)), set()
    for length in range(1, 20):
        mask = (1 << length) - 1
        partitions.add(min(mask, full ^ mask))
    for event in event_order:
        left, right = map(permutation.index, pairs[event])
        assert abs(left - right) == 1
        permutation[left], permutation[right] = permutation[right], permutation[left]
        mask = sum(1 << v for v in permutation[:min(left, right) + 1])
        partitions.add(min(mask, full ^ mask))
    assert permutation == list(reversed(range(20))) and len(partitions) == 190
    cache = {}
    obstructions = Counter()

    def check_child(mask):
        if mask in cache:
            return cache[mask]
        vertices = [v for v in range(20) if mask >> v & 1]
        if len(vertices) <= 2:
            cache[mask] = True
            return True
        events = [e for e, pair in enumerate(pairs) if all(mask >> v & 1 for v in pair)]
        local = {event: i for i, event in enumerate(events)}
        arcs = []
        for vertex in vertices:
            incident = sorted((e for e in events if vertex in pairs[e]), key=rank.__getitem__)
            for position, first in enumerate(incident):
                last = incident[(position + 1) % len(incident)]
                wrap = int(position == len(incident) - 1)
                same = (pairs[first][0] == vertex) == (pairs[last][0] == vertex)
                arcs.append((local[first], local[last], wrap, int(same if wrap else not same)))
        potential, cycle = feasible(len(events), arcs, 18, 5)
        if potential is None:
            assert cycle
            for index, edge in enumerate(cycle):
                assert arcs[edge][1] == arcs[cycle[(index + 1) % len(cycle)]][0]
            winding = sum(arcs[e][2] for e in cycle)
            delay = sum(arcs[e][3] for e in cycle)
            assert winding in (1, 2) and 18 * winding < 5 * delay
            obstructions[Fraction(delay, winding)] += 1
        cache[mask] = potential is not None
        return cache[mask]

    for mask in sorted(partitions):
        assert not (check_child(mask) and check_child(full ^ mask))
    print('PASS actual rational projection sweep and all 190 separated bipartitions')
    print('PASS each separated bipartition has a child with an exact negative cycle at width 18/5')
    print('Negative-cycle ratios among checked children', dict(sorted(obstructions.items())))

    original_part = {0, 3, 5, 7, 9, 11, 13, 14, 17, 19}
    mask = sum(1 << v for v in range(20) if initial[v] in original_part)
    assert mask.bit_count() == 10
    assert min(mask, full ^ mask) not in partitions
    assert check_child(mask) and check_child(full ^ mask)
    print('PASS a non-separated ten-plus-ten partition has feasible independent child retimings')
    print('Finite order-based obstruction. Universal unrestricted partition and original B remain open.')


if __name__ == '__main__':
    main()
