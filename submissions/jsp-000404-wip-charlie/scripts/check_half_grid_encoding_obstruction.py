"""Exhaust all graphs for a fixed-sign encoding obstruction and verify its retiming repair."""

import json
from itertools import combinations
from pathlib import Path

from check_half_grid_independent_encoding import check_example


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    path = Path('verification/independent-encoding-obstruction-20261105/counterexample.json')
    data = json.loads(path.read_text(encoding='utf-8'))
    size, period = data['size'], data['doubled_period']
    assert size == 9 and period == 7
    pairs = list(combinations(range(size), 2))
    times = dict(zip(pairs, data['times']))
    assert len(times) == len(data['times']) == 36
    assert all(type(value) is int and 0 <= value < period for value in times.values())
    for i, j, k in combinations(range(size), 3):
        a, b, c = times[i, j], times[i, k], times[j, k]
        assert min(a, c) <= b <= max(a, c)
        assert abs(a - c) >= 2
        assert abs(a - b) <= period - 2 and abs(b - c) <= period - 2

    order, seen, previous = list(range(size)), set(), -1
    rank = {}
    for index, (time, i, j) in enumerate(data['events']):
        assert i < j and (i, j) not in seen and times[i, j] == time
        assert previous <= time
        previous = time
        left, right = order.index(i), order.index(j)
        assert abs(left - right) == 1
        order[left], order[right] = order[right], order[left]
        seen.add((i, j))
        rank[i, j] = index
    assert seen == set(pairs) and order == list(reversed(range(size)))
    positive, negative = [0] * size, [0] * size
    for (i, j), time in times.items():
        plus, minus = (i, j) if time % 2 == 0 else (j, i)
        positive[plus] |= 1 << time
        negative[minus] |= 1 << time
    assert list(map(list, zip(positive, negative))) == data['rows']
    assert all(p & n == 0 for p, n in zip(positive, negative))
    print('PASS all 84 triangle constraints and the 36-event adjacent-swap reversal')

    total_graphs, total_triangle_free = 0, 0
    for flip in range(1 << period):
        rows = [((p & ~flip) | (n & flip), (n & ~flip) | (p & flip))
                for p, n in zip(positive, negative)]
        allowed = [(i, j) for i, j in combinations(range(period), 2)
                   if all(not (p >> i & 1 and p >> j & 1) for p, _ in rows)]
        triangle_free_count = 0
        for mask in range(1 << len(allowed)):
            edges = {allowed[i] for i in range(len(allowed)) if mask >> i & 1}
            if any((i, j) in edges and (i, k) in edges and (j, k) in edges
                   for i, j, k in combinations(range(period), 3)):
                continue
            triangle_free_count += 1
            neighbors = [set() for _ in range(period)]
            for i, j in edges:
                neighbors[i].add(j)
                neighbors[j].add(i)
            independent = [code for code in range(1 << period)
                           if all(not (code >> i & 1 and code >> j & 1) for i, j in edges)]
            maximal = [code for code in independent
                       if all(code >> i & 1 or any(code >> j & 1 for j in neighbors[i])
                              for i in range(period))]
            assert any(not any(code & p == p and code & n == 0 for code in maximal)
                       for p, n in rows), 'A valid encoding would refute this certificate'
        total_graphs += 1 << len(allowed)
        total_triangle_free += triangle_free_count
        if flip in (0, (1 << period) - 1):
            print(f'PASS polarity mask {flip}: all {1 << len(allowed)} allowed-edge subgraphs, '
                  f'{triangle_free_count} triangle-free graphs, zero encodings')
    assert data['exhaustion'] == dict(polarities=1 << period, graph_choices=total_graphs,
                                      triangle_free_choices=total_triangle_free)
    print(f'PASS all {1 << period} coordinate polarity choices, {total_graphs} graph choices, '
          f'{total_triangle_free} triangle-free choices, zero encodings')

    repair = data['canonical_retiming']
    repaired_times = dict(zip(pairs, repair['times']))
    for vertex in range(size):
        incident = sorted((pair for pair in pairs if vertex in pair), key=rank.__getitem__)
        for position, first in enumerate(incident):
            last = incident[(position + 1) % len(incident)]
            wrap = int(position == len(incident) - 1)
            same = (first[0] == vertex) == (last[0] == vertex)
            delay = int(same if wrap else not same)
            assert repaired_times[last] - repaired_times[first] + wrap * period >= 2 * delay
    check_example(repair)
    print('PASS the same cyclic wire order has a sign-preserving encoding after retiming')
    print('The fixed-schedule representation fails. The prior-retiming version remains open.')


if __name__ == '__main__':
    main()
