"""Check critical-root clocks that exclude every consecutive five-coordinate core.

The finite certificates use exact integers and the Python standard library.
They concern a proposed encoding restriction. Family B remains open.
"""

import json
from itertools import combinations
from pathlib import Path

from check_half_grid_independent_encoding import check_example


def check_witness(data):
    size, period = data['size'], data['doubled_period']
    pairs = list(combinations(range(size), 2))
    times = data['times']
    assert len(times) == len(pairs)
    assert all(type(time) is int and 0 <= time < period for time in times)
    pair_id = {pair: index for index, pair in enumerate(pairs)}
    order, rank, previous = list(range(size)), {}, -1
    for index, (phase, i, j) in enumerate(data['events']):
        event = pair_id[i, j]
        assert event not in rank and times[event] == phase and previous <= phase
        previous = phase
        left, right = order.index(i), order.index(j)
        assert abs(left - right) == 1
        order[left], order[right] = order[right], order[left]
        rank[event] = index
    assert len(rank) == len(pairs) and order == list(reversed(range(size)))

    arcs = []
    for vertex in range(size):
        incident = sorted((index for index, pair in enumerate(pairs) if vertex in pair),
                          key=rank.__getitem__)
        for position, source in enumerate(incident):
            target = incident[(position + 1) % len(incident)]
            wrap = int(position == len(incident) - 1)
            same = (pairs[source][0] == vertex) == (pairs[target][0] == vertex)
            arcs.append((source, target, wrap, int(same if wrap else not same)))
    assert all(times[u] <= times[v] + period * wrap - 2 * delay
               for u, v, wrap, delay in arcs)
    cycle = data['critical_cycle']
    assert cycle and len(set(cycle)) == len(cycle)
    assert len({arcs[edge][0] for edge in cycle}) == len(cycle)
    assert all(arcs[edge][1] == arcs[cycle[(i + 1) % len(cycle)]][0]
               for i, edge in enumerate(cycle))
    winding = sum(arcs[edge][2] for edge in cycle)
    delay = sum(arcs[edge][3] for edge in cycle)
    assert winding == 2 and delay == period
    root = data['root']
    assert root in {arcs[edge][0] for edge in cycle}
    assert len(data['tight_paths_to_root']) == len(pairs)
    for start, path in enumerate(data['tight_paths_to_root']):
        current = start
        for edge in path:
            u, v, wrap, lag = arcs[edge]
            assert current == u
            assert times[u] == times[v] + period * wrap - 2 * lag
            current = v
        assert current == root
    assert all(any(u == source and times[u] == times[v] + period * wrap - 2 * lag
                   for u, v, wrap, lag in arcs) for source in range(len(pairs)))
    print(f'PASS N={size}, q={period}: feasible clock, critical cycle with '
          f'winding {winding}, tight paths from every event to its root')

    positive, negative = [0] * size, [0] * size
    for (i, j), phase in zip(pairs, times):
        plus, minus = (i, j) if phase % 2 == 0 else (j, i)
        positive[plus] |= 1 << phase
        negative[minus] |= 1 << phase
    core_codes = [sum(1 << i for i in pair) for pair in combinations(range(5), 2)
                  if (pair[0] - pair[1]) % 5 in (2, 3)]
    assert len(core_codes) == 5
    for start in range(period):
        coordinates = [(start + i) % period for i in range(5)]
        mask = sum(1 << slot for slot in coordinates)
        codes = [sum(1 << slot for i, slot in enumerate(coordinates) if code >> i & 1)
                 for code in core_codes]
        for flip in (False, True):
            rows = list(zip(negative, positive) if flip else zip(positive, negative))
            assert any(not any(code & p == p & mask and code & n == 0 for code in codes)
                       for p, n in rows)
    print(f'PASS N={size}, q={period}: all {2 * period} consecutive-core/polarity choices fail')
    encoding = data['sparse_core_encoding']
    assert encoding['size'] == size and encoding['doubled_period'] == period
    assert encoding['times'] == times and len(encoding['cycle']) == 5
    check_example(encoding)


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    path = Path('verification/critical-clock-core-20261105/witnesses.json')
    data = json.loads(path.read_text(encoding='utf-8'))
    for witness in data['witnesses']:
        check_witness(witness)
    print('The consecutive-core restriction fails for critical-root clocks.')
    print('The general choice of a core and the original family-B bound remain open.')


if __name__ == '__main__':
    main()
