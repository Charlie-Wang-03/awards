"""Verify finite coherent schedules and maximal-independent-set encoding certificates.

Only the Python standard library is used. Universal existence of these encodings
remains a research conjecture. These finite checks are outside the Lean proof chain.
"""

import argparse
import json
from itertools import combinations
from pathlib import Path


def check_example(data):
    size, period = data['size'], data['doubled_period']
    assert 5 <= period <= 15 and period % 2 == 1
    pairs = list(combinations(range(size), 2))
    times = data['times']
    assert len(times) == len(pairs) and all(type(value) is int for value in times)
    before = [set() for _ in range(size)]
    phase = {}
    positive, negative = [0] * size, [0] * size
    for (i, j), time in zip(pairs, times):
        turns, slot = divmod(time, period)
        first, last = (i, j) if turns % 2 == 0 else (j, i)
        before[last].add(first)
        phase[i, j] = slot
        first_sign = time % 2 == 0
        if data['flip']:
            first_sign = not first_sign
        plus, minus = (i, j) if first_sign else (j, i)
        positive[plus] |= 1 << slot
        negative[minus] |= 1 << slot

    order = sorted(range(size), key=lambda v: len(before[v]))
    assert [len(before[v]) for v in order] == list(range(size))
    assert all(i in before[j] for i, j in combinations(order, 2))

    def value(i, j):
        return phase[min(i, j), max(i, j)]

    for i, j, k in combinations(order, 3):
        a, b, c = value(i, j), value(i, k), value(j, k)
        assert min(a, c) <= b <= max(a, c)
        assert abs(a - c) >= 2
        assert abs(a - b) <= period - 2 and abs(b - c) <= period - 2

    current = order.copy()
    for slot in range(period):
        pending = {pair for pair in pairs if phase[pair] == slot}
        while pending:
            ready = next((pair for pair in sorted(pending)
                          if abs(current.index(pair[0]) - current.index(pair[1])) == 1), None)
            assert ready is not None, 'Event block has no adjacent-swap refinement'
            left, right = map(current.index, ready)
            current[left], current[right] = current[right], current[left]
            pending.remove(ready)
    assert current == list(reversed(order))

    assert all(p & n == 0 for p, n in zip(positive, negative))
    assert all(positive[i] & negative[j] or positive[j] & negative[i]
               for i, j in pairs)
    for mask in positive + negative:
        assert all(not (mask >> i & 1 and mask >> ((i + 1) % period) & 1)
                   for i in range(period))

    cycle, matching = data['cycle'], data['matching']
    assert len(cycle) >= 5 and len(cycle) % 2 == 1
    assert cycle == sorted(cycle)
    flattened = cycle + [v for pair in matching for v in pair]
    assert sorted(flattened) == list(range(period))
    assert all(len(pair) == 2 and pair[0] < pair[1] for pair in matching)
    remaining = list(range(period))
    pending = [tuple(pair) for pair in matching]
    while pending:
        ready = next((pair for pair in pending
                      if (remaining.index(pair[0]) - remaining.index(pair[1])) % len(remaining)
                      in (1, len(remaining) - 1)), None)
        assert ready is not None, 'Matching does not arise by cyclic adjacent-pair deletion'
        remaining = [v for v in remaining if v not in ready]
        pending.remove(ready)
    assert remaining == cycle

    edges = {tuple(sorted((cycle[i], cycle[(i + 1) % len(cycle)])))
             for i in range(len(cycle))}
    edges.update(map(tuple, matching))
    neighbors = [set() for _ in range(period)]
    for i, j in edges:
        neighbors[i].add(j)
        neighbors[j].add(i)
    assert all(len(row) <= 2 for row in neighbors)
    assert all(not (j in neighbors[i] and k in neighbors[i] and k in neighbors[j])
               for i, j, k in combinations(range(period), 3))

    def maximal_independent(mask):
        independent = all(not (mask >> i & 1 and mask >> j & 1) for i, j in edges)
        dominating = all(mask >> i & 1 or any(mask >> j & 1 for j in neighbors[i])
                         for i in range(period))
        return independent and dominating

    family = {mask for mask in range(1 << period) if maximal_independent(mask)}
    codes = data['codes']
    assert len(codes) == len(set(codes)) == size
    assert all(code in family and code & p == p and code & n == 0
               for code, p, n in zip(codes, positive, negative))
    assert len(family) == data['mis_count']
    assert size <= len(family) <= 5 * 2 ** ((period - 5) // 2)
    print(f"PASS {data['label']}: {size} wires, {len(pairs)} events, "
          f"{period} graph vertices, {len(family)} maximal independent sets")


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path, nargs='?',
                        default=Path('verification/independent-encoding-20261105/examples.json'))
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text(encoding='utf-8'))
    for example in data['examples']:
        check_example(example)
    print('Finite exact verification complete. The arbitrary-size encoding remains unproved.')


if __name__ == '__main__':
    main()
