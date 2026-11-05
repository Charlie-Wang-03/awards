"""Verify a coherent schedule whose active interval bits never extend after collapse.

All arithmetic and all colour searches are exact and use only the standard
library. Piecewise-affine threshold checks cover every real phase.
"""

import json
from fractions import Fraction
from itertools import combinations
from pathlib import Path


def data_at_phase(data, phase):
    period = data['period_quarters']
    order = data['initial_order'].copy()
    for event in data['events']:
        if event['time_quarters'] < phase:
            first, second = event['edge']
            a, b = order.index(first), order.index(second)
            assert abs(a - b) == 1
            order[a], order[b] = order[b], order[a]
    rank = {vertex: index for index, vertex in enumerate(order)}
    values, affine, forced = {}, {}, {}
    for event in data['events']:
        first, second = event['edge']
        time = Fraction(event['time_quarters'])
        turns = (time - phase) // period
        theta = time - phase - turns*period
        values[first, second] = max(Fraction(0), theta - 4)
        affine[first, second] = (0, 0) if theta < 4 else (time - turns*period - 4, -1)
        if theta < 4:
            lower, upper = (first, second) if rank[first] < rank[second] else (second, first)
            for vertex, bit in [(lower, False), (upper, True)]:
                assert vertex not in forced or forced[vertex] == bit
                forced[vertex] = bit

    def value(first, second):
        return values[min(first, second), max(first, second)]

    bad = []
    for first, middle, last in combinations(order, 3):
        a, b, c = value(first, middle), value(first, last), value(middle, last)
        assert min(a, c) <= b <= max(a, c)
        if abs(c - a) < 4 or abs(b - a) > period - 8 or abs(c - b) > period - 8:
            bad.append((first, middle, last))
    return order, affine, forced, bad


def colourings(size, forced, bad, different_pairs=()):
    valid = []
    for word in range(1 << size):
        bits = [bool(word >> i & 1) for i in range(size)]
        if any(bits[i] != bit for i, bit in forced.items()):
            continue
        if any(bits[i] == bits[j] for i, j in different_pairs):
            continue
        if all(len({bits[i], bits[j], bits[k]}) > 1 for i, j, k in bad):
            valid.append(word)
    return valid


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    project = Path(__file__).resolve().parent.parent
    data = json.loads((project / 'verification/forced-compression-20261105/witness.json')
                      .read_text(encoding='utf-8'))
    size, period = data['size'], data['period_quarters']
    assert size == 9 and period == 18
    pairs = list(combinations(range(size), 2))
    assert sorted(tuple(event['edge']) for event in data['events']) == pairs
    times = [event['time_quarters'] for event in data['events']]
    assert times == sorted(times) and all(0 < time < period for time in times)
    order = data['initial_order'].copy()
    assert sorted(order) == list(range(size))
    for event in data['events']:
        first, second = event['edge']
        a, b = order.index(first), order.index(second)
        assert abs(a - b) == 1
        order[a], order[b] = order[b], order[a]
    assert order == data['initial_order'][::-1]
    parent = {tuple(event['edge']): event['time_quarters'] for event in data['events']}
    for i, j, k in combinations(data['initial_order'], 3):
        a = parent[min(i, j), max(i, j)]
        b = parent[min(i, k), max(i, k)]
        c = parent[min(j, k), max(j, k)]
        assert min(a, c) <= b <= max(a, c)
        assert abs(c - a) >= 4
        assert abs(b - a) <= period - 4 and abs(c - b) <= period - 4

    # All mode-change and child-gap thresholds occur at odd integer phases.
    critical = [Fraction(0)] + [Fraction(i) for i in range(1, period, 2)] + [Fraction(period)]
    samples = [(phase, None) for phase in critical[:-1]]
    samples += [((left + right)/2, (left, right)) for left, right in zip(critical, critical[1:])]
    for phase, interval in samples:
        order, affine, forced, bad = data_at_phase(data, phase)
        assert not colourings(size, forced, bad), ('Unexpected extension', phase)
        active_edges = [event['edge'] for event in data['events']
                        if (Fraction(event['time_quarters']) - phase) % period < 4]
        assert not colourings(size, {}, bad, active_edges), ('Unexpected active-edge colouring', phase)
        if interval is None:
            continue
        left, right = interval
        for time in times:
            for turns in (-1, 0, 1):
                for boundary in (0, 4):
                    root = Fraction(time - turns*period - boundary)
                    assert not left < root < right
        for i, j, k in combinations(order, 3):
            edges = [(min(i, j), max(i, j)), (min(i, k), max(i, k)),
                     (min(j, k), max(j, k))]
            for first, second, threshold in [(0, 2, 4), (0, 1, period - 8),
                                             (1, 2, period - 8)]:
                a, b = affine[edges[first]], affine[edges[second]]
                constant, slope = a[0] - b[0], a[1] - b[1]
                if slope:
                    for target in (-threshold, threshold):
                        root = Fraction(target - constant, slope)
                        assert not left < root < right
    _, _, _, bad = data_at_phase(data, Fraction(0))
    free = colourings(size, {}, bad)
    assert free
    first = free[0]
    parts = [[i for i in range(size) if bool(first >> i & 1) == bit] for bit in (False, True)]
    print('PASS: nine wires, 36 adjacent swaps, reversed endpoint order, and all parent gaps.')
    print('PASS: all 512 colourings checked at each of 20 exact phase cases.')
    print('PASS: affine threshold checks cover every open phase interval.')
    print('PASS: allowing independent active-component flips still leaves no extension.')
    print('CONCLUSION: the prescribed active source/sink bits admit no unit-collapse extension at any phase.')
    print('A freely chosen colouring does work at phase zero:', parts)
    print('Scope: a coherent weak schedule at period 9/2. Full Lean certification is pending.')


if __name__ == '__main__':
    main()
