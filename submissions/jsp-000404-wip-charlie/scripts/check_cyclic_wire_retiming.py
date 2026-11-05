"""Exact checks of cyclic projection-wire retiming on deterministic point sets.

Uses only the Python standard library. The output checks finite examples and
does not certify the proposed arbitrary-size geometric construction in Lean.
"""

import argparse
import json
import random
from collections import Counter
from fractions import Fraction
from itertools import combinations
from pathlib import Path


def determinant(a, b, c):
    return ((b[0] - a[0]) * (c[1] - a[1])
            - (b[1] - a[1]) * (c[0] - a[0]))


def wire_graph(points):
    assert len(set(map(tuple, points))) == len(points)
    assert all(determinant(*triple) for triple in combinations(points, 3))
    scale = 1 + 2 * max(abs(y) for _, y in points)
    # A scaled rotation gives a generic initial projection with exact integers.
    rotated = [(scale*x + y, -x + scale*y) for x, y in points]
    order = sorted(range(len(points)), key=lambda i: rotated[i][0])
    coordinates = [rotated[i] for i in order]
    assert len({x for x, _ in coordinates}) == len(coordinates)
    pairs = list(combinations(range(len(points)), 2))
    slopes = [Fraction(coordinates[j][1] - coordinates[i][1],
                       coordinates[j][0] - coordinates[i][0]) for i, j in pairs]
    arcs = []
    for point in range(len(points)):
        incident = sorted((index for index, pair in enumerate(pairs) if point in pair),
                          key=lambda index: slopes[index])
        assert len({slopes[index] for index in incident}) == len(incident)
        for position, first in enumerate(incident):
            second = incident[(position + 1) % len(incident)]
            wrap = int(position == len(incident) - 1)
            same_sign = (pairs[first][0] == point) == (pairs[second][0] == point)
            delay = int(same_sign if wrap else not same_sign)
            arcs.append((first, second, wrap, delay))
    return order, pairs, arcs


def feasible(vertices, arcs, numerator, denominator):
    """Return exact integer potentials or an explicit negative cycle."""
    potentials = [0] * vertices
    predecessor = [None] * vertices
    for _ in range(vertices):
        changed = None
        for index, (first, second, wrap, delay) in enumerate(arcs):
            bound = wrap*numerator - delay*denominator
            candidate = potentials[second] + bound
            if potentials[first] > candidate:
                potentials[first] = candidate
                predecessor[first] = index
                changed = first
        if changed is None:
            assert all(potentials[second] - potentials[first] + wrap*numerator
                       >= delay*denominator for first, second, wrap, delay in arcs)
            return potentials, None
    vertex = changed
    for _ in range(vertices):
        vertex = arcs[predecessor[vertex]][1]
    start = vertex
    cycle = []
    while True:
        index = predecessor[vertex]
        cycle.append(index)
        vertex = arcs[index][1]
        if vertex == start:
            break
    assert sum(arcs[index][2]*numerator - arcs[index][3]*denominator
               for index in cycle) < 0
    return None, cycle


def optimum_half_period(vertices, arcs, point_count):
    lower, upper = 1, 2*point_count + 2
    assert feasible(vertices, arcs, upper, 2)[0] is not None
    while upper - lower > 1:
        middle = (lower + upper) // 2
        if feasible(vertices, arcs, middle, 2)[0] is None:
            lower = middle
        else:
            upper = middle
    # Every simple cycle uses at most vertices arcs. This perturbation is
    # smaller than the gap from a half-integer to any distinct cycle ratio.
    scale = vertices + 1
    below, cycle = feasible(vertices, arcs, upper*scale - 1, 2*scale)
    assert below is None, 'A non-half-integral cyclic optimum needs investigation'
    winding = sum(arcs[index][2] for index in cycle)
    delay = sum(arcs[index][3] for index in cycle)
    assert winding in (1, 2)
    assert Fraction(delay, winding) == Fraction(upper, 2)
    potentials, _ = feasible(vertices, arcs, upper, 2)
    assert potentials is not None
    return upper, potentials, cycle


def enumerate_cycle_windings(vertices, arcs):
    outgoing = [[] for _ in range(vertices)]
    for first, second, wrap, _ in arcs:
        outgoing[first].append((second, wrap))
    counts = Counter()
    for start in range(vertices):
        stack = [(start, 1 << start, 0)]
        while stack:
            vertex, visited, winding = stack.pop()
            for target, wrap in outgoing[vertex]:
                if target == start:
                    counts[winding + wrap] += 1
                    assert winding + wrap in (1, 2)
                elif target > start and not (visited >> target & 1):
                    stack.append((target, visited | (1 << target), winding + wrap))
    return dict(sorted(counts.items()))


def check(points, enumerate_cycles):
    initial_order, pairs, arcs = wire_graph(points)
    doubled_period, potentials, critical_cycle = optimum_half_period(
        len(pairs), arcs, len(points))
    period = Fraction(doubled_period, 2)
    preceding = {i: set() for i in range(len(points))}
    directions = {}
    for (first, second), potential in zip(pairs, potentials):
        # The cut at 1/4 avoids every terminal half-grid event.
        turns = (2*potential - 1) // (2*doubled_period)
        lower, upper = (first, second) if turns % 2 == 0 else (second, first)
        preceding[upper].add(lower)
        directions[first, second] = Fraction((2*potential - 1) % (2*doubled_period), 4)
    order = sorted(range(len(points)), key=lambda i: len(preceding[i]))
    assert [len(preceding[i]) for i in order] == list(range(len(points)))
    assert all(first in preceding[second] for first, second in combinations(order, 2))

    def direction(first, second):
        return directions[min(first, second), max(first, second)]

    for first, middle, last in combinations(order, 3):
        a = direction(first, middle)
        b = direction(first, last)
        c = direction(middle, last)
        assert min(a, c) <= b <= max(a, c)
        assert abs(c - a) >= 1
        assert abs(b - a) <= period - 1 and abs(c - b) <= period - 1
    bands = (doubled_period + 1) // 2
    integer_times, _ = feasible(len(pairs), arcs, bands, 1)
    assert integer_times is not None
    words = []
    for point in range(len(points)):
        specified = {}
        for (first, second), time in zip(pairs, integer_times):
            if point not in (first, second):
                continue
            band = time % bands
            sign = (point == first) ^ bool((time // bands) % 2)
            assert band not in specified or specified[band] == sign
            specified[band] = sign
        words.append(tuple(specified.get(band, False) for band in range(bands)))
    assert len(set(words)) == len(points)
    assert len(points) <= 2 ** bands
    cycle_counts = enumerate_cycle_windings(len(pairs), arcs) if enumerate_cycles else None
    return dict(points=points, period=str(period), initial_order=initial_order,
                retimed_order=order, doubled_potentials=potentials,
                critical_cycle_arcs=critical_cycle, cycle_windings=cycle_counts)


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--count', type=int, default=60)
    parser.add_argument('--seed', type=int, default=504506)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    generator = random.Random(args.seed)
    examples = []
    while len(examples) < args.count:
        size = generator.randint(3, 16)
        points = [(generator.randrange(-100000, 100001),
                   generator.randrange(-100000, 100001)) for _ in range(size)]
        if all(determinant(*triple) for triple in combinations(points, 3)):
            examples.append(points)
    project = Path(__file__).resolve().parent.parent
    affine_cover = project / 'verification' / 'affine-partition-20261105' / 'cover.json'
    examples.append(json.loads(affine_cover.read_text(encoding='utf-8'))['points'])
    results = [check(points, enumerate_cycles=(len(points) <= 8)) for points in examples]
    total_cycles = sum(sum(item['cycle_windings'].values()) for item in results
                       if item['cycle_windings'] is not None)
    print(f'PASS: {len(results)} cyclic optima have an exact half-integer cycle certificate.')
    print('PASS: every exact potential array retains a total cut order and all triangle inequalities.')
    print('PASS: integral-period endpoint signs give consistent, distinct Boolean words.')
    print(f'PASS: all {total_cycles} enumerated simple cycles have winding one or two.')
    print(f'The twenty-point affine obstruction has cyclic optimum {results[-1]["period"]}.')
    print('These finite checks do not replace the general embedded-cycle and retiming proof.')
    if args.output:
        payload = dict(seed=args.seed, random_count=args.count, results=results)
        args.output.write_text(json.dumps(payload, indent=2) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
