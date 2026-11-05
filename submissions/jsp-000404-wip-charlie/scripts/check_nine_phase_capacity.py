"""Exhaustively check the finite nine-phase capacity argument, without SAT.

This verifies the complete finite row model independently of Lean. The actual
geometric bridge is proved separately in OrderedNinePhase and PlanarNinePhaseThreshold.
"""

import argparse
import json
from itertools import combinations, permutations, product
from pathlib import Path


SLOTS = [73, 83, 85, 101, 107, 146, 149, 153, 165, 166, 169, 170, 171, 173,
         179, 181, 202, 205, 213, 214, 219, 292, 297, 298, 306, 309, 330,
         332, 338, 340, 341, 342, 345, 346, 358, 362, 365, 404, 410, 426, 428, 438]
CORE = [(292, 146), (69, 274), (41, 148), (328, 162), (73, 292)]


def indexed_catalog():
    """The fixed hole-order indexing used by the Lean constants."""
    result = []
    for holes in range(512):
        if holes.bit_count() % 2 != 1:
            continue
        if any(holes >> i & 1 and holes >> ((i + 1) % 9) & 1 for i in range(9)):
            continue
        occupied = [i for i in range(9) if not holes >> i & 1]
        positive = sum(1 << i for position, i in enumerate(occupied) if position % 2 == 0)
        negative = 511 ^ holes ^ positive
        result.extend([(positive, negative), (negative, positive)])
    return result


def valid(row):
    return all(row[i] == 0 or row[(i + 1) % 9] == 0 or row[i] != row[(i + 1) % 9]
               for i in range(9))


def maximal(row):
    for i, value in enumerate(row):
        if value:
            continue
        for replacement in (1, 2):
            candidate = list(row)
            candidate[i] = replacement
            if valid(candidate):
                return False
    return True


def masks(row):
    return tuple(sum(1 << i for i, value in enumerate(row) if value == bit) for bit in (1, 2))


def separated(left, right):
    return bool(left[0] & right[1] or left[1] & right[0])


def shared_phases(left, right):
    return [i for i in range(9) if ((left[0] & right[1]) | (left[1] & right[0])) >> i & 1]


def coherent_triple(rows, vertices, times):
    before = {}
    for a, b in combinations(vertices, 2):
        phase = times[a, b]
        before[a, b] = bool(rows[a][0] >> phase & 1) == (phase % 2 == 0)
        before[b, a] = not before[a, b]
    for i, j, k in permutations(vertices):
        if before[i, j] and before[j, k] and before[i, k]:
            a, b, c = [times[tuple(sorted(edge))] for edge in [(i, j), (i, k), (j, k)]]
            return min(a, c) <= b <= max(a, c)
    return False


def check_core(core):
    pairs = list(combinations(range(5), 2))
    domains = [shared_phases(core[a], core[b]) for a, b in pairs]
    assignments = 0
    for values in product(*domains):
        assignments += 1
        times = dict(zip(pairs, values))
        assert any(not coherent_triple(core, triple, times) for triple in combinations(range(5), 3))
    assert assignments == 3
    return dict(rows=core, assignments=assignments, domains=domains)


def check():
    proper = [row for row in product(range(3), repeat=9) if valid(row)]
    rows = sorted(masks(row) for row in proper if maximal(row))
    assert len(rows) == 78 and len(set(rows)) == 78
    assert sorted(indexed_catalog()) == rows
    assert len(SLOTS) == len(set(SLOTS)) == 42
    supports = [sum(1 << j for j, word in enumerate(SLOTS)
                    if word & p == p and word & n == 0) for p, n in rows]
    assert all(mask.bit_count() == 2 for mask in supports)
    # Finite inclusion-maximal extension is also checked constructively.
    for row in proper:
        extended = list(row)
        for i in range(9):
            if extended[i]:
                continue
            for value in (1, 2):
                candidate = extended[:]
                candidate[i] = value
                if valid(candidate):
                    extended = candidate
                    break
        assert maximal(extended) and masks(extended) in rows
        assert all(value == 0 or value == extended[i] for i, value in enumerate(row))
    bad_cores = [set(CORE), {(n, p) for p, n in CORE}]
    core_checks = [check_core(CORE), check_core([(n, p) for p, n in CORE])]
    by_slot = [sum(1 << i for i, support in enumerate(supports) if support >> j & 1)
               for j in range(42)]
    conflicts = [sum(1 << j for j, other in enumerate(rows)
                     if not separated(row, other) or supports[i] & supports[j])
                 for i, row in enumerate(rows)]
    nodes = 0
    solutions = []

    def search(covered, remaining, selected):
        nonlocal nodes
        nodes += 1
        if covered == (1 << 42) - 1:
            assert len(selected) == 21
            family = {rows[i] for i in selected}
            assert any(core <= family for core in bad_cores)
            solutions.append(sorted(selected))
            return
        options = min((by_slot[j] & remaining for j in range(42) if not covered >> j & 1),
                      key=int.bit_count)
        while options:
            bit = options & -options
            options ^= bit
            i = bit.bit_length() - 1
            search(covered | supports[i], remaining & ~conflicts[i], selected + [i])

    search(0, (1 << len(rows)) - 1, [])
    assert len(solutions) == len({tuple(s) for s in solutions}) == 4
    return dict(status='PASS', partial_rows_tested=3**9, proper_rows=len(proper),
                maximal_rows=len(rows), cover_slots=len(SLOTS), coverage_per_maximal_row=2,
                equality_search_nodes=nodes, equality_families=len(solutions),
                core_checks=core_checks, rows=rows, families=solutions,
                scope='Independent finite coherent-row capacity check; geometric bridge in Lean')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ('rows', 'families', 'core_checks')},
                     indent=2))
