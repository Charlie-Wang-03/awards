"""Exact-rational feasibility of ordered direction models with a narrow observer."""

import argparse
import json
import sys
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'artifacts' / 'python-deps'))
import z3


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('n', type=int)
    ap.add_argument('residual', type=int)
    ap.add_argument('--delta', default='99/100')
    ap.add_argument('--timeout', type=int, default=60)
    ap.add_argument('--out', type=Path)
    args = ap.parse_args()
    size = args.residual + 1
    delta = z3.RealVal(args.delta)
    width = args.n + delta
    edge = {(i, j): z3.Real(f'd_{i}_{j}') for i, j in combinations(range(size), 2)}
    solver = z3.SolverFor('QF_RDL')
    solver.set(timeout=1000 * args.timeout)
    for value in edge.values():
        solver.add(value >= 0, value < width)
    for j in range(1, size):
        solver.add(edge[0, j] >= 0, edge[0, j] <= delta)
    for i, j, k in combinations(range(size), 3):
        left, long, right = edge[i, j], edge[i, k], edge[j, k]
        solver.add(z3.Or(
            z3.And(left < long, long < right, right - left >= 1,
                   long - left <= width - 1, right - long <= width - 1),
            z3.And(right < long, long < left, left - right >= 1,
                   left - long <= width - 1, long - right <= width - 1)))
    status = solver.check()
    result = dict(n=args.n, delta=args.delta, residual=args.residual,
                  status=str(status), z3=z3.get_version_string(),
                  scope='Abstract ordered directions; planar realization is an extra obligation')
    if status == z3.sat:
        model = solver.model()
        result['directions'] = {f'{i},{j}': str(model[value]) for (i, j), value in edge.items()}
    if status == z3.unknown:
        result['reason'] = solver.reason_unknown()
    print(json.dumps(result, indent=2), flush=True)
    if args.out:
        args.out.write_text(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
