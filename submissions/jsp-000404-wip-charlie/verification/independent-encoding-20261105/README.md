# Independent-set encoding research certificates

This continuation follows `449be4d2f099c853ea1f1e052456101b4106ace6`, which
contains the completed family-A Lean proof and its focused audit. The
first-threshold hash manifest is anchored to that immutable commit.

`examples.json` contains four coherent half-grid schedules and graph codes.
`check_half_grid_independent_encoding.py` verifies them using exact integer
arithmetic and exhaustive finite graph enumeration. It passed with exit 0
under Python 3.12.13. Its output is retained in `check.log`.

The checked properties include all parent triple inequalities, a complete
adjacent-swap reversal refinement, consistent cyclic signed rows, the
adjacent-pair deletion construction of the graph, triangle-freeness,
maximality and independence of every code, preservation of all specified
signs, distinctness, and the complete number of maximal independent sets.

The examples have 10, 20, 9, and 7 wires. Their graph families have 10, 20,
20, and 7 maximal independent sets, respectively. The seven-wire example
retains a seven-cycle. The other three use a five-cycle and disjoint edges.

These are finite computational certificates. Universal existence of the
encoding, its connection to an arbitrary actual point set, and the family-B
Lean proof remain open. The exact conjecture and exploratory results are in
`../../HALF_GRID_INDEPENDENT_SET_RESEARCH.md`.

Run from the research project directory.

```powershell
python -B scripts/check_half_grid_independent_encoding.py
```

The data are generated research examples. The twenty-point order comes from
the previously retained local affine-partition witness, and the nine-wire
order comes from the previously retained forced-interval-colouring witness.
Canonical UTF-8/LF hashes for this checkpoint are in `source-sha256.json`.
