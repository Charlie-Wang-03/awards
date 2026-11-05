# Cyclic projection-wire checkpoint verification

2026-11-05, Windows. The complete JSP-000404 goal remains open.
The source starts from preserved checkpoint
`7091e8ca0f0f1e23d7ad3aead1842dd9ad116fab`.

## Kernel checks

- Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
  All ten dependency heads and tracked trees were checked again.
  `dependencies.json` records their exact revisions.
- Focused incremental build of `MobiusReturnOrder` and `CyclicHalfGrid`
  passed, exit 0, 3,097 Lake jobs. The latter imports `CyclicGraphPotential`.
  The final replay is recorded in `focused-build.log`.
- `Audit.lean` passed, exit 0. Its log prints three full statements and
  thirteen transitive axiom queries. Only `propext`, `Classical.choice`, and
  `Quot.sound` occur. Some algebraic lemmas use only `propext`.
- After adding the new imports, `lake env lean JSP000404Research.lean`
  passed, exit 0, with empty compiler output. This checks the umbrella using
  the existing dependency cache. `umbrella-file-check.log` is empty.
- The three new source modules contain no executable `sorry`, `admit`, or
  new axiom declaration. Their lines are at most 100 characters long.
  The source hashes in `source-sha256.json` use canonical UTF-8/LF bytes.

The return theorem assumes actual disjoint continuous strip paths. The graph
rounding theorem assumes the one-or-two-turn property for every nonempty
simple cycle. The construction of these objects from an arbitrary planar set
is still a formalization obligation. Neither theorem hides the missing
geometric premise. The integer-band coding bridge is also pending.

The earlier full 10,619-declaration audit belongs to its earlier immutable
source. It was not rerun for this checkpoint. Its separately admitted WIP
still has the documented `sorryAx` dependency and remains outside the umbrella.

## Exact finite checks

`cyclic-check.log` records the standard-library checker on sixty deterministic
integer point sets with seed 504506 and the previously certified twenty-point
affine-partition example. It verifies an exact critical-cycle certificate and
integer potential for each half-integer optimum, the transported total order,
every triangle inequality, and the independent integral-band Boolean words.
For selected inputs of size at most eight it exhausts all 78,268 simple
cycles, each having winding one or two. These are finite checks.

`row-check.log` records the independent integer checks of the 21-row half-grid
family. All pair conditions and separate-triple checks pass, and the
conditional four-cycle argument excludes joint realization. The accompanying
continuous geometric proof is in `DIRECTION_ORDER_RESEARCH.md` and awaits Lean
assembly.

The broader exploratory Z3 enumeration and 779-retiming observations remain
in the local ignored `artifacts/` directory, with their scripts and JSON
outputs. The committed standard-library checker reproduces the finite checks
listed above without those exploratory dependencies.

## Reproduction

From `D:\awards\submissions\jsp-000404-wip-charlie` with the pinned toolchain
and dependency cache, run

```powershell
$env:LEAN_NUM_THREADS='2'
lake build JSP000404Research.MobiusReturnOrder JSP000404Research.CyclicHalfGrid
lake env lean verification/cyclic-wires-20261105/Audit.lean
lake env lean JSP000404Research.lean
python -B scripts/check_cyclic_wire_retiming.py
python -B scripts/check_half_grid_coherence.py
```

The proposed all-n A argument is written in `CYCLIC_WIRE_RETIMING.md`.
Its complete kernel chain and the all-n B bound remain outstanding.
