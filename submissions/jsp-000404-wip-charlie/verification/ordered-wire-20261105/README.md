# Concrete ordered-wire verification

2026-11-05. This stage follows safely pushed checkpoint
`1e0d4bd9679c1c450163bab70f44d7fa5a6c9bdf`. The full JSP-000404 goal remains open.

## Executed checks

- The focused `ProjectionStrictWireDirections` target built successfully,
  exit 0, with 3,238 Lake jobs. Its closure includes the new `CyclicWireLocalGaps`,
  `CyclicWireGraph`, and `OrderedDirectionWires` modules.
- `Audit.lean` passed, exit 0. It prints three statements with their hypotheses
  and sixteen transitive axiom lists. Only `propext`, `Classical.choice`, and
  `Quot.sound` occur. The quiver path construction needs fewer of these axioms.
- Lean 4.34.0 and the existing pinned Mathlib dependency
  `5ed2965256430c3649e86755f9576b54eca72435` were used. The preceding cyclic-wire
  dependency audit remains available. This build used the local cache.
- The four new files contain no executable `sorry`, `admit`, or new axioms.
  Their lines are at most 100 characters. Canonical UTF-8/LF hashes are in
  `source-sha256.json`.

The new modules are standalone. The umbrella source has not gained these
four imports, and a large umbrella rebuild was unnecessary for this scoped
check. Replayed warnings in older dependency modules are retained in the log.
Trailing whitespace in diagnostic suggestions is trimmed in the committed
build log. The pre-trim stream is preserved locally as
`artifacts/ordered-wire-focused-build-before-trim.log`.

## Mathematical scope

The local cyclic delays, graph construction, connectivity, integer retiming,
and Boolean capacity implication are checked. The actual planar generic
DirectionData has the required injective local values. The theorem
`OrderedWires.card_le_two_pow_of_winding` retains the one-or-two-turn condition
on nonempty simple cycles of its explicitly constructed graph. That remaining
condition has a written geometric argument but still needs a complete Lean
bridge. The all-n A conclusion and the all-n B bound remain outstanding.

The independent nine-wire compression obstruction has its own exact checker
and data under `../forced-compression-20261105/`. Its full Lean assembly is
pending, and it is outside the main kernel chain.

## Reproduction

From the research project directory with the pinned toolchain and cache, run

```powershell
$env:LEAN_NUM_THREADS='2'
lake build JSP000404Research.ProjectionStrictWireDirections
lake env lean verification/ordered-wire-20261105/Audit.lean
python -B scripts/check_forced_compression_obstruction.py
```
