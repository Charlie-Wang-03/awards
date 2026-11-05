# Paused eleven-phase research checkpoint

2026-11-06. The user paused proof work while this branch was in progress. This
is an explicitly incomplete research checkpoint, not a proof of the 5*pi/6
threshold or of the original problem. The last fully assembled and audited
original lower bound remains `original_lower_three_through_forty` at parent
commit `b091f83b53c08f536824976b1f3f188bf285c49b`.

The following focused targets built with the pinned Lean 4.34.0 and Mathlib
dependency: `ElevenPhaseOrder`, `ElevenPhaseCores`, `ElevenPhaseCoreLemmas`,
`ElevenPhaseLRAT`, `ElevenPhaseCNFModel`, `ElevenPhaseSATHelpers`,
`ElevenPhaseCNFSemantics`, `ElevenPhaseSequential`, `ElevenPhaseValuation`,
`ElevenPhasePackingLogic`, `ElevenPhaseCoverData`, and `ElevenPhaseCounting`.
The proofs' printed axioms are among `propext`, `Classical.choice`, and
`Quot.sound`. Their individual success does not establish a full imported-
closure audit or discharge the missing geometric capacity claim.

The last `ElevenPhaseCountTransport` build failed at lines 11, 30, 43 and 58.
Lean printed `sorryAx` for declarations in that failed elaboration; those
declarations did not successfully compile, and are not valid proofs. The
catalog completion build was interrupted when proof work was paused. The
obstruction-set bridge has not been built. `ElevenPhaseRows`,
`ElevenPhaseSchedule`, `OrderedElevenPhase`, and
`PlanarElevenPhaseThreshold` are generated drafts and depend on an as-yet
absent `ElevenPhaseCapacity` module. None is imported by the existing umbrella.
Do not treat this checkpoint as a successful full build.

The `coherence-search.json` file records the untrusted finite search and its
88 learned row obstructions. The concrete CNF and trimmed RUP-only LRAT proof
are `../../JSP000404Research/ElevenPhaseCertificate/packing.cnf` and
`packing.lrat`. `ElevenPhaseLRAT` turns that certificate into a Lean proof
term; `ElevenPhaseCNFModel` checks that it is exactly the structural formula.
`ElevenPhasePackingLogic` proves a contradiction from explicit counting and
separation premises. The corresponding premises have not all been connected
to an arbitrary coherent row family.

From the project directory, reproduce the CNF without a SAT solver:

```powershell
python -B scripts/generate_eleven_phase_cnf.py --output artifacts/eleven-cnf-reproduced.cnf
Get-FileHash -Algorithm SHA256 artifacts/eleven-cnf-reproduced.cnf
Get-FileHash -Algorithm SHA256 JSP000404Research/ElevenPhaseCertificate/packing.cnf
```

The hashes matched at checkpoint preparation. Rebuild a previously passing
individual target with `lake build JSP000404Research.ElevenPhaseLRAT` or its
corresponding target name. Full rebuilds may be expensive. Lean's exact
dependencies remain those in `lake-manifest.json`; the ten dependency
revisions and tracked trees were checked for this checkpoint. `build-evidence.json`
records the observed log states and hashes, while raw logs remain ignored in
the local `artifacts/` directory.

No downloaded research papers, experimental point sets, or unrelated inputs
are included in this checkpoint. The initial user checkpoint `e2168310` is an
ancestor. No upstream repository, award record, or catalog has been changed.
