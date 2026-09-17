# Verification record

Date: 2026-09-17. Checks were performed by the submitting agent with OpenAI
Codex assistance, not by independent reviewers or the prize organizers.

## Reproduction performed

All 130 supplied `Probe/` Lean modules, plus the root module, were built in the
separate submission checkout. Pinned Mathlib dependencies were reused from a
local cache; rebuilding all third-party dependencies is not claimed. The cache
is not included in Git. Pins are recorded in `lean-toolchain`, `lakefile.toml`,
and `lake-manifest.json`.

Command, from the submission directory:

```sh
python3 scripts/verify.py
```

Result: PASS. The full build completed successfully (1445 jobs, including cached
dependencies), without warnings or errors. The verifier checked exact input-hash
coverage and that the root target imports every supplied module transitively.
It scanned all submitted Lean sources for proof placeholders, explicit axioms,
and native decision calls; none were found.

Eight audit modules were then run directly with Lean, independently of cached
build output. All 456 declared targets matched their printed axiom closures:

| Audit module | Named targets |
| --- | ---: |
| FoundationAudit | 120 |
| ColorInductionAudit | 39 |
| VertexDeletionAudit | 54 |
| ChordSeparationAudit | 111 |
| ComponentRotationAudit | 22 |
| RotationIsoAudit | 10 |
| FanInsertionAudit | 85 |
| SharpnessAudit | 15 |

Every closure is a subset of `propext`, `Classical.choice`, and `Quot.sound`.
The audited declarations include the recursive
`triangulated_disk_precolored`, final `genusZero_five_list_coloring`, and
`Gutner.geometric_four_list_obstruction`, not only their supporting lemmas.
All integer coordinate checks are proved using `decide +kernel`; the full
coordinate module was rebuilt from source in this separate checkout. See [verifier output](verification.log) and
[source hashes](SOURCE-SHA256SUMS). Hashes cover all Lean sources, the dependency
and toolchain pins, and the verifier script.

## Repository checks

Repository schema validation, local-link checks, deterministic data generation
and checking, immutable-history checking against base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`, and all 22 unit tests passed for this
update. Generated data did not change. Those checks do not execute Lean proofs;
the separate proof verification above does.

## Limits

The evidence establishes compilation and the stated axiom closures for the
finite genus-zero rotation-model upper bound and the explicit geometric
four-list counterexample. It does not establish independent mathematical review,
the general upper-bound geometric-planarity correspondence, prize priority, or
award eligibility. The complete original problem is not solved by this submission.
