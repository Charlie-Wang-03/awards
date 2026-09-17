# Verification record

Date: 2026-09-17. These checks were performed by the submitting agent with
OpenAI Codex assistance, not by independent reviewers or the prize organizers.

## Reproduction performed

The submission was copied into a separate checkout and all 20 supplied Lean
modules, plus the root module, were built there from source. Prebuilt pinned
Mathlib dependencies were reused from a local cache; no claim is made that
all third-party dependencies were rebuilt. That cache is not included in Git.
The project and package pins are recorded in `lean-toolchain`, `lakefile.toml`,
and `lake-manifest.json`.

Command, from the submission directory:

```sh
python3 scripts/verify.py
```

Result: PASS. The full build completed successfully (1264 jobs, including
cached dependencies). The verifier then directly reran `Probe/FoundationAudit.lean`
and matched all 65 declared audit targets. Each reported a subset of `propext`,
`Classical.choice`, and `Quot.sound`. The submitted source scan found no
`sorry`, `admit`, explicit `axiom`, or `native_decide` token.

See [verifier output](verification.log) and [source hashes](SOURCE-SHA256SUMS).
Hashes cover the Lean source, dependency/toolchain pins, and verifier script.

## Repository checks

The official repository validation, local-link checks, deterministic data
generation/check, immutable-history check against base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`, and all 22 unit tests passed.
Generated data did not change. These repository checks do not execute Lean
proofs; the separate proof verification above does.

## Limits

This demonstrates compilation and the audited axiom closures for the stated
supporting theorems. It does not establish independent mathematical review,
faithfulness of a future planar-coloring theorem, prize priority, or award
eligibility. No such completed theorem is included.
