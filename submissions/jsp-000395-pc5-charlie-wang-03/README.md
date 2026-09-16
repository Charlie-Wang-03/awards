# JSP-000395 PC5 restricted-result submission package

> Submission-preparation package for review. This package proves and formalizes a **restricted partial result** associated with JSP-000395 / Erdős Problem #488. It does **not** claim a complete solution of JSP-000395 and does not request any catalog, candidate, award, or payment status change by itself.

## Result submitted

For five strictly increasing pairwise-coprime integers

\[
2\le q_1<q_2<q_3<q_4<q_5,
\]

let

\[
F_A(x)=\#\{1\le t\le x:\exists i,\ q_i\mid t\}.
\]

The submitted theorem proves that, whenever \(q_5\le n\) and \(m>0\),

\[
\boxed{nF_A(m)<2mF_A(n)}.
\]

Hence it implies the corresponding restricted case with \(m>n\ge q_5\).

The extra assumptions `|A| = 5` and pairwise coprimality are genuine restrictions. See `STATEMENT.md` for clause-by-clause scope comparison.

## Proof contents

- `PROOF.md` — complete English mathematical proof.
- `FORMALIZATION.md` — map from the mathematical proof to the Lean modules.
- `PC5488.lean` and `PC5488/*.lean` — complete Lean proof.
- `STATEMENT.md` — source/statement correspondence and explicit restricted/non-equivalent scope.
- `ATTRIBUTION.md` — contribution, AI-assistance, and self-submission disclosure.
- `Audit.lean` — final-theorem and axiom audit entry point.
- `verify.sh` — reproducible build, axiom audit, and source-hash commands.
- `verification/` — public submitter-run verification and archival evidence.

## Pinned environment

- Lean: `v4.34.0`
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (`v4.34.0`)
- Transitive package revisions: pinned in `lake-manifest.json`.

## Source provenance

The Lean proof modules are copied byte-for-byte from the proof-complete development artifact in `Charlie-Wang-03/awards`, clean proof commit:

`0fc48b977f1d4b672c81751c58b71c9cb630b62a`

The submission `lakefile.lean` strengthens dependency pinning from the release tag to the exact Mathlib commit above; it does not change the proof source.

## Reproduction

From this directory:

```bash
./verify.sh
```

The script obtains the pinned Mathlib cache, builds the complete `PC5488` library, runs `Audit.lean`, and prints SHA-256 digests for the proof/toolchain files.

## Submitter-run verification

Package-specific GitHub Actions run `35127171862` completed successfully on staging commit `6c45d37755a40c469eaf80f1848ae6731f168c62`.

Observed results:

- Lean `v4.34.0` installed successfully on Ubuntu 24.04;
- Mathlib checked out exactly `5ed2965256430c3649e86755f9576b54eca72435`;
- `lake build` completed successfully with 8930 jobs;
- `PC5488.pc5_488` elaborated with the intended quantified statement;
- axiom report: `[propext, Classical.choice, Quot.sound]`;
- proof/toolchain SHA-256 values are recorded in `verification/source-sha256.txt`.

The run also produced GitHub Actions artifact ID `10459483087`; retention-limited artifact metadata is recorded in `verification/artifact.txt`.

## Permanent external archive

The complete source snapshot used for submission is permanently archived in OSF Registries:

- Registration ID: `gtzra`
- DOI: `10.17605/OSF.IO/GTZRA`
- Registration URL: `https://osf.io/gtzra/`
- Archived file: `awards-ce0daafbebf78ca1559bd8955837cd2d4c85f94c.zip`
- Archived source snapshot commit: `ce0daafbebf78ca1559bd8955837cd2d4c85f94c`
- Exact byte count: `329586`
- SHA-256: `5ab30ed8102e5d20c07686bf2505b361e8908713eb7964354c90cb4d121bb22e`

The hash and byte count were computed from the ZIP downloaded back from the public OSF registration after DOI assignment. See `verification/archive.txt`.

This verification is development/submission evidence from the submitting account. It is not represented as independent human review, independent-kernel verification, curator verification, recipient confirmation, eligibility approval, or an award decision.
