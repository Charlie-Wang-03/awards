# JSP-000301 — Lean formalization of the powerful-number counterexample

## Scope

This package formalizes the complete negative answer to the **scoped yes/no question currently recorded as JSP-000301**:

> If two consecutive positive integers are powerful, must at least one be a perfect square?

The upstream catalog records the counterexample `12167 = 23^3` and `12168 = 2^3 * 3^2 * 13^2`. This package does **not** claim discovery of that historical counterexample. It supplies an independently prepared Lean 4 formalization, statement-alignment audit, natural-language exposition, and reproducibility evidence.

This package does **not** address the separate counting/asymptotic question associated with Erdős problem #365; the upstream catalog explicitly distinguishes that problem from the scoped JSP-000301 question.

## Prior-submission disclosure

Before upstream submission, the repository was re-audited for existing JSP-000301 filings. Multiple earlier public formalizations of the same scoped counterexample already exist, including upstream PRs `#13`, `#17`, `#55`, and `#187`, together with several correction / recipient issues. PR `#13` was already public before this submission branch was created.

Accordingly, this package makes **no claim of first-public-formalization priority, exclusive formalization credit, or novelty of the underlying Lean theorem**. It is submitted only as an independently prepared supplementary formalization/evidence package so the maintainers can decide whether it has any incremental, joint-recognition, verification, or archival value. See `PRIOR_ART.md` for the comparison record.

## Result

The top-level formal theorem is:

```text
JSP000301.jsp_000301
```

It proves the negation of the universal assertion by exhibiting the consecutive pair `12167, 12168` and verifying from first principles that:

- both numbers are positive;
- both are powerful under the standard prime-divisor definition;
- they are consecutive;
- neither is a perfect square.

The companion existential theorem is:

```text
JSP000301.jsp_000301_counterexample
```

## Reproduction

Pinned environment:

- Lean: `v4.34.0`
- Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`
- transitive Lake dependencies: pinned in `lake-manifest.json`

Run:

```sh
./verify.sh
```

The script retrieves the Mathlib cache for the pinned revision, builds the package, runs `Audit.lean`, prints the theorem and its axioms, and emits SHA-256 values for the proof/toolchain files.

## File map

- `JSP000301.lean` — definitions, arithmetic lemmas, counterexample, and top-level negative theorem.
- `PROOF.md` — complete natural-language proof.
- `STATEMENT.md` — clause-by-clause correspondence between the upstream question and Lean theorem.
- `FORMALIZATION.md` — proof-step to Lean-lemma map.
- `PRIOR_ART.md` — earlier public JSP-000301 submissions and the resulting no-priority boundary.
- `ATTRIBUTION.md` — historical attribution, submitted contribution, AI-assistance disclosure, and conflict statement.
- `Audit.lean` — theorem/axiom audit entry point.
- `verify.sh` — deterministic reproduction command.
- `lean-toolchain`, `lakefile.lean`, `lake-manifest.json` — exact toolchain/dependency pinning.
- `verification/` — CI, axiom, hash, artifact, and archive evidence.

## Review boundary

A successful Lean kernel check establishes that the encoded theorem follows in the pinned formal environment. It is not, by itself, independent verification of source alignment, attribution, priority, incremental contribution, or prize eligibility. Those remain subject to upstream review.
