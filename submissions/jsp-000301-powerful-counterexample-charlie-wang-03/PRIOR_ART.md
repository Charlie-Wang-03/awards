# Prior submissions and overlap audit

## Purpose

This file records the pre-submission duplicate / priority audit for the independently prepared JSP-000301 formalization in this package.

The mathematical counterexample is classical and already present in the upstream catalog. The relevant question here is therefore not mathematical discovery priority, but whether the formalization itself is first, independent, overlapping, or merely supplementary.

## Earlier public upstream filings located

The following upstream pull requests were located during the re-audit and predate this package's upstream submission stage:

| PR | Public filing time (UTC) | Characterization in the upstream filing |
| --- | --- | --- |
| `TheJustinSunPrize/awards#13` | 2026-09-16 08:50:14 | complete Lean formalization of the known `12167,12168` counterexample; no new-mathematics claim |
| `TheJustinSunPrize/awards#17` | earlier than this package | additional Mathlib-based implementation; explicitly acknowledges `#13` as earlier |
| `TheJustinSunPrize/awards#55` | 2026-09-16 12:45:03 | additional Lean formalization; explicitly lists earlier submissions including `#13`, `#17`, `#33`, and correction issue `#25` |
| `TheJustinSunPrize/awards#187` | 2026-09-16 18:31:41 | Mathlib formalization/evidence package; no first-formalization claim |

Related correction / recipient issues also exist, including issue `#25` and several later recipient / verification threads for the same scoped problem.

This table is an overlap disclosure, not an attempt to adjudicate which earlier submission is ultimately valid, eligible, selected, independently verified, or entitled to display credit. Those questions remain with upstream maintainers.

## Comparison with this package

This package proves the same scoped negative answer using:

- Lean `v4.34.0`;
- Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`;
- direct prime-divisor definition of powerfulness;
- explicit counterexample `12167,12168`;
- a general lemma that every `a^2 b^3` is powerful;
- a successive-square gap argument for nonsquareness;
- top-level universal-negation theorem `JSP000301.jsp_000301`;
- exact dependency pinning, GitHub Actions build/audit, source hashes, and archive-oriented evidence packaging.

These implementation choices do not make the underlying theorem novel, and substantial conceptual overlap with earlier Mathlib formalizations remains.

## Frozen priority boundary

The submitting account therefore asserts only:

> This is an independently prepared and kernel-checked JSP-000301 formalization/evidence package attributable to the submitting account's own implementation work.

It does **not** assert:

- first mathematical solution;
- first Lean formalization;
- first public formalization;
- sole or exclusive formalization credit;
- displacement of an earlier valid submission;
- that stronger CI or archival evidence creates priority over an earlier formalization;
- eligibility, award allocation, or payment entitlement.

If upstream considers multiple submissions within an applicable evaluation window, joint-recognition rule, verification fallback, or supplementary-evidence process, this package may be evaluated on that basis. Otherwise it should be treated as an additional independent artifact without priority effect.
