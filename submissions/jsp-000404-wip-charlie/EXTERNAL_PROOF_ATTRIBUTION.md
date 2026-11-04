# External proof dependency: ordinary-point sharpness

The Lake dependency `jsp-000404` refers to
[aznikline/jsp-000404-lean](https://github.com/aznikline/jsp-000404-lean)
at the immutable commit
`cbfbbef188f5f98eead6045d7c3548de3c1b701a`.
Its toolchain and Mathlib revision match this research package exactly.
The package is MIT licensed. It is fetched under ignored `.lake/packages/`;
third-party source code and research data are not copied into this repository.

`JSP000404Research.OriginalUpperBound` imports `Jsp000404.UpperBound`.
Aznikline's `sendov_upper` supplies ordinary point configurations for every
N >= 3 and every positive epsilon, using the actual unoriented Euclidean
angle. Our wrapper only enumerates its noduplicate list by `Fin N` and
transports the same angle inequality. It does not supply a new construction.

The binary and three-centre construction proofs are by **superpilot69 and
ChatGPT 6 Astra**, from
[superpilot69/awards](https://github.com/superpilot69/awards/tree/722cb3caa86710c788296ca0ec954a79e9a0adcc/submissions/jsp-000404),
commit `722cb3caa86710c788296ca0ec954a79e9a0adcc`. They are vendored unchanged
in the dependency's `ThirdParty/Sendov/`, with their MIT license,
`ATTRIBUTION.md`, and `UPSTREAM.json` containing per-file SHA-256 hashes.
Aznikline supplies the formula, all-cardinality assembly, and list interface.
The construction's classical mathematical attribution is to Szekeres,
Erdős–Szekeres, and Sendov; this integration makes no priority claim.

The new wrapper and accompanying workspace checks were prepared with Codex
assistance. The separate written realization proof in
`SHARPNESS_CONSTRUCTIONS.md` was prepared before this integration; it describes
the same classical construction and is not a claim of new mathematical ideas.

## Scope and verification

The dependency's general lower theorem explicitly requires
`GeometricCertificates`. That premise is not proved there and is not used by
our upper-bound import. No import of its `MainTheorem` or
`CertificateIntegration` is needed. Its N <= 8 lower proof is also separate.

The precise plane type, distinctness, triple ordering, corrected first
numerator 2, N = 3 and N = 4 cases, integer-exponent boundary, and strict
epsilon conclusion have been checked in the source. The 14 vendored file
hashes in `UPSTREAM.json` match the canonical Git blobs. The clean Windows
checkout uses CRLF, so its raw working-file hashes differ without source edits.

Local Windows `lake build JSP000404Research.OriginalUpperBound` completed
with exit 0 (3,243 jobs), using the fixed Lean 4.34.0 and Mathlib pins.
All four printed local declarations, as well as `Jsp404.sendov_upper` and
`Jsp404.alpha_le_alphaN`, have only `propext`, `Classical.choice`, and
`Quot.sound`. The actual raw log is
`artifacts/restore-20261105/original-upper-bound-first.log`.

The wrapper also proves exact correspondence between injective Fin N
configurations and finite sets, and between the full two-sided statement
and equality with the genuine geometric extremum `JSP404.alpha`.
Those equivalences do not assert that the outstanding lower bound holds.

The all-N sharpness branch is therefore locally proved. This is a focused
result; the entire research umbrella has not yet passed. The original
arbitrary-N lower bound, including the genuine
global capacity/payment problem, remains open. No complete-prize submission
is justified by this dependency or its integration.
