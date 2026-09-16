# Verification evidence

This directory records reproducibility evidence for the JSP-000301 formalization package.

## Verified proof content

The warning-clean proof/toolchain content was validated on GitHub Actions from development commit `333570d885cf4405397c6e13546108b4d74a3ec1`.

- workflow: `JSP-000301 formalization probe`
- run ID: `35139863025`
- job ID: `104941391786`
- conclusion: `success`
- runner OS: Ubuntu 24.04.5 LTS
- Lean: `v4.34.0`
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`

The clean submission branch is reconstructed directly from the upstream-aligned base with the same verified proof/toolchain bytes plus documentation/evidence files. Its branch CI should be treated as the final repository-level check.

## Axiom audit

Both exported result theorems depend on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` appears in the axiom audit.

## Evidence classes

- `build.log` — compact record of the successful proof build/audit run.
- `axioms.log` — theorem names and exact axiom output.
- `source-sha256.txt` — hashes emitted by the verification script for proof/toolchain files.
- `artifact.txt` — GitHub Actions artifact metadata. The Actions artifact has a retention deadline and is **not** the permanent archive.

A permanent external archive must be published separately before an upstream submission can truthfully check the archive requirement. Its public ID/DOI, downloaded-back byte count, and SHA-256 belong in `archive.txt` after publication.
