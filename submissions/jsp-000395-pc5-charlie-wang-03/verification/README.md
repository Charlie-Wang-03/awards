# Verification evidence

This directory records submitter-run public verification evidence for the pinned submission package.

Authoritative reproduction command:

```bash
../verify.sh
```

## Recorded run

- GitHub Actions run: `35127171862`
- Job: `104898948449`
- Tested staging commit: `6c45d37755a40c469eaf80f1848ae6731f168c62`
- Runner: Ubuntu 24.04 (`ubuntu-24.04` image)
- Lean: `v4.34.0`
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`
- Result: PASS

The run built the full top-level library, executed `Audit.lean`, printed the final axiom set, and generated the SHA-256 list preserved here.

## Permanent external archive

The submission artifact is permanently archived in OSF Registries:

- Registration ID: `gtzra`
- Registration URL: `https://osf.io/gtzra/`
- DOI: `10.17605/OSF.IO/GTZRA`
- Archived file: `awards-ce0daafbebf78ca1559bd8955837cd2d4c85f94c.zip`
- Archived source snapshot: `ce0daafbebf78ca1559bd8955837cd2d4c85f94c`
- Exact byte count: `329586`
- SHA-256: `5ab30ed8102e5d20c07686bf2505b361e8908713eb7964354c90cb4d121bb22e`

See `archive.txt` for the immutable archive record. The hash and byte count were computed from the file downloaded back from the public OSF registration after DOI assignment.

`artifact.txt` separately records the GitHub Actions artifact used as reproducibility evidence; it is retention-limited and is not the permanent archive.

These records are submitter-run evidence only. They do not constitute independent human review, an independent kernel implementation check, curator certification, recipient confirmation, eligibility approval, or an award decision.
