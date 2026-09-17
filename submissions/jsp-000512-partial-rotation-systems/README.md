# JSP-000512: five-list-coloring in the finite genus-zero rotation model

**This remains a partial formalization of JSP-000512 / Erdős #631.** The
submission now proves the five-list-coloring upper bound for every finite graph
supplied with a genus-zero rotation system. The correspondence with ordinary
geometric planar embeddings and a planar non-four-choosable witness remain
unproved. No solved status or award eligibility is claimed.

The principal theorem is `RotationSystem.genusZero_five_list_coloring`: for
any color type and any finite lists of size at least five, a finite graph with
`HasGenusZero` admits a proper Mathlib coloring respecting every list. The
rotation and genus assumptions are purely combinatorial and contain neither a
coloring conclusion nor a recursive coloring certificate.

The proof constructs maximal triangular augmentation, actual smaller induced
disks from chord splitting and boundary deletion, and the complete vertex-count
induction extending a precolored outer edge with three/five list bounds. The
chord construction preserves the actual oriented precolored edge on the new
outer face, not just its endpoints. Coloring the second side with the first
side's chord colors makes the two colorings agree and permits gluing.

## Scope and correspondence

See [precise statements and limitations](STATEMENT.md). These are formalizations
of known mathematics, not a new coloring bound or a claim of first-solver credit.
The completed combinatorial upper bound does not by itself complete the original
problem's geometric-planarity and sharpness requirements.

## Reproduce

Lean `v4.34.0` and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` are pinned. From this directory:

```sh
lake exe cache get
python3 scripts/verify.py
```

The verifier checks exact source-manifest coverage, source hashes, absence of
proof placeholders, root-import coverage of every supplied module, the full
build, and 441 named axiom audits across seven audit modules. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. See the
[verification record](evidence/VERIFICATION.md).

## Attribution and request

Submission account: **xpzwzwz**, with **OpenAI Codex** assistance.
Only the supplied formalization work is claimed. No mathematical discovery
priority is claimed for Thomassen's theorem or its standard supporting facts.
[Sources and provenance](evidence/SOURCES.md) identify prior work inspected.
First-party source and documentation are under [MIT](LICENSE); dependencies
retain their licenses.

Requested review: the verified combinatorial upper bound and its supporting
constructions as a partial formalization/community contribution. Any prize
consideration is limited to this stated scope and subject to the organizers'
decision. No candidate, award, solved, or claim-status records are changed.
