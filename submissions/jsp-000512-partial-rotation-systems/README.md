# JSP-000512: partial formalization of rotation-system foundations

**This is not a solution of JSP-000512 / Erdős #631.** It is a submission of
completed supporting Lean theorems for consideration as a formalization or
community contribution. It does not establish award eligibility, claim a
completed problem, or request any solved/claim-status change.

The main structural result is now **triangular augmentation in the finite
combinatorial genus-zero model**: any graph on at least three vertices with a
genus-zero rotation system has a spanning connected genus-zero supergraph in
which every facial orbit has exactly three darts. The facial successor returns
after three steps, and no facial orbit repeats a vertex.

The proof develops actual edge insertion/deletion and vertex splitting,
Euler nonnegativity, maximal extensions, connectivity after vertex deletion,
and facial vertex simplicity. It then restricts to a facial clique while
preserving the original face, handles the isolated vertices exactly, and uses
a sharpened edge/face-length bound to exclude faces of length at least four.
These formalize standard mathematical facts, not new coloring bounds.

## Scope and correspondence

See [precise statements and limitations](STATEMENT.md). In particular,
`HasGenusZero` is defined by graph counts and permutation face orbits; it
contains neither a coloring conclusion nor a recursive coloring certificate.
The connection to ordinary geometric planar embeddings is not proved here.
Neither the five-list-coloring theorem nor its sharpness is proved here.
No partial theorem is presented as the original problem's complete solution.

## Reproduce

Lean `v4.34.0` and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` are pinned in the project files.
From this directory, with Lean/elan, Python 3, and network access for dependencies:

```sh
lake exe cache get
python3 scripts/verify.py
```

The verifier builds every supplied Lean module, checks source hashes, scans for
proof placeholders, and reruns the 120 named axiom audits. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted by that audit.
See the [verification record](evidence/VERIFICATION.md).

## Attribution and request

Submission account: **xpzwzwz**, with **OpenAI Codex** assistance.
Only the supplied Lean formalization work is claimed; no first-solver credit
for Thomassen's theorem or the underlying standard graph theory is claimed.
[Sources and provenance](evidence/SOURCES.md) identify prior work inspected.
First-party source and documentation are provided under [MIT](LICENSE);
Mathlib and other dependencies retain their licenses.

Requested review: verify the stated supporting theorems and advise whether
this partial foundation contribution fits the prize's community/formalization
contribution process. Prize consideration, if any, is requested only for this
explicitly limited scope and remains subject to the organizers' decision.
