# JSP-000512: partial formalization of rotation-system foundations

**This is not a solution of JSP-000512 / Erdős #631.** It is a submission of
completed supporting Lean theorems for consideration as a formalization or
community contribution. It does not establish award eligibility, claim a
completed problem, or request any solved/claim-status change.

The contribution develops finite graph rotation systems and proves Euler
nonnegativity, preservation of combinatorial genus zero under edge deletion,
and existence of genus-zero rotations on spanning subgraphs. It also proves
exact face and component counts for edge deletion, including bridges,
pendant edges, isolated edges, disconnected graphs, and isolated vertices.
It also constructs a rotation system after adding a missing edge between
two nonisolated vertices at specified corners, and proves the dart reversal
and face-successor correspondence. For corners on the same face, the construction preserves Euler defect and
genus zero. Every finite genus-zero graph also has an edge-maximal spanning genus-zero
extension. Its facial vertex sets are cliques, and any bridge has singleton
endpoint rotations. Joining two components at nonisolated vertices preserves
genus zero. Adding a pendant edge to an isolated vertex also preserves genus zero.
Every maximal extension on a nonempty vertex type is connected; the edgeless
case is handled by a verified single-edge construction. General triangulation remains
unproved. These are formalizations of standard mathematical facts, not new mathematical
discoveries or improved bounds for five-list-coloring.

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
proof placeholders, and reruns the 78 named axiom audits. Only `propext`,
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
