# First unconditional threshold verification

2026-11-05. This stage follows safely pushed checkpoint
`58f97b1b249c95f1e14ba76b40912350d29af6fa`. Family A is proved. Family B and
the complete original-problem goal remain open.

## Executed checks

- `lake build JSP000404Research.OriginalFirstBranch` passed with exit 0 and
  3,255 Lake jobs, using the existing dependency cache.
- `Audit.lean` passed with exit 0. The transitive collector inspected every
  research declaration in the imported closure, including private declarations.
  It checked **47 modules and 811 declarations with zero failures**. Every
  collected axiom belongs to `propext`, `Classical.choice`, or `Quot.sound`.
  The log also prints the five principal theorem statements in full.
- `lake env lean JSP000404Research.lean` passed with exit 0 and empty output
  after adding the complete first-branch import. This checks compatibility
  with the existing umbrella imports.
- All ten pinned dependency revisions and tracked working trees passed the
  recorded check in `dependencies.json`. Lean is 4.34.0 and Mathlib is pinned
  at `5ed2965256430c3649e86755f9576b54eca72435`.
- The eight new Lean modules contain no `sorry`, `admit`, or axiom declarations.
  Their lines are at most 100 characters. Workspace and new-source ownership
  were checked as the normal Windows user. `git diff --check` passed.

The earlier 1,008-module umbrella axiom audit belongs to its historical
source. This stage audits the complete first-threshold dependency closure
and separately checks the updated umbrella source. Replayed warnings from
older dependencies are retained in the focused build log.

Committed logs use UTF-8 with LF line endings and trim trailing whitespace
from diagnostic suggestions. Raw streams remain under `artifacts/`.
The raw focused build log SHA-256 is
`c263948d7824f69b3f6f8cc30a17f9676ba9cd40fd270ebe3d814cbbb8d4c4e9`.
The raw audit stream SHA-256 is
`67309b967220a426b25575717d12f7c8b8a8e4fca1787a90233ad5fac6c423ef`.
Canonical source and evidence hashes are in `source-sha256.json`.

## Mathematical scope

`planar_card_le_two_pow_of_strict_angles` proves, for every n>=1 and every
finite injective planar point map, that a strict cap at
`pi-pi/(n+1/2)` implies cardinality at most `2^n`.
`planar_first_threshold_angle` supplies the contraposed actual triple.
`first_threshold_formula` identifies this angle with
`(1-2/(2*n+1))*pi`.

`original_lower_three` proves the original N=3 statement.
`original_lower_first_branch` proves the exact first interval of the audited
`Jsp404.alphaN` formula. The theorem keeps only its arithmetic branch-selection
hypotheses. Its geometry is unconditional for every injective point map.

The proof constructs actual continuous projection curves, identifies all
pair intersections, extracts simple-cycle period pieces, proves their
disjointness, and establishes winding one or two. Integer retiming and the
signed-band injection then give the bound. Finite strict-cap slack and the
small-cardinality cases are included. The natural-language proof is in
`../../CYCLIC_WIRE_RETIMING.md`, especially its completed actual-point section.

The second threshold `5*2^(n-2)` at a strict cap of `(1-1/(n+1))*pi` remains
open. All-N epsilon sharpness retains its previously recorded external
attribution. A complete prize submission is still pending that second bound
and final full-scope verification.

## Reproduction

Run from the research project directory with the pinned toolchain and cache.

```powershell
$env:LEAN_NUM_THREADS='2'
lake build JSP000404Research.OriginalFirstBranch
lake env lean verification/first-threshold-20261105/Audit.lean
lake env lean JSP000404Research.lean
```
