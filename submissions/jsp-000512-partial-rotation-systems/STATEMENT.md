# Statement correspondence and exclusions

## Actual mathematical objects

`RotationSystem G` is a permutation of the darts (oriented edges) of Mathlib's
`SimpleGraph G`. It preserves the source and has exactly one orbit among the
outgoing darts at each nonisolated vertex. The face successor is rotation
composed with dart reversal. Faces are all permutation orbits.

Write `c` for the number of connected components (including isolated vertices),
`v` for the vertex count, `s` for the nonisolated vertex count, `e` for the edge
count, and `f` for the number of dart-face orbits. The integer invariant is
`D = 2*c - 2*v + s + e - f`. The correction accounts for isolated vertices,
which have no darts. `HasGenusZero R` means exactly `D = 0`.
Neither definition assumes a coloring or a recursive coloring certificate.

`IsTriangulatedDisk R pre` requires genus zero, connectedness, injectivity of
sources on the chosen outer facial orbit, and closure in three face steps for
every dart off that orbit. A two-dart outer face is allowed as a base case.
These are structural graph/permutation conditions, not induction hypotheses.

## Principal coloring conclusions

The declarations are in `JSP512Probe.RotationSystem`.

- `triangulated_disk_precolored`: every finite triangulated disk extends a
  precoloring of an oriented outer edge. Its two endpoint lists are distinct
  singletons; every other outer vertex has at least three colors and every
  other interior vertex at least five. The conclusion is a proper Mathlib
  coloring that chooses a color from every list.
- `triangulated_disk_list_coloring`: without a prescribed edge coloring,
  boundary lists of size at least three and interior lists of size at least
  five suffice on the same disk model.
- `genusZero_five_list_coloring`: for **every** finite simple graph `G`, rotation
  system `R` with `R.HasGenusZero`, arbitrary color type `C`, and function
  `L : V -> Finset C` with `5 <= (L x).card` at each vertex, there exists
  `c : G.Coloring C` with `c x` in `L x` for every vertex.

The last theorem includes disconnected graphs, isolated vertices, and graphs
with fewer than three vertices. It assumes neither maximality nor a supplied
disk decomposition. All three theorems are checked without proof placeholders
or extra axioms beyond the standard Lean axiom set listed in the verifier.

## Constructed structural steps

The implementation proves Euler-defect nonnegativity, deletion and insertion
formulas, genus-zero closure under spanning subgraphs, actual maximal
augmentation, facial simplicity, and triangularity of maximal augmentations
on at least three vertices. `exists_triangular_augmentation` gives a spanning
connected genus-zero supergraph with triangular facial orbits.

For the coloring induction, a chordless boundary deletion constructs the
actual smaller induced graph, its rotation, exact outer orbit, list-size
bounds, and extension of every respecting smaller coloring. A chord instead
yields two actual induced disks with strictly fewer vertices, a cover of all
vertices and edges, and intersection exactly at the chord endpoints.

The chord sides are constructed from refined rotation components and finite
fan restoration; no disk structure or separator is postulated as an input.
`chord_disk_separator_boundary_edges` retains inherited outer vertices and
the original oriented incoming boundary edge on the first side's outer orbit.
This is the facial-edge premise needed to recurse with the original
precoloring. The second side is precolored at its chord endpoints using the
first coloring. The checked gluing theorem then respects every original list.

`triangulated_disk_precolored` performs well-founded recursion on the actual
finite vertex count, with the isolated-edge base case, chordless deletion,
and chord splitting branches. `genusZero_five_list_coloring` constructs a
maximal supergraph, applies the disk theorem, and restricts the coloring back
to the original graph. Small and edgeless graphs are treated explicitly.

## Relationship to JSP-000512

This proves the full five-list upper bound **in the explicitly defined finite
zero-genus rotation model**. It does not yet prove the correspondence between
that model and ordinary noncrossing geometric planar embeddings. It also does
not supply a planar graph with a four-element list assignment that admits no
respecting proper coloring.

Consequently the submission is not a complete solution of JSP-000512 / Erdős
#631. The remaining requirements are geometric-planarity correspondence and
sharpness; neither is assumed as an axiom or imported from an unfinished proof.
No award eligibility, mathematical novelty, or independent review is asserted.
