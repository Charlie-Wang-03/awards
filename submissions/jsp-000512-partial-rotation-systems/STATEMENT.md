# Statement correspondence and exclusions

## Actual mathematical objects

`RotationSystem G` consists of a permutation of the darts (oriented edges) of
Mathlib's `SimpleGraph G`, preserving each dart's source and having exactly one
orbit among the outgoing darts at each nonisolated vertex. Face successors are
rotation composed with dart reversal. Faces are all permutation orbits.
No geometric planarity assumption is built into this structure.

Write `c` for the number of connected components (including isolated vertices),
`v` for the vertex count, `s` for the nonisolated vertex count, `e` for the edge
count, and `f` for the number of dart-face orbits. The integer invariant is
`D = 2*c - 2*v + s + e - f`. The term `v-s` corrects for isolated vertices,
which have no darts. `HasGenusZero R` means exactly `D = 0`.

## Principal verified conclusions

All declarations below are in `JSP512Probe.RotationSystem` unless specified.

| Declaration | Proven scope |
| --- | --- |
| `defect_nonnegative` | Every finite rotation system satisfies `0 <= D`. |
| `genusZero_delete` | Deleting any actual graph edge preserves `D = 0`. |
| `genusZero_bridge_iff_sameFace` | For `D = 0`, an edge is a graph-theoretic bridge iff its two darts belong to the same face orbit. |
| `genusZero_subgraph` | For graphs on the same finite vertex type and `H <= G`, a genus-zero rotation on `G` yields a genus-zero rotation on `H`. |
| `bridge_component_count` | Deleting a bridge increases the component count by one. |
| `nonbridge_component_count` | Deleting a nonbridge preserves the component count. |
| `supportSize_delete` | Exact nonisolated vertex-count correction at the two endpoints. |
| `delete_face_count_same`, `delete_face_count_different` | Exact face-count changes under their stated endpoint/face hypotheses. |
| `delete_face_count_source_leaf`, `delete_face_count_target_leaf`, `delete_face_count_isolated_edge` | Remaining endpoint cases, including isolated-edge deletion. |

`JSP512Probe.CycleSurgery.swap_cycle_count` and `swap_split_count` prove that
swapping two distinct targets in different/same cycles decreases/increases
the number of permutation orbits by one. Fixed-point cycles are included.

## Edge insertion extension

`JSP512Probe.CycleSurgery.insertAfter_sameCycle` and `insertAfter_orbit_count`
prove that inserting a new element into an existing permutation cycle preserves
the old orbit relation and orbit count. Source-fiber preservation and a separate
fresh-source singleton construction are also proved.

`JSP512Probe.EdgeInsertion.addEdge` constructs a rotation system on the actual
augmented `SimpleGraph` when two distinct, nonadjacent, nonisolated vertices
have chosen outgoing darts as insertion corners. `dartEquiv` proves its darts
are exactly the old darts plus the two orientations of the new edge.
`added_face_embed` relates its face successor to the explicit extended carrier.

This construction has no cofacial assumption and no genus-zero conclusion.
It therefore does not yet justify inserting a diagonal in a planar face or
triangulating a planar graph. The isolated-endpoint graph construction is also
not supplied, despite the separate permutation-level fresh-source lemma.

## Relationship to JSP-000512

These theorems support a possible future formalization of ordinary planar
five-list-coloring. They do not prove that every planar graph is five-choosable,
nor provide a planar graph that is not four-choosable. No parameter bound or
new special case of that original coloring problem is claimed here.

Outstanding steps include the correspondence with ordinary planar embeddings,
augmentation/triangulation, the full disk/chord/fan decomposition needed by the
coloring induction, the coloring theorem itself, and a checked sharpness
witness. The submitted code includes no assumptions asserting these missing
steps and does not import an unfinished proof of them.
