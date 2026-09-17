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

The additional theorem `cofacial_genusZero` proves that, under the same
endpoint hypotheses and `R.face.SameCycle a.symm b.symm`, this insertion
preserves genus zero. `cofacial_defect` proves the stronger equality of Euler
defects without assuming genus zero. `cofacial_added_face_count` proves the
face count increases by one; edge count also increases by one, while support
and component counts remain unchanged. All of these concern the explicit
combinatorial rotation model.

General triangulation is still not proved. Pendant insertion with one isolated
endpoint is supplied below. The correspondence with geometric planar embeddings
remains outside this submission.

## Maximal extensions

`RotationSystem.exists_maximal_augmentation` constructs an edge-count-maximal
spanning genus-zero supergraph by finite maximization over actual graphs.
`maximal_supergraph_eq` shows there is no proper genus-zero supergraph on
that vertex type. No triangular-face property is assumed in this definition.

`maximal_cofacial_adj`, `maximal_face_vertices_adj`, and
`maximal_face_isClique` show that distinct vertices on a face are pairwise
adjacent, using the verified cofacial insertion theorem.
`maximal_bridge_endpoints_fixed` shows that every bridge has singleton
rotations at both endpoints, so neither endpoint can have another incident
edge. This excludes nontrivial bridge attachments. Connectedness is proved
separately below; triangular facial walks are not yet proved.

## Joining components

`EdgeInsertion.delete_added_edge` proves that deleting the inserted edge
recovers the original graph. For insertion corners in different components,
`separate_component_count` and `separate_face_count` each prove a decrease by
one, while the edge count increases by one and support is unchanged.
`separate_defect` proves equality of Euler defects, and `separate_genusZero`
preserves genus zero for the actual augmented rotation system.

`RotationSystem.maximal_dart_sources_reachable` and
`maximal_support_reachable` consequently prove that all nonisolated vertices
of a maximal genus-zero graph lie in one connected component. The next
construction removes the nonisolated-vertex restriction.

## Pendant insertion and full connectedness

`EdgeInsertion.addPendant` constructs an actual rotation system after connecting
an existing nonisolated source to an isolated vertex. `pendant_face_formula`
identifies its face permutation as two insertions into an old face cycle;
`pendant_face_count` proves the face count is unchanged. The inserted edge is
a bridge whose deletion recovers the original graph. With the verified deletion
counts, `pendant_defect` and `pendant_genusZero` prove preservation of Euler
defect and genus zero.

`maximal_support_univ` excludes isolated vertices in a maximal genus-zero graph
containing an edge. `singleEdgeRotation` and `singleEdge_genusZero` supply the
single-edge witness needed for the edgeless case. `maximal_preconnected` proves
pairwise reachability without a nonemptiness assumption, while
`maximal_connected` proves connectedness on every nonempty vertex type.
This does not establish triangular faces or a coloring theorem.

## Bridges and facial edge uniqueness

`RotationSystem.reachable_of_endpoints_fixed` shows that when both endpoint
rotations of an edge are singletons, its entire connected component consists
of those endpoints. Combining this with full connectedness gives
`maximal_bridge_card`: a bridge in a maximal genus-zero graph forces exactly
two vertices. `maximal_not_bridge` therefore excludes bridges when there are
at least three vertices.

Under that cardinality hypothesis, `maximal_edge_distinct_faces` separates the
two orientations of each edge into different facial orbits, and
`maximal_face_edge_injective` proves that cofacial darts with equal undirected
edges must be equal. `maximal_face_two_steps_ne` excludes length-two facial
orbits; length-one orbits are already excluded by `face_ne_self`.
`maximal_rotations_nonfixed` also excludes singleton endpoint rotations.
These results do not yet exclude repeated vertices within a face and do not
prove that faces are triangles.

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
