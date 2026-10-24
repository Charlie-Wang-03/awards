# JSP-000404 — an abstract five-minimum C4 profile compatibility witness

**Research scope only; not a counterexample to the original planar theorem.**

The `FiveMinimaC4UniqueCanary` kernel theorem makes the C4-bearing colour
unique on the five minima. The uniqueness is a strict improvement over the
old at-most-two estimate. It does **not**, by itself, contradict the exact
reduced active-colour profile `3,3,2,2,2`.

## Explicit finite edge-colouring witness (manual combinatorial audit)

Let the five minima be `0,1,2,3,4`, and colour each of the ten
unordered edges with colours `A,B,C` as follows.

| Colour | Complete edge class | Shape |
| --- | --- | --- |
| A | `01,02,13,23` | the C4 `0–1–3–2–0` |
| B | `03,12,24,34` | the path `0–3–4–2–1` |
| C | `04,14` | the path `0–4–1` |

The three classes are pairwise edge-disjoint and partition all ten edges
of `K5`. Each class is bipartite (the last two are trees).
Only colour A has any C4. The distinct incident colours are:

- vertex 0: `A,B,C` (3)
- vertex 1: `A,B,C` (3)
- vertex 2: `A,B` (2)
- vertex 3: `A,B` (2)
- vertex 4: `B,C` (2)

Thus the exact active profile `3,3,2,2,2`, total incidence 12, edge count
10, bipartiteness of every colour class, and unique C4 exception are
**simultaneously compatible at the abstract graph-colouring level**.

The construction is not asserted to arise from actual planar rays,
AngleCap, the cut-saturation hypotheses, or a particular global
`BinaryEdgePartition` satisfying every additional projective constraint.
It demonstrates only that the listed *combinatorial* constraints cannot,
in isolation, yield a contradiction.

## Resulting proof frontier

The dependent theorem `two_bad_minima_share_monochromatic_fourCycle_colour`
(source submitted; kernel check pending) aims to force both exceptional minima
into the same C4 colour under the actual reduced profile and root conditions.
Membership in that colour's active palette must *not* be confused with
membership in a particular four-cycle.

To close the original six-source `sorry`, some further **genuine planar**
obstruction or non-reusing geometric-to-Boolean-hole charge must be proved.
Abstract C4 uniqueness is insufficient by the witness above. No additional
axiom, `sorry` or false unused-hole credit is justified.

Evidence of the previously certified uniqueness:
https://github.com/Charlie-Wang-03/awards/actions/runs/40103687396
