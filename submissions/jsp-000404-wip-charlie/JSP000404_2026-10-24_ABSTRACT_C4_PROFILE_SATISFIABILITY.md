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


## Stronger obstruction to a tempting overclaim: the bad vertex can lie OUTSIDE C4

Even granting *both* bad minima are active in the unique C4-bearing
colour, it is **not** combinatorially forced that both minima lie on that
C4. A second explicit K5 edge-colouring gives a witness:

| Colour | Edges | Bipartite structure |
| --- | --- | --- |
| A | `01,02,23` | path `1–0–2–3` |
| B | `03,12,13,24,34` | C4 `1–2–4–3–1` with pendant `0–3` |
| C | `04,14` | path `0–4–1` |

The incident-colour counts at vertices `0,1,2,3,4` are again
`3,3,2,2,2`, and the only C4-bearing colour B is active at both
exceptional vertices 0 and 1. **Vertex 0 is not on that C4**; it is
pendant to it. The example satisfies only the stipulated abstract
three-colour finite graph constraints; it is not a geometric or
`AngleCap` realization.

Consequently the conditional theorem
`two_bad_minima_share_monochromatic_fourCycle_colour`, even once
kernel-certified, cannot justify the stronger statement that BOTH
bad minima get the cycle-neighbour small-angle conclusion from the
same specified four-cycle. At least one is on the C4 by five-vertex
cardinality; the off-cycle bad vertex requires a pendant analysis
or an independent actual-plane angle argument.
