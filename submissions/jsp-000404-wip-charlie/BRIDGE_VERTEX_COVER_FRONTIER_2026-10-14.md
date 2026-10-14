# JSP-000404 · Nonreused bipartite vertex-cover frontier
## 2026-10-14 — Verified finite matching reduction, global payment still open

Research branch: `research/jsp-000404-sharp-centre`.
The following source-native reductions have been *compiled* under
the repo-pinned Lean v4.34.0 / Mathlib snapshot. They are not a proof
of the overall planar Sendov/Blumenthal extremal result.

### Two sorry-free Lean modules

- `JSP000404Research/ResidualFiniteBipartiteCoverCapacity.lean`:
  a finite matching/vertex-cover bound without appealing to a
  presumed geometric Hall or König principle. Every source is
  assigned ONE tagged cover endpoint, with source injectivity on
  each side.
- `JSP000404Research/ResidualNetCollisionExactShellBipartiteCover.lean`:
  specializes the abstract lemma to ACTUAL NET forward/reverse hard
  collision sink words. Its source-original bridge owners and
  flip colours supply lower and upper slots; permitted graph edges
  must satisfy BOTH genuine two-bit source-compatible soft bridge
  eligibility and exact singleton target violation conditions.

The geometric specialization formally proves:

1. `net_collision_actual_pair_mem_exact_shell_slot_edges`:
   each genuine NET collision source selects an actual edge of
   the broader target-compatible candidate slot graph.
2. `net_collision_same_target_lower_slot_injective`:
   at fixed canonical diagonal d, the original lower endpoint
   paired with original REVERSE colour determines the source.
3. `net_collision_same_target_upper_slot_injective`:
   the upper endpoint paired with original FORWARD colour does too.
4. `net_collision_target_fibre_card_le_exact_slot_vertex_cover`:
   every mathematically verified finite vertex cover `A_d,B_d`
   of the allowed candidate graph satisfies the nonreused bound
   `|D^-1(d)| <= |A_d| + |B_d|`.
5. `net_collision_duplicate_debt_le_sum_exact_slot_cover_excess`:
   a verified family of covers for all actually hit target words
   yields `E_D <= sum_(d in D(I)) (|A_d|+|B_d|-1)`.
6. `net_mobile_mass_le_holes_covered_exact_slot_cover_excess`:
   combines the preceding source-collision excess bound with the
   existing NET mobile hard-source ledger while still separating
   literal TRUE Boolean holes, singleton/soft covered words,
   distinct already-COVERED diagonal blockers and source duplicate
   excess; no class is reclassified into holes.

All six theorems are proof-checked independently of the old global
six-source `sorry`. Generic matching plus domain specialization
therefore produce SEVEN new sorry-free Lean theorems.

### Why this is a mathematically stronger counting tool

Previously the best unconditional *numerical* bound was
`min (|two-bit eligible bridges|) (min |exact lower slots| |exact upper slots|)`.
A bipartite graph may have far fewer mutually compatible
endpoint pairs than the sizes of those sets suggest; a concrete
vertex cover can exploit those restrictions. The new statement
retains those source-native edge conditions rather than simply
summing candidate populations.

**Important limitation:** existence of a sufficiently SMALL cover
is NOT guaranteed by the theorem. Choosing all available lower
or upper slots gives a trivial cover and only recovers the earlier
type of bound. Any desired improvement must be certified from
actual target-specific graph structure. Slot covers themselves
are NOT literal TRUE Boolean holes nor independently unreserved
dyadic profile surplus.

### Verification

- Abstract proof: https://github.com/Charlie-Wang-03/awards/actions/runs/38498758996
  — PASS, 3,092 build jobs; `#print axioms` excludes `sorryAx`.
- True NET geometry specialization: https://github.com/Charlie-Wang-03/awards/actions/runs/38499020339
  — PASS, 3,270 build jobs; four declarations exclude `sorryAx`.
- Global exact debt / mobile ledger: https://github.com/Charlie-Wang-03/awards/actions/runs/38499277401
  — PASS, 3,270 build jobs; two more declarations exclude `sorryAx`.

The initial abstract proof exhibited real Lean elaboration failures
for impossibility of mixed `Sum.inl`/`Sum.inr` branches and
`Finset.card_image` simplification. Both were corrected with
explicit case analysis and injectivity lemmas, not admitted axioms.
There remain harmless deprecation warnings for old `if_pos`
rewrites but no compilation errors in the certified source.

### Honest remaining gap

The one deliberately admitted theorem in
`PlanarLowerBranchProofAdmittedWIP.lean` still needs a globally
valid six-source geometric payment theorem. In particular, no
proof currently constructs sufficiently economical target-specific
slot covers and simultaneously pays distinct covered diagonals,
fifth-centre blockers, terminal twins, mixed rigid, soft overlap
and projected profile losses out of genuinely NONREUSED Boolean
holes or genuinely UNRESERVED dyadic mass.

Overall JSP-000404 remains OPEN. The new results are local certified
nonreuse infrastructure and a stronger conditional payment
reduction; they do not settle the complete extremum.
