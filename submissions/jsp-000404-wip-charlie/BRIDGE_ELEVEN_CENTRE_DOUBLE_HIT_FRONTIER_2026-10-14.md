# JSP-000404 — Exact double-hit ledger for at most eleven original centres

Research date: 2026-10-14. Status: **three sorry-free theorems verified**, full JSP-000404 OPEN.

## Mathematical step

The previously verified SOURCE-NATIVE hard-carrier matching theorem gives, for
every actual NET collision target diagonal d:

  4 * |F_d| <= |V|,

where F_d is the genuine source fibre. Thus for |V| <= 11, all target
fibres have size at most two. Because every target in the actual image
has at least one source, the exact established fibre-debt identity
now specializes to

  E_D = sum_(d in actual image) (|F_d| - 1)
      = #{d in actual image : |F_d| = 2}
      <= |actual image|.

This is **exact counting**, not an assumption that geometric target
diagonals are free/true Boolean holes. It removes all multiplicity >=3
cases from the <=11-centre target-fibre accounting.

## Lean

Module:
  JSP000404Research/ResidualNetCollisionElevenCentreDoubleHit.lean

Kernel-checked declarations:

- net_collision_fibre_card_le_two_of_centres_le_eleven
- net_collision_duplicate_debt_eq_double_hit_card_of_centres_le_eleven
- net_collision_duplicate_debt_le_diagonal_image_card_of_centres_le_eleven

Initial development found a REAL Lean arithmetic failure: the tactic
`omega` saw the local `F d` abbreviation and its expanded original
fibre term as distinct atoms. It was repaired with
`change (F d).card <= 2 at hle`, without changing any mathematical
statement.

Verified incremental CI (standalone new module, prior to import wiring):
https://github.com/Charlie-Wang-03/awards/actions/runs/38548784678
  PASS, 3,465 Lean build jobs.
For all three theorems:
  [propext, Classical.choice, Quot.sound]
  NO sorryAx.

The root research import and the separate admitted-WIP import are now
wired to the module. Verify those exact integrated sources on their
own new branch HEAD; the cited earlier run only certifies the isolated
module and its imports.

## Open geometric obligation

The genuinely unproved global six-source planar payment in
PlanarLowerBranchProofAdmittedWIP.lean is unchanged. The at-most-eleven
centre identity simplifies the duplicate-image component ONLY; it
does not discharge distinct already-covered targets, terminal twins,
mixed rigid, soft overlap, fifth-centre obstruction or projected loss.
It does not prove or disprove unrestricted JSP-000404.
