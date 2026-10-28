import JSP000404Research.ResidualLossCollisionDoubleFlipCrossActivity
import JSP000404Research.ResidualLossCollisionThreePointExternalHoleObstruction
import Mathlib.Tactic

/-!
# Source-native zero-hole obstruction for actual two-coordinate loss collisions

An actual retained-edge source/blocker collision already eliminates
THREE distinct words of its Boolean square from external true-hole
credit. The fourth/opposite word can be a genuine external hole only
if the first original source cube is active in the OTHER chosen flip
coordinate, and conversely at the second original source cube.

Thus if either opposite-coordinate activity is absent, the ENTIRE
four-corner square is disjoint from true external holes, not merely
cardinality-at-most-one.

No conditional "Hall eligible neighbourhood" is invented: this is a
necessary obstruction derived from the original retained cubes.
It does NOT establish global six-source payment or full JSP-000404.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- When a real earliest retained-edge loss collision has a missing
opposite retained-active coordinate at EITHER owner, its entire
two-flip Boolean square contains ZERO exterior true-hole credits. -/
theorem actual_loss_collision_inactive_cross_square_no_external_holes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hw : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p)
    (hinactive :
      d ∉ retainedActive C p.1 ∨ c ∉ retainedActive C p.2) :
    Disjoint
      (insert word
        (insert (flipBoolWordAt word c)
          (insert (flipBoolWordAt word d)
            ({flipBoolWordAt (flipBoolWordAt word c) d} :
              Finset (Fin n → Bool)))))
      (lossLedgerOutsideTranslatedTrueHoles C exponent choice) := by
  classical
  have hearly :=
    lossEarliestActualEdgeCarrier_subset_earliestPair
      C exponent choice c d p hp hw
  have hpair :=
    Finset.mem_inter.mp (Finset.mem_sdiff.mp hearly).1
  have hc : word ∈ translatedLossSliceWords C exponent choice c := by
    simpa [lossSliceAtNat, c.isLt] using hpair.1
  have hd : word ∈ translatedLossSliceWords C exponent choice d := by
    simpa [lossSliceAtNat, d.isLt] using hpair.2
  rw [Finset.disjoint_left]
  intro target hsquare htrue
  have htarget :
      target = flipBoolWordAt (flipBoolWordAt word c) d :=
    cross_loss_collision_square_external_hole_only_double_flip
      C exponent choice hcd hc hd hsquare htrue
  rw [htarget] at htrue
  have hcross :=
    actual_loss_collision_double_flip_external_hole_forces_cross_activity
      C exponent choice hcd p hp hw htrue
  rcases hinactive with h | h
  · exact h hcross.1
  · exact h hcross.2

#print axioms actual_loss_collision_inactive_cross_square_no_external_holes

end OrderedEdgeColoring
end JSP000404Research
