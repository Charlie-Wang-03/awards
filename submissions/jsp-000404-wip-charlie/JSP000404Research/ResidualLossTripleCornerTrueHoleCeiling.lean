import JSP000404Research.ResidualLossOppositeFibreExactPairCriterion
import JSP000404Research.ResidualLossCollisionThreePointExternalHoleObstruction
import Mathlib.Tactic

/-!
# True outside-hole ceiling forced by a COMPLETE genuine n=3 collision fibre

Unlike purely numerical multiplicity upper bounds, this is a real-resource
OBSTRUCTION. Suppose ALL THREE original earliest-prior source tests at
coordinates (1,0),(2,0),(2,1) pass for one concrete opposite target q.
Their three source squares cover SEVEN of the eight Boolean 3-words;
the only uncovered position is the full antipode of q.

An already certified genuine loss-collision square contains NO TRUE
outside-translated hole other than its opposite target q.
Consequently the ENTIRE actual true outside-hole set Q can occupy
ONLY {q, antipode(q)}. In particular |Q| <= 2, with NO assumption
that q or its antipode actually is a hole.

This is an unconditional implication from THREE actual original
earliest-prior loss-collision source events, not an invented exterior
hole credit or an assumed global Hall payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The three two-flip collision squares with the SAME opposite q cover
all n=3 Boolean words EXCEPT possibly the full antipode of q.
This is a finite, exact Boolean identity independent of any geometry. -/
theorem bool_three_triple_square_cover :
    ∀ (q r : Fin 3 → Bool),
      r = (fun i => !(q i)) ∨
      r ∈ lossCollisionSquareWords 3
        ((1 : Fin 3), (0 : Fin 3),
          flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (1 : Fin 3)) ∨
      r ∈ lossCollisionSquareWords 3
        ((2 : Fin 3), (0 : Fin 3),
          flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (2 : Fin 3)) ∨
      r ∈ lossCollisionSquareWords 3
        ((2 : Fin 3), (1 : Fin 3),
          flipBoolWordAt (flipBoolWordAt q (1 : Fin 3)) (2 : Fin 3)) := by
  decide

/-- THREE genuine, exact earliest-prior collisions sharing q force
the FULL GLOBAL outside-translated true-hole pool to be supported
on just q and its antipodal Boolean 3-word. There may be ZERO actual
holes in that two-word set. -/
theorem actual_three_colour_triple_collision_all_true_holes_subset_pair
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (q : Fin 3 → Bool)
    (h10 :
      flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (1 : Fin 3) ∈
        lossEarliestPairWords (lossSliceAtNat C exponent choice) 1 0)
    (h20 :
      flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (2 : Fin 3) ∈
        lossEarliestPairWords (lossSliceAtNat C exponent choice) 2 0)
    (h21 :
      flipBoolWordAt (flipBoolWordAt q (1 : Fin 3)) (2 : Fin 3) ∈
        lossEarliestPairWords (lossSliceAtNat C exponent choice) 2 1) :
    lossLedgerOutsideTranslatedTrueHoles C exponent choice ⊆
      ({q, (fun i => !(q i))} : Finset (Fin 3 → Bool)) := by
  classical
  let Q := lossLedgerOutsideTranslatedTrueHoles C exponent choice
  let w10 := flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (1 : Fin 3)
  let w20 := flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (2 : Fin 3)
  let w21 := flipBoolWordAt (flipBoolWordAt q (1 : Fin 3)) (2 : Fin 3)
  have h10s := (Finset.mem_inter.mp (Finset.mem_sdiff.mp h10).1)
  have h20s := (Finset.mem_inter.mp (Finset.mem_sdiff.mp h20).1)
  have h21s := (Finset.mem_inter.mp (Finset.mem_sdiff.mp h21).1)
  have h10i : w10 ∈ translatedLossSliceWords C exponent choice (1 : Fin 3) := by
    simpa [w10, lossSliceAtNat] using h10s.1
  have h10j : w10 ∈ translatedLossSliceWords C exponent choice (0 : Fin 3) := by
    simpa [w10, lossSliceAtNat] using h10s.2
  have h20i : w20 ∈ translatedLossSliceWords C exponent choice (2 : Fin 3) := by
    simpa [w20, lossSliceAtNat] using h20s.1
  have h20j : w20 ∈ translatedLossSliceWords C exponent choice (0 : Fin 3) := by
    simpa [w20, lossSliceAtNat] using h20s.2
  have h21i : w21 ∈ translatedLossSliceWords C exponent choice (2 : Fin 3) := by
    simpa [w21, lossSliceAtNat] using h21s.1
  have h21j : w21 ∈ translatedLossSliceWords C exponent choice (1 : Fin 3) := by
    simpa [w21, lossSliceAtNat] using h21s.2
  have h10only (r : Fin 3 → Bool) (hr : r ∈ Q)
      (hs : r ∈ lossCollisionSquareWords 3
        ((1 : Fin 3),(0 : Fin 3),w10)) : r = q := by
    have h := cross_loss_collision_square_external_hole_only_double_flip
      C exponent choice (by decide : (1 : Fin 3) ≠ 0) h10i h10j
      (by simpa only [lossCollisionSquareWords] using hs) hr
    simpa only [w10, flipBoolWordAt_involutive] using h
  have h20only (r : Fin 3 → Bool) (hr : r ∈ Q)
      (hs : r ∈ lossCollisionSquareWords 3
        ((2 : Fin 3),(0 : Fin 3),w20)) : r = q := by
    have h := cross_loss_collision_square_external_hole_only_double_flip
      C exponent choice (by decide : (2 : Fin 3) ≠ 0) h20i h20j
      (by simpa only [lossCollisionSquareWords] using hs) hr
    simpa only [w20, flipBoolWordAt_involutive] using h
  have h21only (r : Fin 3 → Bool) (hr : r ∈ Q)
      (hs : r ∈ lossCollisionSquareWords 3
        ((2 : Fin 3),(1 : Fin 3),w21)) : r = q := by
    have h := cross_loss_collision_square_external_hole_only_double_flip
      C exponent choice (by decide : (2 : Fin 3) ≠ 1) h21i h21j
      (by simpa only [lossCollisionSquareWords] using hs) hr
    simpa only [w21, flipBoolWordAt_involutive] using h
  intro r hr
  rcases bool_three_triple_square_cover q r with hant | hsq10 | hsq20 | hsq21
  · simp [hant]
  · simp [h10only r hr hsq10]
  · simp [h20only r hr hsq20]
  · simp [h21only r hr hsq21]

/-- Numerical GLOBAL RESOURCE ceiling, derived from exact original
three-source collision occurrences. Unlike local Hall estimates,
this bounds ALL true outside-translated holes, including remote ones. -/
theorem actual_three_colour_triple_collision_true_holes_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (q : Fin 3 → Bool)
    (h10 :
      flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (1 : Fin 3) ∈
        lossEarliestPairWords (lossSliceAtNat C exponent choice) 1 0)
    (h20 :
      flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (2 : Fin 3) ∈
        lossEarliestPairWords (lossSliceAtNat C exponent choice) 2 0)
    (h21 :
      flipBoolWordAt (flipBoolWordAt q (1 : Fin 3)) (2 : Fin 3) ∈
        lossEarliestPairWords (lossSliceAtNat C exponent choice) 2 1) :
    (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card ≤ 2 := by
  classical
  have hsub := actual_three_colour_triple_collision_all_true_holes_subset_pair
    C exponent choice q h10 h20 h21
  have hcard := Finset.card_le_card hsub
  have hpair : ({q, (fun i => !(q i))} : Finset (Fin 3 → Bool)).card ≤ 2 := by
    simp [Finset.card_insert_eq_ite]
    split_ifs <;> omega
  omega

#print axioms bool_three_triple_square_cover
#print axioms actual_three_colour_triple_collision_all_true_holes_subset_pair
#print axioms actual_three_colour_triple_collision_true_holes_card_le_two

end OrderedEdgeColoring
end JSP000404Research
