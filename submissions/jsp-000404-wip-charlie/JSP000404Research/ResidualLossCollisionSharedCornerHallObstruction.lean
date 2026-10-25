import JSP000404Research.ResidualLossCollisionExactLocalHoleEligibility
import Mathlib.Tactic

/-!
# Finite-family Hall obstruction for actual two-coordinate collision squares

Each *actual* cross-slice collision square contains at most one true exterior
hole: its opposite double-flip word.  Distinct collision records can have the
SAME opposite word.  This theorem handles an arbitrary finite family of such
records, not just a selected pair.

If all records share one opposite word, the union of ALL their square-local
true exterior holes has cardinality at most one.  Consequently two or more
distinct records in such a family cannot each be paid by distinct *local*
true-hole credits.  This is a genuine Hall-deficient local neighbourhood,
not an assumption that a collision produces a hole.

IMPORTANT: this does not rule out payments by unrelated exterior holes or
genuinely unreserved surplus elsewhere in the global eight-source ledger.
The all-centre AngleCap -> global nonreusing payment obligation remains OPEN.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

private def lossCollisionSquareWords (n : ℕ)
    (a : Fin n × Fin n × (Fin n → Bool)) : Finset (Fin n → Bool) :=
  insert a.2.2
    (insert (flipBoolWordAt a.2.2 a.1)
      (insert (flipBoolWordAt a.2.2 a.2.1)
        ({flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1} :
          Finset (Fin n → Bool))))

/-- Exact source-native finite-family identity: the UNION of all REAL
square-local exterior holes is precisely the set of distinct opposite
double-flip words that are genuinely exterior to every translated loss
and every original retained completion cube.  No credit is invented. -/
theorem actual_cross_loss_family_local_holes_exact_image_inter
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (S : Finset (Fin n × Fin n × (Fin n → Bool)))
    (hdifferent : ∀ a ∈ S, a.1 ≠ a.2.1)
    (hleft : ∀ a ∈ S,
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.1)
    (hright : ∀ a ∈ S,
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.2.1) :
    S.biUnion (fun a =>
      lossCollisionSquareWords n a ∩
        lossLedgerOutsideTranslatedTrueHoles C exponent choice) =
      (S.image (fun a =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)) ∩
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
  classical
  ext target
  constructor
  · intro htarget
    obtain ⟨a, ha, hlocal⟩ := Finset.mem_biUnion.mp htarget
    obtain ⟨hsquare, hhole⟩ := Finset.mem_inter.mp hlocal
    have hSquare :
        target ∈ insert a.2.2
          (insert (flipBoolWordAt a.2.2 a.1)
            (insert (flipBoolWordAt a.2.2 a.2.1)
              ({flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1} :
                Finset (Fin n → Bool)))) := hsquare
    have heq : target =
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 :=
      cross_loss_collision_square_external_hole_only_double_flip
        C exponent choice (hdifferent a ha) (hleft a ha) (hright a ha)
        hSquare hhole
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨a, ha, heq.symm⟩, hhole⟩
  · intro htarget
    obtain ⟨himage, hhole⟩ := Finset.mem_inter.mp htarget
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp himage
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_inter.mpr ⟨?_, hhole⟩⟩
    change target ∈ insert a.2.2
      (insert (flipBoolWordAt a.2.2 a.1)
        (insert (flipBoolWordAt a.2.2 a.2.1)
          ({flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1} :
            Finset (Fin n → Bool))))
    rw [← heq]
    simp

/-- The total number of distinct REAL square-local exterior holes in ANY
finite family of cross-coordinate translated-loss collisions is bounded by
the number of DISTINCT opposite double-flip Boolean words. In particular,
multiplicity of collision records does not multiply true-hole credits. -/
theorem actual_cross_loss_family_local_holes_le_distinct_doubleflips
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (S : Finset (Fin n × Fin n × (Fin n → Bool)))
    (hdifferent : ∀ a ∈ S, a.1 ≠ a.2.1)
    (hleft : ∀ a ∈ S,
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.1)
    (hright : ∀ a ∈ S,
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.2.1) :
    (S.biUnion (fun a =>
      lossCollisionSquareWords n a ∩
        lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card ≤
      (S.image (fun a =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)).card := by
  classical
  have hsubset :
      S.biUnion (fun a =>
        lossCollisionSquareWords n a ∩
          lossLedgerOutsideTranslatedTrueHoles C exponent choice) ⊆
      S.image (fun a =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1) := by
    intro w hw
    obtain ⟨a, ha, hwa⟩ := Finset.mem_biUnion.mp hw
    have hSquare :
        w ∈ insert a.2.2
          (insert (flipBoolWordAt a.2.2 a.1)
            (insert (flipBoolWordAt a.2.2 a.2.1)
              ({flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1} :
                Finset (Fin n → Bool)))) := by
      exact (Finset.mem_inter.mp hwa).1
    have hHole :
        w ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice :=
      (Finset.mem_inter.mp hwa).2
    have hwOpposite :
        w = flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 :=
      cross_loss_collision_square_external_hole_only_double_flip
        C exponent choice (hdifferent a ha) (hleft a ha) (hright a ha)
        hSquare hHole
    exact Finset.mem_image.mpr ⟨a, ha, hwOpposite.symm⟩
  exact Finset.card_le_card hsubset

/-- If there are more distinct collision records than distinct double-flip
candidates, the S-indexed LOCAL square-hole neighbourhood fails Hall's
cardinality test. This does not preclude nonlocal holes or surplus. -/
theorem actual_cross_loss_family_local_hall_shortfall_of_repeated_candidates
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (S : Finset (Fin n × Fin n × (Fin n → Bool)))
    (hdifferent : ∀ a ∈ S, a.1 ≠ a.2.1)
    (hleft : ∀ a ∈ S,
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.1)
    (hright : ∀ a ∈ S,
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.2.1)
    (hRepeated :
      (S.image (fun a =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)).card <
        S.card) :
    ¬ S.card ≤
      (S.biUnion (fun a =>
        lossCollisionSquareWords n a ∩
          lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card := by
  intro hpay
  have hbound :=
    actual_cross_loss_family_local_holes_le_distinct_doubleflips
      C exponent choice S hdifferent hleft hright
  omega

/-- Any finite family of genuine cross-coordinate translated-loss
collisions sharing a single opposite double-flip corner has at most ONE
distinct square-local TRUE exterior-hole credit, including the case where
that common candidate is covered or reused and there are ZERO credits. -/
theorem actual_cross_loss_family_common_opposite_local_holes_le_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (S : Finset (Fin n × Fin n × (Fin n → Bool)))
    (q : Fin n → Bool)
    (hdifferent : ∀ a ∈ S, a.1 ≠ a.2.1)
    (hleft : ∀ a ∈ S,
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.1)
    (hright : ∀ a ∈ S,
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.2.1)
    (hsame : ∀ a ∈ S,
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 = q) :
    (S.biUnion (fun a =>
      lossCollisionSquareWords n a ∩
        lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card ≤ 1 := by
  classical
  have hsubset :
      S.biUnion (fun a =>
        lossCollisionSquareWords n a ∩
          lossLedgerOutsideTranslatedTrueHoles C exponent choice) ⊆
        ({q} : Finset (Fin n → Bool)) := by
    intro w hw
    obtain ⟨a, ha, hwa⟩ := Finset.mem_biUnion.mp hw
    have hSquare :
        w ∈ insert a.2.2
          (insert (flipBoolWordAt a.2.2 a.1)
            (insert (flipBoolWordAt a.2.2 a.2.1)
              ({flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1} :
                Finset (Fin n → Bool)))) := by
      exact (Finset.mem_inter.mp hwa).1
    have hHole :
        w ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice :=
      (Finset.mem_inter.mp hwa).2
    have hwq : w =
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 :=
      cross_loss_collision_square_external_hole_only_double_flip
        C exponent choice (hdifferent a ha) (hleft a ha) (hright a ha)
        hSquare hHole
    exact Finset.mem_singleton.mpr (hwq.trans (hsame a ha))
  exact (Finset.card_le_card hsubset).trans (by simp)

/-- A same-opposite-corner collision family with at least two distinct
records is Hall-deficient if its ONLY eligible resources are the original
exterior true holes INSIDE those collision squares.  It says nothing about
other possible resources in the full payment ledger. -/
theorem actual_cross_loss_family_same_opposite_local_hall_shortfall
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (S : Finset (Fin n × Fin n × (Fin n → Bool)))
    (q : Fin n → Bool)
    (hdifferent : ∀ a ∈ S, a.1 ≠ a.2.1)
    (hleft : ∀ a ∈ S,
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.1)
    (hright : ∀ a ∈ S,
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.2.1)
    (hsame : ∀ a ∈ S,
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 = q)
    (htwo : 2 ≤ S.card) :
    ¬ S.card ≤
      (S.biUnion (fun a =>
        lossCollisionSquareWords n a ∩
          lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card := by
  intro hpay
  have hbound :=
    actual_cross_loss_family_common_opposite_local_holes_le_one
      C exponent choice S q hdifferent hleft hright hsame
  omega

#print axioms actual_cross_loss_family_local_holes_exact_image_inter
#print axioms actual_cross_loss_family_local_holes_le_distinct_doubleflips
#print axioms actual_cross_loss_family_local_hall_shortfall_of_repeated_candidates
#print axioms actual_cross_loss_family_common_opposite_local_holes_le_one
#print axioms actual_cross_loss_family_same_opposite_local_hall_shortfall

end OrderedEdgeColoring
end JSP000404Research
