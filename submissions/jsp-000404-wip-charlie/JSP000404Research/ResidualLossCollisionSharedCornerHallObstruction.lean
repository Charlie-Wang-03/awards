import JSP000404Research.ResidualLossCollisionExactLocalHoleEligibility
import JSP000404Research.ResidualLossEarliestCollision
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

private noncomputable def lossCollisionSquareWords (n : ℕ)
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

/-
Canonicalization note: an arbitrary ordered (c,d,w) collision-record set
is NOT itself a measure of actual duplicate debt: swapping c and d merely
renames the same two-coordinate intersection.  The exact prior-first
coordinate ledger counts each word once for every LATER slice after its
first appearance. The finite records below are taken from those exact
earliest-prior components, and always satisfy j < i.
-/

/-- Concrete earliest-prior collision records from the ORIGINAL duplicate
debt decomposition. A record is (later coordinate i, earliest previous
coordinate j, shared Boolean word); j < i forbids swapping coordinates
into a second, spurious record. -/
noncomputable def actualEarliestLossCollisionRecords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    Finset (Fin n × Fin n × (Fin n → Bool)) :=
  (Finset.univ : Finset (Fin n × Fin n × (Fin n → Bool))).filter
    (fun a =>
      a.2.1 < a.1 ∧
        a.2.2 ∈ lossEarliestPairWords
          (lossSliceAtNat C exponent choice) a.1.val a.2.1.val)

/-- Every genuine prior-first debt record has two DIFFERENT original
chosen-coordinate slices, with the LATER coordinate stored first.
No reverse-coordinate copy was inserted into the debt record set. -/
theorem actual_earliest_loss_collision_record_valid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (a : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice) :
    a.1 ≠ a.2.1 ∧
      a.2.1 < a.1 ∧
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.1 ∧
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.2.1 := by
  classical
  obtain ⟨horder, hfirst⟩ :=
    (Finset.mem_filter.mp ha).2
  have hslices :=
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp hfirst).1)
  have hi :
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.1 := by
    simpa [lossSliceAtNat, a.1.isLt] using hslices.1
  have hj :
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.2.1 := by
    simpa [lossSliceAtNat, a.2.1.isLt] using hslices.2
  exact ⟨(ne_of_lt horder).symm, horder, hi, hj⟩

/-- Exact (not over-counted) earliest-prior collision-source family:
its square-local REAL holes equal the distinct opposite corners which
are actually globally exterior. This now uses the SAME finite records
appearing in the exact original duplicate-debt sum, not arbitrary
ordered coordinate pairs or fabricated hole tokens. -/
theorem actual_earliest_loss_collision_local_holes_exact_image_inter
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    (actualEarliestLossCollisionRecords C exponent choice).biUnion
      (fun a =>
        lossCollisionSquareWords n a ∩
          lossLedgerOutsideTranslatedTrueHoles C exponent choice) =
      ((actualEarliestLossCollisionRecords C exponent choice).image
        (fun a =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)) ∩
        lossLedgerOutsideTranslatedTrueHoles C exponent choice := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  have hvalid : ∀ a ∈ S,
      a.1 ≠ a.2.1 ∧ a.2.1 < a.1 ∧
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.1 ∧
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.2.1 := by
    intro a ha
    exact actual_earliest_loss_collision_record_valid C exponent choice a ha
  exact actual_cross_loss_family_local_holes_exact_image_inter
    C exponent choice S
    (fun a ha => (hvalid a ha).1)
    (fun a ha => (hvalid a ha).2.2.1)
    (fun a ha => (hvalid a ha).2.2.2)

/-- Any two actual earliest-prior records sharing an opposite corner
cannot BOTH be paid by distinct TRUE holes WITHIN their source squares.
This does NOT prohibit other global credits. -/
theorem actual_earliest_loss_collision_local_hall_shortfall_of_reused_corner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hRepeated :
      ((actualEarliestLossCollisionRecords C exponent choice).image
        (fun a =>
          flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1)).card <
        (actualEarliestLossCollisionRecords C exponent choice).card) :
    ¬ (actualEarliestLossCollisionRecords C exponent choice).card ≤
      ((actualEarliestLossCollisionRecords C exponent choice).biUnion
        (fun a =>
          lossCollisionSquareWords n a ∩
            lossLedgerOutsideTranslatedTrueHoles C exponent choice)).card := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  have hvalid : ∀ a ∈ S,
      a.1 ≠ a.2.1 ∧ a.2.1 < a.1 ∧
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.1 ∧
      a.2.2 ∈ translatedLossSliceWords C exponent choice a.2.1 := by
    intro a ha
    exact actual_earliest_loss_collision_record_valid C exponent choice a ha
  exact actual_cross_loss_family_local_hall_shortfall_of_repeated_candidates
    C exponent choice S
    (fun a ha => (hvalid a ha).1)
    (fun a ha => (hvalid a ha).2.2.1)
    (fun a ha => (hvalid a ha).2.2.2)
    hRepeated

#print axioms actual_earliest_loss_collision_record_valid
#print axioms actual_earliest_loss_collision_local_holes_exact_image_inter
#print axioms actual_earliest_loss_collision_local_hall_shortfall_of_reused_corner


#print axioms actual_cross_loss_family_local_holes_exact_image_inter
#print axioms actual_cross_loss_family_local_holes_le_distinct_doubleflips
#print axioms actual_cross_loss_family_local_hall_shortfall_of_repeated_candidates
#print axioms actual_cross_loss_family_common_opposite_local_holes_le_one
#print axioms actual_cross_loss_family_same_opposite_local_hall_shortfall

end OrderedEdgeColoring
end JSP000404Research
