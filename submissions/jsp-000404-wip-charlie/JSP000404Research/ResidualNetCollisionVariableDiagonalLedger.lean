import JSP000404Research.ResidualTwoFlipDiagonalGlobalCollisionRigidity
import Mathlib.Tactic

/-!
# Exact global VARIABLE-COLOUR diagonal allocation for actual NET collisions

Previous two-class cardinality lemmas assume fixed flip colours on
each class and four-coordinate separation between two classes.
Neither premise has been established globally under planar AngleCap.

Here BOTH selected colours are allowed to depend on each genuine
NET forward/reverse sink collision word. No pairwise separation,
no global injectivity, and no absence of external centres is
assumed. The actual collision source set is the exact image
intersection, not the hypothetical bridge union.

The exact global conservation identity is

   |NET actual sink collisions|
     = |distinct TRUE-hole diagonals|
       + |distinct COVERED diagonals|
       + |duplicate diagonal hits|.

The duplicate term is defined as source size minus distinct
target-image size and is always nonnegative. It measures exactly
how much globally injective hole-credit would be double-booked.
Covered diagonals still cannot be claimed as true holes or
genuinely unreserved profile surplus.

A second theorem confines every duplicate pair of actual source
words to disagreement on at most the four coordinates selected
by their two source-dependent colour pairs.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A variable-colour double-flip target from an actual NET collision
sink word. The colour functions can vary per source word. -/
noncomputable def netCollisionVariableDiagonalWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (forwardColour reverseColour : (Fin n → Bool) → Fin n) :
    Finset (Fin n → Bool) := by
  classical
  exact
    (netActualForwardReverseCollisionWords C exponent hexp honeLoss).image
      (fun w => flipCompletionWord (forwardColour w)
        (flipCompletionWord (reverseColour w) w))

/-- DISTINCT actual diagonal targets that are genuine global holes. -/
noncomputable def netCollisionVariableTrueHoleDiagonals
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (forwardColour reverseColour : (Fin n → Bool) → Fin n) :
    Finset (Fin n → Bool) :=
  netCollisionVariableDiagonalWords C exponent hexp honeLoss
      forwardColour reverseColour ∩
    ((Finset.univ : Finset (Fin n → Bool)) \
      coveredCompletionWords C)

/-- DISTINCT actual diagonal targets already globally covered. -/
noncomputable def netCollisionVariableCoveredDiagonals
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (forwardColour reverseColour : (Fin n → Bool) → Fin n) :
    Finset (Fin n → Bool) :=
  netCollisionVariableDiagonalWords C exponent hexp honeLoss
      forwardColour reverseColour ∩ coveredCompletionWords C

/-- Exact number of source hits lost by collapsing identical
double-flip targets. It is ZERO precisely when the map is
injective on the actual NET collision set. -/
noncomputable def netCollisionVariableDuplicateDebt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (forwardColour reverseColour : (Fin n → Bool) → Fin n) : ℕ :=
  (netActualForwardReverseCollisionWords C exponent hexp honeLoss).card -
    (netCollisionVariableDiagonalWords C exponent hexp honeLoss
      forwardColour reverseColour).card

/-- Exact global accounting with NO fixed-pair, separation, or
hole-availability hypothesis. This is an unconditional refinement
of the earlier conditional two-class hole-capacity result. -/
theorem net_collision_variable_diagonal_exact_three_debts
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (forwardColour reverseColour : (Fin n → Bool) → Fin n) :
    (netActualForwardReverseCollisionWords C exponent hexp honeLoss).card =
      (netCollisionVariableTrueHoleDiagonals
        C exponent hexp honeLoss forwardColour reverseColour).card +
      (netCollisionVariableCoveredDiagonals
        C exponent hexp honeLoss forwardColour reverseColour).card +
      netCollisionVariableDuplicateDebt
        C exponent hexp honeLoss forwardColour reverseColour := by
  classical
  let S := netActualForwardReverseCollisionWords C exponent hexp honeLoss
  let D := netCollisionVariableDiagonalWords C exponent hexp honeLoss
    forwardColour reverseColour
  let K := coveredCompletionWords C
  let H := (Finset.univ : Finset (Fin n → Bool)) \ K
  have hpart : D = (D ∩ H) ∪ (D ∩ K) := by
    ext d
    by_cases hd : d ∈ K <;> simp [H, hd]
  have hdisj : Disjoint (D ∩ H) (D ∩ K) := by
    apply Finset.disjoint_left.mpr
    intro d hH hK
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hH).2).2
      (Finset.mem_inter.mp hK).2
  have hsplit : D.card = (D ∩ H).card + (D ∩ K).card := by
    calc
      D.card = ((D ∩ H) ∪ (D ∩ K)).card := by rw [← hpart]
      _ = (D ∩ H).card + (D ∩ K).card :=
        Finset.card_union_of_disjoint hdisj
  have hsize : D.card ≤ S.card := by
    unfold D netCollisionVariableDiagonalWords
    exact Finset.card_image_le
  change S.card = (D ∩ H).card + (D ∩ K).card +
    (S.card - D.card)
  omega

/-- Every actual NET collision source is chargeable to a TRUE hole,
a covered diagonal blocker, or a duplicate-target debt, without
double-counting image points. -/
theorem net_collision_variable_hole_capacity_with_two_obstructions
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (forwardColour reverseColour : (Fin n → Bool) → Fin n) :
    (netActualForwardReverseCollisionWords C exponent hexp honeLoss).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (netCollisionVariableCoveredDiagonals
        C exponent hexp honeLoss forwardColour reverseColour).card +
      netCollisionVariableDuplicateDebt
        C exponent hexp honeLoss forwardColour reverseColour := by
  have heq := net_collision_variable_diagonal_exact_three_debts
    C exponent hexp honeLoss forwardColour reverseColour
  have hhole :
      (netCollisionVariableTrueHoleDiagonals
        C exponent hexp honeLoss forwardColour reverseColour).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card := by
    apply Finset.card_le_card
    intro d hd
    exact (Finset.mem_inter.mp hd).2
  omega

/-- For possibly SOURCE-DEPENDENT flip colours, two actual NET
collisions can map to the same diagonal only if their sink words
agree outside their four selected flip coordinates. Unlike
the earlier two-class result, no colours need to be constant
on entire carrier or bridge families. -/
theorem net_collision_variable_equal_diagonals_agree_outside_four
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (forwardColour reverseColour : (Fin n → Bool) → Fin n)
    (w z : Fin n → Bool)
    (_hw : w ∈ netActualForwardReverseCollisionWords
      C exponent hexp honeLoss)
    (_hz : z ∈ netActualForwardReverseCollisionWords
      C exponent hexp honeLoss)
    (heq :
      flipCompletionWord (forwardColour w)
        (flipCompletionWord (reverseColour w) w) =
      flipCompletionWord (forwardColour z)
        (flipCompletionWord (reverseColour z) z))
    (e : Fin n)
    (hfW : e ≠ forwardColour w)
    (hrW : e ≠ reverseColour w)
    (hfZ : e ≠ forwardColour z)
    (hrZ : e ≠ reverseColour z) :
    w e = z e :=
  double_flip_target_eq_source_agree_outside_four w z
    (forwardColour w) (reverseColour w)
    (forwardColour z) (reverseColour z) heq e hfW hrW hfZ hrZ

#print axioms net_collision_variable_diagonal_exact_three_debts
#print axioms net_collision_variable_hole_capacity_with_two_obstructions
#print axioms net_collision_variable_equal_diagonals_agree_outside_four

end OrderedEdgeColoring
end JSP000404Research
