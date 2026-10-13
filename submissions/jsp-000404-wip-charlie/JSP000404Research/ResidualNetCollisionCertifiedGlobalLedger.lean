import JSP000404Research.ResidualNetCollisionCertifiedDiagonalWitness
import Mathlib.Tactic

/-!
# Genuine global NET-collision diagonal allocation: certified colours

The SOURCE of each diagonal in this file is an ACTUAL forward/reverse
NET collision word, and the selected two flip colours come from its
unique original forward hard carrier and reverse strict-rigid carrier.
The previous variable-colour global ledger required external colour
selector functions; this version is attached to ACTUAL certified
sources and needs no such extra data.

Exact equality:
  |net actual collisions| =
    |distinct true-hole diagonals|
      + |distinct globally covered diagonals|
      + |duplicate actual diagonal hits|.

The two still-obstructing sets/debts are retained explicitly;
this is NOT an unproved claim of total hole payment or no reuse.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Actual diagonal image, with each member's two colours
uniquely determined by its original hard transport sources. -/
noncomputable def netCollisionCertifiedDiagonalWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Finset (Fin n → Bool) := by
  classical
  exact (Finset.univ : Finset
    {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}).image
    (netCollisionCertifiedDiagonal C exponent hexp honeLoss)

/-- DISTINCT genuinely uncovered targets of certified actual
NET-collision opposite diagonals. -/
noncomputable def netCollisionCertifiedTrueHoleDiagonals
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Finset (Fin n → Bool) :=
  netCollisionCertifiedDiagonalWords C exponent hexp honeLoss ∩
    ((Finset.univ : Finset (Fin n → Bool)) \
      coveredCompletionWords C)

/-- DISTINCT actual diagonal targets occupied by at least
one other completion centre. Not Boolean holes. -/
noncomputable def netCollisionCertifiedCoveredDiagonals
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Finset (Fin n → Bool) :=
  netCollisionCertifiedDiagonalWords C exponent hexp honeLoss ∩
    coveredCompletionWords C

/-- Global multiplicity loss for certified original-source
double-flip diagonals: this is the exact amount by which the
variable-colour target mapping FAILS to be injective. -/
noncomputable def netCollisionCertifiedDuplicateDebt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) : ℕ :=
  (netActualForwardReverseCollisionWords C exponent hexp honeLoss).card -
    (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card

/-- The UNCONDITIONAL exact global three-way budget for
ACTUAL collision colours. It needs only the same residual
one-layer hypotheses as the genuine transport maps; no
new source-separation, exterior-hole, or geometric axiom. -/
theorem net_collision_certified_diagonal_exact_three_debts
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netActualForwardReverseCollisionWords C exponent hexp honeLoss).card =
      (netCollisionCertifiedTrueHoleDiagonals
        C exponent hexp honeLoss).card +
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card +
      netCollisionCertifiedDuplicateDebt
        C exponent hexp honeLoss := by
  classical
  let S := netActualForwardReverseCollisionWords C exponent hexp honeLoss
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
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
    have htmp :
        ((Finset.univ : Finset
          {w : Fin n → Bool // w ∈ S}).image
          (netCollisionCertifiedDiagonal C exponent hexp honeLoss)).card ≤
        (Finset.univ : Finset {w : Fin n → Bool // w ∈ S}).card :=
      Finset.card_image_le
    simpa [D, S, netCollisionCertifiedDiagonalWords,
      Finset.card_univ, Fintype.card_coe] using htmp
  change S.card = (D ∩ H).card + (D ∩ K).card +
    (S.card - D.card)
  omega

/-- The resulting GLOBAL hole bound with precisely two quantified
obstructions: DISTINCT covered diagonals and actual multiplicity
debt. This is for certified source-dependent flip colours. -/
theorem net_collision_certified_true_hole_capacity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netActualForwardReverseCollisionWords C exponent hexp honeLoss).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card +
      netCollisionCertifiedDuplicateDebt
        C exponent hexp honeLoss := by
  have hsplit := net_collision_certified_diagonal_exact_three_debts
    C exponent hexp honeLoss
  have hholes :
      (netCollisionCertifiedTrueHoleDiagonals
        C exponent hexp honeLoss).card ≤
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card := by
    apply Finset.card_le_card
    intro d hd
    exact (Finset.mem_inter.mp hd).2
  omega

#print axioms net_collision_certified_diagonal_exact_three_debts
#print axioms net_collision_certified_true_hole_capacity

end OrderedEdgeColoring
end JSP000404Research
