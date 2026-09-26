
import JSP000404Research.ConcreteMinimumOverweightRigidity
import JSP000404Research.SecondDeletionSlack
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# The first deleted configuration as a genuine second-deletion workspace

The abstract second-deletion arithmetic becomes useful only after identifying
the first deletion child with an honest finite centre-cycle family.

Fix a parent configuration and delete r.

* The child index type is DeletedVertexType r = {v // v != r}.
* Its cardinality is exactly card(V)-1.
* For every child centre j, restrictDelete applied to the parent cycle C(j)
  is the canonical child CentreProjectiveCycle.
* The sum of child dyadic weights is exactly the parent deletionPostWeight
  column at r.

Hence, when one minimum deletion column is rigid with post mass 2^n, the
resulting child is literally an exact-mass 2^n profile to which
SecondDeletionSlack may be applied for a second deletion.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Deleting one vertex reduces finite cardinality by exactly one. -/
theorem card_deletedVertexType
    {V : Type*} [Fintype V]
    (r : V) :
    Fintype.card (DeletedVertexType r) =
      Fintype.card V - 1 := by
  classical
  have h :=
    Fintype.card_subtype_compl
      (fun v : V => v = r)
  simpa [DeletedVertexType] using h

/-- A parent with at least four vertices leaves a child with at least three,
so the uniform concrete deletion table can be used again inside the child. -/
theorem three_le_card_deletedVertexType
    {V : Type*} [Fintype V]
    (r : V)
    (hcard : 4 ≤ Fintype.card V) :
    3 ≤ Fintype.card (DeletedVertexType r) := by
  rw [card_deletedVertexType r]
  omega

/-- The genuine centre-cycle family on the configuration obtained by deleting
r. -/
noncomputable def deletedCycleFamily
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    (r : V)
    (j : DeletedVertexType r) :
    CentreProjectiveCycle
      (restrictedPoint_injective hp r) j := by
  let hother :
      Nonempty
        (OtherVertex
          (survivingCentre r j.1 j.2)) :=
    child_other_nonempty_of_card_ge_three
      hcard j.2
  have hcycle :=
    (C j.1).restrictDelete r j.2 hother
  simpa [survivingCentre] using hcycle

/-- Child exponent equals the corresponding genuine parent deletion-table
entry. -/
theorem deletedCycleFamily_exponent_eq_concreteDeletionAfter
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    (r : V)
    (j : DeletedVertexType r)
    (t : ℝ) :
    centreExponent
        (deletedCycleFamily C hcard r j) t
      =
    concreteDeletionAfter C hcard t r j.1 := by
  rw [concreteDeletionAfter_eq C hcard t j.2]
  unfold deletedCycleFamily
  simp only
  congr 2

/-- Generic finite sum over the deleted subtype equals the erase-sum over the
parent vertex set. -/
theorem sum_deletedVertexType_eq_sum_erase
    {V : Type*} [Fintype V]
    (f : V → ℕ)
    (r : V) :
    (∑ j : DeletedVertexType r, f j.1)
      =
    ∑ i ∈ (Finset.univ : Finset V).erase r, f i := by
  classical
  have hsub :=
    Fintype.sum_eq_add_sum_subtype_ne f r
  have herase :=
    Finset.add_sum_erase
      (Finset.univ : Finset V) f
      (Finset.mem_univ r)
  omega

/-- Exact first-child mass identity. -/
theorem deletedCycleFamily_dyadicMass_eq_deletionPostWeight
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    (r : V)
    (t : ℝ) :
    (∑ j : DeletedVertexType r,
      2 ^ centreExponent
        (deletedCycleFamily C hcard r j) t)
      =
    deletionPostWeight
      (concreteDeletionAfter C hcard t) r := by
  classical
  calc
    (∑ j : DeletedVertexType r,
      2 ^ centreExponent
        (deletedCycleFamily C hcard r j) t)
        =
      ∑ j : DeletedVertexType r,
        2 ^ concreteDeletionAfter
          C hcard t r j.1 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [deletedCycleFamily_exponent_eq_concreteDeletionAfter]
    _ =
      ∑ i ∈ (Finset.univ : Finset V).erase r,
        2 ^ concreteDeletionAfter C hcard t r i :=
      sum_deletedVertexType_eq_sum_erase
        (fun i =>
          2 ^ concreteDeletionAfter C hcard t r i) r
    _ =
      deletionPostWeight
        (concreteDeletionAfter C hcard t) r := by
          rfl

/-- Root-column pointwise rigidity transports to exact equality of child and
parent exponents. -/
theorem deletedCycleFamily_exponent_eq_parent_of_root_rigid
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    (r : V)
    (t : ℝ)
    (hrigid :
      ∀ i : V, i ≠ r →
        concreteDeletionAfter C hcard t r i =
          centreExponent (C i) t)
    (j : DeletedVertexType r) :
    centreExponent
        (deletedCycleFamily C hcard r j) t
      =
    centreExponent (C j.1) t := by
  rw [deletedCycleFamily_exponent_eq_concreteDeletionAfter]
  exact hrigid j.1 j.2

/-- If the first root deletion column has exact mass 2^n, then the genuine
child cycle family has exact dyadic mass 2^n. -/
theorem deletedCycleFamily_dyadicMass_eq_bound_of_root_column
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    (r : V)
    (t : ℝ)
    (n : ℕ)
    (hpost :
      deletionPostWeight
          (concreteDeletionAfter C hcard t) r
        = 2 ^ n) :
    (∑ j : DeletedVertexType r,
      2 ^ centreExponent
        (deletedCycleFamily C hcard r j) t)
      =
    2 ^ n := by
  rw [deletedCycleFamily_dyadicMass_eq_deletionPostWeight,
      hpost]

#print axioms card_deletedVertexType
#print axioms three_le_card_deletedVertexType
#print axioms deletedCycleFamily_exponent_eq_concreteDeletionAfter
#print axioms sum_deletedVertexType_eq_sum_erase
#print axioms deletedCycleFamily_dyadicMass_eq_deletionPostWeight
#print axioms deletedCycleFamily_exponent_eq_parent_of_root_rigid
#print axioms deletedCycleFamily_dyadicMass_eq_bound_of_root_column

end JSP000404Research
