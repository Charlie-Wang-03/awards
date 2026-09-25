
import JSP000404Research.UnitGainDeletionBonus
import Mathlib.Tactic

/-!
# Existence of a stable maximal-exponent centre

UnitGainDeletionBonus proves that any prescribed maximal-exponent centre is
immune to one-unit gains when no deletion is compensated.

For later geometric arguments it is more convenient to package the finite
existence statement: every nonempty finite exponent profile has a maximizer,
and under survivor monotonicity plus global failure of compensated deletion
one may choose such a maximizer which has no full-unit gain in any other
deletion column.
-/

namespace JSP000404Research

/-- A finite nonempty natural-valued profile attains its maximum. -/
theorem exists_maximal_exponent
    {V : Type*} [Fintype V] [Nonempty V]
    (exponent : V → ℕ) :
    ∃ i : V, ∀ j : V, exponent j ≤ exponent i := by
  classical
  let S : Finset V := Finset.univ
  have hS : S.Nonempty := Finset.univ_nonempty
  let i : V := S.max' hS
  -- max' is with respect to the ambient order, not exponent, so use the
  -- finite image of exponent instead.
  let E : Finset ℕ := S.image exponent
  have hE : E.Nonempty := hS.image exponent
  let M : ℕ := E.max' hE
  have hMmem : M ∈ E := Finset.max'_mem E hE
  obtain ⟨i, _hiS, hiM⟩ := Finset.mem_image.mp hMmem
  refine ⟨i, ?_⟩
  intro j
  have hjE : exponent j ∈ E := by
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ j, rfl⟩
  have hjLe : exponent j ≤ M :=
    Finset.le_max' E (exponent j) hjE
  simpa [hiM] using hjLe

/-- There exists a maximal exponent centre with no one-unit survivor gain in
any deletion, provided no deletion is compensated. -/
theorem exists_maximal_no_unit_gain_of_no_compensated
    {V : Type*} [Fintype V] [Nonempty V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (hnocomp :
      ∀ r,
        deletionPostWeight after r <
          ∑ i : V, 2 ^ exponent i) :
    ∃ i : V,
      (∀ j : V, exponent j ≤ exponent i) ∧
      (∀ r : V, i ≠ r →
        ¬ exponent i + 1 ≤ after r i) := by
  obtain ⟨i, hmax⟩ :=
    exists_maximal_exponent exponent
  refine ⟨i, hmax, ?_⟩
  exact maximal_exponent_no_unit_gain_of_no_compensated
    exponent after hmono hnocomp i hmax

/-- Contrapositive existence form: if every maximal centre has at least one
unit-gain deletion, then some deletion is compensated. -/
theorem exists_compensated_deletion_of_every_max_has_unit_gain
    {V : Type*} [Fintype V] [Nonempty V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (hunstable :
      ∀ i : V,
        (∀ j : V, exponent j ≤ exponent i) →
        ∃ r : V, i ≠ r ∧
          exponent i + 1 ≤ after r i) :
    ∃ r : V,
      (∑ j : V, 2 ^ exponent j) ≤
        deletionPostWeight after r := by
  obtain ⟨i, hmax⟩ :=
    exists_maximal_exponent exponent
  obtain ⟨r, hir, hgain⟩ :=
    hunstable i hmax
  exact exists_compensated_deletion_of_maximal_unit_gain
    exponent after hmono i hmax
    ⟨r, hir, hgain⟩

#print axioms exists_maximal_exponent
#print axioms exists_maximal_no_unit_gain_of_no_compensated
#print axioms exists_compensated_deletion_of_every_max_has_unit_gain

end JSP000404Research
