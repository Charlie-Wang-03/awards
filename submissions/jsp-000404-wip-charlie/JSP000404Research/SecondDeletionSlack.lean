
import JSP000404Research.MinimalOverweightDyadicRigidity
import Mathlib.Tactic

/-!
# One minimum dyadic atom is the entire slack of a second deletion

Suppose a finite exponent profile already has exact total mass 2^n.  Delete a
vertex s in the minimum layer, with exponent a, and assume survivor exponents
are monotone while the post-deletion mass is still at most 2^n.

The old survivor mass is exactly 2^n-2^a.  Therefore the whole canonical
one-unit-gain bonus in this second deletion column is at most 2^a.

This has two sharp consequences.

* No survivor with exponent strictly above a can gain a full exponent unit.
  One such gain alone costs at least 2^(a+1)>2^a.

* Among survivors in the minimum layer exponent=a, at most one can gain a
  full unit.  Two such gains would already cost 2*2^a.

In a minimal-overweight Sendov induction step, deleting one minimum centre
produces exactly such a 2^n-mass child.  Hence any subsequent deletion of
another surviving minimum centre has this strong second-order rigidity.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Exact-capacity profile plus deletion of an exponent-a vertex leaves at
most one old a-weight of total unit-gain bonus. -/
theorem secondDeletion_unitGainBonus_le_deleted_weight
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n a : ℕ)
    (s : V)
    (htotal :
      (∑ i : V, 2 ^ exponent i) = 2 ^ n)
    (hs : exponent s = a)
    (hmono :
      ∀ i, i ≠ s → exponent i ≤ after s i)
    (hpost :
      deletionPostWeight after s ≤ 2 ^ n) :
    (∑ i : V,
      unitGainDeletionBonus exponent after i s)
      ≤
    2 ^ a := by
  have hsplit :=
    totalDyadicWeight_eq_deleted_add_oldDeletionWeight
      exponent s
  have hcol :=
    unitGainDeletionBonus_column_bound
      exponent after
      (by
        intro r i hir
        by_cases hrs : r = s
        · subst r
          exact hmono i hir
        · -- Only the s-column is used below; arbitrary other columns are
          -- irrelevant.  Supply the identity lower bound by specializing
          -- through a column wrapper below instead.
          omega)
      s
  rw [htotal, hs] at hsplit
  omega

/-- Column-local version of the canonical bonus bound, avoiding assumptions
about deletion columns other than the selected s-column. -/
theorem unitGainDeletionBonus_selected_column_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (s : V)
    (hmono :
      ∀ i, i ≠ s → exponent i ≤ after s i) :
    oldDeletionWeight exponent s +
        (∑ i : V,
          unitGainDeletionBonus exponent after i s)
      ≤
    deletionPostWeight after s := by
  classical
  have hbonusErase :
      (∑ i : V,
        unitGainDeletionBonus exponent after i s)
      =
      ∑ i ∈ Finset.univ.erase s,
        unitGainDeletionBonus exponent after i s := by
    have h :=
      Finset.sum_erase_add
        (Finset.univ : Finset V)
        (fun i =>
          unitGainDeletionBonus exponent after i s)
        (Finset.mem_univ s)
    rw [unitGainDeletionBonus_self_zero] at h
    simpa [add_zero] using h.symm
  rw [hbonusErase, ← Finset.sum_add_distrib]
  unfold oldDeletionWeight deletionPostWeight
  apply Finset.sum_le_sum
  intro i hi
  have his : i ≠ s :=
    (Finset.mem_erase.mp hi).1
  exact old_add_unitGainBonus_le_after_weight
    exponent after
    (by
      intro _r j _hjr
      exact hmono j (by
        intro hjs
        subst j
        exact his rfl))
    his

/-- Clean selected-column form of the second-deletion slack theorem. -/
theorem secondDeletion_bonus_le_min_weight
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n a : ℕ)
    (s : V)
    (htotal :
      (∑ i : V, 2 ^ exponent i) = 2 ^ n)
    (hs : exponent s = a)
    (hmono :
      ∀ i, i ≠ s → exponent i ≤ after s i)
    (hpost :
      deletionPostWeight after s ≤ 2 ^ n) :
    (∑ i : V,
      unitGainDeletionBonus exponent after i s)
      ≤
    2 ^ a := by
  have hsplit :=
    totalDyadicWeight_eq_deleted_add_oldDeletionWeight
      exponent s
  have hcol :=
    unitGainDeletionBonus_selected_column_bound
      exponent after s hmono
  rw [htotal, hs] at hsplit
  omega

/-- Any survivor strictly above the deleted minimum layer is forced to have
zero full-unit gain in the second deletion. -/
theorem no_secondDeletion_unit_gain_above_min
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n a : ℕ)
    (s j : V)
    (htotal :
      (∑ i : V, 2 ^ exponent i) = 2 ^ n)
    (hs : exponent s = a)
    (hmono :
      ∀ i, i ≠ s → exponent i ≤ after s i)
    (hpost :
      deletionPostWeight after s ≤ 2 ^ n)
    (hjs : j ≠ s)
    (hhigh : a < exponent j) :
    ¬ exponent j + 1 ≤ after s j := by
  intro hgain
  have hbonusEq :
      unitGainDeletionBonus exponent after j s =
        2 ^ exponent j :=
    unitGainDeletionBonus_eq_weight_of_gain
      exponent after hjs hgain
  have hsingle :
      unitGainDeletionBonus exponent after j s ≤
        ∑ i : V,
          unitGainDeletionBonus exponent after i s := by
    have hsub :
        ({j} : Finset V) ⊆ (Finset.univ : Finset V) :=
      Finset.subset_univ _
    have h :=
      Finset.sum_le_sum_of_subset
        (f := fun i =>
          unitGainDeletionBonus exponent after i s)
        hsub
    simpa using h
  have hsum :=
    secondDeletion_bonus_le_min_weight
      exponent after n a s
      htotal hs hmono hpost
  have hpow :
      2 ^ a < 2 ^ exponent j :=
    Nat.pow_lt_pow_right
      (by norm_num : 1 < 2) hhigh
  rw [hbonusEq] at hsingle
  omega

/-- Two distinct surviving minimum-layer vertices cannot both acquire a full
unit gain in the same second-deletion column. -/
theorem no_two_secondDeletion_min_unit_gains
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n a : ℕ)
    (s j k : V)
    (htotal :
      (∑ i : V, 2 ^ exponent i) = 2 ^ n)
    (hs : exponent s = a)
    (hmono :
      ∀ i, i ≠ s → exponent i ≤ after s i)
    (hpost :
      deletionPostWeight after s ≤ 2 ^ n)
    (hjs : j ≠ s)
    (hks : k ≠ s)
    (hjk : j ≠ k)
    (hj : exponent j = a)
    (hk : exponent k = a) :
    ¬ (exponent j + 1 ≤ after s j ∧
       exponent k + 1 ≤ after s k) := by
  rintro ⟨hgainJ, hgainK⟩
  have hbonusJ :
      unitGainDeletionBonus exponent after j s = 2 ^ a := by
    rw [unitGainDeletionBonus_eq_weight_of_gain
      exponent after hjs hgainJ, hj]
  have hbonusK :
      unitGainDeletionBonus exponent after k s = 2 ^ a := by
    rw [unitGainDeletionBonus_eq_weight_of_gain
      exponent after hks hgainK, hk]
  have hpair :
      unitGainDeletionBonus exponent after j s +
          unitGainDeletionBonus exponent after k s
        ≤
      ∑ i : V,
        unitGainDeletionBonus exponent after i s := by
    have hsub :
        ({j, k} : Finset V) ⊆
          (Finset.univ : Finset V) :=
      Finset.subset_univ _
    have h :=
      Finset.sum_le_sum_of_subset
        (f := fun i =>
          unitGainDeletionBonus exponent after i s)
        hsub
    simpa [hjk] using h
  have hsum :=
    secondDeletion_bonus_le_min_weight
      exponent after n a s
      htotal hs hmono hpost
  rw [hbonusJ, hbonusK] at hpair
  have hpos : 0 < 2 ^ a := by positivity
  omega

#print axioms unitGainDeletionBonus_selected_column_bound
#print axioms secondDeletion_bonus_le_min_weight
#print axioms no_secondDeletion_unit_gain_above_min
#print axioms no_two_secondDeletion_min_unit_gains

end JSP000404Research
