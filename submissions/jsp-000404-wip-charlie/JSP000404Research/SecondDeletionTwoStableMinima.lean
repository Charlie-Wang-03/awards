
import JSP000404Research.SecondDeletionSlack
import JSP000404Research.MinimalOverweightDyadicRigidity
import Mathlib.Tactic

/-!
# Two stable minimum survivors in a second deletion

Assume a first minimum deletion has produced an exact child of total dyadic
mass 2^n and has left all survivor exponents unchanged.

Inside that child, delete a second vertex s from the same minimum layer.  If
the second child is still bounded by 2^n, SecondDeletionSlack says that among
the surviving minimum-layer vertices at most one can gain a full exponent
unit.

Hence, if at least three minimum-layer vertices other than s survive in the
first child, at least two of them have no unit gain in the second deletion.

This is the combinatorial bridge needed before applying local two-step merge
rigidity at concrete survivor centres.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Minimum-layer vertices of a profile at level a. -/
def exponentLayer
    {V : Type*} [Fintype V]
    (exponent : V → ℕ) (a : ℕ) : Finset V :=
  Finset.univ.filter fun v => exponent v = a

@[simp] theorem mem_exponentLayer
    {V : Type*} [Fintype V]
    (exponent : V → ℕ) (a : ℕ) (v : V) :
    v ∈ exponentLayer exponent a ↔ exponent v = a := by
  simp [exponentLayer]

/-- Vertices in the minimum layer, different from the second deleted vertex,
which acquire a full unit gain in that deletion column. -/
def secondGainMinima
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (a : ℕ) (s : V) : Finset V :=
  Finset.univ.filter fun v =>
    v ≠ s ∧ exponent v = a ∧ exponent v + 1 ≤ after s v

@[simp] theorem mem_secondGainMinima
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (a : ℕ) (s v : V) :
    v ∈ secondGainMinima exponent after a s ↔
      v ≠ s ∧ exponent v = a ∧
        exponent v + 1 ≤ after s v := by
  simp [secondGainMinima]

/-- SecondDeletionSlack implies that at most one surviving minimum vertex can
gain a full unit. -/
theorem secondGainMinima_card_le_one
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
    (secondGainMinima exponent after a s).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hj' :=
    (mem_secondGainMinima exponent after a s j).1 hj
  have hk' :=
    (mem_secondGainMinima exponent after a s k).1 hk
  by_contra hjk
  exact
    (no_two_secondDeletion_min_unit_gains
      exponent after n a s j k
      htotal hs hmono hpost
      hj'.1 hk'.1 hjk hj'.2.1 hk'.2.1)
      ⟨hj'.2.2, hk'.2.2⟩

/-- If the minimum layer has at least four vertices including s, then after
deleting s at least two surviving minimum vertices have no unit gain. -/
theorem exists_two_minimum_survivors_without_second_gain
    {V : Type*} [Fintype V] [DecidableEq V]
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
      deletionPostWeight after s ≤ 2 ^ n)
    (hlayer :
      4 ≤ (exponentLayer exponent a).card) :
    ∃ j k : V,
      j ≠ k ∧ j ≠ s ∧ k ≠ s ∧
      exponent j = a ∧ exponent k = a ∧
      ¬ exponent j + 1 ≤ after s j ∧
      ¬ exponent k + 1 ≤ after s k := by
  classical
  let M := exponentLayer exponent a
  let G := secondGainMinima exponent after a s
  let T := M.erase s
  let Z := T  G
  have hsM : s ∈ M := by
    simpa [M] using hs
  have hTcard :
      3 ≤ T.card := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hsM]
    omega
  have hGcard :
      G.card ≤ 1 :=
    secondGainMinima_card_le_one
      exponent after n a s htotal hs hmono hpost
  have hInter :
      (T ∩ G).card ≤ 1 := by
    exact (Finset.card_le_card Finset.inter_subset_right).trans hGcard
  have hsplit :=
    Finset.card_sdiff_add_card_inter T G
  have hZcard : 1 < Z.card := by
    dsimp [Z]
    omega
  obtain ⟨j, hjZ, k, hkZ, hjk⟩ :=
    Finset.one_lt_card.mp hZcard
  have hjData :
      j ∈ T ∧ j ∉ G := by
    simpa [Z] using hjZ
  have hkData :
      k ∈ T ∧ k ∉ G := by
    simpa [Z] using hkZ
  have hjM :
      j ∈ M := (Finset.mem_erase.mp hjData.1).2
  have hkM :
      k ∈ M := (Finset.mem_erase.mp hkData.1).2
  have hjs :
      j ≠ s := (Finset.mem_erase.mp hjData.1).1
  have hks :
      k ≠ s := (Finset.mem_erase.mp hkData.1).1
  have hjExp :
      exponent j = a := by
    simpa [M] using hjM
  have hkExp :
      exponent k = a := by
    simpa [M] using hkM
  have hjNo :
      ¬ exponent j + 1 ≤ after s j := by
    intro hgain
    exact hjData.2
      ((mem_secondGainMinima exponent after a s j).2
        ⟨hjs, hjExp, hgain⟩)
  have hkNo :
      ¬ exponent k + 1 ≤ after s k := by
    intro hgain
    exact hkData.2
      ((mem_secondGainMinima exponent after a s k).2
        ⟨hks, hkExp, hgain⟩)
  exact ⟨j, k, hjk, hjs, hks,
    hjExp, hkExp, hjNo, hkNo⟩

/-- Five root minimum vertices remain sufficient after one first minimum
deletion: the first child has at least four vertices in the same minimum
layer, so a second bounded minimum deletion leaves two no-gain minimum
survivors. -/
theorem exists_two_no_gain_minima_after_first_minimum_removed
    {V : Type*} [Fintype V] [DecidableEq V]
    (rootExponent : V → ℕ)
    (r s : V)
    (a : ℕ)
    (hr : rootExponent r = a)
    (hs : rootExponent s = a)
    (hrs : r ≠ s)
    (hlayer :
      5 ≤ (exponentLayer rootExponent a).card) :
    4 ≤
      ((exponentLayer rootExponent a).erase r).card := by
  have hrM :
      r ∈ exponentLayer rootExponent a := by
    simpa using hr
  rw [Finset.card_erase_of_mem hrM]
  omega

#print axioms secondGainMinima_card_le_one
#print axioms exists_two_minimum_survivors_without_second_gain
#print axioms exists_two_no_gain_minima_after_first_minimum_removed

end JSP000404Research
