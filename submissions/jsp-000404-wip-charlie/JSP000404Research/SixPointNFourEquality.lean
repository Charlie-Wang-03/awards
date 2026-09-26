import JSP000404Research.SixPointUnitGapBudget
import JSP000404Research.ConcreteDeficitThree
import Mathlib.Tactic

/-!
# Equality case of the ten unit-gap budget at n=4

In the six-point terminal with n=4, the profile is one top centre with
exponent 3 and five minimum centres with exponent 1.

The global unit-gap budget is at most ten. If equality holds, every minimum
centre attains its individual upper bound two.

For a minimum centre, floorExcess(q)=1 and support(q)<=3. Two unit
coordinates contribute support two and zero excess. Positive excess one
therefore forces exactly one further positive coordinate, equal to two.
Thus every minimum quotient vector has positive multiset {1,1,2}.
In a six-point configuration the full quotient cycle has length five, hence
the multiset is exactly {1,1,2,0,0}.
-/

namespace JSP000404Research

open scoped BigOperators

def twoSupport
    {I : Type*} [Fintype I]
    (q : I → ℕ) : ℕ :=
  ∑ i, if q i = 2 then 1 else 0

theorem floorExcess_eq_one_unitSupport_eq_two_support_le_three_shape
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hex : floorExcess q = 1)
    (hunit : unitSupport q = 2)
    (hsupp : positiveSupport q ≤ 3) :
    positiveSupport q = 3 ∧
    twoSupport q = 1 ∧
    ∀ i, q i ≠ 0 → q i = 1 ∨ q i = 2 := by
  classical
  have hnonunit :
      nonUnitPositiveSupport q = 1 := by
    have hsplit := positiveSupport_eq_unit_add_nonUnit q
    have hpos :=
      nonUnitPositiveSupport_pos_of_floorExcess_pos q (by omega)
    have hsupp' : unitSupport q + nonUnitPositiveSupport q ≤ 3 := by
      rwa [← hsplit]
    omega
  have hposSupp : positiveSupport q = 3 := by
    rw [positiveSupport_eq_unit_add_nonUnit q, hunit, hnonunit]
  have hall :
      ∀ i, q i ≠ 0 → q i = 1 ∨ q i = 2 := by
    intro i hi
    by_cases h1 : q i = 1
    · exact Or.inl h1
    · have h2le : 2 ≤ q i := by omega
      by_contra h2
      have h3 : 3 ≤ q i := by omega
      have hterm : 2 ≤ q i - 1 := by omega
      unfold floorExcess at hex
      have hsingle :
          q i - 1 ≤ ∑ j : I, (q j - 1) :=
        Finset.single_le_sum
          (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      rw [hex] at hsingle
      omega
  have htwoCard : twoSupport q = 1 := by
    have hEq :
        twoSupport q = nonUnitPositiveSupport q := by
      unfold twoSupport nonUnitPositiveSupport
      apply Finset.sum_congr rfl
      intro i _
      by_cases h2 : q i = 2
      · simp [h2]
      · by_cases hle : 2 ≤ q i
        · have hi0 : q i ≠ 0 := by omega
          have hshape := hall i hi0
          rcases hshape with h1 | h2'
          · omega
          · exact False.elim (h2 h2')
        · simp [h2, hle]
    rw [hEq, hnonunit]
  exact ⟨hposSupp, htwoCard, hall⟩

theorem six_point_unitSupport_sum_eq_ten_forces_every_min_two
    {V : Type*} [Fintype V]
    (u : V → ℕ)
    (top : V)
    (hcard : Fintype.card V = 6)
    (htop : u top = 0)
    (hmin : ∀ i, i ≠ top → u i ≤ 2)
    (hsum : (∑ i : V, u i) = 10) :
    ∀ i, i ≠ top → u i = 2 := by
  classical
  intro i hitop
  have hothers :
      ∑ j ∈ (Finset.univ.erase top), u j = 10 := by
    have hsplit :=
      Finset.sum_erase_add (Finset.univ : Finset V) u
        (Finset.mem_univ top)
    rw [htop, add_zero] at hsplit
    rw [← hsplit]
    exact hsum
  have hcount :
      (Finset.univ.erase top).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ top)]
    simp [hcard]
  by_contra hne
  have hui : u i ≤ 1 := by
    have := hmin i hitop
    omega
  have hiMem : i ∈ Finset.univ.erase top := by
    simp [hitop]
  let T := (Finset.univ.erase top).erase i
  have hTcard : T.card = 4 := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hiMem, hcount]
  have hrest :
      ∑ j ∈ T, u j ≤ 2 * T.card := by
    calc
      ∑ j ∈ T, u j ≤ ∑ _j ∈ T, 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjTop : j ≠ top := by
          have hjOuter :
              j ∈ Finset.univ.erase top :=
            Finset.mem_of_mem_erase hj
          exact (Finset.mem_erase.mp hjOuter).1
        exact hmin j hjTop
      _ = 2 * T.card := by simp [Nat.mul_comm]
  have hsplit :
      ∑ j ∈ (Finset.univ.erase top), u j =
        u i + ∑ j ∈ T, u j := by
    dsimp [T]
    rw [← Finset.add_sum_erase
      (Finset.univ.erase top) u hiMem]
  rw [hothers, hsplit, hTcard] at hrest
  omega

theorem six_point_n_four_unit_budget_equality_forces_11200
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V,
        unitSupport (centreQuotient (C i) t)) = 10) :
    ∀ i : V, i ≠ top →
      unitSupport (centreQuotient (C i) t) = 2 ∧
      positiveSupport (centreQuotient (C i) t) = 3 ∧
      twoSupport (centreQuotient (C i) t) = 1 ∧
      ∀ r,
        centreQuotient (C i) t r ≠ 0 →
        centreQuotient (C i) t r = 1 ∨
          centreQuotient (C i) t r = 2 := by
  have hdelta1 : delta < 1 := by linarith
  have htop0 :
      unitSupport (centreQuotient (C top) t) = 0 :=
    centre_unitSupport_eq_zero_of_exponent_n_sub_one
      (C top) (by norm_num : 4 ≤ 4)
      hdelta0 hdelta1 ht hTop
  have hmin2 :
      ∀ i : V, i ≠ top →
        unitSupport (centreQuotient (C i) t) ≤ 2 := by
    intro i hi
    exact centre_unitSupport_le_two_of_exponent_n_sub_three
      (C i) (by norm_num : 4 ≤ 4)
      hdelta0 hdelta1 ht
      (by simpa using hMin i hi)
  have hevery :=
    six_point_unitSupport_sum_eq_ten_forces_every_min_two
      (fun i => unitSupport (centreQuotient (C i) t))
      top hcard htop0 hmin2 hunitTotal
  intro i hitop
  have hu := hevery i hitop
  have hex :
      floorExcess (centreQuotient (C i) t) = 1 := by
    change centreExponent (C i) t = 1
    exact hMin i hitop
  have hsum :=
    centreQuotient_function_sum_le_n
      (C i) 4 delta t (by norm_num)
      hdelta0 hdelta1 ht
  have hsupp :
      positiveSupport (centreQuotient (C i) t) ≤ 3 := by
    have h :=
      positiveSupport_le_deficit
        (centreQuotient (C i) t) 4 hsum
    rw [hex] at h
    omega
  have hshape :=
    floorExcess_eq_one_unitSupport_eq_two_support_le_three_shape
      (centreQuotient (C i) t) hex hu hsupp
  exact ⟨hu, hshape.1, hshape.2.1, hshape.2.2⟩

#print axioms floorExcess_eq_one_unitSupport_eq_two_support_le_three_shape
#print axioms six_point_unitSupport_sum_eq_ten_forces_every_min_two
#print axioms six_point_n_four_unit_budget_equality_forces_11200

end JSP000404Research
