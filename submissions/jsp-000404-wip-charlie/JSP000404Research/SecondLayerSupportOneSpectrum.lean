import JSP000404Research.DeficitTwo
import JSP000404Research.SupportTwoNarrowClusters
import Mathlib.Tactic

/-!
# Support-one deficit-two quotient spectrum

At a second-layer centre the deficit is exactly two.  In the support-one
branch, DeficitTwo forces total quotient sum n-1.  Since there is only one
positive quotient, every canonical quotient is therefore either zero or n-1.
-/

namespace JSP000404Research

theorem list_sum_eq_single_positive_of_positiveCount_one
    (qs : List ℕ) {q : ℕ}
    (hq0 : q ≠ 0)
    (hsupport : listPositiveCount qs = 1)
    (hqmem : q ∈ qs) :
    qs.sum = q := by
  obtain ⟨left,right,hsplit,hleft,hright⟩ :=
    split_unique_positive_of_count_one
      qs q hq0 hsupport hqmem
  have zeroSum :
      ∀ xs : List ℕ,
        (∀ x ∈ xs, x = 0) →
        xs.sum = 0 := by
    intro xs hzero
    induction xs with
    | nil => simp
    | cons x xs ih =>
        have hx : x = 0 := hzero x (by simp)
        have htail :
            ∀ y ∈ xs, y = 0 := by
          intro y hy
          exact hzero y (by simp [hy])
        simp [hx, ih htail]
  rw [hsplit]
  rw [List.sum_append, List.sum_cons,
      zeroSum left hleft, zeroSum right hright]
  simp

theorem deficitTwo_supportOne_quotient_spectrum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1) :
    ∀ q ∈ quotientList t C.gaps,
      q = 0 ∨ q = n - 1 := by
  have hQ :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 2 := by
    change n - centreExponent C t = 2
    rw [hexp]
    omega
  have hstruct :=
    deficit_two_structure
      (centreQuotient C t) n hn3 hQ hdef
  have hsumFn :
      (∑ r, centreQuotient C t r) = n - 1 := by
    rcases hstruct with h1 | h2
    · exact h1.2
    · rw [hsupport] at h2
      omega
  have hsumList :
      (quotientList t C.gaps).sum = n - 1 := by
    rw [← centreQuotient_sum_eq_list_sum C t]
    exact hsumFn
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 1 := by
    rw [← centreQuotient_ofFn C t,
        listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport

  intro q hqmem
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  · right
    have hsumEq :=
      list_sum_eq_single_positive_of_positiveCount_one
        (quotientList t C.gaps)
        hq0 hsupportList hqmem
    rw [hsumList] at hsumEq
    exact hsumEq.symm

#print axioms list_sum_eq_single_positive_of_positiveCount_one
#print axioms deficitTwo_supportOne_quotient_spectrum

end JSP000404Research
