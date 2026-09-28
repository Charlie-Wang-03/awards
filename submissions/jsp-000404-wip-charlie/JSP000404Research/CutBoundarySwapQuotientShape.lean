import JSP000404Research.CutBoundarySwapWrapQuotient
import JSP000404Research.CutSupportInvariant
import JSP000404Research.CutBadOrdinaryMismatchShape
import Mathlib.Tactic

/-!
# Exact cut quotient shape once the wrap quotient is two

At an exact n-3 six-point minimum, canonical quotient support is preserved by
an arbitrary projective cut.  If the cut-wrap quotient is exactly two, then
it contributes one positive support position and mass two.

Hence for canonical support s:

  positiveCount(qOrd) = s-1,
  sum(qOrd) = n-5+s.

In particular:
* support two: qOrd has exactly one positive entry and its value is n-3;
* support three: qOrd has exactly two positive entries with total n-2.

These formulas are the exact mixed-support boundary-swap shapes.
-/

namespace JSP000404Research

theorem cut_wrap_two_ordinary_shape_of_deficit_three_support
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {t c : ℝ} {n s : ℕ}
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = s)
    (hwrap :
      Nat.floor (a + t - xs.getLastD a) = 2) :
    let qOrd := (successiveDiffsFrom a xs).map Nat.floor
    listPositiveCount qOrd = s - 1 ∧
      qOrd.sum = n - 5 + s := by
  let qOrd := (successiveDiffsFrom a xs).map Nat.floor
  let qWrap := Nat.floor (a + t - xs.getLastD a)

  have hfullSupport :
      listPositiveCount (R.gapQuotients t) = s := by
    have h :=
      R.gapQuotients_positiveCount_eq_canonical hp htpos
    rw [hsupport] at h
    exact h

  have hfullExp :
      listExponent (R.gapQuotients t) = n - 3 := by
    have h := R.exponent_eq_centreExponent hp htpos
    rw [hexp] at h
    exact h

  have hfullSum :
      (R.gapQuotients t).sum = (n - 3) + s := by
    have h :=
      listExponent_add_listPositiveCount
        (R.gapQuotients t)
    rw [hfullExp, hfullSupport] at h
    exact h.symm

  have hdecomp :
      R.gapQuotients t = qOrd ++ [qWrap] := by
    unfold CentreCutRayCycle.gapQuotients
    rw [hvalues]
    simpa [qOrd, qWrap] using
      linearCyclicGapQuotients_cons_decompose t a xs

  have hwrap' : qWrap = 2 := by
    simpa [qWrap] using hwrap
  have hwrapPos :
      listPositiveCount [qWrap] = 1 := by
    rw [hwrap']
    norm_num [listPositiveCount]

  have hqPos :
      listPositiveCount qOrd = s - 1 := by
    rw [hdecomp, listPositiveCount_append, hwrapPos]
      at hfullSupport
    omega

  have hqSum :
      qOrd.sum = n - 5 + s := by
    rw [hdecomp, List.sum_append] at hfullSum
    simp only [List.sum_singleton] at hfullSum
    rw [hwrap'] at hfullSum
    omega

  exact ⟨hqPos, hqSum⟩

/-- Support-two specialization: one positive ordinary quotient, necessarily
equal to n-3, plus the cut-wrap quotient two. -/
theorem cut_wrap_two_support_two_unique_ordinary_eq_n_sub_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {t c : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (hwrap :
      Nat.floor (a + t - xs.getLastD a) = 2) :
    let qOrd := (successiveDiffsFrom a xs).map Nat.floor
    listPositiveCount qOrd = 1 ∧
      qOrd.sum = n - 3 ∧
      (∀ q ∈ qOrd, q ≠ 0 → q = n - 3) := by
  let qOrd := (successiveDiffsFrom a xs).map Nat.floor
  have hshape :=
    cut_wrap_two_ordinary_shape_of_deficit_three_support
      hp hn5 htpos C R hvalues hexp hsupport hwrap
  have hpos : listPositiveCount qOrd = 1 := by
    simpa [qOrd] using hshape.1
  have hsum : qOrd.sum = n - 3 := by
    simpa [qOrd] using hshape.2
  refine ⟨hpos, hsum, ?_⟩
  intro q hq hq0
  have hqsum :=
    list_sum_eq_member_of_positiveCount_one
      qOrd hpos hq hq0
  omega

/-- Support-three specialization: exactly two positive ordinary quotients with
total n-2, plus the cut-wrap quotient two. -/
theorem cut_wrap_two_support_three_ordinary_shape
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {t c : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    {a : ℝ} {xs : List ℝ}
    (hvalues : R.normalizedValues t = a :: xs)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hwrap :
      Nat.floor (a + t - xs.getLastD a) = 2) :
    let qOrd := (successiveDiffsFrom a xs).map Nat.floor
    listPositiveCount qOrd = 2 ∧
      qOrd.sum = n - 2 := by
  simpa using
    cut_wrap_two_ordinary_shape_of_deficit_three_support
      hp hn5 htpos C R hvalues hexp hsupport hwrap

#print axioms cut_wrap_two_ordinary_shape_of_deficit_three_support
#print axioms cut_wrap_two_support_two_unique_ordinary_eq_n_sub_three
#print axioms cut_wrap_two_support_three_ordinary_shape

end JSP000404Research
