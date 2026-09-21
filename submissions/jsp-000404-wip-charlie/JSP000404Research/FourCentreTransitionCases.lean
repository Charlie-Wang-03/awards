import JSP000404Research.HighExponentTransitionPacking
import JSP000404Research.DeficitTwo
import JSP000404Research.SharpDeficit
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Three-centre transition packing consequences

For three distinct high-exponent centres we specialize the global
strict-support transition packing to a Fin 3 family.

This gives the key four-centre sharp-layer reductions:

* a unit-deficit centre contributes transition quotient n;
* a deficit-two/support-one centre contributes n-1;
* therefore two support-one deficit-two centres cannot coexist with one
  unit-deficit centre when n>=3;
* in the mixed support-one/support-two case, the support-two transition
  quotient is forced to be exactly one.

The remaining quotient mass of that support-two centre is consequently n-1.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Pack the transition quotients of three explicitly named distinct centres. -/
theorem three_transition_quotient_sum_le_two_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (certS : HighExponentTransitionIntervalCertificate hp t s Cs)
    (certA : HighExponentTransitionIntervalCertificate hp t a Ca)
    (certB : HighExponentTransitionIntervalCertificate hp t b Cb) :
    certS.qe + certA.qe + certB.qe ≤ 2 * n := by
  let centre : Fin 3 → V := ![s,a,b]
  have hcentre : Function.Injective centre := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [centre] at hxy ⊢
    · exact False.elim (hsa hxy)
    · exact False.elim (hsb hxy)
    · exact False.elim (hsa hxy.symm)
    · exact False.elim (hab hxy)
    · exact False.elim (hsb hxy.symm)
    · exact False.elim (hab hxy.symm)
  let C : ∀ r : Fin 3, CentreProjectiveCycle hp (centre r) :=
    fun r => by
      fin_cases r
      · simpa [centre] using Cs
      · simpa [centre] using Ca
      · simpa [centre] using Cb
  let cert : ∀ r : Fin 3,
      HighExponentTransitionIntervalCertificate hp t (centre r) (C r) :=
    fun r => by
      fin_cases r
      · simpa [centre, C] using certS
      · simpa [centre, C] using certA
      · simpa [centre, C] using certB
  have h :=
    highTransition_quotient_sum_le_two_n
      hp hn hdelta0 hdeltaHalf ht
      centre hcentre C cert
  simpa [cert, C, centre, Fin.sum_univ_succ] using h

/-- Concrete unit deficit forces quotient support one. -/
theorem concrete_unit_deficit_support_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 1) :
    positiveSupport (centreQuotient C t) = 1 := by
  have hsum :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega) hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 1 := by
    rw [← show centreExponent C t =
      floorExcess (centreQuotient C t) by rfl, hexp]
    omega
  exact (unit_deficit_structure
    (centreQuotient C t) n hn hsum hdef).1

/-- Unit-deficit transition quotient is exactly n. -/
theorem unit_deficit_transition_qe_eq_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (cert : HighExponentTransitionIntervalCertificate hp t i C)
    {t delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 1) :
    cert.qe = n := by
  have hs :=
    concrete_unit_deficit_support_one
      C hn hdelta0 hdelta1 ht hexp
  have hq :=
    highTransition_qe_eq_exponent_add_one_of_support_one
      C cert hs
  rw [hexp] at hq
  omega

/-- Deficit-two/support-one transition quotient is exactly n-1. -/
theorem deficit_two_support_one_transition_qe_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (cert : HighExponentTransitionIntervalCertificate hp t i C)
    {n : ℕ}
    (hn : 3 ≤ n)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 1) :
    cert.qe = n - 1 := by
  have hq :=
    highTransition_qe_eq_exponent_add_one_of_support_one
      C cert hsupport
  rw [hexp] at hq
  omega

/-- A sharp/unit-deficit centre cannot coexist with two support-one
deficit-two centres. -/
theorem no_sharp_with_two_support_one_deficit_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (certS : HighExponentTransitionIntervalCertificate hp t s Cs)
    (certA : HighExponentTransitionIntervalCertificate hp t a Ca)
    (certB : HighExponentTransitionIntervalCertificate hp t b Cb)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 1) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have hqS :=
    unit_deficit_transition_qe_eq_n
      Cs certS (by omega) hdelta0 hdelta1 ht hS
  have hqA :=
    deficit_two_support_one_transition_qe_eq
      Ca certA hn hA hsupA
  have hqB :=
    deficit_two_support_one_transition_qe_eq
      Cb certB hn hB hsupB
  have hpack :=
    three_transition_quotient_sum_le_two_n
      hp (by omega) hdelta0 hdeltaHalf ht
      hsa hsb hab Cs Ca Cb certS certA certB
  rw [hqS, hqA, hqB] at hpack
  omega

/-- In the mixed sharp + support-one deficit-two + support-two deficit-two
configuration, transition packing forces the support-two transition quotient
to be exactly one. -/
theorem mixed_deficit_two_transition_qe_eq_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (certS : HighExponentTransitionIntervalCertificate hp t s Cs)
    (certA : HighExponentTransitionIntervalCertificate hp t a Ca)
    (certB : HighExponentTransitionIntervalCertificate hp t b Cb)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1) :
    certB.qe = 1 := by
  have hdelta1 : delta < 1 := by linarith
  have hqS :=
    unit_deficit_transition_qe_eq_n
      Cs certS (by omega) hdelta0 hdelta1 ht hS
  have hqA :=
    deficit_two_support_one_transition_qe_eq
      Ca certA hn hA hsupA
  have hpack :=
    three_transition_quotient_sum_le_two_n
      hp (by omega) hdelta0 hdeltaHalf ht
      hsa hsb hab Cs Ca Cb certS certA certB
  have hqBpos : 1 ≤ certB.qe :=
    Nat.one_le_iff_ne_zero.mpr certB.qe_ne
  rw [hqS, hqA] at hpack
  omega

/-- A list with exactly one positive entry contains its positive sum. -/
theorem list_sum_mem_of_positiveCount_one
    (qs : List ℕ)
    (hsupport : listPositiveCount qs = 1)
    (hsumpos : 0 < qs.sum) :
    qs.sum ∈ qs := by
  induction qs with
  | nil =>
      simp at hsumpos
  | cons q qs ih =>
      by_cases hq : q = 0
      · subst q
        simp only [listPositiveCount, if_pos rfl, zero_add] at hsupport
        simp only [List.sum_cons, zero_add, List.mem_cons]
        right
        exact ih hsupport hsumpos
      · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
        simp only [listPositiveCount, if_neg hq] at hsupport
        have htail0 : listPositiveCount qs = 0 := by omega
        have htailSum :=
          list_sum_eq_zero_of_positiveCount_eq_zero qs htail0
        simp [htailSum, hq]

/-- If exactly two list entries are positive, one of them is 1, and the total
sum is n>=3, then the other positive entry is n-1. -/
theorem n_sub_one_mem_of_positiveCount_two_and_one_mem
    (qs : List ℕ) (n : ℕ)
    (hn : 3 ≤ n)
    (hsupport : listPositiveCount qs = 2)
    (hsum : qs.sum = n)
    (hone : 1 ∈ qs) :
    n - 1 ∈ qs := by
  induction qs with
  | nil =>
      simp at hone
  | cons q qs ih =>
      rw [List.mem_cons] at hone
      by_cases hq0 : q = 0
      · subst q
        simp only [listPositiveCount, if_pos rfl, zero_add] at hsupport
        simp only [List.sum_cons, zero_add] at hsum
        rcases hone with hbad | hone
        · omega
        · exact ih hn hsupport hsum hone
      · simp only [listPositiveCount, if_neg hq0] at hsupport
        have htailSupport : listPositiveCount qs = 1 := by omega
        rcases hone with hq1 | honeTail
        · subst q
          have htailSum : qs.sum = n - 1 := by
            simp only [List.sum_cons] at hsum
            omega
          have htailPos : 0 < qs.sum := by
            rw [htailSum]
            omega
          have hmem :=
            list_sum_mem_of_positiveCount_one
              qs htailSupport htailPos
          rw [htailSum] at hmem
          exact List.mem_cons_of_mem _ hmem
        · have honeOnly :
              qs.sum = 1 := by
            have hsumMem :=
              list_sum_mem_of_positiveCount_one
                qs htailSupport (by
                  have : 0 < qs.sum := by
                    by_contra hzero
                    have hz : qs.sum = 0 := Nat.eq_zero_of_not_pos hzero
                    have hallzero : ∀ x ∈ qs, x = 0 := by
                      intro x hx
                      have hxle : x ≤ qs.sum :=
                        List.single_le_sum (fun _ _ => Nat.zero_le _) hx
                      omega
                    exact (by simpa [hallzero 1 honeTail] using honeTail)
                  exact this)
            have hsumLower : 1 ≤ qs.sum := by
              exact List.le_sum_of_mem honeTail
            have hsupportOne := htailSupport
            -- With one positive entry and 1 present, the whole sum is 1.
            have hsumEq :
                qs.sum = 1 := by
              have hmemsum :=
                list_sum_mem_of_positiveCount_one
                  qs hsupportOne (by omega)
              have huniq :
                  ∀ x ∈ qs, x ≠ 0 → x = 1 := by
                intro x hx hx0
                -- two distinct positive values would force count >=2
                by_contra hx1
                induction qs with
                | nil => simp at hx
                | cons y ys =>
                    simp_all [listPositiveCount]
              exact huniq qs.sum hmemsum (by omega)
            exact hsumEq
          have hqEq : q = n - 1 := by
            simp only [List.sum_cons, honeOnly] at hsum
            omega
          rw [hqEq]
          exact List.mem_cons_self

/-- Mixed four-centre arithmetic: the support-two centre contains a second
positive quotient equal to n-1. -/
theorem mixed_support_two_has_hidden_n_sub_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (cert : HighExponentTransitionIntervalCertificate hp t i C)
    {t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (hqe : cert.qe = 1) :
    n - 1 ∈ quotientList t C.gaps := by
  have hdelta1 : delta < 1 := by linarith
  have hsumBound :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega) hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 2 := by
    rw [← show centreExponent C t =
      floorExcess (centreQuotient C t) by rfl, hexp]
    omega
  have hstruct :=
    deficit_two_structure
      (centreQuotient C t) n hn hsumBound hdef
  have hsumFn : (∑ r, centreQuotient C t r) = n := by
    rcases hstruct with h1 | h2
    · omega
    · exact h2.2
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) = 2 := by
    rw [← centreQuotient_ofFn]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hsumList :
      (quotientList t C.gaps).sum = n := by
    rw [← centreQuotient_sum_eq_list_sum C t]
    exact hsumFn
  have hone :
      1 ∈ quotientList t C.gaps := by
    rw [← hqe]
    exact cert.qe_mem
  exact n_sub_one_mem_of_positiveCount_two_and_one_mem
    (quotientList t C.gaps) n hn
    hsupportList hsumList hone

#print axioms three_transition_quotient_sum_le_two_n
#print axioms concrete_unit_deficit_support_one
#print axioms no_sharp_with_two_support_one_deficit_two
#print axioms mixed_deficit_two_transition_qe_eq_one
#print axioms n_sub_one_mem_of_positiveCount_two_and_one_mem
#print axioms mixed_support_two_has_hidden_n_sub_one

end JSP000404Research
