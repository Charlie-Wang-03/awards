import JSP000404Research.SeparatedSupportTwoThirdStrict
import Mathlib.Tactic

/-!
# Uniform six-or-more-centre exclusion at the one-third endpoint

This strengthens the exactly-six-centre result: the nonreuse budget is
not claimed, but a double-zero sharp-top incident pair is impossible for
*every* finite original-plane configuration containing at least six
centres. The argument uses the full nodup/complete ray cycle, aligned
quotient counts and strict positivity of original Euclidean angles.
-/

namespace JSP000404Research

/-- If both outer quotient entries vanish, and at least three internal
positions have only two positive entries, a zero internal entry exists. -/
theorem middle_zero_of_at_least_three_slots_and_two_positive
    (qFirst qLast : ℕ) (qmid : List ℕ)
    (hmid3 : 3 ≤ qmid.length)
    (hcount : listPositiveCount (qFirst :: qmid ++ [qLast]) = 2)
    (hends : qFirst = 0 ∧ qLast = 0) :
    0 ∈ qmid := by
  have hmidCount : listPositiveCount qmid = 2 := by
    simpa [listPositiveCount_eq_sum_map, List.map_append,
      List.sum_append, hends.1, hends.2] using hcount
  by_contra hnot
  have hnonzero : ∀ q ∈ qmid, q ≠ 0 := by
    intro q hq hq0
    subst q
    exact hnot hq
  have hfull := listPositiveCount_eq_length_of_all_ne_zero qmid hnonzero
  omega

/-- Actual AngleCap excludes simultaneous zero quotient endpoints at
delta=1/3 for any original centre set of size >= 6, under a sharp
top of exponent n-1 and a support-two deficit-three centre. -/
theorem separated_support_two_at_least_six_centres_no_double_zero_at_third
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (Cfam : ∀ v : V, CentreProjectiveCycle hp v)
    (hSixPlus : 6 ≤ Fintype.card V)
    (hn : 5 ≤ n)
    (hthird : delta = (1 : ℝ) / 3)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (Cfam top) t = n - 1)
    {i : V}
    (hit : i ≠ top)
    (hI : centreExponent (Cfam i) t = n - 3)
    (hsupport : positiveSupport (centreQuotient (Cfam i) t) = 2) :
    ∃ (k : ℕ) (r : OtherVertex i) (rest : List (OtherVertex i))
      (qFirst qLast : ℕ) (qmid : List ℕ),
      (Cfam i).rays.rotate k =
        (⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest ∧
      (quotientList t (Cfam i).gaps).rotate k =
        qFirst :: qmid ++ [qLast] ∧
      ¬ (qFirst = 0 ∧ qLast = 0) := by
  have hdelta0 : 0 ≤ delta := by rw [hthird]; norm_num
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  obtain ⟨k, r, rest, qFirst, qLast, qmid,
      hrays, hquot, hmasszero⟩ :=
    separated_support_two_double_zero_at_third_middle_mass_eq_zero
      hp hcap Cfam hn hthird ht hlam top hTop hit hI hsupport
  refine ⟨k, r, rest, qFirst, qLast, qmid, hrays, hquot, ?_⟩
  intro hends
  letI : DecidableEq V := LinearOrder.toDecidableEq
  have hOtherMin : 5 ≤ Fintype.card (OtherVertex i) := by
    change 5 ≤ Fintype.card {v : V // v ≠ i}
    rw [Fintype.card_subtype_compl (fun v : V => v = i)]
    omega
  have hRayCard :
      (Cfam i).rays.length = Fintype.card (OtherVertex i) := by
    have hc := List.toFinset_card_of_nodup (Cfam i).nodup
    have hcompleteCard := congrArg Finset.card (Cfam i).complete
    calc
      (Cfam i).rays.length =
          (Cfam i).rays.toFinset.card := hc.symm
      _ = Fintype.card (OtherVertex i) := by
        simpa using hcompleteCard
  have hRayMin : 5 ≤ (Cfam i).rays.length := by omega
  have hQuotRayLength :
      (quotientList t (Cfam i).gaps).length = (Cfam i).rays.length := by
    rw [quotientList_length, (Cfam i).gaps_length]
  have hRotEq :
      ((quotientList t (Cfam i).gaps).rotate k).length =
        ((Cfam i).rays.rotate k).length := by
    simpa using hQuotRayLength
  rw [hquot, hrays] at hRotEq
  simp only [List.length_cons, List.length_append,
    List.length_singleton, List.length_nil] at hRotEq
  have hRotMin : 5 ≤ ((Cfam i).rays.rotate k).length := by
    simpa using hRayMin
  rw [hrays] at hRotMin
  simp only [List.length_cons] at hRotMin
  have hmidMin : 3 ≤ qmid.length := by omega
  have hmidPosCount :
      listPositiveCount (qFirst :: qmid ++ [qLast]) = 2 := by
    rw [← hquot, listPositiveCount_rotate]
    rw [← centreQuotient_ofFn (Cfam i) t,
        listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  have hzero : 0 ∈ qmid :=
    middle_zero_of_at_least_three_slots_and_two_positive
      qFirst qLast qmid hmidMin hmidPosCount hends
  have hmidLen :
      qmid.length =
        (consecutiveRayAngles (p := p) i r rest).length := by
    rw [consecutiveRayAngles_length]
    omega
  have hrotNodup :
      ((⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest).Nodup := by
    rw [← hrays]
    simpa using (Cfam i).nodup
  have htailNodup : (r :: rest).Nodup :=
    (List.nodup_cons.mp hrotNodup).2
  have hactualPositive :
      ∀ A ∈ consecutiveRayAngles (p := p) i r rest, 0 < A :=
    all_consecutiveRayAngles_pos_of_AngleCap
      hp hcap hlampos i r rest htailNodup
  have hmassPositive :=
    listZeroAngleMass_pos_of_zero_mem_and_angles_pos
      qmid (consecutiveRayAngles (p := p) i r rest)
      hmidLen hactualPositive hzero
  have hmassZero := hmasszero hends
  linarith

#print axioms middle_zero_of_at_least_three_slots_and_two_positive
#print axioms separated_support_two_at_least_six_centres_no_double_zero_at_third

end JSP000404Research
